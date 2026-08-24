//go:build ignore

// Find a valid single Vandiver witness l = 2Np+1 for prime p: prime l < p^2-p
// such that Q_i^k != 1 (k=(l-1)/p) at EVERY even index i (source-of-truth qi).
// Tests candidates by increasing N, early-bailing on the first failing index.
package main

import (
	"fmt"
	"math/bits"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
)

func mm(a, b, m uint64) uint64 { hi, lo := bits.Mul64(a, b); _, r := bits.Div64(hi%m, lo, m); return r }
func pm(b, e, m uint64) uint64 {
	if m == 1 {
		return 0
	}
	r := uint64(1)
	b %= m
	for e > 0 {
		if e&1 == 1 {
			r = mm(r, b, m)
		}
		b = mm(b, b, m)
		e >>= 1
	}
	return r
}
func isPrime(n uint64) bool {
	if n < 2 {
		return false
	}
	for _, sp := range []uint64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} {
		if n%sp == 0 {
			return n == sp
		}
	}
	d := n - 1
	s := 0
	for d&1 == 0 {
		d >>= 1
		s++
	}
	for _, a := range []uint64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} {
		x := pm(a, d, n)
		if x == 1 || x == n-1 {
			continue
		}
		ok := false
		for range s - 1 {
			x = mm(x, x, n)
			if x == n-1 {
				ok = true
				break
			}
		}
		if !ok {
			return false
		}
	}
	return true
}
func qi(p, i, l, t, k uint64) uint64 {
	half := (p - 1) / 2
	m2 := 2 * (l - 1)
	var d uint64
	for a := uint64(1); a <= half; a++ {
		d = (d + pm(a, p-i, m2)) % m2
	}
	e := mm(k%m2, d, m2)
	ex := (e / 2) % (l - 1)
	pref := pm(pm(t, l-2, l), ex, l)
	prod := uint64(1)
	tk := pm(t, k, l)
	tkb := uint64(1)
	for b := uint64(1); b <= half; b++ {
		tkb = mm(tkb, tk, l)
		base := (tkb + l - 1) % l
		prod = mm(prod, pm(base, pm(b, p-1-i, l-1), l), l)
	}
	return mm(pref, prod, l)
}
func firstValidT(l, k uint64) uint64 {
	t := uint64(2)
	for pm(t, k, l) == 1 {
		t++
	}
	return t
}

// checkAll returns (ok, failIndex). ok=true means Q_i^k != 1 for all even i.
func checkAll(p, l, t, k uint64, nw int) (bool, uint64) {
	nIdx := (p - 3) / 2 // number of even indices (positions 0..nIdx-1)
	var bad int64 = -1
	var next uint64
	var wg sync.WaitGroup
	for w := 0; w < nw; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for {
				if atomic.LoadInt64(&bad) >= 0 {
					return
				}
				pos := atomic.AddUint64(&next, 1) - 1
				if pos >= nIdx {
					return
				}
				i := 2 * (pos + 1)
				if pm(qi(p, i, l, t, k), k, l) == 1 {
					atomic.CompareAndSwapInt64(&bad, -1, int64(i))
					return
				}
			}
		}()
	}
	wg.Wait()
	if bad >= 0 {
		return false, uint64(bad)
	}
	return true, 0
}

func main() {
	p, _ := strconv.ParseUint(os.Args[1], 10, 64)
	nStart, _ := strconv.ParseUint(os.Args[2], 10, 64)
	nEnd, _ := strconv.ParseUint(os.Args[3], 10, 64)
	nw := 62
	if len(os.Args) > 4 {
		v, _ := strconv.Atoi(os.Args[4])
		nw = v
	}
	limit := p*p - p
	fmt.Printf("searching Vandiver witness for p=%d, N in [%d,%d), l<%d, workers=%d\n", p, nStart, nEnd, limit, nw)
	for N := nStart; N < nEnd; N++ {
		l := 2*N*p + 1
		if l >= limit {
			fmt.Printf("reached l>=%d at N=%d; stop\n", limit, N)
			break
		}
		if !isPrime(l) {
			continue
		}
		k := 2 * N
		t := firstValidT(l, k)
		ok, failI := checkAll(p, l, t, k, nw)
		if ok {
			fmt.Printf("FOUND: l=%d N=%d t=%d k=%d  (Q_i^k != 1 at ALL %d even indices)\n", l, N, t, k, (p-3)/2)
			return
		}
		fmt.Printf("  N=%d l=%d t=%d: FAIL at i=%d\n", N, l, t, failI)
	}
	fmt.Println("no witness found in range")
}
