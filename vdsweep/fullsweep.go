//go:build ignore

// fullsweep: for every prime 5 <= p < maxP, find the least full Vandiver
// witness l = 2Np+1 < p^2-p (t = smallest base with t^k != 1, k = 2N) such
// that Q_i^k != 1 at EVERY even index 2 <= i <= p-3 — i.e. exactly the
// artifact's vandiverCert p l t (evenIndices p) hypothesis.
//
// Fast check (validated against the naive qi below via `selftest`):
// with h = t^k of exact order p in (Z/l)*, define c(y) = dlog_h(y^k) in Z/p,
// a homomorphism. Since t^{kb} = h^b, the factor (t^{kb}-1)^{b^{p-1-i}}
// contributes c_b * b^{p-1-i} with c_b = dlog_h((h^b - 1)^k), and the
// prefactor t^{-k d_i/2} contributes -N*d_i (all mod p). So
//   Q_i^k = 1  <=>  S_i := sum_b c_b b^{p-1-i}  ==  N * D_i (mod p),
// where D_i = sum_a a^{p-i} = sum_a a * a^{p-1-i} mod p. Both S_i and D_i
// are swept over all even i with one incremental pass (w_b *= b^2 per step).
//
// Usage:  go run fullsweep.go selftest
//         go run fullsweep.go sweep <maxP> <workers> <out.csv>
package main

import (
	"bufio"
	"fmt"
	"math/bits"
	"os"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"
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

func firstValidT(l, k uint64) uint64 {
	t := uint64(2)
	for pm(t, k, l) == 1 {
		t++
	}
	return t
}

// ---- naive reference (verbatim port of findwitness.go / QiCertificate.lean) ----

func qiNaive(p, i, l, t, k uint64) uint64 {
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

// ---- fast full check ----

// checkAllFast: true iff Q_i^k != 1 for every even i in [2, p-3].
// Returns (ok, failing i or 0).
func checkAllFast(p, l, t, k, n uint64) (bool, uint64) {
	h := pm(t, k, l) // order exactly p (h != 1 guaranteed by caller)
	// dlog table of the order-p subgroup: value -> exponent
	tbl := make(map[uint64]uint32, p)
	cur := uint64(1)
	for j := uint64(0); j < p; j++ {
		tbl[cur] = uint32(j)
		cur = mm(cur, h, l)
	}
	half := (p - 1) / 2
	// c_b = dlog_h((h^b - 1)^k), b = 1..half
	c := make([]uint64, half+1)
	hb := uint64(1)
	for b := uint64(1); b <= half; b++ {
		hb = mm(hb, h, l)
		x := (hb + l - 1) % l // h^b - 1, nonzero since h has order p > b
		j, ok := tbl[pm(x, k, l)]
		if !ok {
			panic("dlog miss")
		}
		c[b] = uint64(j)
	}
	// incremental sweep over even i descending from p-3 to 2:
	// exponent e = p-1-i runs 2, 4, ..., p-3? (p-1-i for i=p-3 is 2; for i=2 is p-3)
	w := make([]uint64, half+1)   // w_b = b^{p-1-i} mod p
	bsq := make([]uint64, half+1) // b^2 mod p
	for b := uint64(1); b <= half; b++ {
		bsq[b] = b * b % p
		w[b] = bsq[b]
	}
	nModP := n % p
	for i := p - 3; i >= 2; i -= 2 {
		var s, d uint64 // accumulate; terms < 2^34, half < 2^16 => sums < 2^50
		for b := uint64(1); b <= half; b++ {
			s += c[b] * w[b]
			d += b * w[b]
			w[b] = w[b] * bsq[b] % p
		}
		if s%p == mm(nModP, d%p, p) { // S_i == N*D_i (mod p)  <=>  Q_i^k = 1
			return false, i
		}
	}
	return true, 0
}

// findWitness: least valid (l, N, t) for p; also returns candidates tried.
func findWitness(p uint64) (l, n, t, tries uint64, ok bool) {
	limit := p*p - p
	for n = 1; ; n++ {
		l = 2*n*p + 1
		if l >= limit {
			return 0, 0, 0, tries, false
		}
		if !isPrime(l) {
			continue
		}
		tries++
		k := 2 * n
		t = firstValidT(l, k)
		if good, _ := checkAllFast(p, l, t, k, n); good {
			return l, n, t, tries, true
		}
	}
}

func primesBelow(x uint64) []uint64 {
	sieve := make([]bool, x)
	var ps []uint64
	for i := uint64(2); i < x; i++ {
		if !sieve[i] {
			if i >= 5 {
				ps = append(ps, i)
			}
			for j := i * i; j < x; j += i {
				sieve[j] = true
			}
		}
	}
	return ps
}

func selftest() {
	// 1. fast checker verdict == naive verdict, every candidate/index, p < 260
	for _, p := range primesBelow(260) {
		limit := p*p - p
		for n := uint64(1); n <= 40; n++ {
			l := 2*n*p + 1
			if l >= limit || !isPrime(l) {
				continue
			}
			k := 2 * n
			t := firstValidT(l, k)
			fastOK, fastI := checkAllFast(p, l, t, k, n)
			naiveOK, naiveI := true, uint64(0)
			for i := uint64(2); i <= p-3; i += 2 {
				if pm(qiNaive(p, i, l, t, k), k, l) == 1 {
					naiveOK, naiveI = false, i
					break
				}
			}
			_ = naiveI // first-failure index differs by scan order; verdicts must agree
			if fastOK != naiveOK {
				panic(fmt.Sprintf("MISMATCH p=%d l=%d: fast=%v naive=%v", p, l, fastOK, naiveOK))
			}
			if !fastOK && pm(qiNaive(p, fastI, l, t, k), k, l) != 1 {
				panic(fmt.Sprintf("BAD FAIL INDEX p=%d l=%d i=%d", p, l, fastI))
			}
		}
	}
	fmt.Println("selftest 1 ok: fast == naive on every (p, l) candidate, p < 260")
	// 2. artifact anchors must pass with the recorded (l, t)
	anchors := []struct{ p, l, t uint64 }{
		{5, 11, 2}, {7, 29, 2}, {11, 67, 2}, {13, 53, 2}, {37, 149, 2}, {59, 709, 2}, {163, 5869, 2},
	}
	for _, a := range anchors {
		n := (a.l - 1) / (2 * a.p)
		k := 2 * n
		if firstValidT(a.l, k) != a.t {
			panic(fmt.Sprintf("anchor t mismatch p=%d", a.p))
		}
		if ok, i := checkAllFast(a.p, a.l, a.t, k, n); !ok {
			panic(fmt.Sprintf("anchor FAILED p=%d l=%d at i=%d", a.p, a.l, i))
		}
	}
	fmt.Println("selftest 2 ok: artifact anchors (5,7,11,13,37,59,163) all fire")
}

func main() {
	switch os.Args[1] {
	case "selftest":
		selftest()
	case "sweep":
		maxP, _ := strconv.ParseUint(os.Args[2], 10, 64)
		nw, _ := strconv.Atoi(os.Args[3])
		path := os.Args[4]
		// resume: collect primes already recorded
		doneSet := map[uint64]bool{}
		if b, err := os.ReadFile(path); err == nil {
			for _, line := range strings.Split(string(b), "\n") {
				var p, l, n, t, tries uint64
				var oks string
				if c, _ := fmt.Sscanf(line, "%d,%d,%d,%d,%d,%s", &p, &l, &n, &t, &tries, &oks); c == 6 {
					doneSet[p] = true
				}
			}
		}
		out, err := os.OpenFile(path, os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
		if err != nil {
			panic(err)
		}
		defer out.Close()
		w := bufio.NewWriter(out)
		defer w.Flush()
		if len(doneSet) == 0 {
			fmt.Fprintln(w, "p,l,N,t,tries,found")
			w.Flush()
		}
		var ps []uint64
		for _, p := range primesBelow(maxP) {
			if !doneSet[p] {
				ps = append(ps, p)
			}
		}
		fmt.Printf("sweep: %d primes to do (%d already in %s)\n", len(ps), len(doneSet), path)
		// largest first so stragglers start early
		sort.Slice(ps, func(a, b int) bool { return ps[a] > ps[b] })
		var next int64 = -1
		var done, nFail int64
		var maxTries, worst uint64
		var mu sync.Mutex
		start := time.Now()
		var wg sync.WaitGroup
		for wk := 0; wk < nw; wk++ {
			wg.Add(1)
			go func() {
				defer wg.Done()
				for {
					mu.Lock()
					next++
					idx := next
					mu.Unlock()
					if int(idx) >= len(ps) {
						return
					}
					p := ps[idx]
					l, n, t, tries, ok := findWitness(p)
					mu.Lock()
					fmt.Fprintf(w, "%d,%d,%d,%d,%d,%v\n", p, l, n, t, tries, ok)
					done++
					if !ok {
						nFail++
						fmt.Printf("!!! NO WITNESS BELOW BOUND: p=%d\n", p)
					}
					if tries > maxTries {
						maxTries, worst = tries, p
					}
					if done%10 == 0 {
						w.Flush()
					}
					if done%200 == 0 || int(done) == len(ps) {
						fmt.Printf("%d/%d primes, %s elapsed\n", done, len(ps),
							time.Since(start).Round(time.Second))
					}
					mu.Unlock()
				}
			}()
		}
		wg.Wait()
		fmt.Printf("DONE: %d primes this run, %d without witness, max tries %d (at p=%d), %s\n",
			done, nFail, maxTries, worst, time.Since(start).Round(time.Second))
	}
}
