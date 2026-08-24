//go:build ignore

// Independent oracle: for a fixed (p, l, t), check the Q_i certificate at a
// contiguous range of even-index POSITIONS (matching Lean's evenIndices/drop/take).
// Reports any position where Q_i^k == 1 (the cert would FAIL there in Lean).
// Reuses the exact mulmod/powmod/qi arithmetic from main.go (source of truth).
package main

import (
	"fmt"
	"math/bits"
	"os"
	"strconv"
	"sync"
	"sync/atomic"
)

func mulmod(a, b, m uint64) uint64 {
	hi, lo := bits.Mul64(a, b)
	_, r := bits.Div64(hi%m, lo, m)
	return r
}
func powmod(b, e, m uint64) uint64 {
	if m == 1 {
		return 0
	}
	r := uint64(1)
	b %= m
	for e > 0 {
		if e&1 == 1 {
			r = mulmod(r, b, m)
		}
		b = mulmod(b, b, m)
		e >>= 1
	}
	return r
}
func qi(p, i, l, t, k uint64) uint64 {
	half := (p - 1) / 2
	mod2 := 2 * (l - 1)
	var d uint64
	for a := uint64(1); a <= half; a++ {
		d = (d + powmod(a, p-i, mod2)) % mod2
	}
	e := mulmod(k%mod2, d, mod2)
	exp := (e / 2) % (l - 1)
	tinv := powmod(t, l-2, l)
	pref := powmod(tinv, exp, l)
	prod := uint64(1)
	tk := powmod(t, k, l)
	tkb := uint64(1)
	for b := uint64(1); b <= half; b++ {
		tkb = mulmod(tkb, tk, l)
		base := (tkb + l - 1) % l
		ex := powmod(b, p-1-i, l-1)
		prod = mulmod(prod, powmod(base, ex, l), l)
	}
	return mulmod(pref, prod, l)
}

func main() {
	// args: p l t startPos endPos  (positions into evenIndices; even index = 2*(pos+1))
	p, _ := strconv.ParseUint(os.Args[1], 10, 64)
	l, _ := strconv.ParseUint(os.Args[2], 10, 64)
	t, _ := strconv.ParseUint(os.Args[3], 10, 64)
	start, _ := strconv.ParseUint(os.Args[4], 10, 64)
	end, _ := strconv.ParseUint(os.Args[5], 10, 64) // exclusive
	k := (l - 1) / p
	fmt.Printf("p=%d l=%d t=%d k=%d positions [%d,%d)  (%d indices)\n", p, l, t, k, start, end, end-start)

	var fails int64
	var done int64
	nw := 12
	var wg sync.WaitGroup
	ch := make(chan uint64, 256)
	for w := 0; w < nw; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for pos := range ch {
				i := 2 * (pos + 1) // evenIndices[pos]
				q := qi(p, i, l, t, k)
				qk := powmod(q, k, l)
				if qk == 1 {
					atomic.AddInt64(&fails, 1)
					fmt.Printf("  FAIL at pos=%d  i=%d  (Q_i^k == 1)\n", pos, i)
				}
				n := atomic.AddInt64(&done, 1)
				if n%1000 == 0 {
					fmt.Printf("  ... %d/%d checked, fails=%d\n", n, end-start, atomic.LoadInt64(&fails))
				}
			}
		}()
	}
	for pos := start; pos < end; pos++ {
		ch <- pos
	}
	close(ch)
	wg.Wait()
	fmt.Printf("DONE: %d positions checked, %d FAILURES\n", end-start, fails)
	if fails == 0 {
		fmt.Println("RESULT: certificate VALID over this range (witness fires at every index)")
	} else {
		fmt.Println("RESULT: certificate INVALID — witness genuinely fails")
	}
}
