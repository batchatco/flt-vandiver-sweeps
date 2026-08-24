// sgsweep: for every odd prime p up to a limit, find the smallest k such that
// q = 2kp+1 is prime and the Sophie Germain / Legendre auxiliary conditions hold:
//
//	(A) no three nonzero p-th power residues mod q sum to 0, and
//	(B) p is not a p-th power residue mod q.
//
// These are the same conditions as the flt-vandiver artifact's sgCert (which
// states (A) as "for all a, b in S, -(a+b) is not in S"). The p-th power
// residues mod q form the subgroup S of order 2k in (Z/q)*, so both checks are
// cheap: enumerate S as powers of an order-2k element and do O((2k)^2) set
// lookups. Membership in S is x^(2k) == 1 (mod q).
//
// Values of k divisible by 3 are skipped: Wendt's determinant W_{2k} vanishes
// iff 3 | 2k, so condition (A) provably fails there.
//
// Output: CSV rows "p,k,q" (smallest working k per p) plus a summary with the
// k histogram and the record-holders. Any prime exceeding -maxk is reported as
// a FAILURE — none is expected; one would be a counterexample candidate for
// the Landau existence question and worth immediate attention.
package main

import (
	"bufio"
	"flag"
	"fmt"
	"math/bits"
	"os"
	"runtime"
	"sort"
	"sync"
)

// mulmod computes a*b mod m for a, b < m < 2^63 using the 128-bit product.
func mulmod(a, b, m uint64) uint64 {
	hi, lo := bits.Mul64(a, b)
	_, rem := bits.Div64(hi, lo, m)
	return rem
}

// powmod computes a^e mod m.
func powmod(a, e, m uint64) uint64 {
	result := uint64(1)
	a %= m
	for e > 0 {
		if e&1 == 1 {
			result = mulmod(result, a, m)
		}
		a = mulmod(a, a, m)
		e >>= 1
	}
	return result
}

// mrBases is deterministic for all n < 3.3 * 10^24.
var mrBases = []uint64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}

// isPrime is a deterministic Miller-Rabin test for 64-bit n.
func isPrime(n uint64) bool {
	if n < 2 {
		return false
	}
	for _, small := range []uint64{2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37} {
		if n%small == 0 {
			return n == small
		}
	}
	d := n - 1
	r := 0
	for d&1 == 0 {
		d >>= 1
		r++
	}
witness:
	for _, a := range mrBases {
		x := powmod(a, d, n)
		if x == 1 || x == n-1 {
			continue
		}
		for range r - 1 {
			x = mulmod(x, x, n)
			if x == n-1 {
				continue witness
			}
		}
		return false
	}
	return true
}

// primeFactors returns the distinct prime factors of n by trial division
// (n here is at most 2*maxk, so this is cheap).
func primeFactors(n uint64) []uint64 {
	var fs []uint64
	for d := uint64(2); d*d <= n; d++ {
		if n%d == 0 {
			fs = append(fs, d)
			for n%d == 0 {
				n /= d
			}
		}
	}
	if n > 1 {
		fs = append(fs, n)
	}
	return fs
}

// subgroupGen returns an element of exact order 2k in (Z/q)*, where q = 2kp+1,
// by taking p-th powers of successive bases and checking the order. Returns 0
// if none is found (practically impossible; the subgroup is cyclic of order 2k).
func subgroupGen(p, k, q uint64, kFactors []uint64) uint64 {
	order := 2 * k
	for base := uint64(2); base < 2+256; base++ {
		h := powmod(base, p, q)
		if h == 1 {
			continue
		}
		ok := true
		for _, r := range append([]uint64{2}, kFactors...) {
			if powmod(h, order/r, q) == 1 {
				ok = false
				break
			}
		}
		if ok {
			return h
		}
	}
	return 0
}

// checkQ tests conditions (A) and (B) for q = 2kp+1 (q already known prime).
func checkQ(p, k, q uint64, kFactors []uint64) bool {
	order := 2 * k
	// Condition (B): p is a p-th power residue iff p^(2k) == 1 (mod q).
	if powmod(p, order, q) == 1 {
		return false
	}
	h := subgroupGen(p, k, q, kFactors)
	if h == 0 {
		return false // could not exhibit the subgroup; treat as failure to certify
	}
	// Enumerate S = <h>, the nonzero p-th power residues.
	s := make([]uint64, 0, order)
	elem := uint64(1)
	inS := make(map[uint64]struct{}, order)
	for range order {
		s = append(s, elem)
		inS[elem] = struct{}{}
		elem = mulmod(elem, h, q)
	}
	// Condition (A): for all a, b in S, -(a+b) mod q must not lie in S.
	for _, a := range s {
		for _, b := range s {
			sum := a + b
			if sum >= q {
				sum -= q
			}
			neg := q - sum
			if neg == q {
				neg = 0
			}
			if _, bad := inS[neg]; bad {
				return false
			}
		}
	}
	return true
}

// smallestK returns the least valid k for p, or 0 if none up to maxk works.
func smallestK(p uint64, maxk uint64) (k, q uint64) {
	for k = 1; k <= maxk; k++ {
		if k%3 == 0 {
			continue // Wendt: W_{2k} = 0 when 3 | 2k, condition (A) cannot hold
		}
		q = 2*k*p + 1
		if !isPrime(q) {
			continue
		}
		if checkQ(p, k, q, primeFactors(k)) {
			return k, q
		}
	}
	return 0, 0
}

// sieve returns all primes in [5, limit], using a bitset (limit/8 bytes).
func sieve(limit uint64) []uint64 {
	words := make([]uint64, limit/64+1)
	isComposite := func(n uint64) bool { return words[n/64]&(1<<(n%64)) != 0 }
	mark := func(n uint64) { words[n/64] |= 1 << (n % 64) }
	var primes []uint64
	for n := uint64(2); n <= limit; n++ {
		if isComposite(n) {
			continue
		}
		if n >= 5 {
			primes = append(primes, n)
		}
		if n <= limit/n {
			for m := n * n; m <= limit; m += n {
				mark(m)
			}
		}
	}
	return primes
}

type result struct {
	p, k, q uint64
}

func main() {
	limit := flag.Uint64("limit", 1_000_000, "sweep all odd primes p <= limit (p >= 5)")
	maxk := flag.Uint64("maxk", 100_000, "give up (and report FAILURE) past this k")
	workers := flag.Int("workers", runtime.NumCPU(), "parallel workers")
	out := flag.String("out", "sgsweep.csv", "output CSV path")
	single := flag.Uint64("p", 0, "test a single prime p instead of sweeping")
	flag.Parse()

	if *single != 0 {
		k, q := smallestK(*single, *maxk)
		if k == 0 {
			fmt.Printf("FAILURE: no auxiliary prime found for p=%d with k <= %d\n", *single, *maxk)
			os.Exit(1)
		}
		fmt.Printf("p=%d k=%d q=%d (q = %d*p+1)\n", *single, k, q, 2*k)
		return
	}

	primes := sieve(*limit)
	fmt.Fprintf(os.Stderr, "sweeping %d primes in [5, %d] with %d workers\n",
		len(primes), *limit, *workers)

	const blockSize = 1 << 16
	nBlocks := (len(primes) + blockSize - 1) / blockSize

	jobs := make(chan int, 64)
	type block struct {
		idx int
		res []result
	}
	blocks := make(chan block, 64)
	var wg sync.WaitGroup
	for range *workers {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for idx := range jobs {
				lo := idx * blockSize
				hi := min(lo+blockSize, len(primes))
				res := make([]result, 0, hi-lo)
				for _, p := range primes[lo:hi] {
					k, q := smallestK(p, *maxk)
					res = append(res, result{p, k, q})
				}
				blocks <- block{idx, res}
			}
		}()
	}
	go func() {
		for idx := range nBlocks {
			jobs <- idx
		}
		close(jobs)
		wg.Wait()
		close(blocks)
	}()

	f, err := os.Create(*out)
	if err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	w := bufio.NewWriterSize(f, 1<<20)
	fmt.Fprintln(w, "p,k,q")

	// Streaming statistics.
	hist := map[uint64]int{}
	var failures []uint64
	var maxK result
	var sumK, count uint64
	type decade struct {
		count, sumK, maxK uint64
	}
	decades := map[int]*decade{}

	pending := map[int][]result{}
	next := 0
	emit := func(res []result) {
		for _, r := range res {
			if r.k == 0 {
				failures = append(failures, r.p)
				fmt.Fprintf(os.Stderr, "FAILURE: p=%d has no auxiliary prime with k <= %d\n", r.p, *maxk)
				continue
			}
			fmt.Fprintf(w, "%d,%d,%d\n", r.p, r.k, r.q)
			hist[r.k]++
			sumK += r.k
			count++
			if r.k > maxK.k {
				maxK = r
			}
			d := len(fmt.Sprintf("%d", r.p)) - 1 // decade = digits-1
			dc := decades[d]
			if dc == nil {
				dc = &decade{}
				decades[d] = dc
			}
			dc.count++
			dc.sumK += r.k
			if r.k > dc.maxK {
				dc.maxK = r.k
			}
		}
	}
	for b := range blocks {
		pending[b.idx] = b.res
		for {
			res, ok := pending[next]
			if !ok {
				break
			}
			emit(res)
			delete(pending, next)
			next++
			if next%64 == 0 {
				fmt.Fprintf(os.Stderr, "  %.1f%% (%d/%d blocks)\n",
					100*float64(next)/float64(nBlocks), next, nBlocks)
			}
		}
	}
	w.Flush()
	f.Close()

	fmt.Printf("primes swept:   %d\n", count)
	fmt.Printf("failures:       %d %v\n", len(failures), failures)
	fmt.Printf("mean k:         %.2f\n", float64(sumK)/float64(count))
	fmt.Printf("max k:          %d (at p=%d, q=%d)\n", maxK.k, maxK.p, maxK.q)
	fmt.Println("decade table (10^d..10^(d+1): count, mean k, max k):")
	var ds []int
	for d := range decades {
		ds = append(ds, d)
	}
	sort.Ints(ds)
	for _, d := range ds {
		dc := decades[d]
		fmt.Printf("  10^%d: %10d  mean_k=%6.2f  max_k=%d\n",
			d, dc.count, float64(dc.sumK)/float64(dc.count), dc.maxK)
	}
	var ks []uint64
	for k := range hist {
		ks = append(ks, k)
	}
	sort.Slice(ks, func(i, j int) bool { return ks[i] < ks[j] })
	fmt.Println("k histogram (k <= 20 and any k with >= 0.1% share):")
	for _, k := range ks {
		if hist[k] >= int(count/1000) || k <= 20 {
			fmt.Printf("  %4d: %d\n", k, hist[k])
		}
	}
	fmt.Printf("output: %s\n", *out)
}
