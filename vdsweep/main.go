// vdsweep: witness census for the Q_i / vandiverCert test (Washington Cor 8.19)
// at scale — the Vandiver-side companion of sgsweep and grascheck.
//
// Go port of ~/vandiver/vandiver_probe/witness_census.py (qi_fast is the
// source of truth for the Q_i formula; see QiCertificate.lean for the Lean
// form). For every irregular pair (p, i) from the input pair file and each of
// the first nL primes l = m*p + 1 (any m, base t = smallest with t^k != 1,
// k = m), it records WHICH p-th root of unity Q_i^k lands on: the discrete log
// u in [0, p) of Q_i^k base t^k (BSGS in the order-p subgroup). u = 0 means
// Q_i^k = 1 — the witness FAILS at this l (a ~1/p Chebotarev event); u > 0
// means the certificate fires. The heuristic under test: u is uniform on
// [0, p), so failures are 1/p per cell and never persistent (persistent
// failure at every l = genuine Vandiver counterexample at (p, i)).
//
// Exponent care (mirrors qi_fast): d = Σ_{a≤(p-1)/2} a^{p-i} is computed mod
// 2(l-1); e = k·d mod 2(l-1) has the parity of k·d, so exp = (e/2) mod (l-1)
// is (k·d)/2 mod (l-1) exactly. The artifact's vandiverCert additionally
// requires 2 | k; rows with even m are that exact subset (filter in analysis).
//
// Input:  pair file, lines "p i" (e.g. grascheck/pairs_100k.txt).
// Output: CSV "p,i,m,l,t,u" per cell (u = 0 iff FAIL), stderr progress,
//         trailing "# DONE ..." summary line on stderr.
//
// Self-tests at startup: the artifact anchor (p=37, i=32, l=149, t=2 must
// fire) and a t-invariance re-check every tCheckStride cells.
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
	"sync/atomic"
	"time"
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

// Deterministic Miller-Rabin, valid for n < 3.3e24 with these bases
// (we only need n < ~2^50).
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
		x := powmod(a, d, n)
		if x == 1 || x == n-1 {
			continue
		}
		ok := false
		for range s - 1 {
			x = mulmod(x, x, n)
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

// qi computes Q_i mod l per qi_fast (witness_census.py).
func qi(p, i, l, t, k uint64) uint64 {
	half := (p - 1) / 2
	mod2 := 2 * (l - 1)
	var d uint64
	for a := uint64(1); a <= half; a++ {
		d = (d + powmod(a, p-i, mod2)) % mod2
	}
	e := mulmod(k%mod2, d, mod2) // k*d mod 2(l-1); parity of k*d preserved
	exp := (e / 2) % (l - 1)     // (k*d)/2 mod (l-1)
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

func firstValidT(l, k uint64) uint64 {
	t := uint64(2)
	for powmod(t, k, l) == 1 {
		t++
	}
	return t
}

// dlogOrderP: u in [0, p) with x = h^u, where h has exact order p mod l.
// Baby-step giant-step. Panics on failure (x outside <h> would be a bug).
func dlogOrderP(x, h, p, l uint64) uint64 {
	if x == 1 {
		return 0
	}
	mSteps := uint64(1)
	for mSteps*mSteps < p {
		mSteps++
	}
	baby := make(map[uint64]uint64, mSteps)
	cur := uint64(1)
	for j := uint64(0); j < mSteps; j++ {
		if _, dup := baby[cur]; !dup {
			baby[cur] = j
		}
		cur = mulmod(cur, h, l)
	}
	// factor = h^{-mSteps}
	factor := powmod(powmod(h, l-2, l), mSteps, l)
	gamma := x
	for iStep := uint64(0); iStep <= mSteps; iStep++ {
		if j, ok := baby[gamma]; ok {
			return (iStep*mSteps + j) % p
		}
		gamma = mulmod(gamma, factor, l)
	}
	panic(fmt.Sprintf("dlog failure: x=%d h=%d p=%d l=%d", x, h, p, l))
}

type pairGroup struct {
	p   uint64
	irr []uint64
}

type cellRow struct {
	p, i, m, l, t, u uint64
}

const tCheckStride = 997

func main() {
	pairFile := flag.String("pairs", "", "pair file: lines \"p i\"")
	nL := flag.Int("nl", 100, "number of auxiliary primes l per pair")
	maxP := flag.Uint64("maxp", 1<<62, "skip pairs with p > maxp")
	out := flag.String("o", "vdsweep.csv", "output CSV")
	workers := flag.Int("w", runtime.NumCPU()-2, "worker goroutines")
	flag.Parse()
	if *pairFile == "" {
		fmt.Fprintln(os.Stderr, "usage: vdsweep -pairs pairs.txt [-nl N] [-maxp P] [-o out.csv]")
		os.Exit(2)
	}

	// Self-test: the artifact anchor p=37, l=149 (k=4, t=2 valid), irr=[32];
	// vandiverCert fires there (QiCertificate.lean), so Q_32^4 != 1.
	{
		q := qi(37, 32, 149, 2, 4)
		if powmod(q, 4, 149) == 1 {
			panic("self-test failed: (37,32,149) must fire")
		}
		u := dlogOrderP(powmod(q, 4, 149), powmod(2, 4, 149), 37, 149)
		if u == 0 || powmod(powmod(2, 4, 149), u, 149) != powmod(q, 4, 149) {
			panic("self-test failed: dlog inconsistent at (37,32,149)")
		}
	}

	// Read and group pairs by p.
	f, err := os.Open(*pairFile)
	if err != nil {
		panic(err)
	}
	byP := map[uint64][]uint64{}
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		var p, i uint64
		if n, _ := fmt.Sscan(sc.Text(), &p, &i); n == 2 && p <= *maxP {
			byP[p] = append(byP[p], i)
		}
	}
	f.Close()
	var groups []pairGroup
	for p, irr := range byP {
		sort.Slice(irr, func(a, b int) bool { return irr[a] < irr[b] })
		groups = append(groups, pairGroup{p, irr})
	}
	sort.Slice(groups, func(a, b int) bool { return groups[a].p < groups[b].p })
	nPairs := 0
	for _, g := range groups {
		nPairs += len(g.irr)
	}
	fmt.Fprintf(os.Stderr, "# %d pairs (%d primes), nl=%d, workers=%d\n",
		nPairs, len(groups), *nL, *workers)

	of, err := os.Create(*out)
	if err != nil {
		panic(err)
	}
	w := bufio.NewWriterSize(of, 1<<20)
	fmt.Fprintln(w, "p,i,m,l,t,u")
	var wMu sync.Mutex

	var cells, fails, tviol, done atomic.Uint64
	start := time.Now()
	jobs := make(chan pairGroup)
	var wg sync.WaitGroup
	for range max(*workers, 1) {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for g := range jobs {
				rows := make([]cellRow, 0, len(g.irr)**nL)
				tested := 0
				for m := uint64(1); tested < *nL; m++ {
					l := m*g.p + 1
					if !isPrime(l) {
						continue
					}
					tested++
					k := m
					t := firstValidT(l, k)
					h := powmod(t, k, l)
					for _, i := range g.irr {
						q := qi(g.p, i, l, t, k)
						x := powmod(q, k, l)
						u := dlogOrderP(x, h, g.p, l)
						if u == 0 {
							fails.Add(1)
						}
						n := cells.Add(1)
						if n%tCheckStride == 0 { // t-invariance spot check
							t2 := t + 1
							for powmod(t2, k, l) == 1 {
								t2++
							}
							q2 := qi(g.p, i, l, t2, k)
							if (powmod(q2, k, l) == 1) != (u == 0) {
								tviol.Add(1)
								fmt.Fprintf(os.Stderr, "# TCHECK-VIOLATION p=%d i=%d l=%d t=%d t2=%d\n",
									g.p, i, l, t, t2)
							}
						}
						rows = append(rows, cellRow{g.p, i, m, l, t, u})
					}
				}
				wMu.Lock()
				for _, r := range rows {
					fmt.Fprintf(w, "%d,%d,%d,%d,%d,%d\n", r.p, r.i, r.m, r.l, r.t, r.u)
				}
				wMu.Unlock()
				if d := done.Add(uint64(len(g.irr))); d%500 < uint64(len(g.irr)) {
					fmt.Fprintf(os.Stderr, "# %d/%d pairs, %d fails, %s\n",
						d, nPairs, fails.Load(), time.Since(start).Round(time.Second))
				}
			}
		}()
	}
	for _, g := range groups {
		jobs <- g
	}
	close(jobs)
	wg.Wait()
	wMu.Lock()
	w.Flush()
	of.Close()
	wMu.Unlock()
	fmt.Fprintf(os.Stderr, "# DONE pairs=%d cells=%d fails=%d tviol=%d elapsed=%s\n",
		nPairs, cells.Load(), fails.Load(), tviol.Load(), time.Since(start).Round(time.Second))
}
