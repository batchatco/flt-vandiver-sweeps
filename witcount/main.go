// witcount: for every prime 5 <= p < maxP, count the full Vandiver witnesses
// l = kp+1 (k even, p does not divide k, all even Q_i^k != 1, t = least valid base)
// in two windows:
//
//	old budget   l < p^2 - p            <=> k <= p-3
//	bad-cert     2l <= 3p^2 - 5p + 2    <=> k <= (3p-5)/2  (Bad(p,l) = {} proved there)
//
// The Q_i test is the dlog-table check of playground/vdsweep/fullsweep.go
// (validated there against the naive QiCertificate port and the artifact anchors).
//
// Usage: go run . <maxP> <workers> <out.csv> [<fullwitness.csv for cross-check>]
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
func checkAllFast(p, l, t, k, n uint64) bool {
	h := pm(t, k, l)
	tbl := make(map[uint64]uint32, p)
	cur := uint64(1)
	for j := range p {
		tbl[cur] = uint32(j)
		cur = mm(cur, h, l)
	}
	half := (p - 1) / 2
	c := make([]uint64, half+1)
	hb := uint64(1)
	for b := uint64(1); b <= half; b++ {
		hb = mm(hb, h, l)
		x := (hb + l - 1) % l
		j, ok := tbl[pm(x, k, l)]
		if !ok {
			panic("dlog miss")
		}
		c[b] = uint64(j)
	}
	w := make([]uint64, half+1)
	bsq := make([]uint64, half+1)
	for b := uint64(1); b <= half; b++ {
		bsq[b] = b * b % p
		w[b] = bsq[b]
	}
	nModP := n % p
	for i := p - 3; i >= 2; i -= 2 {
		var s, d uint64
		for b := uint64(1); b <= half; b++ {
			s += c[b] * w[b]
			d += b * w[b]
			w[b] = w[b] * bsq[b] % p
		}
		if s%p == mm(nModP, d%p, p) {
			return false
		}
	}
	return true
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

type row struct {
	p, candOld, witOld, candBad, witBad, firstL, firstLBad uint64
	sgOld, sgBad, jointOld, jointBad, firstJoint, sgNonWit uint64
	witListBad, jointListBad                               []uint64
}

// sgPass: the artifact's sgCert: no a with a and a+1 both nonzero p-th powers
// mod l, and p itself not a p-th power mod l. H = <g^p> for a primitive root g.
func sgPass(p, l, k uint64) bool {
	// prime factors of l-1 = k*p
	var fs []uint64
	m := k
	for q := uint64(2); q*q <= m; q++ {
		if m%q == 0 {
			fs = append(fs, q)
			for m%q == 0 {
				m /= q
			}
		}
	}
	if m > 1 {
		fs = append(fs, m)
	}
	fs = append(fs, p)
	var g uint64
	for g = 2; ; g++ {
		ok := true
		for _, q := range fs {
			if pm(g, (l-1)/q, l) == 1 {
				ok = false
				break
			}
		}
		if ok {
			break
		}
	}
	if pm(p, k, l) == 1 { // p is a p-th power mod l  <=>  p^k = 1
		return false
	}
	h := pm(g, p, l)
	H := make(map[uint64]struct{}, k)
	cur := uint64(1)
	for range k {
		H[cur] = struct{}{}
		cur = mm(cur, h, l)
	}
	if uint64(len(H)) != k {
		panic("subgroup size")
	}
	for a := range H {
		if _, ok := H[(a+1)%l]; ok {
			return false
		}
	}
	return true
}

func count(p uint64) row {
	r := row{p: p}
	kBad := (3*p - 5) / 2
	for k := uint64(2); k <= kBad; k += 2 {
		if k%p == 0 {
			continue
		}
		l := k*p + 1
		if !isPrime(l) {
			continue
		}
		old := k <= p-3
		r.candBad++
		if old {
			r.candOld++
		}
		t := firstValidT(l, k)
		sg := sgPass(p, l, k)
		if sg {
			r.sgBad++
			if old {
				r.sgOld++
			}
		}
		wit := checkAllFast(p, l, t, k, k/2)
		if sg && !wit {
			r.sgNonWit++
		}
		if wit && sg {
			r.jointBad++
			r.jointListBad = append(r.jointListBad, l)
			if r.firstJoint == 0 {
				r.firstJoint = l
			}
			if old {
				r.jointOld++
			}
		}
		if wit {
			r.witBad++
			r.witListBad = append(r.witListBad, l)
			if r.firstLBad == 0 {
				r.firstLBad = l
			}
			if old {
				r.witOld++
				if r.firstL == 0 {
					r.firstL = l
				}
			}
		}
	}
	return r
}

func main() {
	maxP, _ := strconv.ParseUint(os.Args[1], 10, 64)
	nw, _ := strconv.Atoi(os.Args[2])
	out, err := os.Create(os.Args[3])
	if err != nil {
		panic(err)
	}
	defer out.Close()
	known := map[uint64]uint64{}
	if len(os.Args) > 4 {
		b, _ := os.ReadFile(os.Args[4])
		for _, line := range strings.Split(string(b), "\n") {
			f := strings.Split(line, ",")
			if len(f) >= 2 {
				p, e1 := strconv.ParseUint(f[0], 10, 64)
				l, e2 := strconv.ParseUint(f[1], 10, 64)
				if e1 == nil && e2 == nil {
					known[p] = l
				}
			}
		}
	}
	ps := primesBelow(maxP)
	rows := make([]row, len(ps))
	var next int64 = -1
	var mu sync.Mutex
	var wg sync.WaitGroup
	for range nw {
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
				rows[idx] = count(ps[idx])
			}
		}()
	}
	wg.Wait()
	w := bufio.NewWriter(out)
	defer w.Flush()
	fmt.Fprintln(w, "p,cand_old,wit_old,sg_old,joint_old,cand_bad,wit_bad,sg_bad,joint_bad,sg_among_nonwit_bad,first_l_old,first_l_bad,first_joint_bad,witnesses_bad,joint_bad_list")
	mismatch := 0
	var minOld, minBad = ^uint64(0), ^uint64(0)
	var argOld, argBad uint64
	for _, r := range rows {
		ls := make([]string, len(r.witListBad))
		for i, l := range r.witListBad {
			ls[i] = strconv.FormatUint(l, 10)
		}
		js := make([]string, len(r.jointListBad))
		for i, l := range r.jointListBad {
			js[i] = strconv.FormatUint(l, 10)
		}
		fmt.Fprintf(w, "%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%d,%s,%s\n", r.p, r.candOld, r.witOld, r.sgOld, r.jointOld, r.candBad, r.witBad, r.sgBad, r.jointBad, r.sgNonWit, r.firstL, r.firstLBad, r.firstJoint, strings.Join(ls, " "), strings.Join(js, " "))
		if l, ok := known[r.p]; ok && l != r.firstL {
			mismatch++
			fmt.Printf("CROSS-CHECK MISMATCH p=%d: fullsweep %d vs here %d\n", r.p, l, r.firstL)
		}
		if r.witOld < minOld {
			minOld, argOld = r.witOld, r.p
		}
		if r.witBad < minBad {
			minBad, argBad = r.witBad, r.p
		}
	}
	sort.Slice(rows, func(a, b int) bool { return rows[a].witBad < rows[b].witBad })
	fmt.Printf("primes: %d (5 <= p < %d); cross-checked first witnesses: %d, mismatches: %d\n", len(ps), maxP, len(known), mismatch)
	fmt.Printf("min witnesses in old budget: %d at p=%d; min in bad-cert bound: %d at p=%d\n", minOld, argOld, minBad, argBad)
	fmt.Println("lowest bad-cert counts:")
	for i := 0; i < 12 && i < len(rows); i++ {
		r := rows[i]
		fmt.Printf("  p=%d old %d/%d bad %d/%d first_old=%d first_bad=%d\n", r.p, r.witOld, r.candOld, r.witBad, r.candBad, r.firstL, r.firstLBad)
	}
}
