#!/usr/bin/env python3
"""Statistics for the Vandiver/depth certificate sweeps.

Depth (Gras digit) input: grascheck output lines "p i a1 G" — G is the second
p-adic digit of L_p(1, ω^i) (G = 0 ⟺ depth anomaly ⟺ hypothesis (2) of C4
fails at p, non-retryably); a1 is the λ-defect check digit (a1 = 0 ⟺ λ > 1).

Witness (Q_i census) input: vdsweep CSV "p,i,m,l,t,u" — u is the p-th root of
unity index Q_i^k lands on (u = 0 ⟺ witness fails at this l, a ~1/p event).

For each digit we test uniformity on [0,1) via a χ² over NBINS equal bins of
the normalized value (digit/p), report zero counts against the Σ 1/p
expectation, and give the resulting failure-probability calibration.
"""

import csv
import math
import sys

NBINS = 20


def chi2_uniform(vals01):
    n = len(vals01)
    exp = n / NBINS
    obs = [0] * NBINS
    for v in vals01:
        obs[min(int(v * NBINS), NBINS - 1)] += 1
    x2 = sum((o - exp) ** 2 / exp for o in obs)
    return x2, NBINS - 1, obs


def chi2_pvalue(x2, dof):
    # survival function of chi² via the regularized upper incomplete gamma,
    # series/continued-fraction free approximation good enough for reporting:
    # use Wilson–Hilferty cube-root normal approximation.
    z = ((x2 / dof) ** (1 / 3) - (1 - 2 / (9 * dof))) / math.sqrt(2 / (9 * dof))
    return 0.5 * math.erfc(z / math.sqrt(2))


def report_digit(name, rows, digit_ix):
    """rows: list of (p, i, a1, G) ints; digit_ix 2 for a1, 3 for G."""
    vals, zeros, exp_zero = [], [], 0.0
    min_u, min_row = 2.0, None
    for r in rows:
        p, d = r[0], r[digit_ix]
        exp_zero += 1 / p
        if d == 0:
            zeros.append(r)
        else:
            u = d / p
            vals.append(u)
            if u < min_u:
                min_u, min_row = u, r
    x2, dof, _ = chi2_uniform(vals)
    pv = chi2_pvalue(x2, dof)
    print(f"[{name}] pairs={len(rows)} zeros={len(zeros)} "
          f"(expected {exp_zero:.2f} under 1/p model)")
    print(f"  chi2({dof}) = {x2:.1f}, p-value ~ {pv:.3f} "
          f"({'consistent with uniform' if pv > 0.01 else 'NOT uniform'})")
    print(f"  closest call: digit/p = {min_u:.2e} at (p={min_row[0]}, i={min_row[1]})")
    for z in zeros[:10]:
        print(f"  ZERO: p={z[0]} i={z[1]}")
    return exp_zero


def load_gras(paths):
    rows, seen = [], set()
    for path in paths:
        with open(path) as f:
            for line in f:
                if line.startswith("#") or not line.strip():
                    continue
                parts = line.split()
                if len(parts) < 4 or not parts[0].isdigit():
                    continue
                key = (int(parts[0]), int(parts[1]))
                if key in seen:
                    continue
                seen.add(key)
                rows.append(tuple(int(x) for x in parts[:4]))
    return rows


def witness_stats(csv_path):
    vals, cells, fails, exp_fails = [], 0, [], 0.0
    fails_even_k, cells_even_k, exp_even = 0, 0, 0.0
    by_pair = {}
    with open(csv_path) as f:
        for row in csv.DictReader(f):
            p, i, m, u = int(row["p"]), int(row["i"]), int(row["m"]), int(row["u"])
            cells += 1
            exp_fails += 1 / p
            if m % 2 == 0:
                cells_even_k += 1
                exp_even += 1 / p
            if u == 0:
                fails.append((p, i, m, int(row["l"])))
                by_pair[(p, i)] = by_pair.get((p, i), 0) + 1
                if m % 2 == 0:
                    fails_even_k += 1
            else:
                vals.append(u / p)
    x2, dof, _ = chi2_uniform(vals)
    pv = chi2_pvalue(x2, dof)
    print(f"[witness] cells={cells} fails={len(fails)} "
          f"(expected {exp_fails:.2f} under 1/p model)")
    print(f"  even-k (artifact-exact) subset: cells={cells_even_k} "
          f"fails={fails_even_k} (expected {exp_even:.2f})")
    print(f"  landing-index chi2({dof}) = {x2:.1f}, p-value ~ {pv:.3f} "
          f"({'consistent with uniform' if pv > 0.01 else 'NOT uniform'})")
    multi = {k: v for k, v in by_pair.items() if v > 1}
    print(f"  pairs with >1 failure: {len(multi)} {sorted(multi.items())[:8]}")
    worst = sorted(fails)[:12]
    print(f"  first failures (p,i,m,l): {worst}")


if __name__ == "__main__":
    gras_paths = [a for a in sys.argv[1:] if not a.endswith(".csv")]
    csv_paths = [a for a in sys.argv[1:] if a.endswith(".csv")]
    if gras_paths:
        rows = load_gras(gras_paths)
        report_digit("depth digit G = L_p(1,ω^i)/p mod p", rows, 3)
        report_digit("λ-defect digit a1", rows, 2)
    for c in csv_paths:
        witness_stats(c)
