# vdsweep — witness census for the Q_i/Vandiver certificate

The Vandiver-side companion of `sgsweep` (Sophie Germain auxiliary primes) and
`~/vandiver/grascheck` (depth/Gras digit): together they measure how fragile
each of the three hypotheses of the paper's reduction theorem (C4) is.

## What it measures

For every irregular pair `(p, i)` and each of the first `-nl` primes
`l = m·p + 1`: compute `Q_i` (Washington Cor 8.19; formula ported verbatim
from `~/vandiver/vandiver_probe/witness_census.py::qi_fast`, the validated
reference for `QiCertificate.lean`'s `vandiverCert`), take `x = Q_i^k` with
`k = m`, and record the discrete log `u ∈ [0, p)` of `x` base `t^k` (BSGS in
the order-`p` subgroup; `t` = smallest base with `t^k ≠ 1`).

* `u = 0` ⟺ `x = 1` ⟺ the witness **fails** at this `l` — under the
  Chebotarev heuristic a probability-`1/p` event.
* `u` uniform on `[0, p)` is the heuristic itself; `stats.py` χ²-tests it.
* A pair failing at **every** `l` is what a genuine Vandiver counterexample
  looks like (the test is one-sided).
* The artifact's `vandiverCert` additionally requires `2 | k` — which holds
  for every row automatically: `l = m·p + 1` with `p` odd is only prime for
  even `m`. Every census cell is artifact-exact.

Self-tests: the artifact anchor `(p=37, i=32, l=149, t=2)` must fire, and a
t-invariance re-check runs every 997 cells (verdict must not depend on `t`).

## Usage

```
go build .
./vdsweep -pairs ~/vandiver/grascheck/pairs_100k.txt -nl 100 -o vdsweep-100k.csv
python3 stats.py ~/vandiver/vandiver_probe/gras_sweep_100k.txt \
                 ~/vandiver/grascheck/sweep_u64.txt vdsweep-100k.csv
```

Pair files: lines `p i` (grascheck format). HHO's table to 2³¹ is in
`~/vandiver/grascheck/twobillion.tar.bz2` for larger campaigns (cost per cell
is O(p) modular ops, so scale ranges accordingly; p < 10⁵ × 100 l's ≈ minutes
on 10 cores, the u64 pair file (p < 2.64M) wants the c4d box and fewer l's).

## Companion depth statistics (already-computed data)

`stats.py` also ingests grascheck output (`p i a1 G`): `G` is the second
p-adic digit of `L_p(1, ω^i)` — `G = 0` is a depth anomaly (hypothesis (2)
of C4 fails at `p`, with **no retry parameter**, unlike the two witnessed
certificates). Result on the existing 96,673 pairs (p < 2,642,239):
zero anomalies vs 0.62 expected, digit uniform (χ²(19)=14.6, p≈0.75),
closest call `G/p ≈ 4.1e-06` at `(p=1950107, i=1530566)`.
