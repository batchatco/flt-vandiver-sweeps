# witcount: how many witnesses, not just the first

For every prime `5 <= p < maxP`, counts the full Vandiver witnesses
`l = kp + 1` (`k` even, `p` not dividing `k`, every even `Q_i^k != 1` at the
least valid base `t`; exactly the artifact's `vandiverCert p l t (evenIndices p)`)
in two windows:

* old budget: `l < p^2 - p`, i.e. `k <= p - 3` (the artifact's `hsize`);
* bad-cert window: `2l <= 3p^2 - 5p + 2`, i.e. `k <= (3p-5)/2`, where
  `Bad(p, l) = {}` is proved (`../bad-certificate/BadCertificate.lean`,
  `noBad_of_two_mul_le`), so the descent runs without any further check.

It also records, for each candidate, whether Germain's conditions (A) and (B)
hold at `l` (the artifact's `sgCert`: no two consecutive nonzero `p`-th power
residues, and `p` not a `p`-th power residue), and counts joint passes.

The `Q_i` check is the discrete-log reformulation of `../vdsweep/fullsweep.go`
(validated there against the naive per-index `qi` and the artifact anchors).
Cross-check built in: when the fullsweep CSV is given as the fourth argument,
the first witness found here is compared with the one recorded there for every
prime in range (`witcount_6000.csv`: 781 primes, 0 mismatches).

## Results

`witcount_6000.csv` (`p < 6000`, columns `p, cand_old, wit_old, cand_bad,
wit_bad, first_l_old, first_l_bad, witnesses_bad`; produced by the version of
`main.go` before the Germain columns were added) and `witcount_sg_3000.csv`
(`p < 3000`, with the Germain and joint columns; current `main.go`).

* Every prime `5 <= p < 6000` has at least one witness in both windows.
  The minimum is 1, at `p = 5` only (`l = 11` is the sole candidate). From
  `p = 7` on the bad-cert window holds at least two.
* Smallest counts per band (bad-cert window): 22 of 39 candidates at
  `p = 311`; 60 of 104 at `p = 1009`; 157 of 293 at `p = 3041`; 211 of 361
  at `p = 4057`; 259 of 456 at `p = 5113`.
* Pass rate per candidate: 0.607 in every thousand-wide band, the
  `e^{-1/2}` of the `1/p` model (a finite census; it supports the heuristic
  and proves nothing about it).
* Germain (A)+(B) holds at about 45% of the witnesses below 3000 and at the
  same rate among the failing candidates. Every prime below 3000 has a
  joint witness inside the old budget `l < p^2 - p`.
* Outlier: `p = 131`, 2 witnesses of 14 candidates in the old budget
  (8 of 21 in the bad-cert window).

## Running

```
go run . 6000 8 out.csv ../vdsweep/vdsweep-fullwitness-100k.csv
```

Roughly four minutes on 8 cores for `p < 6000`; cost per prime grows like `p^3`.
