# flt-vandiver-sweeps

Search and census tools behind the *evidence* paragraphs of the paper
"Lean 4 Formalization of Fermat's Last Theorem for Every Prime Exponent
Below 1000, Regular and Irregular, and Two Wolstenholme Primes"
(Section 8, "The remaining gap").

Nothing here is load-bearing for any theorem: every proof-relevant claim of
the paper is machine-checked by the Lean kernel in the six `flt-*` artifact
repositories. These tools measure how plausible the reduction theorem's two
open hypotheses are — they are reported computations, published so the
reported numbers can be checked rather than trusted.

## Claim-to-artifact map

| Paper claim (Section 8) | Tool | Result file |
|---|---|---|
| Sophie Germain auxiliary `q` found for every odd prime `p < 2^32`, no failures | `sgsweep/` | `sgsweep-2e32.csv.gz` (1.5 GB — not in this repo; SHA-256 in `sgsweep/sgsweep-2e32.csv.gz.sha256`, file available from the author / archival deposit) |
| Census: 4,795 irregular pairs `(p, i)`, `p < 10^5`, x first 100 candidate `l` = 479,500 cells; 51 witness failures vs 50.0 predicted by the `1/p` model; dlog landing index uniform; no `t`-dependence | `vdsweep/main.go` | `vdsweep/vdsweep-100k.csv` |
| Case II descent runs for `2ℓ ≤ 3p² − 5p + 2`, extending the artifact's `ℓ < p² − p` (Section 8, hypothesis (1)'s "three numbers") | `bad-certificate/BadCertificate.lean` (Lean, checked against flt-vandiver `afm-v1`, standard axioms) | `bad-certificate/check.log` |
| Full witness (the artifact's `vandiverCert p l t (evenIndices p)`, all even indices) exists for **every** prime `5 <= p < 10^5`; max 11 candidate `l`; first candidate succeeds 60.8% (model: `e^{-1/2} ~ 0.607`); least witness `<= 2.08 p log^2 p` | `vdsweep/fullsweep.go` | `vdsweep/vdsweep-fullwitness-100k.csv` |

## Validation

* `vdsweep/main.go` (census) is a port of the validated Python reference
  `witness_census.py::qi_fast`, checked cell-exact against it for `p < 300`;
  the `Q_i` formula is verbatim from the Lean artifact's
  `FltVandiver/QiCertificate.lean`. Self-tests: the artifact anchor
  `(p=37, i=32, l=149, t=2)` must fire, and the verdict is re-checked with a
  different base `t` every 997 cells.
* `vdsweep/fullsweep.go` (full-witness sweep) uses a discrete-log
  reformulation (`Q_i^k = 1  <=>  S_i = N * D_i mod p`; derivation in the
  file header). `go run fullsweep.go selftest` checks it two ways:
  exhaustive agreement with the naive per-index `qi` (verbatim port of the
  Lean definition) on **every** candidate `l` for all `p < 260`, and
  reproduction of the seven witnesses recorded in the published artifact
  (`p` = 5, 7, 11, 13, 37, 59, 163).
* `sgsweep/main.go` checks Germain's conditions (A) and (B) on the subgroup
  of `p`-th power residues, the same check as the artifact's `sgCertSub`.

## Running

Each directory is a Go module; the tools are single files.

```
cd vdsweep
go run fullsweep.go selftest
go run fullsweep.go sweep 100000 10 out.csv     # ~50 min on 10 cores
go run main.go                                   # census; ~10 min on 12 cores
cd ../sgsweep
go run main.go                                   # see file header for flags
```

`vdsweep/stats.py` reproduces the census chi-squared statistics from the CSV.

## Note on local paths

Paths of the form `~/vandiver/...` in code comments and in `vdsweep/README.md`
refer to the author's local validation artifacts (the Python reference
implementation `witness_census.py`, and the Hart--Harvey--Ong irregular-pair
data used to seed the census). They are not part of this repository; the
validation they provided is described under "Validation" above.

## Provenance

(c) Bradley Taylor. Code written largely by Claude (Anthropic) under the
author's direction; see the paper's trust section.
