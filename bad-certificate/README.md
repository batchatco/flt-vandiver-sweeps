# bad-certificate

`BadCertificate.lean` removes the size bound `ℓ < p² − p` from the Case II
descent of the paper's artifact (flt-vandiver, Washington Lemma 9.7), replacing
it by the emptiness of a finite-field "Bad set", and proves that emptiness for
`2ℓ ≤ 3p² − 5p + 2`, i.e. `k = (ℓ−1)/p ≤ (3p−5)/2`, against the artifact's
`k < p − 1`.

**Status.** This file was written as a read-only check against the `afm-v1`
artifact. From release `afm-v2` the same development is part of flt-vandiver
itself (`FltVandiver/BadCertificate.lean`, with the joint-auxiliary interface in
`FltVandiver/JointAuxiliary.lean`), and the paper cites that copy. The copy here
is kept as the record of the original check; `check.log` below is its output
against `afm-v1`.

## Statement

For primes `p ≥ 5` and `ℓ = kp + 1` with `p ∤ k`, and `μ ∈ ℤ/ℓ` of order `p`,

    Bad(p, ℓ) = { w ≠ 0 : (1 − wμ^a)^k = (1 − wμ^{−a})^k for all a }.

Washington's Lemma 9.7 is the statement `Bad(p, ℓ) = ∅` for `k < p − 1`.

| theorem | content | axioms |
|---|---|---|
| `lemma_9_7_dvd_z_bad` | the artifact's `lemma_9_7_dvd_z` with the size hypothesis replaced by `p ∤ k` and `Bad = ∅` | standard 3 |
| `noBad_of_two_mul_le` | `Bad(p, kp+1) = ∅` whenever `2k ≤ 3p − 5` | standard 3 |
| `noBad_of_size` | the same in the artifact's `(ℓ−1)/p` interface: `2ℓ ≤ 3p² − 5p + 2` | standard 3 |
| `fermatLastTheoremFor_of_size_cert` | the artifact's per-prime FLT interface with `ℓ < p² − p` replaced by `2ℓ ≤ 3p² − 5p + 2`, nothing else changed | standard 3 |
| `noBadCert`, `noBadCert_imp` | a computable `O(ℓ)` certificate for `Bad = ∅` and its bridge | standard 3 |
| `fermatLastTheorem_of_bad_supply` | uniform reduction from a `BadWitness` at every `p` (a proposition, not a claim) | standard 3 |
| `example_1777`, `example_1777_size` | FLT(37) via `ℓ = 1777 = 48·37 + 1 > 37² − 37`, `q = 149` | + `native_decide` for the three certificates only |

The bound `2k ≤ 3p − 5` is sharp at `p = 5` (`Bad(5, 31) = {7}` at `k = 6`).

## Checking

`check.log` is the output of

    cd flt-vandiver            # tag afm-v1, Lean v4.31.0, library already built
    lake env lean path/to/BadCertificate.lean

It contains the twelve `#print axioms` results. The file compiles with no
errors, no warnings, and no `sorry`.

## Provenance

Written 2026-09-06 with Claude (Fable); the factorization plumbing is copied
from the artifact's `FltVandiver/CaseII95Descent.lean` and the Lemma 9.6
relaxation from a companion research file. The mathematics of
`noBad_of_two_mul_le` is described in the file's `Step 2` section header.
