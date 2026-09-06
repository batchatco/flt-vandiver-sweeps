import FltVandiver.CaseII95Descent
import FltVandiver.SophieGermain
import Mathlib.NumberTheory.FLT.Three
import Mathlib.NumberTheory.FLT.Four

/-!
# A Bad-set replacement for Washington Lemma 9.7 — step 1

2026-09-06 (Fable). The size bound `ℓ < p² − p` enters the 9.5 descent only
through Lemmas 9.6 and 9.7. Lemma 9.6 needs only `p ∤ (ℓ − 1)/p` (the `_joint`
lemmas, copied from JointAuxiliary.lean). Lemma 9.7's binomial-sum cancellation
is the special case `k < p − 1` of a finite-field statement: the set

  Bad(p, ℓ) = { w ≠ 0 : (1 − w μ^a)^k = (1 − w μ^{−a})^k for all a },  k = (ℓ−1)/p,

is empty. `lemma_9_7_dvd_z_bad` replaces `hsize` by `p ∤ k` and `Bad = ∅`; the
rest of the descent (`caseII_95`) already takes `ℓ ∣ z` and carries no size bound.

The factorization plumbing is copied from Bradley Arthur Taylor's
FltVandiver/CaseII95Descent.lean (frozen, read-only, not modified) and the 9.6
relaxation from JointAuxiliary.lean. No sorry and no new axiom; the only
`native_decide` uses are the three `p = 37` example certificates in the
`Example37`/`Example37Size` sections, and every other theorem below is checked
on the three standard axioms (see `check.log`).

Check (about 15 s once the library is built), from a checkout of flt-vandiver
at tag `afm-v1` (Lean `v4.31.0`):

    lake env lean path/to/BadCertificate.lean
-/

set_option linter.style.nativeDecide false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace Research20260906Bad

open CyclotomicNT FltVandiver FltVandiver.QiCert FltVandiver.Descent92
open FltVandiver.Descent95
open NumberField NumberField.IsCMField Polynomial UniqueFactorizationMonoid
open scoped NumberField

/-- The mod-`ℓ` obstruction to Lemma 9.7: a nonzero `w` (playing `z/y`) all of
whose conjugate ratios `(1 − wμ^a)/(1 − wμ^{−a})` are `p`-th powers, i.e. are
killed by the `k`-th power (`k = (ℓ−1)/p`). Independent of the choice of `μ`. -/
def IsBad {ℓ : ℕ} (p k : ℕ) (μ w : ZMod ℓ) : Prop :=
  w ≠ 0 ∧ ∀ a ∈ Finset.range p,
    (1 - w * μ ^ a) ^ k = (1 - w * μ ^ ((p - 1) * a)) ^ k

/-- **Lemma 9.7, finite-field core, certificate form.** The per-index equations
`yb − μ^a zb = g s₁^p`, `yb − μ^{−a} zb = g s₂^p` make `w = zb/yb` bad unless
`zb = 0`; so Bad-emptiness forces `zb = 0`. This is the exact content of
Washington's `k < p − 1` cancellation, with the cancellation replaced by the
hypothesis it proves. -/
theorem lemma_9_7_zmod_bad {ℓ : ℕ} [Fact ℓ.Prime] {p k : ℕ} {μ : ZMod ℓ}
    (hℓk : ℓ = k * p + 1)
    {yb zb : ZMod ℓ} (hy : yb ≠ 0)
    (heq : ∀ a ∈ Finset.range p, ∃ g s₁ s₂ : ZMod ℓ, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      yb - μ ^ a * zb = g * s₁ ^ p ∧ yb - μ ^ ((p - 1) * a) * zb = g * s₂ ^ p)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p k μ w) :
    zb = 0 := by
  by_contra hz
  apply hnobad (zb * yb⁻¹)
  refine ⟨mul_ne_zero hz (inv_ne_zero hy), ?_⟩
  intro a ha
  obtain ⟨g, s₁, s₂, hs₁, hs₂, h₁, h₂⟩ := heq a ha
  -- `s^{pk} = s^{ℓ−1} = 1` (Fermat), so both `k`-th powers equal `g^k`
  have hpk : p * k = ℓ - 1 := by
    rw [hℓk, mul_comm]
    omega
  have hpow : ∀ s : ZMod ℓ, s ≠ 0 → (s ^ p) ^ k = 1 := by
    intro s hs
    rw [← pow_mul, hpk]
    exact ZMod.pow_card_sub_one_eq_one hs
  have e₁ : (yb - μ ^ a * zb) ^ k = g ^ k := by
    rw [h₁, mul_pow, hpow s₁ hs₁, mul_one]
  have e₂ : (yb - μ ^ ((p - 1) * a) * zb) ^ k = g ^ k := by
    rw [h₂, mul_pow, hpow s₂ hs₂, mul_one]
  -- factor out `yb`
  have hinv : yb * yb⁻¹ = 1 := mul_inv_cancel₀ hy
  have f : ∀ c : ZMod ℓ, yb - c * zb = yb * (1 - zb * yb⁻¹ * c) := by
    intro c
    linear_combination (c * zb) * hinv
  have e := e₁.trans e₂.symm
  rw [f, f, mul_pow, mul_pow] at e
  exact mul_left_cancel₀ (pow_ne_zero _ hy) e

/-! ### Generalized Lemma 9.6 (copied from JointAuxiliary.lean, 2026-09-06) -/

theorem lemma_9_6_zmod_joint {ℓ : ℕ} [Fact ℓ.Prime] {p k : ℕ} {μ : ZMod ℓ}
    (hpp : p.Prime)
    (hμ : IsPrimitiveRoot μ p) (hp2 : 2 < p) (hkp : ¬ p ∣ k) (hℓk : ℓ = k * p + 1)
    {zb : ZMod ℓ} (hz : zb ≠ 0) {a : ℕ} (ha : ¬ p ∣ a)
    {g s₁ s₂ : ZMod ℓ} (hs₁ : s₁ ≠ 0) (hs₂ : s₂ ≠ 0)
    (he₁ : -(μ ^ a * zb) = g * s₁ ^ p)
    (he₂ : -(μ ^ ((p - 1) * a) * zb) = g * s₂ ^ p) : False := by
  have hppos : 0 < p := by omega
  have hμ0 : μ ≠ 0 := fun h0 => by
    have := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at this
    exact zero_ne_one this
  have hg : g ≠ 0 := by
    intro h0
    rw [h0, zero_mul, neg_eq_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hz) he₁
  have hμp : μ ^ (p * a) = 1 := by
    rw [pow_mul, hμ.pow_eq_one, one_pow]
  have hkey : g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * (s₂ ^ p * μ ^ a) := by
    have h1 : g * s₁ ^ p * μ ^ ((p - 1) * a) = -(μ ^ a * zb) * μ ^ ((p - 1) * a) := by
      rw [he₁]
    have h2 : g * s₂ ^ p * μ ^ a = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      rw [he₂]
    have h3 : -(μ ^ a * zb) * μ ^ ((p - 1) * a) = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by
      ring
    calc g * (s₁ ^ p * μ ^ ((p - 1) * a)) = g * s₁ ^ p * μ ^ ((p - 1) * a) := by ring
      _ = -(μ ^ ((p - 1) * a) * zb) * μ ^ a := by rw [h1, h3]
      _ = g * s₂ ^ p * μ ^ a := h2.symm
      _ = g * (s₂ ^ p * μ ^ a) := by ring
  have hkey' : s₁ ^ p * μ ^ ((p - 1) * a) = s₂ ^ p * μ ^ a :=
    mul_left_cancel₀ hg hkey
  have hup : s₁ ^ p = s₂ ^ p * μ ^ (2 * a) := by
    have h4 : s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a) = s₂ ^ p * (μ ^ a * μ ^ a) := by
      calc s₁ ^ p * (μ ^ ((p - 1) * a) * μ ^ a)
          = (s₁ ^ p * μ ^ ((p - 1) * a)) * μ ^ a := by ring
        _ = (s₂ ^ p * μ ^ a) * μ ^ a := by rw [hkey']
        _ = s₂ ^ p * (μ ^ a * μ ^ a) := by ring
    have h5 : μ ^ ((p - 1) * a) * μ ^ a = 1 := by
      rw [← pow_add, show (p - 1) * a + a = p * a by
        have : 1 ≤ p := by omega
        zify [this]
        ring, hμp]
    have h6 : μ ^ a * μ ^ a = μ ^ (2 * a) := by
      rw [← pow_add, two_mul]
    rw [h5, h6, mul_one] at h4
    exact h4
  set u : ZMod ℓ := s₁ * s₂⁻¹ with hu
  have hupow : u ^ p = μ ^ (2 * a) := by
    rw [hu, mul_pow, hup, mul_comm (s₂ ^ p) (μ ^ (2 * a)), mul_assoc, ← mul_pow,
      mul_inv_cancel₀ hs₂, one_pow, mul_one]
  have hp2a : ¬ p ∣ 2 * a := by
    intro hdvd
    rcases (Nat.Prime.dvd_mul hpp).mp hdvd with h2 | hA
    · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    · exact ha hA
  have hne1 : μ ^ (2 * a) ≠ 1 := fun h1 => hp2a ((hμ.pow_eq_one_iff_dvd _).mp h1)
  have hupp : u ^ (p * p) = 1 := by
    rw [pow_mul, hupow, ← pow_mul, mul_comm (2 * a) p, pow_mul, hμ.pow_eq_one, one_pow]
  have hdvd_pp : orderOf u ∣ p ^ 2 := by
    rw [pow_two]
    exact orderOf_dvd_of_pow_eq_one hupp
  have hnot_p : ¬ orderOf u ∣ p := by
    intro hdp
    exact hne1 (by rw [← hupow]; exact orderOf_dvd_iff_pow_eq_one.mp hdp)
  have hord : orderOf u = p ^ 2 := by
    obtain ⟨m, hm2, hm⟩ := (Nat.dvd_prime_pow hpp).mp hdvd_pp
    interval_cases m
    · rw [pow_zero] at hm
      rw [hm] at hnot_p
      exact absurd (one_dvd p) hnot_p
    · rw [pow_one] at hm
      rw [hm] at hnot_p
      exact absurd dvd_rfl hnot_p
    · exact hm
  have hu0 : u ≠ 0 := mul_ne_zero hs₁ (inv_ne_zero hs₂)
  have hdvd_card : orderOf u ∣ ℓ - 1 :=
    orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hu0)
  rw [hord] at hdvd_card
  have hpk : p ∣ k := by
    have h7 : p * p ∣ k * p := by
      rw [← pow_two]
      exact hdvd_card.trans (dvd_of_eq (by omega))
    exact (Nat.mul_dvd_mul_iff_right (by omega : 0 < p)).mp h7
  exact hkp hpk

variable {p : ℕ}

theorem aux_k_joint {ℓ : ℕ} [hℓpri : Fact ℓ.Prime] (hp2 : 2 < p)
    (hℓ : ℓ % p = 1) :
    ℓ = (ℓ - 1) / p * p + 1 ∧ 1 ≤ (ℓ - 1) / p := by
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have hdvd : p ∣ ℓ - 1 := by
    have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt (by omega)
    have hmod : (1 : ℕ) ≡ ℓ [MOD p] := by
      unfold Nat.ModEq
      rw [h1, hℓ]
    exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
  obtain ⟨k, hk⟩ := hdvd
  have hkval : (ℓ - 1) / p = k := by
    rw [hk]
    exact Nat.mul_div_cancel_left k (by omega)
  have hℓeq : ℓ = k * p + 1 := by
    rw [mul_comm]
    omega
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hk
      omega
    · exact h
  constructor
  · rw [hkval]
    exact hℓeq
  · rw [hkval]
    exact hk1

section Factor
variable [hpri : Fact p.Prime]
  [IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)]

theorem lemma_9_6_not_dvd_y_joint [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z) (hyz : IsCoprime y z)
    {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (hℓ : ℓ % p = 1) (hkp : ¬ p ∣ (ℓ - 1) / p)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0) :
    ¬ (ℓ : ℤ) ∣ y := by
  intro hly
  obtain ⟨hℓeq, _hk1⟩ := aux_k_joint hp hℓ
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set φ : 𝓞 (CyclotomicField p ℚ) →ₐ[ℤ] ZMod ℓ := redHom hζ hμ with hφ
  have hlz : ¬ (ℓ : ℤ) ∣ z := by
    intro hlz'
    obtain ⟨u, v, huv⟩ := hyz
    have h1 : (ℓ : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left hly u) (Dvd.dvd.mul_left hlz' v)
    have h2 : (ℓ : ℤ) ≤ 1 := Int.le_of_dvd one_pos h1
    have h3 := hℓpri.out.two_le
    omega
  have hzb : ((z : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hlz
  have hyb : ((y : ℤ) : ZMod ℓ) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hly
  obtain ⟨γ, σ, hγreal, heq₁, heq₂⟩ := factor_split_96 hζ hp hvand hfer hx0 hpy hpz hyz 1
    (alpha_pth_power_96 hζ hp hvand hfer hx0 hpy hpz hyz 1)
  have hφY : φ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : ZMod ℓ) := map_intCast φ y
  have hφZ : φ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : ZMod ℓ) := map_intCast φ z
  have hφζ : φ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  have he₁ : -(redRoot p ℓ t ^ 1 * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)) * (φ σ) ^ p := by
    have h1 := congrArg φ heq₁
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  have he₂ : -(redRoot p ℓ t ^ ((p - 1) * 1) * ((z : ℤ) : ZMod ℓ))
      = φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ))
        * (φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ)) ^ p := by
    have h1 := congrArg φ heq₂
    rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ, hyb] at h1
    linear_combination h1
  have hμ0 : redRoot p ℓ t ≠ 0 := fun h0 => by
    have h1 := hμ.pow_eq_one
    rw [h0, zero_pow (by omega : p ≠ 0)] at h1
    exact zero_ne_one h1
  have hs₁ : φ σ ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₁
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₁)
  have hs₂ : φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : p ≠ 0), mul_zero] at he₂
    exact (mul_ne_zero (pow_ne_zero _ hμ0) hzb) (neg_eq_zero.mp he₂)
  exact lemma_9_6_zmod_joint hpri.out hμ hp hkp (by omega) hzb
    (by
      intro hdvd
      have := Nat.le_of_dvd one_pos hdvd
      omega) hs₁ hs₂ he₁ he₂

/-! ### Lemma 9.7 with the size bound replaced by `p ∤ k` and Bad-emptiness -/

/-- **Washington Lemma 9.7, certificate form** — the auxiliary prime divides `z`.
Identical to the frozen `lemma_9_7_dvd_z` except that `hsize : ℓ < p² − p` is
replaced by `p ∤ (ℓ−1)/p` (all that Lemma 9.6 needs) and `Bad(p, ℓ) = ∅` (all
that Lemma 9.7 needs). The per-index `p`-th-power equations are produced exactly
as in the frozen proof; only the finite-field endgame changes. -/
theorem lemma_9_7_dvd_z_bad [NumberField.IsCMField (CyclotomicField p ℚ)]
    {ζ : CyclotomicField p ℚ} (hζ : IsPrimitiveRoot ζ p) (hp : 2 < p)
    (hvand : IsVandiverPrime p)
    {x y z : ℤ} (hfer : x ^ p + y ^ p = z ^ p) (hx0 : x ≠ 0)
    (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hyz : IsCoprime y z) (hxz : IsCoprime x z)
    {ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (hℓ : ℓ % p = 1) (hkp : ¬ p ∣ (ℓ - 1) / p)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w) :
    (ℓ : ℤ) ∣ z := by
  classical
  obtain ⟨hℓeq, _hk1⟩ := aux_k_joint hp hℓ
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set φ : 𝓞 (CyclotomicField p ℚ) →ₐ[ℤ] ZMod ℓ := redHom hζ hμ with hφ
  have hφY : φ ((y : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((y : ℤ) : ZMod ℓ) := map_intCast φ y
  have hφZ : φ ((z : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((z : ℤ) : ZMod ℓ) := map_intCast φ z
  have hφX : φ ((x : ℤ) : 𝓞 (CyclotomicField p ℚ)) = ((x : ℤ) : ZMod ℓ) := map_intCast φ x
  have hφζ : φ hζ.toInteger = redRoot p ℓ t := redHom_zeta hζ hμ
  -- ℓ divides neither y nor x (generalized Lemma 9.6, twice)
  have hly : ¬ (ℓ : ℤ) ∣ y :=
    lemma_9_6_not_dvd_y_joint hζ hp hvand hfer hx0 hpy hpz hyz hℓ hkp ht ht0
  have hy0 : y ≠ 0 := fun h0 => hpy (h0 ▸ dvd_zero _)
  have hfer' : y ^ p + x ^ p = z ^ p := by linear_combination hfer
  have hlx : ¬ (ℓ : ℤ) ∣ x :=
    lemma_9_6_not_dvd_y_joint hζ hp hvand hfer' hy0 hpx hpz hxz hℓ hkp ht ht0
  have hyb : ((y : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hly
  have hxb : ((x : ℤ) : ZMod ℓ) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hlx
  -- no factor image vanishes
  have hfac : ∀ b : ℕ, φ ((y : 𝓞 (CyclotomicField p ℚ))
      - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ))) ≠ 0 := by
    intro b h0
    have hmem := zeta_pow_mem_96 hζ (p := p) b
    have hdvd : ((y : 𝓞 (CyclotomicField p ℚ))
        - hζ.toInteger ^ b * (z : 𝓞 (CyclotomicField p ℚ)))
        ∣ ∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
            ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))) :=
      Finset.dvd_prod_of_mem
        (fun ζ' => (y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ))) hmem
    have h1 : φ (∏ ζ' ∈ nthRootsFinset p (1 : 𝓞 (CyclotomicField p ℚ)),
        ((y : 𝓞 (CyclotomicField p ℚ)) - ζ' * (z : 𝓞 (CyclotomicField p ℚ)))) = 0 := by
      have h2 := map_dvd φ hdvd
      rw [h0] at h2
      exact zero_dvd_iff.mp h2
    rw [prod_factors_96 hζ hp hfer, map_neg, map_pow, hφX, neg_eq_zero] at h1
    exact hxb (pow_eq_zero_iff (by omega : p ≠ 0) |>.mp h1)
  -- the per-index equations for the reduction lemma
  have heq : ∀ a ∈ Finset.range p, ∃ g s₁ s₂ : ZMod ℓ, s₁ ≠ 0 ∧ s₂ ≠ 0 ∧
      ((y : ℤ) : ZMod ℓ) - redRoot p ℓ t ^ a * ((z : ℤ) : ZMod ℓ) = g * s₁ ^ p
      ∧ ((y : ℤ) : ZMod ℓ) - redRoot p ℓ t ^ ((p - 1) * a) * ((z : ℤ) : ZMod ℓ)
        = g * s₂ ^ p := by
    intro a _
    obtain ⟨γ, σ, hγreal, heq₁, heq₂⟩ := factor_split_96 hζ hp hvand hfer hx0 hpy hpz hyz a
      (alpha_pth_power_96 hζ hp hvand hfer hx0 hpy hpz hyz a)
    refine ⟨φ ((γ : (𝓞 (CyclotomicField p ℚ))ˣ) : 𝓞 (CyclotomicField p ℚ)), φ σ,
      φ (ringOfIntegersComplexConj (CyclotomicField p ℚ) σ), ?_, ?_, ?_, ?_⟩
    · intro h0
      apply hfac a
      have h1 := congrArg φ heq₁
      rw [map_mul, map_pow, h0, zero_pow (by omega : p ≠ 0), mul_zero] at h1
      exact h1
    · intro h0
      apply hfac (a * (p - 1))
      have h1 := congrArg φ heq₂
      rw [map_mul, map_pow, h0, zero_pow (by omega : p ≠ 0), mul_zero] at h1
      exact h1
    · have h1 := congrArg φ heq₁
      rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ] at h1
      linear_combination h1
    · have h1 := congrArg φ heq₂
      rw [map_sub, map_mul, map_pow, map_mul, map_pow, hφY, hφZ, hφζ] at h1
      linear_combination h1
  have hzb : ((z : ℤ) : ZMod ℓ) = 0 :=
    lemma_9_7_zmod_bad hℓeq hyb heq hnobad
  have h2 : ((z : ℤ) : ZMod ℓ) = 0 ↔ (ℓ : ℤ) ∣ z := ZMod.intCast_zmod_eq_zero_iff_dvd z ℓ
  exact_mod_cast h2.mp hzb

end Factor

#print axioms lemma_9_7_zmod_bad
#print axioms lemma_9_7_dvd_z_bad

/-! ### A computable certificate for Bad-emptiness -/

/-- Computable Bad-emptiness check for the reduction root `μ = t^k`: every nonzero
`w < ℓ` has some index `a` whose conjugate ratio is not killed by the `k`-th power.
Cost `O(ℓ)` with early exit (the first index already fails for most `w`). -/
def noBadCert (p ℓ t : ℕ) [Fact ℓ.Prime] : Bool :=
  let k := (ℓ - 1) / p
  let μ : ZMod ℓ := (t : ZMod ℓ) ^ k
  (List.range ℓ).all fun w =>
    (w == 0) || (List.range p).any fun a =>
      decide ((1 - (w : ZMod ℓ) * μ ^ a) ^ k ≠ (1 - (w : ZMod ℓ) * μ ^ ((p - 1) * a)) ^ k)

/-- Bridge: the Boolean certificate implies `Bad(p, ℓ) = ∅` for `μ = redRoot p ℓ t`. -/
theorem noBadCert_imp {p ℓ t : ℕ} [hℓpri : Fact ℓ.Prime] (h : noBadCert p ℓ t = true) :
    ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w := by
  haveI : NeZero ℓ := ⟨hℓpri.out.ne_zero⟩
  rintro w ⟨hw0, hw⟩
  simp only [noBadCert, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
    List.any_eq_true, decide_eq_true_eq] at h
  simp only [redRoot] at hw
  obtain h1 | ⟨a, ha, hne⟩ := h w.val (ZMod.val_lt w)
  · apply hw0
    rw [← ZMod.natCast_zmod_val w, h1, Nat.cast_zero]
  · apply hne
    have := hw a (Finset.mem_range.mpr ha)
    rwa [ZMod.natCast_zmod_val]

/-! ### The top: Case II from the `Q_i` certificate, `p ∤ k`, and Bad-emptiness -/

section Top
variable {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime]

/-- **Case II, top level, no size bound.** Mirrors the frozen `caseII_95_top` and the
joint `caseII_joint_top`; `ℓ ∣ z` now comes from `lemma_9_7_dvd_z_bad`. -/
theorem caseII_bad_top (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w)
    {x y z : ℤ} (hxyz : x ^ p + y ^ p = z ^ p)
    (hz0 : z ≠ 0) (hpz : (p : ℤ) ∣ z) (hpx : ¬ (p : ℤ) ∣ x) (hpy : ¬ (p : ℤ) ∣ y)
    (hxy : IsCoprime x y) (hxz : IsCoprime x z) (hyz : IsCoprime y z) :
    False := by
  have hp2 : 2 < p := by omega
  haveI : NeZero p := ⟨hpri.out.ne_zero⟩
  haveI : IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ) :=
    CyclotomicField.isCyclotomicExtension p ℚ
  haveI : NumberField.IsCMField (CyclotomicField p ℚ) :=
    IsCyclotomicExtension.Rat.isCMField (CyclotomicField p ℚ) (S := {p})
      ⟨p, Set.mem_singleton p, hp2⟩
  set ζ : CyclotomicField p ℚ := IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ)
    with hζdef
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  -- the certificate gives Vandiver…
  have hvand : IsVandiverPrime p := qiVandiverBridge_all hcert
  -- …and, decoded, the ℓ-data
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcert
  obtain ⟨⟨⟨⟨hℓp, htk⟩, ht1⟩, hke⟩, hQcert⟩ := hcert
  have hQlist : ∀ i ∈ evenIndices p, qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 :=
    fun i hi => of_decide_eq_true (List.all_eq_true.mp hQcert i hi)
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpri.out.odd_of_ne_two (by omega))
  have hQall : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ p - 3 →
      qi p i ℓ t ^ ((ℓ - 1) / p) ≠ 1 := by
    intro i hiev hi2 hip
    obtain ⟨j, hj⟩ := hiev
    have hidx : i = 2 * ((j - 1) + 1) := by omega
    have hjlt : j - 1 < (p - 3) / 2 := by omega
    rw [hidx]
    exact hQlist _ (mem_evenIndices hpodd hjlt)
  -- ℓ-arithmetic
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : ℓ - 1 ≠ 0)] at ht1
    exact zero_ne_one ht1
  have htred : redRoot p ℓ t ≠ 1 := htk
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓp htred ht0
  obtain ⟨hℓeq, _hk1⟩ := aux_k_joint hp2 hℓp
  have hℓk : ℓ - 1 = (ℓ - 1) / p * p := by omega
  -- Lemma 9.7 in certificate form supplies the seed divisibility ℓ ∣ z
  have hx0 : x ≠ 0 := fun h0 => hpx (h0 ▸ dvd_zero _)
  have hℓz : (ℓ : ℤ) ∣ z :=
    lemma_9_7_dvd_z_bad hζ hp2 hvand hxyz hx0 hpx hpy hpz hyz hxz hℓp hkp htred ht0 hnobad
  exact caseII_95 hζ hp hvand hℓp hμ (k := (ℓ - 1) / p) hℓk hke hQall
    hxyz hz0 hpz hpx hpy hxy hxz hyz hℓz

/-- Orientation reduction (copied from the joint file / frozen `no_Int_Case2_95`). -/
theorem no_Int_Case2_bad (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w)
    {x y z : ℤ} (hcop : IsCoprime x y) (hpy : ¬ (p : ℤ) ∣ y) (hpz : (p : ℤ) ∣ z)
    (hz0 : z ≠ 0) (heq : x ^ p + y ^ p = z ^ p) : False := by
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have hpx : ¬ (p : ℤ) ∣ x := by
    intro hdvd
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : (p : ℤ) ∣ z ^ p - x ^ p :=
      dvd_sub (dvd_pow hpz hpne0) (dvd_pow hdvd hpne0)
    rwa [show z ^ p - x ^ p = y ^ p from by linear_combination -heq] at h1
  have hmix : ∀ {u v : ℤ}, (∀ q : ℤ, Prime q → q ∣ u → q ∣ v → False)
      → u ≠ 0 → IsCoprime u v := by
    intro u v hq hu
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd u v) with hg0 | hgpos
    · exact hu (Int.gcd_eq_zero_iff.mp hg0).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd u v : ℕ) : ℤ) := by exact_mod_cast hqd
      exact hq _ (Nat.prime_iff_prime_int.mp hqp)
        (hqi.trans (Int.gcd_dvd_left u v)) (hqi.trans (Int.gcd_dvd_right u v))
  have hx0 : x ≠ 0 := by
    intro h0
    refine hpy (hpint.dvd_of_dvd_pow (n := p) ?_)
    have h1 : y ^ p = z ^ p := by
      rw [h0, zero_pow hpne0, zero_add] at heq
      exact heq
    rw [h1]
    exact dvd_pow hpz hpne0
  have hxz : IsCoprime x z := by
    refine hmix ?_ hx0
    intro q hq hqx hqz
    have h1 : q ∣ y ^ p := by
      rw [show y ^ p = z ^ p - x ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqx hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' hqx h2)
  have hyz : IsCoprime y z := by
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0] at hpy
      exact hpy (dvd_zero _)
    refine hmix ?_ hy0
    intro q hq hqy hqz
    have h1 : q ∣ x ^ p := by
      rw [show x ^ p = z ^ p - y ^ p from by linear_combination heq]
      exact dvd_sub (dvd_pow hqz hpne0) (dvd_pow hqy hpne0)
    have h2 := hq.dvd_of_dvd_pow h1
    exact hq.not_unit (hcop.isUnit_of_dvd' h2 hqy)
  exact caseII_bad_top hp hcert hkp hnobad heq hz0 hpz hpx hpy hcop hxz hyz

/-- **Case II (symmetric integer form)**: `a^p + b^p = c^p` with `gcd = 1`, `abc ≠ 0`,
`p ∣ abc` is impossible. Copied from the joint file with the hypothesis swapped. -/
theorem caseII_bad_int (hp : 3 < p)
    (hcert : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w)
    {a b c : ℤ} (hprod : a * b * c ≠ 0) (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1)
    (hcaseII : (p : ℤ) ∣ a * b * c) :
    a ^ p + b ^ p ≠ c ^ p := by
  intro heq
  have hppri : Nat.Prime p := Fact.out
  have hpne0 : p ≠ 0 := hppri.ne_zero
  have hodd : Odd p := hppri.odd_of_ne_two (by omega)
  have hpint : Prime ((p : ℤ)) := Nat.prime_iff_prime_int.mp hppri
  have ha : a ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hb : b ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have hc : c ≠ 0 := by intro h; apply hprod; rw [h]; ring
  have div12 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ b → q ∣ c := fun q hq hqa hqb => by
    have hd : q ∣ a ^ p + b ^ p := dvd_add (dvd_pow hqa hpne0) (dvd_pow hqb hpne0)
    rw [heq] at hd; exact hq.dvd_of_dvd_pow hd
  have div13 : ∀ q : ℤ, Prime q → q ∣ a → q ∣ c → q ∣ b := fun q hq hqa hqc => by
    have hd : q ∣ c ^ p - a ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqa hpne0)
    have hrw : c ^ p - a ^ p = b ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have div23 : ∀ q : ℤ, Prime q → q ∣ b → q ∣ c → q ∣ a := fun q hq hqb hqc => by
    have hd : q ∣ c ^ p - b ^ p := dvd_sub (dvd_pow hqc hpne0) (dvd_pow hqb hpne0)
    have hrw : c ^ p - b ^ p = a ^ p := by linear_combination -heq
    rw [hrw] at hd; exact hq.dvd_of_dvd_pow hd
  have hno_common : ∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ a ∧ (q : ℤ) ∣ b ∧ (q : ℤ) ∣ c)
      := by
    rintro q hqp ⟨hqa, hqb, hqc⟩
    have hqgcd : (q : ℤ) ∣ ({a, b, c} : Finset ℤ).gcd id := by
      apply Finset.dvd_gcd
      intros x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact hqa
      · exact hqb
      · exact hqc
    rw [hgcd] at hqgcd
    have hu : IsUnit ((q : ℤ)) := isUnit_of_dvd_one hqgcd
    have hq1 : (q : ℤ) = 1 := by
      rcases Int.isUnit_iff.mp hu with h | h
      · exact h
      · have hge : (q : ℤ) ≥ 0 := Int.natCast_nonneg q
        omega
    have : q = 1 := by exact_mod_cast hq1
    exact hqp.one_lt.ne' this
  have coprime_of_div : ∀ {x y z : ℤ}, x ≠ 0 →
      (∀ q : ℤ, Prime q → q ∣ x → q ∣ y → q ∣ z) →
      (∀ q : ℕ, q.Prime → ¬ ((q : ℤ) ∣ x ∧ (q : ℤ) ∣ y ∧ (q : ℤ) ∣ z)) →
      IsCoprime x y := by
    intros x y z hx hdvdh hno
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra hne
    rcases Nat.eq_zero_or_pos (Int.gcd x y) with hz | hpos
    · exact hx (Int.gcd_eq_zero_iff.mp hz).1
    · obtain ⟨q, hqp, hqd⟩ := Nat.exists_prime_and_dvd hne
      have hqi : (q : ℤ) ∣ ((Int.gcd x y : ℕ) : ℤ) := by exact_mod_cast hqd
      have hqx : (q : ℤ) ∣ x := dvd_trans hqi (Int.gcd_dvd_left x y)
      have hqy : (q : ℤ) ∣ y := dvd_trans hqi (Int.gcd_dvd_right x y)
      have hqprime : Prime ((q : ℤ)) := Nat.prime_iff_prime_int.mp hqp
      have hqz : (q : ℤ) ∣ z := hdvdh _ hqprime hqx hqy
      exact hno q hqp ⟨hqx, hqy, hqz⟩
  have hab : IsCoprime a b := coprime_of_div ha div12 hno_common
  have hac : IsCoprime a c := coprime_of_div ha div13
    (fun q hq ⟨ha', hc', hb'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  have hbc : IsCoprime b c := coprime_of_div hb div23
    (fun q hq ⟨hb', hc', ha'⟩ => hno_common q hq ⟨ha', hb', hc'⟩)
  rcases hpint.dvd_mul.mp hcaseII with hab' | hc'
  · rcases hpint.dvd_mul.mp hab' with hpa | hpb
    · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hab.isUnit_of_dvd' hpa h)
      have heq' : c ^ p + (-b) ^ p = a ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hcop : IsCoprime c (-b) := (IsCoprime.symm hbc).neg_right
      have hnpb : ¬ (p : ℤ) ∣ (-b) := by rwa [dvd_neg]
      exact no_Int_Case2_bad hp hcert hkp hnobad hcop hnpb hpa ha heq'
    · have hpa : ¬ (p : ℤ) ∣ a := fun h => hpint.not_unit (hab.isUnit_of_dvd' h hpb)
      have heq' : (-a) ^ p + c ^ p = b ^ p := by
        rw [Odd.neg_pow hodd]; linear_combination -heq
      have hpc : ¬ (p : ℤ) ∣ c := fun h => hpint.not_unit (hbc.isUnit_of_dvd' hpb h)
      have hcop : IsCoprime (-a) c := hac.neg_left
      exact no_Int_Case2_bad hp hcert hkp hnobad hcop hpc hpb hb heq'
  · have hpb : ¬ (p : ℤ) ∣ b := fun h => hpint.not_unit (hbc.isUnit_of_dvd' h hc')
    exact no_Int_Case2_bad hp hcert hkp hnobad hab hpb hc' hc heq

end Top

/-! ### FLT at `p` from the two decoupled certificates -/

/-- **FLT at `p`, no size bound on the Case II auxiliary.** Case II runs on `ℓ` with the
`Q_i` certificate, `p ∤ k`, and `Bad(p, ℓ) = ∅`; Case I runs on a *separate* Sophie Germain
auxiliary `q`, exactly as in the paper. -/
theorem fermatLastTheoremFor_of_bad_data {p ℓ t q : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hnobad : ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w)
    (hq : q.Prime)
    (hA : ∀ x y z : ZMod q, x ^ p + y ^ p + z ^ p = 0 → x = 0 ∨ y = 0 ∨ z = 0)
    (hB : ∀ s : ZMod q, s ^ p ≠ (p : ZMod q)) :
    FermatLastTheoremFor p := by
  apply fermatLastTheoremFor_iff_int.mpr
  intro a b c ha hb hc e
  have hprod := mul_ne_zero (mul_ne_zero ha hb) hc
  obtain ⟨e', hgcd, hprod'⟩ := FltRegular.MayAssume.coprime e hprod
  let d := ({a, b, c} : Finset ℤ).gcd id
  by_cases hcase : (p : ℤ) ∣ (a / d) * (b / d) * (c / d)
  · exact caseII_bad_int (by omega) hQi hkp hnobad hprod' hgcd hcase e'
  · exact caseI_of_auxiliaryPrime ((Fact.out : p.Prime).odd_of_ne_two (by omega))
      hq hA hB hcase e'

/-- The certificate interface: three Booleans, two primes, no size bound. -/
theorem fermatLastTheoremFor_of_bad_cert {p ℓ t q : ℕ}
    [Fact p.Prime] [Fact ℓ.Prime] [Fact q.Prime] [NeZero q]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hBad : noBadCert p ℓ t = true)
    (hSG : sgCert p q = true) :
    FermatLastTheoremFor p := by
  obtain ⟨hA, hB⟩ := sgCert_imp hSG
  exact fermatLastTheoremFor_of_bad_data hp5 hQi hkp (noBadCert_imp hBad) Fact.out hA hB

#print axioms fermatLastTheoremFor_of_bad_cert

/-- The remaining uniform supply statement in this interface (a proposition, not a claim). -/
def BadWitness (p : ℕ) : Prop :=
  ∃ (ℓ t q : ℕ) (_ : Fact ℓ.Prime) (_ : Fact q.Prime) (_ : NeZero q),
    vandiverCert p ℓ t (evenIndices p) = true ∧ ¬ p ∣ (ℓ - 1) / p ∧
    noBadCert p ℓ t = true ∧ sgCert p q = true

theorem fermatLastTheorem_of_bad_supply
    (hsupply : ∀ p : ℕ, p.Prime → 5 ≤ p → BadWitness p) :
    FermatLastTheorem :=
  FermatLastTheorem.of_odd_primes fun p hp hodd => by
    haveI : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    · subst p
      exact fermatLastTheoremThree
    · have hp5 : 5 ≤ p := by
        have hp2 := hp.two_le
        have hmod := Nat.odd_iff.mp hodd
        omega
      obtain ⟨ℓ, t, q, hℓ, hq, hn, hQi, hkp, hBad, hSG⟩ := hsupply p hp hp5
      exact fermatLastTheoremFor_of_bad_cert hp5 hQi hkp hBad hSG

#print axioms fermatLastTheorem_of_bad_supply

/-! ### Example: `p = 37`, `ℓ = 1777 = 48·37 + 1 > 37² − 37 = 1332`.
The SG-joint interface rejects `1777` (its `p`-th powers contain consecutive pairs);
this interface accepts it. Case I uses the paper's own auxiliary `q = 149`. -/
section Example37
local instance : Fact (Nat.Prime 1777) := ⟨by norm_num⟩

theorem qi37_1777 : vandiverCert 37 1777 2 (evenIndices 37) = true := by native_decide
theorem nobad37_1777 : noBadCert 37 1777 2 = true := by native_decide
theorem sg37_149 : sgCert 37 149 = true := by native_decide

theorem example_1777 : FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_of_bad_cert (ℓ := 1777) (t := 2) (q := 149)
    (by norm_num) qi37_1777 (by norm_num) nobad37_1777 sg37_149

#print axioms qi37_1777
#print axioms nobad37_1777
#print axioms sg37_149
#print axioms example_1777
end Example37


/-! ### Step 2: `Bad(p, ℓ) = ∅` whenever `2k ≤ 3p − 5`

Washington's binomial-sum cancellation handles `k < p − 1`. The 2026-09-06 extension
(central binomials at `r = m, m − 1`, `m = (p−1)/2`) handles `p − 1 ≤ k ≤ (3p−5)/2`.
Both are instances of one identity: multiplying the `a`-th Bad equation by `μ^{a(p−r)}`
and summing over a period extracts the folded coefficient `C_r(u) = Σ_{j ≡ r} C(k,j) u^j`
(`u = −w`) from the left side and `C_{p−r}(u)` from the right, so `C_r = C_{p−r}`.
When the residue class of `r` meets `[0, k]` at most once, both sides are monomials. -/

section Range
variable {ℓ : ℕ} [hℓpri : Fact ℓ.Prime] {p : ℕ} {μ : ZMod ℓ}

/-- Geometric sum of `μ^s` over a full period: `p` if `p ∣ s`, else `0`. -/
theorem geom_root_sum (hμ : IsPrimitiveRoot μ p) (s : ℕ) :
    ∑ a ∈ Finset.range p, (μ ^ s) ^ a = if p ∣ s then (p : ZMod ℓ) else 0 := by
  split_ifs with hs
  · rw [(hμ.pow_eq_one_iff_dvd s).mpr hs]
    simp
  · have hne : μ ^ s ≠ 1 := fun h => hs ((hμ.pow_eq_one_iff_dvd s).mp h)
    rw [geom_sum_eq hne, ← pow_mul, mul_comm, pow_mul, hμ.pow_eq_one, one_pow, sub_self,
      zero_div]

/-- **The fold.** Weighting the `a`-th term by `μ^{as}` and summing over a period keeps
exactly the coefficients with `s + e·j ≡ 0 (mod p)`, each multiplied by `p`. -/
theorem fold_eval (hμ : IsPrimitiveRoot μ p) (c : ℕ → ZMod ℓ) (N s e : ℕ) :
    ∑ a ∈ Finset.range p, μ ^ (a * s) * ∑ j ∈ Finset.range N, c j * μ ^ (e * a * j)
      = (p : ZMod ℓ) * ∑ j ∈ (Finset.range N).filter (fun j => p ∣ s + e * j), c j := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : ∀ a, μ ^ (a * s) * (c j * μ ^ (e * a * j)) = c j * (μ ^ (s + e * j)) ^ a := by
    intro a
    have : (μ ^ (s + e * j)) ^ a = μ ^ (a * s) * μ ^ (e * a * j) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun a _ => h1 a, ← Finset.mul_sum, geom_root_sum hμ]
  split_ifs <;> ring

/-- Binomial expansion of one Bad-equation side in the shape the fold consumes. -/
theorem side_expand (w : ZMod ℓ) (k b : ℕ) :
    (1 - w * μ ^ b) ^ k
      = ∑ j ∈ Finset.range (k + 1), (k.choose j : ZMod ℓ) * (-w) ^ j * μ ^ (b * j) := by
  rw [sub_eq_neg_add, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [one_pow, mul_one]
  rw [← neg_mul, mul_pow, ← pow_mul]
  ring

/-- **Symmetry of the folded coefficients.** From the Bad equations, `C_r = C_{p−r}`,
each side written with the divisibility predicate its fold produces. -/
theorem fold_symm (hμ : IsPrimitiveRoot μ p) (hpℓ : (p : ZMod ℓ) ≠ 0)
    {k : ℕ} {w : ZMod ℓ}
    (hw : ∀ a ∈ Finset.range p, (1 - w * μ ^ a) ^ k = (1 - w * μ ^ ((p - 1) * a)) ^ k)
    (r : ℕ) :
    ∑ j ∈ (Finset.range (k + 1)).filter (fun j => p ∣ (p - r) + 1 * j),
        (k.choose j : ZMod ℓ) * (-w) ^ j
      = ∑ j ∈ (Finset.range (k + 1)).filter (fun j => p ∣ (p - r) + (p - 1) * j),
        (k.choose j : ZMod ℓ) * (-w) ^ j := by
  apply mul_left_cancel₀ hpℓ
  have F1 := fold_eval hμ (fun j => (k.choose j : ZMod ℓ) * (-w) ^ j) (k + 1) (p - r) 1
  have F2 := fold_eval hμ (fun j => (k.choose j : ZMod ℓ) * (-w) ^ j) (k + 1) (p - r) (p - 1)
  beta_reduce at F1 F2
  rw [← F1, ← F2]
  refine Finset.sum_congr rfl fun a ha => ?_
  congr 1
  rw [← side_expand (μ := μ) w k (1 * a), ← side_expand (μ := μ) w k ((p - 1) * a), Nat.one_mul]
  exact hw a ha

/-- The two predicates agree after reflecting `r ↦ p − r`. -/
theorem filter_reflect (hp : 0 < p) {r : ℕ} (hr : r ≤ p) (j : ℕ) :
    p ∣ (p - r) + (p - 1) * j ↔ p ∣ (p - (p - r)) + 1 * j := by
  have h : (p - r) + (p - 1) * j + ((p - (p - r)) + 1 * j) = p * (1 + j) := by
    have h1 : p - r ≤ p := Nat.sub_le p r
    zify [hr, hp, h1]
    ring
  have hsum : p ∣ (p - r) + (p - 1) * j + ((p - (p - r)) + 1 * j) := by
    rw [h]
    exact Dvd.intro _ rfl
  constructor
  · intro hd
    exact (Nat.dvd_add_right hd).mp hsum
  · intro hd
    exact (Nat.dvd_add_left hd).mp hsum

/-- The residue class of `r` meets `[0, k]` only at `j = r` when `0 < r < p`, `k < r + p`. -/
theorem window_eq {p r k j c : ℕ} (hrp : r < p) (hkr : k < r + p)
    (hjk : j < k + 1) (hc : p - r + 1 * j = p * c) : j = r := by
  have hc1 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · rw [h0, Nat.mul_zero] at hc
      omega
    · exact h0
  have hc2 : c < 2 := by
    by_contra hcon
    have h2 : p * 2 ≤ p * c := Nat.mul_le_mul_left p (by omega)
    omega
  have hc3 : c = 1 := by omega
  rw [hc3, Nat.mul_one] at hc
  omega

/-- **Single-term evaluation.** For `0 < r < p` and `k < r + p`, the folded coefficient is
the monomial `C(k, r) u^r` (both sides vanish when `k < r`). -/
theorem filter_single {k r : ℕ} (hrp : r < p) (hkr : k < r + p)
    (u : ZMod ℓ) :
    ∑ j ∈ (Finset.range (k + 1)).filter (fun j => p ∣ (p - r) + 1 * j),
        (k.choose j : ZMod ℓ) * u ^ j
      = (k.choose r : ZMod ℓ) * u ^ r := by
  by_cases hrk : r ≤ k
  · rw [Finset.sum_eq_single r]
    · intro j hj hjr
      exfalso
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      obtain ⟨hjk, c, hc⟩ := hj
      exact hjr (window_eq hrp hkr hjk hc)
    · intro hr
      exfalso
      apply hr
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, 1, by omega⟩
  · rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro j hj
    exfalso
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjk, c, hc⟩ := hj
    have := window_eq hrp hkr hjk hc
    omega

/-- **`Bad(p, ℓ) = ∅` for `2k ≤ 3p − 5`** (`p ≥ 5`, `ℓ = kp + 1` prime, `p ∤ k`).
`k < p − 1` is Washington's `r = 1` cancellation; `p − 1 ≤ k ≤ (3p−5)/2` is the
central-binomial argument: the `r = m` and `r = m − 1` symmetries force `u² = 1` and
then `(k − p)(k + 1) ≡ 0 (mod ℓ)`, impossible. -/
theorem noBad_of_two_mul_le (hpp : p.Prime) (hp5 : 5 ≤ p)
    (hμ : IsPrimitiveRoot μ p) {k : ℕ} (hℓk : ℓ = k * p + 1)
    (hkp : ¬ p ∣ k) (hk1 : 1 ≤ k) (hkle : 2 * k ≤ 3 * p - 5) :
    ∀ w : ZMod ℓ, ¬ IsBad p k μ w := by
  rintro w ⟨hw0, hw⟩
  have hp0 : 0 < p := hpp.pos
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hpp.odd_of_ne_two (by omega))
  have hkℓ : k < ℓ := by
    rw [hℓk]
    nlinarith
  have hpℓ' : p < ℓ := by
    rw [hℓk]
    nlinarith
  -- small naturals are nonzero mod ℓ; binomials `C(k, j)` are nonzero mod ℓ
  have hsmall : ∀ n, 0 < n → n < ℓ → (n : ZMod ℓ) ≠ 0 := by
    intro n hn hnl h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact absurd (Nat.le_of_dvd hn h0) (by omega)
  have hpℓ : (p : ZMod ℓ) ≠ 0 := hsmall p hp0 hpℓ'
  have hchoose : ∀ j, j ≤ k → (k.choose j : ZMod ℓ) ≠ 0 := by
    intro j hj h0
    rw [ZMod.natCast_eq_zero_iff] at h0
    have h1 : ℓ ∣ k.factorial := by
      rw [← Nat.choose_mul_factorial_mul_factorial hj]
      exact (h0.mul_right _).mul_right _
    have h2 := (Nat.Prime.dvd_factorial hℓpri.out).mp h1
    omega
  -- the symmetry, in monomial form
  have key : ∀ r, 0 < r → r < p → k < r + p → k < (p - r) + p →
      (k.choose r : ZMod ℓ) * (-w) ^ r = (k.choose (p - r) : ZMod ℓ) * (-w) ^ (p - r) := by
    intro r hr0 hrp hkr hkr'
    have H := fold_symm hμ hpℓ hw r
    rw [Finset.filter_congr (fun j _ => filter_reflect hp0 hrp.le j)] at H
    rw [filter_single hrp hkr, filter_single (by omega) hkr'] at H
    exact H
  by_cases hsmallk : k < p - 1
  · -- Washington: `r = 1` gives `k·u = C(k, p−1) u^{p−1} = 0`
    have H := key 1 one_pos (by omega) (by omega) (by omega)
    rw [Nat.choose_one_right, Nat.choose_eq_zero_of_lt (by omega : k < p - 1), Nat.cast_zero,
      zero_mul, pow_one] at H
    exact hw0 (neg_eq_zero.mp ((mul_eq_zero.mp H).resolve_left (hsmall k hk1 hkℓ)))
  · set u : ZMod ℓ := -w with hu
    have hu0 : u ≠ 0 := neg_ne_zero.mpr hw0
    set m := (p - 1) / 2 with hm
    have hm2 : 2 ≤ m := by omega
    have hpm : p = 2 * m + 1 := by omega
    have hkm : m + 2 ≤ k := by omega
    have E1 := key m (by omega) (by omega) (by omega) (by omega)
    have E2 := key (m - 1) (by omega) (by omega) (by omega) (by omega)
    rw [show p - m = m + 1 by omega] at E1
    rw [show p - (m - 1) = m + 2 by omega] at E2
    -- cancel the powers of `u`
    have E1' : (k.choose m : ZMod ℓ) = (k.choose (m + 1) : ZMod ℓ) * u := by
      apply mul_right_cancel₀ (pow_ne_zero m hu0)
      rw [E1]
      ring
    have E2' : (k.choose (m - 1) : ZMod ℓ) = (k.choose (m + 2) : ZMod ℓ) * u ^ 3 := by
      apply mul_right_cancel₀ (pow_ne_zero (m - 1) hu0)
      rw [E2]
      have : u ^ (m + 2) = u ^ 3 * u ^ (m - 1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [this]
      ring
    -- the three adjacent-binomial recursions, cast to `ZMod ℓ`
    set M : ZMod ℓ := (m : ZMod ℓ) with hM
    set D : ZMod ℓ := ((k - m : ℕ) : ZMod ℓ) with hD
    have hD1 : ((k - (m + 1) : ℕ) : ZMod ℓ) = D - 1 := by
      rw [hD, eq_sub_iff_add_eq, ← Nat.cast_succ]
      congr 1
      omega
    have hD2 : ((k - (m - 1) : ℕ) : ZMod ℓ) = D + 1 := by
      rw [hD, ← Nat.cast_succ]
      congr 1
      omega
    have R1 : (k.choose (m + 1) : ZMod ℓ) * (M + 1) = (k.choose m : ZMod ℓ) * D := by
      have := congrArg (Nat.cast : ℕ → ZMod ℓ) (Nat.choose_succ_right_eq k m)
      simp only [Nat.cast_mul, Nat.cast_succ] at this
      rw [hM, hD]
      exact this
    have R2 : (k.choose (m + 2) : ZMod ℓ) * (M + 2) = (k.choose (m + 1) : ZMod ℓ) * (D - 1) := by
      have := congrArg (Nat.cast : ℕ → ZMod ℓ) (Nat.choose_succ_right_eq k (m + 1))
      simp only [Nat.cast_mul, Nat.cast_succ] at this
      rw [← hD1, hM, show m + 2 = m + 1 + 1 from rfl]
      linear_combination this
    have R3 : (k.choose m : ZMod ℓ) * M = (k.choose (m - 1) : ZMod ℓ) * (D + 1) := by
      have := congrArg (Nat.cast : ℕ → ZMod ℓ) (Nat.choose_succ_right_eq k (m - 1))
      rw [show m - 1 + 1 = m by omega] at this
      simp only [Nat.cast_mul] at this
      rw [hD2] at this
      rw [hM]
      exact this
    -- eliminate: `M + 1 = u D` and `M (M + 2) = u² (D − 1)(D + 1)`
    have hC1 := hchoose (m + 1) (by omega)
    have hα : M + 1 = u * D := by
      apply mul_left_cancel₀ hC1
      rw [R1, E1']
      ring
    have hδ : M * (M + 2) = u ^ 2 * (D - 1) * (D + 1) := by
      apply mul_left_cancel₀ hC1
      apply mul_left_cancel₀ hu0
      have h1 : u * ((k.choose (m + 1) : ZMod ℓ) * (M * (M + 2)))
          = (k.choose m : ZMod ℓ) * M * (M + 2) := by
        rw [E1']
        ring
      have h2 : (k.choose m : ZMod ℓ) * M * (M + 2)
          = (k.choose (m + 2) : ZMod ℓ) * u ^ 3 * (D + 1) * (M + 2) := by
        rw [R3, E2']
      have h3 : (k.choose (m + 2) : ZMod ℓ) * u ^ 3 * (D + 1) * (M + 2)
          = u * ((k.choose (m + 1) : ZMod ℓ) * (u ^ 2 * (D - 1) * (D + 1))) := by
        linear_combination (u ^ 3 * (D + 1)) * R2
      rw [h1, h2, h3]
    have hu2 : u ^ 2 = 1 := by
      linear_combination (-(u * D + M + 1)) * hα + hδ
    have hfac : (D - (M + 1)) * (D + (M + 1)) = 0 := by
      linear_combination (-(M + 1 + u * D)) * hα + (-D ^ 2) * hu2
    rcases mul_eq_zero.mp hfac with h | h
    · -- `k − m = m + 1`, i.e. `k = p`, contradicting `p ∤ k`
      have e : ((k - m : ℕ) : ZMod ℓ) = ((m + 1 : ℕ) : ZMod ℓ) := by
        rw [Nat.cast_succ, ← hM, ← hD]
        exact sub_eq_zero.mp h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)] at e
      exact hkp ⟨1, by omega⟩
    · -- `k + 1 ≡ 0 (mod ℓ)`, impossible as `0 < k + 1 < ℓ`
      have e : ((k + 1 : ℕ) : ZMod ℓ) = D + (M + 1) := by
        rw [hD, hM, ← Nat.cast_succ, ← Nat.cast_add]
        congr 1
        omega
      rw [h] at e
      have hk1ℓ : k + 1 < ℓ := by
        rw [hℓk]
        nlinarith
      exact hsmall (k + 1) (by omega) hk1ℓ e

end Range

#print axioms noBad_of_two_mul_le

/-- The proved-range corollary in the interface of `fermatLastTheoremFor_of_bad_data`:
for `2ℓ ≤ 3p² − 5p + 2` (i.e. `2k ≤ 3p − 5`) no `noBadCert` computation is needed. -/
theorem noBad_of_size {p ℓ t : ℕ} [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime] (hp5 : 5 ≤ p)
    (hℓ : ℓ % p = 1) (hkp : ¬ p ∣ (ℓ - 1) / p) (hsize : 2 * ℓ ≤ 3 * p * p - 5 * p + 2)
    (ht : redRoot p ℓ t ≠ 1) (ht0 : (t : ZMod ℓ) ≠ 0) :
    ∀ w : ZMod ℓ, ¬ IsBad p ((ℓ - 1) / p) (redRoot p ℓ t) w := by
  have hp2 : 2 < p := by omega
  have hp0 : 0 < p := by omega
  obtain ⟨hℓeq, hk1⟩ := aux_k_joint hp2 hℓ
  have hμ : IsPrimitiveRoot (redRoot p ℓ t) p := isPrimitiveRoot_redRoot hℓ ht ht0
  set k := (ℓ - 1) / p with hk
  refine noBad_of_two_mul_le hpri.out hp5 hμ hℓeq hkp hk1 ?_
  have h1 : 2 * (k * p) + 2 ≤ 3 * p * p - 5 * p + 2 := by omega
  have h3 : 3 * p * p - 5 * p = (3 * p - 5) * p := by
    rw [Nat.sub_mul]
  rw [h3] at h1
  have h4 : 2 * k * p ≤ (3 * p - 5) * p := by
    rw [Nat.mul_assoc]
    omega
  exact Nat.le_of_mul_le_mul_right h4 hp0

#print axioms noBad_of_size

/-! ### The proved-range interface: budget `2ℓ ≤ 3p² − 5p + 2`, no Bad computation -/

/-- **FLT at `p` with the enlarged budget.** The frozen interface needs `ℓ < p² − p`;
this one needs `2ℓ ≤ 3p² − 5p + 2` and `p ∤ (ℓ−1)/p`, with no other change and no
`noBadCert` evaluation, by `noBad_of_size`. -/
theorem fermatLastTheoremFor_of_size_cert {p ℓ t q : ℕ}
    [hpri : Fact p.Prime] [hℓpri : Fact ℓ.Prime] [Fact q.Prime] [NeZero q]
    (hp5 : 5 ≤ p)
    (hQi : vandiverCert p ℓ t (evenIndices p) = true)
    (hkp : ¬ p ∣ (ℓ - 1) / p)
    (hsize : 2 * ℓ ≤ 3 * p * p - 5 * p + 2)
    (hSG : sgCert p q = true) :
    FermatLastTheoremFor p := by
  obtain ⟨hA, hB⟩ := sgCert_imp hSG
  have hc := hQi
  simp only [vandiverCert, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hℓp, htk⟩, ht1⟩, _⟩, _⟩ := hc
  have hℓ2 : 2 ≤ ℓ := hℓpri.out.two_le
  have ht0 : (t : ZMod ℓ) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega : ℓ - 1 ≠ 0)] at ht1
    exact zero_ne_one ht1
  exact fermatLastTheoremFor_of_bad_data hp5 hQi hkp
    (noBad_of_size hp5 hℓp hkp hsize htk ht0) Fact.out hA hB

#print axioms fermatLastTheoremFor_of_size_cert

section Example37Size
local instance : Fact (Nat.Prime 1777) := ⟨by norm_num⟩

/-- `ℓ = 1777` lies inside the proved range: `2·1777 = 3554 ≤ 3·37² − 5·37 + 2 = 3924`,
while `1777 > 37² − 37 = 1332`. So `FermatLastTheoremFor 37` at an auxiliary beyond the
old budget, with no Bad computation: only the two certificates the paper already uses. -/
theorem example_1777_size : FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_of_size_cert (ℓ := 1777) (t := 2) (q := 149)
    (by norm_num) qi37_1777 (by norm_num) (by norm_num) sg37_149

#print axioms example_1777_size
end Example37Size

end Research20260906Bad
