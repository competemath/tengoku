/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.LieLean.LieLean.Algebra.Lie.KacMoody.Super.InvariantFormLie

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Serre relations hold in `G(A, τ)`

Let `A` be a symmetrizable generalized Cartan matrix and `p` a parity with `aᵢⱼ` even whenever
`eᵢ` is odd. The Serre elements `(ad eᵢ)^{1 - aᵢⱼ} eⱼ` and `(ad fᵢ)^{1 - aᵢⱼ} fⱼ` (`i ≠ j`) of
`G̃(A, τ)` lie in the maximal ideal `R`; equivalently the Serre relations hold in
`G(A, τ) = G̃(A, τ) / R` ([Kac78] §1.2, cf. [Kac] §3.3).

The proof follows the even case (`LieLean/Algebra/Lie/KacMoody/Serre.lean`), with two changes.

* An element `x ∈ G̃_β`, `β > 0`, with `[fₖ, x] = 0` for all `k` lies in `R`: here we use that `R`
  is the radical of the invariant form (`mem_maxIdeal_iff`). For `β` not simple, `G̃_{-β}` is
  spanned by the `[fₖ, y]`, and `([fₖ, y] | x) = ±(y | [fₖ, x]) = 0`; for `β = αₖ` we have
  `x ∈ K eₖ` and `[fₖ, eₖ] ≠ 0`.
* For odd `i` the `𝔰𝔩₂` identity is replaced by its super analogue: for `v` with `[fᵢ, v] = 0` and
  `[h, v] = λ(h) v`, `[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v` with `c_m = λ(αᵢ^∨) + m` for `m`
  even and `c_m = m + 1` for `m` odd, since `[fᵢ, eᵢ] = αᵢ^∨` and `[fᵢ, [eᵢ, w]] = [αᵢ^∨, w] -
  [eᵢ, [fᵢ, w]]`. For `v = eⱼ` and `m = -aᵢⱼ` (even) the coefficient vanishes. This is where the
  parity condition on `A` enters.

For `k = j ≠ i` the bracket `[fⱼ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ]` has weight `(1 - aᵢⱼ) αᵢ`; it vanishes
since `G̃_{nαᵢ} = 0` for `n ≥ 3` and for `n = 2`, `i` even, and directly for `aᵢⱼ = 0 = aⱼᵢ`.

## Main definitions

* `Matrix.Realization.SuperEnveloping.adE`, `adF`: the iterated super commutators
  `(ad eᵢ)ⁿ v`, `(ad fᵢ)ⁿ v`.
* `Matrix.Realization.SuperEnveloping.serreE`, `serreF`: the Serre elements.

## Main results

* `Matrix.Realization.SuperEnveloping.omega_mem_maxIdeal`: the Chevalley involution preserves `R`.
* `Matrix.Realization.SuperEnveloping.mem_maxIdeal_of_superBracket_f_eq_zero`: [Kac] Lemma 1.5 for
  `G̃(A, τ)`.
* `Matrix.Realization.SuperEnveloping.superBracket_f_serreE`: `[fₖ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ] = 0`.
* `Matrix.Realization.SuperEnveloping.serreE_mem_maxIdeal`,
  `Matrix.Realization.SuperEnveloping.serreF_mem_maxIdeal`: the Serre relations hold in `G(A, τ)`.

## References

* [Kac78] V. G. Kac, *Infinite-dimensional algebras, Dedekind's η-function, classical Möbius
  function and the very strange formula*, Adv. Math. **30** (1978), 85–136, §1.2.
* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Lemma 1.5, §3.3.
-/

open Module

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H) (p : ι → ZMod 2) [CharZero K]

namespace SuperEnveloping

/-- The enveloping superalgebra `U(G̃(A, τ))`.-/
local notation "𝒰" => SuperEnveloping P p

/-! ### The Chevalley involution preserves `R` -/

/-! ### Iterated super commutators -/

/-- The iterated super commutator `(ad eᵢ)ⁿ v`.-/
def adE (i : ι) (n : ℕ) (v : 𝒰) : 𝒰 := (superBracketRight P p (e P p i) ^ n) v

/-- The iterated super commutator `(ad fᵢ)ⁿ v`.-/
def adF (i : ι) (n : ℕ) (v : 𝒰) : 𝒰 := (superBracketRight P p (f P p i) ^ n) v

omit [CharZero K] in
/--
@isnad1 id=eq.0h8v.s6.c957b354333f from=translated src=- shape=a086fb0d vocab=e1480ffe
-/
@[simp] lemma adE_zero (i : ι) (v : 𝒰) : adE P p i 0 v = v := rfl

omit [CharZero K] in
/--
@isnad1 id=eq.0h9v.s7.56bf13552e75 from=translated src=- shape=1f03ea07 vocab=7f2ab347
-/
lemma adE_succ (i : ι) (n : ℕ) (v : 𝒰) :
    adE P p i (n + 1) v = superBracket P p (e P p i) (adE P p i n v) := by
  rw [adE, pow_succ', Module.End.mul_apply]; rfl

omit [CharZero K] in
/--
@isnad1 id=eq.0h8v.s6.e809cd9869cc from=translated src=- shape=a086fb0d vocab=8ed9cf65
-/
@[simp] lemma adF_zero (i : ι) (v : 𝒰) : adF P p i 0 v = v := rfl

omit [CharZero K] in
/--
@isnad1 id=eq.0h9v.s7.bd01fdae723c from=translated src=- shape=1f03ea07 vocab=baa38ce9
-/
lemma adF_succ (i : ι) (n : ℕ) (v : 𝒰) :
    adF P p i (n + 1) v = superBracket P p (f P p i) (adF P p i n v) := by
  rw [adF, pow_succ', Module.End.mul_apply]; rfl

omit [CharZero K] in
/--
@isnad1 id=eq.0h9v.s9.757d5eb73907 from=translated src=- shape=85acbbe0 vocab=1723931e
-/
lemma omega_adE (i : ι) (n : ℕ) (v : 𝒰) :
    omega P p (adE P p i n v) = adF P p i n (omega P p v) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [adE_succ, adF_succ, omega_superBracket, omega_e, ih]

variable {P p}

/--
@isnad1 id=ishomog.1h10v.s8.8633ccc2fe2b from=translated src=- shape=ca0a83e6 vocab=261f2b4d
-/
lemma isHomog_adE (i : ι) (n : ℕ) {b : ZMod 2} {v : 𝒰} (hv : IsHomog P p b v) :
    IsHomog P p (n * p i + b) (adE P p i n v) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [adE_succ, show ((n + 1 : ℕ) : ZMod 2) * p i + b = p i + (n * p i + b) by push_cast; ring]
    exact (isHomog_e P p i).superBracket ih

omit [CharZero K] in
/--
@isnad1 id=mem.1h10v.s10.d4b317a9e784 from=translated src=- shape=c1a22ce1 vocab=83ff7700
-/
lemma adE_mem_weightSpace (i : ι) (n : ℕ) {μ : Dual K H} {v : 𝒰} (hv : v ∈ weightSpace P p μ) :
    adE P p i n v ∈ weightSpace P p (μ + n • P.root i) := by
  induction n with
  | zero => simpa using hv
  | succ n ih =>
    rw [adE_succ, succ_nsmul, ← add_assoc, add_comm _ (P.root i)]
    exact superBracket_mem_weightSpace (e_mem_weightSpace P p i) ih

/--
@isnad1 id=mem.1h9v.s9.07c1f591503f from=translated src=- shape=258c08b8 vocab=67a7a514
-/
lemma adE_mem_gTilde (i : ι) (n : ℕ) {v : 𝒰} (hv : v ∈ gTilde P p) :
    adE P p i n v ∈ gTilde P p := by
  induction n with
  | zero => exact hv
  | succ n ih => rw [adE_succ]; exact superBracket_e_mem_gTilde P p i ih

/-! ### Brackets with `fₖ` -/

omit [CharZero K] in
/--
@isnad1 id=eq.0h2v.s6.8f3566d66a56 from=translated src=- shape=f0fa78e8 vocab=28c63667
-/
lemma zSign_mul_self' (q : ZMod 2) : zSign K (q * q) = zSign K q := by
  rcases zmod_two_cases q with rfl | rfl <;> rfl

/-- `[fᵢ, [eᵢ, w]] = -(-1)^{p i} ν(αᵢ^∨) w + (-1)^{p i} [eᵢ, [fᵢ, w]]` for `w` of weight `ν`.
@isnad1 id=eq.2h10v.s10.3552e93269a0 from=translated src=- shape=faba68c4 vocab=aac8fc0f
-/
lemma superBracket_f_superBracket_e (i : ι) {c : ZMod 2} {ν : Dual K H} {w : 𝒰}
    (hw : IsHomog P p c w) (hwν : w ∈ weightSpace P p ν) :
    superBracket P p (f P p i) (superBracket P p (e P p i) w) =
      -((zSign K (p i) * ν (P.coroot i)) • w) +
        zSign K (p i) • superBracket P p (e P p i) (superBracket P p (f P p i) w) := by
  rw [superBracket_jacobi (isHomog_f P p i) (isHomog_e P p i) hw, superBracket_f_e,
    ite_eq_left rfl, superBracket_neg_left, superBracket_smul_left,
    superBracket_h_of_mem_weightSpace P p _ hwν, superSign_eq_zSign, zSign_mul_self',
    smul_smul]

/-- For `k ≠ i`, `fₖ` super-commutes with `eᵢ`, so `[fₖ, v] = 0` implies
`[fₖ, (ad eᵢ)ⁿ v] = 0`.
@isnad1 id=eq.3h11v.s8.d26226f94865 from=translated src=- shape=3e2708e2 vocab=40c3afdd
-/
lemma superBracket_f_adE_of_ne {k i : ι} (hki : k ≠ i) (n : ℕ) {b : ZMod 2} {v : 𝒰}
    (hv : IsHomog P p b v) (hfv : superBracket P p (f P p k) v = 0) :
    superBracket P p (f P p k) (adE P p i n v) = 0 := by
  induction n with
  | zero => exact hfv
  | succ n ih =>
    rw [adE_succ, superBracket_jacobi (isHomog_f P p k) (isHomog_e P p i) (isHomog_adE i n hv),
      superBracket_f_e, ite_eq_right hki, smul_zero, neg_zero, superBracket_zero_left, ih,
      superBracket_zero_right, smul_zero, add_zero]

/-- The coefficient `c_m` of `[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v`, for `λ = ⟨wt v, αᵢ^∨⟩`:
`-(m + 1)(λ + m)` for `eᵢ` even, and `λ + m` (`m` even), `m + 1` (`m` odd) for `eᵢ` odd.-/
def serreCoeff (q : ZMod 2) (c : K) (m : ℕ) : K :=
  if q = 1 then (if Even m then c + m else m + 1) else -((m + 1) * (c + m))

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s6.2f1b93c8f255 from=translated src=- shape=e4b8a166 vocab=2d05f5e9
-/
lemma serreCoeff_zero (q : ZMod 2) (c : K) : serreCoeff q c 0 = -(zSign K q * c) := by
  rcases zmod_two_cases q with rfl | rfl <;> simp [serreCoeff, zSign]

omit [CharZero K] in
/--
@isnad1 id=eq.0h4v.s7.3e1cf3b37cf6 from=translated src=- shape=c8245d58 vocab=3a4d45a2
-/
lemma serreCoeff_succ (q : ZMod 2) (c : K) (m : ℕ) :
    serreCoeff q c (m + 1) =
      -(zSign K q * (c + 2 * (m + 1 : ℕ))) + zSign K q * serreCoeff q c m := by
  rcases zmod_two_cases q with rfl | rfl
  · simp only [serreCoeff, zSign, zero_ne_one, ite_false, one_mul]
    push_cast; ring
  · rcases Nat.even_or_odd m with hm | hm
    · have hm' : ¬ Even (m + 1) := Nat.not_even_iff_odd.2 hm.add_one
      simp only [serreCoeff, zSign, ite_true, hm, hm', ite_false]
      push_cast; ring
    · have hm' : Even (m + 1) := hm.add_one
      have hm'' : ¬ Even m := Nat.not_even_iff_odd.2 hm
      simp only [serreCoeff, zSign, ite_true, hm', hm'', ite_false]
      push_cast; ring

/-- The super `𝔰𝔩₂` identity: for `v` of weight `μ` with `[fᵢ, v] = 0`,
`[fᵢ, (ad eᵢ)^{m+1} v] = c_m (ad eᵢ)^m v`.
@isnad1 id=eq.4h11v.s9.d5958b015295 from=translated src=- shape=6a5a3864 vocab=8fe8718c
-/
lemma superBracket_f_adE_succ (hA : A.IsGeneralizedCartan) (i : ι) {b : ZMod 2} {μ : Dual K H}
    {v : 𝒰} (hv : IsHomog P p b v) (hvμ : v ∈ weightSpace P p μ)
    (hfv : superBracket P p (f P p i) v = 0) (m : ℕ) :
    superBracket P p (f P p i) (adE P p i (m + 1) v) =
      serreCoeff (p i) (μ (P.coroot i)) m • adE P p i m v := by
  induction m with
  | zero =>
    rw [adE_succ, adE_zero, superBracket_f_superBracket_e i hv hvμ, hfv, superBracket_zero_right,
      smul_zero, add_zero, serreCoeff_zero, neg_smul]
  | succ m ih =>
    rw [adE_succ, superBracket_f_superBracket_e i (isHomog_adE i (m + 1) hv)
      (adE_mem_weightSpace i (m + 1) hvμ), ih, superBracket_smul_right, ← adE_succ, smul_smul,
      ← neg_smul, ← add_smul, serreCoeff_succ]
    congr 1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, P.root_coroot, hA.diag, nsmul_eq_mul]
    push_cast; ring

/-! ### The Serre elements -/

variable (P p) in
/-- The positive Serre element `(ad eᵢ)^{1 - aᵢⱼ} eⱼ`.-/
def serreE (i j : ι) : 𝒰 := adE P p i ((-A i j).toNat + 1) (e P p j)

variable (P p) in
/-- The negative Serre element `(ad fᵢ)^{1 - aᵢⱼ} fⱼ`.-/
def serreF (i j : ι) : 𝒰 := adF P p i ((-A i j).toNat + 1) (f P p j)

omit [CharZero K] in
/--
@isnad1 id=eq.0h8v.s8.993e1fe7f460 from=translated src=- shape=2667bf65 vocab=bf2c871d
-/
lemma omega_serreE (i j : ι) : omega P p (serreE P p i j) = serreF P p i j := by
  rw [serreE, omega_adE, omega_e, serreF]

/--
@isnad1 id=mem.0h8v.s8.007d50d2658f from=translated src=- shape=e935e0c6 vocab=95835459
-/
lemma serreE_mem_gTilde (i j : ι) : serreE P p i j ∈ gTilde P p :=
  adE_mem_gTilde i _ (nPlus_le_gTilde P p (e_mem_nPlus P p j))

omit [CharZero K] in
/--
@isnad1 id=mem.0h8v.s9.d6e8132876b7 from=translated src=- shape=53bca55a vocab=d8c7e1d9
-/
lemma serreE_mem_weightSpace (i j : ι) :
    serreE P p i j ∈ weightSpace P p (P.root j + ((-A i j).toNat + 1) • P.root i) :=
  adE_mem_weightSpace i _ (e_mem_weightSpace P p j)

/-- `[fₖ, (ad eᵢ)^{1 - aᵢⱼ} eⱼ] = 0` for all `k` ([Kac78] §1.2, cf. [Kac] §3.3).
@isnad1 id=eq.3h9v.s7.27e9926e44b8 from=translated src=- shape=1adb6719 vocab=8a0b052d
-/
theorem superBracket_f_serreE (hA : A.IsGeneralizedCartan) (hp : A.IsSuperAdmissible p)
    {i j : ι} (hij : i ≠ j) (k : ι) : superBracket P p (f P p k) (serreE P p i j) = 0 := by
  have hn : ((-A i j).toNat : ℤ) = -A i j := Int.toNat_of_nonneg (by
    linarith [hA.offDiag_nonpos i j hij])
  by_cases hki : k = i
  · subst hki
    rw [serreE, superBracket_f_adE_succ hA k (isHomog_e P p j) (e_mem_weightSpace P p j)
      (by rw [superBracket_f_e, ite_eq_right hij, smul_zero, neg_zero]), P.root_coroot]
    have hc : serreCoeff (p k) (A k j : K) (-A k j).toNat = 0 := by
      have hn' : (((-A k j).toNat : ℕ) : K) = -(A k j : K) := by exact_mod_cast hn
      unfold serreCoeff
      split_ifs with hk he
      · rw [hn']; ring
      · exact absurd (by
          obtain ⟨r, hr⟩ := hp k j hk
          exact ⟨(-r).toNat, by omega⟩) he
      · rw [hn']; ring
    rw [hc, zero_smul]
  by_cases hkj : k = j
  · subst hkj
    set n := (-A i k).toNat with hn_def
    have hw : superBracket P p (f P p k) (serreE P p i k) ∈
        weightSpace P p ((n + 1) • P.root i) := by
      have := superBracket_mem_weightSpace (f_mem_weightSpace P p k) (serreE_mem_weightSpace i k)
      rwa [neg_add_cancel_left] at this
    have hG : superBracket P p (f P p k) (serreE P p i k) ∈ gTilde P p :=
      superBracket_f_mem_gTilde P p k (serreE_mem_gTilde i k)
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rcases Nat.lt_or_ge n 1 with h1 | h1
      · -- `aᵢⱼ = 0`, so `aⱼᵢ = 0` and `[fⱼ, [eᵢ, eⱼ]] = ±[eᵢ, hⱼ] = 0`
        have hA0 : A i k = 0 := by omega
        have hA0' : A k i = 0 := (hA.zero_comm i k).1 hA0
        rw [serreE, ← hn_def, show n = 0 by omega, adE_succ, adE_zero,
          superBracket_jacobi (isHomog_f P p k) (isHomog_e P p i) (isHomog_e P p k),
          superBracket_f_e, ite_eq_right hki, superBracket_f_e, ite_eq_left rfl, smul_zero,
          neg_zero, superBracket_zero_left, zero_add,
          show ∀ y, superBracket P p (e P p i) (-y) = -superBracket P p (e P p i) y from
            fun y ↦ (superBracketRight P p (e P p i)).map_neg y,
          superBracket_smul_right, superBracket_e_h, P.root_coroot, hA0']
        simp
      · -- `n = 1`, so `aᵢⱼ = -1` is odd and `eᵢ` is even: `G̃_{2αᵢ} = 0`
        have hA1 : A i k = -1 := by omega
        have hi : p i = 0 := by
          rcases zmod_two_cases (p i) with hi | hi
          · exact hi
          · obtain ⟨r, hr⟩ := hp i k hi; omega
        refine eq_zero_of_mem_two_root_of_even P p hi hG (Or.inl ?_)
        rwa [show n + 1 = 2 by omega] at hw
    · exact eq_zero_of_mem_weightSpace_nsmul_root P p (by omega) hG hw
  · rw [serreE]
    exact superBracket_f_adE_of_ne hki _ (isHomog_e P p j)
      (by rw [superBracket_f_e, ite_eq_right hkj, smul_zero, neg_zero])

/-! ### The Serre elements lie in `R` -/

variable [FiniteDimensional K H] (S : A.Symmetrization)

end SuperEnveloping

end Matrix.Realization
