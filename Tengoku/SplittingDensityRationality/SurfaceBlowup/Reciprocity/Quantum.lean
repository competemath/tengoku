/-
Copyright (c) 2026 Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G, Claude (Anthropic), GPT-6-Astra (OpenAI)
-/
import Tengoku.SplittingDensityRationality.SurfaceBlowup.Reciprocity.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reciprocity: the quantum torus, dilations and reciprocal substitution

Algebraic properties of the reciprocity setting of `SurfaceBlowup.Reciprocity.Defs`. We show that
`q ↦ q⁻¹` is an involution of `ℚ(q)` and of `Coef`, commuting with the Adams operations; that the
reciprocal substitution `recipSer` and the dilations `dilate`/`codilate` act coefficientwise and
commute with the plethystic powers; that the twisted product on contact series is associative and
compatible with `ι₊`, `ι₋`, the anti-involution `†` and the diagonal substitution; and we relate
the representation `qact` to its `q ↦ q⁻¹` conjugate through the Gauss twist `Φ`.

## Main results

* `recipRat_recipRat`, `recipCoef_recipCoef`, `recipCoef_adamsCoef`, `adamsCoef_adamsCoef`.
* `qmul_assoc`, `qdagger_qmul`, `qdagger_qplus`, `qdagger_qminus`, `qdiag_mul`,
  `qcongr_qdiag_mul_qdagger`.
* `recipSer_pPow`, `dilate_pPow`, `codilate_pPow`, `moebiusSum_plethSum`, `plethSum_moebiusSum`.
* `gaussPhi_qactRecip_gaussPhiInv`: `Φ ∘ ρ̄(v V) ∘ Φ⁻¹ = S⁻¹ ∘ ρ(V†) ∘ S` for symmetric `V`.
* `SCongr.mul`, `SCongr.of_mul_right`, `SCongr.expSer`, `SCongr.logSer`: congruences of series.

Provenance: `Thm_SurfaceBlowupV2_recip_{qplus_mul, qpositive_basic, recipRat_apply,
adamsCoef_recipCoef_single, adamsSer_exp_log, plethSum_moebiusSum, projectiveNormalizer_recip,
qact_recip, qpow_scalar_arith, qdagger_mul, qdagger_qplus_qminus, qmul_assoc, recipSer_hom,
dilate_hom, dilate_pleth, gaussPhi_inv, gauss_conjugation, qdiag_mul, qdiag_central, recipSer_pleth,
scalar_cancel, scongr_basic, scongr_cancel, scongr_exp_log}`.
-/

noncomputable section

namespace SurfaceBlowup

/-! ### The substitution `q ↦ q⁻¹` and Adams operations on coefficients -/

private theorem recipRat_recipPoly (g : Polynomial ℚ) :
    recipRat (recipPoly g) = algebraMap (Polynomial ℚ) (RatFunc ℚ) g := by
  change recipRat (g.eval₂ RatFunc.C (RatFunc.X : RatFunc ℚ)⁻¹) = _
  rw [Polynomial.hom_eval₂,
    show recipRat.comp (RatFunc.C : ℚ →+* RatFunc ℚ) = RatFunc.C from RingHom.ext recipRat_C,
    map_inv₀, recipRat_X, inv_inv]
  exact eval₂_C_X_eq_algebraMap g

/-- `q ↦ q⁻¹` is an involution of `ℚ(q)`.
@isnad1 id=eq.0h1v.s7.b8ae8bd45229 from=translated src=- shape=12b11dcb vocab=7a2da644
-/
theorem recipRat_recipRat (f : RatFunc ℚ) : recipRat (recipRat f) = f := by
  conv_lhs => rw [← RatFunc.num_div_denom f]
  rw [map_div₀, map_div₀, recipRat_algebraMap, recipRat_algebraMap, recipRat_recipPoly,
    recipRat_recipPoly, RatFunc.num_div_denom]

/-- `v(q^k) = q^{-k}` for integer `k`.-/
private theorem recipRat_zpow_X (k : ℤ) :
    recipRat ((RatFunc.X : RatFunc ℚ) ^ k) = (RatFunc.X : RatFunc ℚ) ^ (-k) := by
  rw [map_zpow₀, recipRat_X, zpow_neg, inv_zpow]

/-- `ψ_δ` on a monomial: `q ↦ q^δ` on the coefficient and `Z_{e,f} ↦ Z_{e,δf}` on the type.
@isnad1 id=eq.0h3v.s8.246feccfc26b from=translated src=- shape=08c3e74b vocab=a02f92ec
-/
theorem adamsCoef_single (δ : ℕ) (σ : FactorType) (f : RatFunc ℚ) :
    adamsCoef δ (AddMonoidAlgebra.single σ f) =
      AddMonoidAlgebra.single (scaleType δ σ) (adamsRat δ f) := by
  simp [adamsCoef, AddMonoidAlgebra.mapRingHom_single, scaleTypeHom]
  rfl

/-- `v` on a monomial acts on the coefficient only.
@isnad1 id=eq.0h2v.s8.a647038cb76d from=translated src=- shape=4280a546 vocab=92912bb8
-/
theorem recipCoef_single (σ : FactorType) (f : RatFunc ℚ) :
    recipCoef (AddMonoidAlgebra.single σ f) = AddMonoidAlgebra.single σ (recipRat f) := by
  simp [recipCoef, AddMonoidAlgebra.mapRingHom_single]

/-- `ψ_δ` on scalars is `q ↦ q^δ`.
@isnad1 id=eq.0h2v.s8.61013a7e4b79 from=translated src=- shape=a246b2f9 vocab=e805f4bb
-/
theorem adamsCoef_scalar (δ : ℕ) (f : RatFunc ℚ) :
    adamsCoef δ (scalar f) = scalar (adamsRat δ f) := by
  simp only [scalar, adamsCoef_single, scaleType, Multiset.map_zero]

/-- `v` on scalars is `q ↦ q⁻¹`.
@isnad1 id=eq.0h1v.s7.131e0d8cd1c3 from=translated src=- shape=1e06e3df vocab=f420f322
-/
theorem recipCoef_scalar (f : RatFunc ℚ) : recipCoef (scalar f) = scalar (recipRat f) :=
  recipCoef_single 0 f

/-- `v` on coefficients: `(v x)_σ = v(x_σ)`.
@isnad1 id=eq.0h2v.s8.97f06b0079f0 from=translated src=- shape=cdb0faa6 vocab=fa1942e6
-/
theorem recipCoef_coeff (x : Coef) (σ : FactorType) :
    (recipCoef x).coeff σ = recipRat (x.coeff σ) := by
  simp [recipCoef, AddMonoidAlgebra.coeff_mapRingHom]

private theorem coef_ringHom_ext {F G : Coef →+* Coef}
    (h : ∀ σ g, F (AddMonoidAlgebra.single σ g) = G (AddMonoidAlgebra.single σ g)) (y : Coef) :
    F y = G y :=
  DFunLike.congr_fun (AddMonoidAlgebra.ringHom_ext (fun r ↦ h 0 r) (fun m ↦ h m 1)) y

/-- `v` is an involution of `Coef`.
@isnad1 id=eq.0h1v.s8.63147259aba0 from=translated src=- shape=c3d0c544 vocab=1b68a911
-/
theorem recipCoef_recipCoef (x : Coef) : recipCoef (recipCoef x) = x :=
  coef_ringHom_ext (F := recipCoef.comp recipCoef) (G := RingHom.id _) (fun σ g ↦ by
    simp only [RingHom.comp_apply, recipCoef_single, recipRat_recipRat, RingHom.id_apply]) x

/-- `v` commutes with the Adams operations on `Coef`.
@isnad1 id=eq.1h2v.s9.47a2c787edec from=translated src=- shape=eff00f84 vocab=a0f56d2c
-/
theorem recipCoef_adamsCoef (δ : ℕ) (hδ : 0 < δ) (x : Coef) :
    recipCoef (adamsCoef δ x) = adamsCoef δ (recipCoef x) :=
  coef_ringHom_ext (F := recipCoef.comp (adamsCoef δ)) (G := (adamsCoef δ).comp recipCoef)
    (fun σ g ↦ by
      simp only [RingHom.comp_apply, recipCoef_single, adamsCoef_single, adamsRat_recipRat δ hδ]) x

/-- `ψ_δ ∘ ψ_k = ψ_{δk}` on `Coef`.
@isnad1 id=eq.2h3v.s8.06a612b29d50 from=translated src=- shape=3a0914a2 vocab=19f86a05
-/
theorem adamsCoef_adamsCoef (δ k : ℕ) (hδ : 0 < δ) (hk : 0 < k) (x : Coef) :
    adamsCoef δ (adamsCoef k x) = adamsCoef (δ * k) x :=
  coef_ringHom_ext (F := (adamsCoef δ).comp (adamsCoef k)) (G := adamsCoef (δ * k))
    (fun σ g ↦ by
      simp only [RingHom.comp_apply, adamsCoef_single, adamsRat_adamsRat δ k hδ hk, scaleType,
        Multiset.map_map, Function.comp_def, mul_assoc]) x

/-- `ψ_1` is the identity of `Coef`.
@isnad1 id=eq.0h1v.s7.8c52d0332735 from=translated src=- shape=2cf3cb28 vocab=9d803a85
-/
theorem adamsCoef_one (x : Coef) : adamsCoef 1 x = x :=
  coef_ringHom_ext (F := adamsCoef 1) (G := RingHom.id _) (fun σ g ↦ by
    simp [adamsCoef_single, adamsRat_one, scaleType]) x

/-- `scalar : ℚ(q) → Coef` is multiplicative.
@isnad1 id=eq.0h2v.s6.6696468d0e45 from=translated src=- shape=31b9e54f vocab=08778671
-/
theorem scalar_mul (f g : RatFunc ℚ) : scalar (f * g) = scalar f * scalar g := by
  simp only [scalar, AddMonoidAlgebra.single_mul_single, add_zero]

/-- `scalar : ℚ(q) → Coef` is additive.
@isnad1 id=eq.0h2v.s6.81bef9709932 from=translated src=- shape=31b9e54f vocab=c01a6d6b
-/
theorem scalar_add (f g : RatFunc ℚ) : scalar (f + g) = scalar f + scalar g :=
  AddMonoidAlgebra.single_add _ _ _

/-- `scalar 1 = 1`.
@isnad1 id=eq.0h0v.s5.9d2707d0acb5 from=translated src=- shape=479f814a vocab=5a757957
-/
theorem scalar_one : scalar 1 = 1 := rfl

/-- `scalar` is the algebra map `ℚ(q) → Coef`.
@isnad1 id=eq.0h1v.s7.aa6884460f0a from=translated src=- shape=441ff565 vocab=399ab863
-/
theorem scalar_eq_algebraMap (f : RatFunc ℚ) : scalar f = algebraMap (RatFunc ℚ) Coef f := by
  ext i
  simp [scalar, AddMonoidAlgebra.coe_algebraMap]

/-- Multiplication by `scalar r` is the `ℚ(q)`-scalar action.
@isnad1 id=eq.0h2v.s7.3ba4825ab654 from=translated src=- shape=083881b5 vocab=161b4d95
-/
theorem scalar_mul_eq_smul (r : RatFunc ℚ) (x : Coef) : scalar r * x = r • x := by
  rw [scalar_eq_algebraMap, Algebra.smul_def]

/-- The `ℚ`-scalar action on `Coef` is multiplication by the constant scalar.
@isnad1 id=eq.0h2v.s7.c073f32286b6 from=translated src=- shape=6641d062 vocab=6800e024
-/
theorem rat_smul_eq_scalar_mul (q : ℚ) (x : Coef) : q • x = scalar (RatFunc.C q) * x := by
  rw [scalar_eq_algebraMap, Algebra.smul_def,
    IsScalarTower.algebraMap_apply ℚ (RatFunc ℚ) Coef, eq_ratCast (algebraMap ℚ _) q,
    eq_ratCast RatFunc.C q]

/-- `v(q^j) = q^{-j}`.-/
private theorem recipCoef_qpow (j : ℤ) : recipCoef (qpow j) = qpow (-j) := by
  rw [qpow, recipCoef_scalar, recipRat_zpow_X, qpow]

/-- `ψ_δ(q^j) = q^{δj}`.-/
private theorem adamsCoef_qpow (δ : ℕ) (hδ : 0 < δ) (j : ℤ) :
    adamsCoef δ (qpow j) = qpow ((δ : ℤ) * j) := by
  rw [qpow, adamsCoef_scalar, adamsRat_zpow_X δ hδ, qpow]

/-- `q^n` for natural `n` is the scalar `X^n`.
@isnad1 id=eq.0h1v.s5.392f2fbdda6e from=translated src=- shape=ff7214d6 vocab=b654317d
-/
theorem qpow_natCast (n : ℕ) : qpow (n : ℤ) = scalar ((RatFunc.X : RatFunc ℚ) ^ n) := by
  simp [qpow]

/-- `q^1` is the scalar `X`.
@isnad1 id=eq.0h0v.s3.d5bcabae78ac from=translated src=- shape=d44d1fee vocab=b64c8bcf
-/
theorem qpow_one : qpow 1 = scalar (RatFunc.X : RatFunc ℚ) := by simp [qpow]

/-- `q^{-j} q^j = 1`.
@isnad1 id=eq.0h1v.s6.0509601ff71b from=translated src=- shape=aad84fc8 vocab=ffbb6f1f
-/
theorem qpow_neg_mul_qpow (j : ℤ) : qpow (-j) * qpow j = 1 := by
  rw [← qpow_add, neg_add_cancel, qpow_zero]

/-! ### The twisted product on contact series -/

/-- Positivity (vanishing on the axes away from `(0,0)`) is preserved by the twisted product.
@isnad1 id=qpositiv.2h2v.s3.ef4e751b98da from=translated src=- shape=03e07a40 vocab=e16da7f7
-/
theorem QPositive.qmul {U V : QSer} (hU : QPositive U) (hV : QPositive V) :
    QPositive (qmul U V) := by
  intro c h hc hn
  refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hr
  have : U p.1 r.1 * V p.2 r.2 = 0 := by
    rcases hc with rfl | rfl
    · by_cases h1 : r.1 = 0
      · have : r.2 ≠ 0 := by omega
        have : p.1 = 0 := by omega
        have : p.2 = 0 := by omega
        rw [hV p.2 r.2 (Or.inl ‹_›) (by omega), mul_zero]
      · rw [hU p.1 r.1 (Or.inl (by omega)) (by omega), zero_mul]
    · by_cases h1 : p.1 = 0
      · have : p.2 ≠ 0 := by omega
        rw [hV p.2 r.2 (Or.inr (by omega)) (by omega), mul_zero]
      · rw [hU p.1 r.1 (Or.inr (by omega)) (by omega), zero_mul]
  rw [this, mul_zero]

/-- Positivity is preserved by `†`.
@isnad1 id=qpositiv.1h1v.s3.08d1159419ac from=translated src=- shape=2c86d966 vocab=c9c1f608
-/
theorem QPositive.qdagger {U : QSer} (hU : QPositive U) : QPositive (qdagger U) :=
  fun c h hc hn ↦ by simp [SurfaceBlowup.qdagger, hU c h hc hn]

/-- Positivity is preserved by `ι₊`.
@isnad1 id=qpositiv.1h1v.s3.12b87accff12 from=translated src=- shape=2c86d966 vocab=bd133d8a
-/
theorem QPositive.qplus {U : QSer} (hU : QPositive U) : QPositive (qplus U) := by
  intro c k hc hn
  unfold SurfaceBlowup.qplus
  split_ifs with h1
  · rw [hU c (k - c) (by omega) (by omega), mul_zero]
  · rfl

/-- Positivity is preserved by `ι₋`.
@isnad1 id=qpositiv.1h1v.s3.9322fe60e2e1 from=translated src=- shape=2c86d966 vocab=73d798b8
-/
theorem QPositive.qminus {U : QSer} (hU : QPositive U) : QPositive (qminus U) := by
  intro k h hc hn
  unfold SurfaceBlowup.qminus
  split_ifs with h1
  · rw [hU (k - h) h (by omega) (by omega), mul_zero]
  · rfl

/-- The diagonal substitution of a series is positive.
@isnad1 id=qpositiv.0h1v.s2.7413e0d2f08d from=translated src=- shape=76a08d12 vocab=df9355a1
-/
theorem qPositive_qdiag (f : Ser) : QPositive (qdiag f) := fun c h hc hn ↦ by
  unfold qdiag
  rw [ite_eq_right (by omega)]

/-- The constant term of a twisted product: `(U V)₀₀ = U₀₀ V₀₀`.
@isnad1 id=eq.0h2v.s6.e127d1db30aa from=translated src=- shape=79c181e4 vocab=c6a661e7
-/
theorem qmul_zero_zero (U V : QSer) : (qmul U V) 0 0 = U 0 0 * V 0 0 := by
  simp [qmul, qpow_zero]

/-! ### Adams operations, `exp` and `log` -/

private theorem adamsSer_subst (k : ℕ) (hk : k ≠ 0) (φ : Ser)
    (hφ : PowerSeries.map (adamsCoef k) φ = φ) (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    adamsSer k (φ.subst f) = φ.subst (adamsSer k f) := by
  have hs' : PowerSeries.HasSubst (PowerSeries.map (adamsCoef k) f) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, map_zero])
  have hm : PowerSeries.map (adamsCoef k) (φ.subst f) =
      φ.subst (PowerSeries.map (adamsCoef k) f) := by
    have := PowerSeries.map_subst (h := adamsCoef k)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf) φ
    rwa [hφ] at this
  rw [adamsSer, adamsSer, dite_eq_right hk, dite_eq_right hk, hm]
  exact PowerSeries.expand_subst k hk hs' φ

/-- `ψ_k` on series commutes with the logarithm (`k ≠ 0`, `g(0) = 1`).
@isnad1 id=eq.2h2v.s7.784e62662003 from=translated src=- shape=a7dae240 vocab=ca6a28e4
-/
theorem adamsSer_logSer (k : ℕ) (hk : k ≠ 0) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    adamsSer k (logSer g) = logSer (adamsSer k g) := by
  rw [logSer, logSer, PowerSeries.logOf_eq, PowerSeries.logOf_eq,
    adamsSer_subst k hk _ (PowerSeries.map_log _) _ (by simp [hg]), adamsSer_sub k hk,
    adamsSer_one k hk]

/-- Reindexing a double divisor sum: pairs `(k, j)` with `k ∣ n`, `j ∣ n/k` correspond to pairs
`(m, k)` with `m ∣ n`, `k ∣ m` via `m = kj`.
@isnad1 id=eq.0h3v.s6.ed6a2d843933 from=translated src=- shape=aff39646 vocab=318677d1
-/
theorem sum_divisors_sum_divisors_div {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : ℕ → ℕ → M) :
    ∑ k ∈ n.divisors, ∑ j ∈ (n / k).divisors, F k j
      = ∑ m ∈ n.divisors, ∑ k ∈ m.divisors, F k (m / k) := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ ↦ ⟨x.1 * x.2, x.1⟩) (fun y _ ↦ ⟨y.2, y.1 / y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨k, j⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hk, hn⟩, hj, hnk⟩ := h
    refine ⟨⟨?_, hn⟩, Dvd.intro _ rfl, ?_⟩
    · obtain ⟨a, ha⟩ := hj
      exact ⟨a, by rw [mul_assoc, ← ha, Nat.mul_div_cancel' hk]⟩
    · have hk0 : k ≠ 0 := by rintro rfl; exact hn (zero_dvd_iff.1 hk)
      have hj0 : j ≠ 0 := by rintro rfl; exact hnk (zero_dvd_iff.1 hj)
      exact mul_ne_zero hk0 hj0
  · rintro ⟨m, k⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h ⊢
    obtain ⟨⟨hm, hn⟩, hk, hm0⟩ := h
    refine ⟨⟨dvd_trans hk hm, hn⟩, ?_, ?_⟩
    · obtain ⟨a, ha⟩ := hm
      obtain ⟨b, hb⟩ := hk
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hm0 (by simpa using hb))
      refine ⟨a, ?_⟩
      rw [ha, hb, mul_assoc, Nat.mul_div_cancel_left _ hk0, Nat.mul_div_cancel_left _ hk0]
    · have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hk (Nat.pos_of_ne_zero hm0)
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (dvd_trans hk hm)) hk0
      omega
  · rintro ⟨k, j⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    simp [Nat.mul_div_cancel_left _ hk0]
  · rintro ⟨m, k⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h
    simp [Nat.mul_div_cancel' h.2.1]
  · rintro ⟨k, j⟩ h
    simp only [Finset.mem_sigma, Nat.mem_divisors] at h
    have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
    simp [Nat.mul_div_cancel_left _ hk0]

/-- The divisor transform `[xⁿ] ↦ Σ_{k ∣ n} w(k) ψ_k([x^{n/k}] f)`.-/
private def divisorTransform (w : ℕ → ℚ) (f : Ser) : Ser :=
  PowerSeries.mk fun n ↦ ∑ k ∈ n.divisors, w k • adamsCoef k (PowerSeries.coeff (n / k) f)

private theorem plethSum_eq (f : Ser) : plethSum f = divisorTransform (fun k ↦ (k : ℚ)⁻¹) f := rfl

private theorem moebiusSum_eq (f : Ser) :
    moebiusSum f = divisorTransform (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℚ) / k) f :=
  rfl

private theorem coeff_divisorTransform_comp (a b : ℕ → ℚ) (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (divisorTransform a (divisorTransform b f)) =
      ∑ m ∈ n.divisors, (∑ k ∈ m.divisors, a k * b (m / k)) •
        adamsCoef m (PowerSeries.coeff (n / m) f) := by
  simp only [divisorTransform, PowerSeries.coeff_mk, map_sum, map_rat_smul, Finset.smul_sum]
  have h1 : ∀ k ∈ n.divisors, ∀ j ∈ (n / k).divisors,
      a k • b j • adamsCoef k (adamsCoef j (PowerSeries.coeff (n / k / j) f))
        = (fun k j ↦ (a k * b j) • adamsCoef (k * j) (PowerSeries.coeff (n / (k * j)) f)) k j := by
    intro k hk j hj
    have hk0 : 0 < k := Nat.pos_of_mem_divisors hk
    have hj0 : 0 < j := Nat.pos_of_mem_divisors hj
    simp only [smul_smul, adamsCoef_adamsCoef k j hk0 hj0, Nat.div_div_eq_div_mul]
  rw [Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl (h1 k hk),
    sum_divisors_sum_divisors_div]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]

/-- `Σ_{k ∣ m} μ(k)` is `1` for `m = 1` and `0` otherwise.
@isnad1 id=eq.0h1v.s5.d0f2cc61b814 from=translated src=- shape=2c947f87 vocab=dd7b9957
-/
theorem sum_divisors_moebius (m : ℕ) :
    ∑ k ∈ m.divisors, ((ArithmeticFunction.moebius k : ℤ) : ℚ) = if m = 1 then 1 else 0 := by
  have := congrArg (fun F ↦ F m) (ArithmeticFunction.moebius_mul_coe_zeta)
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
  rw [← Int.cast_sum, this]
  split_ifs <;> simp

private theorem divisorTransform_inv (a b : ℕ → ℚ) (f : Ser) (hf : PowerSeries.constantCoeff f = 0)
    (hab : ∀ m, ∑ k ∈ m.divisors, a k * b (m / k) = if m = 1 then 1 else 0) :
    divisorTransform a (divisorTransform b f) = f := by
  ext n
  rw [coeff_divisorTransform_comp]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hf]
  · simp only [hab, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq']
    simp [Nat.ne_of_gt hn, adamsCoef_one]

private theorem moebius_weight_left (m : ℕ) :
    ∑ k ∈ m.divisors, (((ArithmeticFunction.moebius k : ℤ) : ℚ) / (k : ℚ)) * ((m / k : ℕ) : ℚ)⁻¹
      = if m = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : ∀ k ∈ m.divisors,
      (((ArithmeticFunction.moebius k : ℤ) : ℚ) / (k : ℚ)) * ((m / k : ℕ) : ℚ)⁻¹
      = ((ArithmeticFunction.moebius k : ℤ) : ℚ) * (m : ℚ)⁻¹ := by
    intro k hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hk) hk0]
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul, sum_divisors_moebius]
  split_ifs with h <;> simp [h]

private theorem moebius_weight_right (m : ℕ) :
    ∑ k ∈ m.divisors,
      ((k : ℚ))⁻¹ * (((ArithmeticFunction.moebius (m / k) : ℤ) : ℚ) / ((m / k : ℕ) : ℚ))
      = if m = 1 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have : ∀ k ∈ m.divisors,
      ((k : ℚ))⁻¹ * (((ArithmeticFunction.moebius (m / k) : ℤ) : ℚ) / ((m / k : ℕ) : ℚ))
      = ((ArithmeticFunction.moebius (m / k) : ℤ) : ℚ) * (m : ℚ)⁻¹ := by
    intro k hk
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hk).ne'
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hk) hk0]
    have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  rw [Finset.sum_congr rfl this, ← Finset.sum_mul,
    Nat.sum_div_divisors m (fun k ↦ ((ArithmeticFunction.moebius k : ℤ) : ℚ)),
    sum_divisors_moebius]
  split_ifs with h <;> simp [h]

/-- Möbius inversion: `moebiusSum (plethSum f) = f` for `f(0) = 0`.
@isnad1 id=eq.1h1v.s7.8427029f9f91 from=translated src=- shape=2f3348cb vocab=7e5550dc
-/
theorem moebiusSum_plethSum (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    moebiusSum (plethSum f) = f :=
  divisorTransform_inv _ _ f hf moebius_weight_left

/-- Möbius inversion: `plethSum (moebiusSum f) = f` for `f(0) = 0`.
@isnad1 id=eq.1h1v.s7.3b964b0a796f from=translated src=- shape=2f3348cb vocab=7e5550dc
-/
theorem plethSum_moebiusSum (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    plethSum (moebiusSum f) = f :=
  divisorTransform_inv _ _ f hf moebius_weight_right

/-- `plethSum` is additive.
@isnad1 id=eq.0h2v.s6.f9bf5bc1a4da from=translated src=- shape=a13ca989 vocab=d0cf0fa3
-/
theorem plethSum_add (f g : Ser) : plethSum (f + g) = plethSum f + plethSum g := by
  ext n; simp [plethSum, Finset.sum_add_distrib]

/-- `plethSum f` has constant term `0`.
@isnad1 id=eq.0h1v.s7.066cb073653c from=translated src=- shape=dcb63727 vocab=55d2e18e
-/
theorem constantCoeff_plethSum (f : Ser) : PowerSeries.constantCoeff (plethSum f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [plethSum]

/-- `moebiusSum f` has constant term `0`.
@isnad1 id=eq.0h1v.s7.172b54be6f87 from=translated src=- shape=dcb63727 vocab=85c41011
-/
theorem constantCoeff_moebiusSum (f : Ser) : PowerSeries.constantCoeff (moebiusSum f) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]; simp [moebiusSum]

/-! ### The projective normalizer -/

private theorem fraction_pow_var (i : ℕ) :
    (Expr.pow Expr.var i).fraction = ((Polynomial.X : Polynomial ℚ) ^ i, 1) := by
  induction i with
  | zero => simp [Expr.pow, Expr.fraction]
  | succ k ih => simp [Expr.pow, Expr.fraction, ih, pow_succ]

private theorem fraction_sum_pow_var (L : List ℕ) :
    (Expr.sum (L.map fun i ↦ Expr.pow Expr.var i)).fraction
      = ((L.map fun i ↦ (Polynomial.X : Polynomial ℚ) ^ i).sum, 1) := by
  induction L with
  | nil => simp [Expr.sum, Expr.fraction]
  | cons a L ih =>
    simp only [List.map_cons, Expr.sum, List.foldr_cons] at ih ⊢
    rw [Expr.fraction, ih, fraction_pow_var]
    simp

/-- The projective normalizer is `[n+1]_q = 1 + q + ⋯ + qⁿ`.-/
private theorem rational_projectiveNormalizer (n : ℕ) :
    (projectiveNormalizer n).rational =
      ∑ i ∈ Finset.range (n + 1), (RatFunc.X : RatFunc ℚ) ^ i := by
  unfold projectiveNormalizer Expr.rational
  rw [fraction_sum_pow_var]
  simp only [map_one, div_one]
  have e (m : ℕ) (f : ℕ → Polynomial ℚ) :
      ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i := by
    induction m with
    | zero => simp
    | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp
  rw [e, map_sum]
  simp [map_pow, RatFunc.algebraMap_X]

/-- `v([n+1]_q) = q⁻ⁿ [n+1]_q`.
@isnad1 id=eq.0h1v.s7.fe1ce67b5536 from=translated src=- shape=eb36196a vocab=6e841e42
-/
theorem recipRat_projectiveNormalizer (n : ℕ) :
    recipRat (projectiveNormalizer n).rational =
      (RatFunc.X ^ n)⁻¹ * (projectiveNormalizer n).rational := by
  rw [rational_projectiveNormalizer, map_sum]
  simp only [map_pow, recipRat_X, inv_pow]
  rw [← Finset.sum_range_reflect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  rw [show i + k + 1 - 1 - i = k by omega, pow_add]
  have : (RatFunc.X : RatFunc ℚ) ^ i ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  field_simp

/-- The projective normalizer is a nonzero rational function.
@isnad1 id=ne.0h1v.s4.88f8d27d9db6 from=translated src=- shape=3bfafbec vocab=734ac8e5
-/
theorem projectiveNormalizer_rational_ne_zero (n : ℕ) : (projectiveNormalizer n).rational ≠ 0 := by
  have : ∑ i ∈ Finset.range (n + 1), (RatFunc.X : RatFunc ℚ) ^ i = algebraMap (Polynomial ℚ)
      (RatFunc ℚ) (∑ i ∈ Finset.range (n + 1), (Polynomial.X : Polynomial ℚ) ^ i) := by
    simp [map_sum, RatFunc.algebraMap_X]
  rw [rational_projectiveNormalizer, this]
  refine RatFunc.algebraMap_ne_zero fun h ↦ ?_
  have := congrArg (fun p ↦ Polynomial.coeff p 0) h
  simp [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow] at this

/-! ### Reciprocal substitution and the quantum torus -/

/-- Conjugating `ρ(U)` by the reciprocal substitution gives `ρ̄(v U)`.
@isnad1 id=eq.0h2v.s3.b7f0b652b648 from=translated src=- shape=c45dcd47 vocab=36a2e84c
-/
theorem recipSer_qact (U : QSer) (f : Ser) :
    recipSer (qact U f) = qactRecip (qrecip U) (recipSer f) := by
  refine PowerSeries.ext fun n ↦ ?_
  simp only [recipSer, qact, qactRecip, qrecip, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    map_sum, map_mul, recipCoef_qpow]
  refine Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun r _ ↦ ?_
  congr 2; ring

/-- `†` is an anti-homomorphism of the twisted product.
@isnad1 id=eq.0h2v.s3.771b1b32fa49 from=translated src=- shape=0e1e4560 vocab=25fd62e6
-/
theorem qdagger_qmul (U V : QSer) : qdagger (qmul U V) = qmul (qdagger V) (qdagger U) := by
  funext c h
  simp only [qdagger, qmul, map_sum, map_mul, recipCoef_qpow, Finset.mul_sum]
  rw [← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [← Finset.Nat.sum_antidiagonal_swap]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hr
  subst hp hr
  simp only [Prod.fst_swap, Prod.snd_swap, neg_neg]
  have e : qpow ((((p.1 + p.2 : ℕ) : ℤ) + ((r.1 + r.2 : ℕ) : ℤ) -
        ((p.1 + p.2 : ℕ) : ℤ) * ((r.1 + r.2 : ℕ) : ℤ))) * qpow ((p.2 : ℤ) * (r.1 : ℤ)) =
      qpow (-((p.1 : ℤ) * (r.2 : ℤ))) * (qpow ((p.1 : ℤ) + (r.1 : ℤ) - (p.1 : ℤ) * (r.1 : ℤ)) *
        qpow ((p.2 : ℤ) + (r.2 : ℤ) - (p.2 : ℤ) * (r.2 : ℤ))) := by
    rw [← qpow_add, ← qpow_add, ← qpow_add]
    congr 1
    push_cast
    ring
  linear_combination (recipCoef (U p.2 r.2) * recipCoef (V p.1 r.1)) * e

private theorem qdagger_twist (c k : ℕ) (x : Coef) (hck : c ≤ k) :
    qpow ((c : ℤ) + k - c * k) * (recipCoef (qpow (-(chooseTwo c : ℤ)) * x)) =
      qpow (-(chooseTwo c : ℤ)) *
        (qpow (((c : ℤ) + ((k - c : ℕ) : ℤ)) - c * ((k - c : ℕ) : ℤ)) * recipCoef x) := by
  rw [map_mul, recipCoef_qpow, neg_neg, ← mul_assoc, ← mul_assoc, ← qpow_add, ← qpow_add]
  have := two_mul_chooseTwo c
  congr 2
  push_cast [Nat.cast_sub hck]
  linarith

/-- `†` commutes with `ι₊`.
@isnad1 id=eq.0h1v.s3.1237b7f789f2 from=translated src=- shape=2e76f3a7 vocab=697df1b0
-/
theorem qdagger_qplus (U : QSer) : qdagger (qplus U) = qplus (qdagger U) := by
  funext c k
  simp only [qdagger, qplus]
  split_ifs with h
  · exact qdagger_twist c k _ h
  · simp

/-- `†` commutes with `ι₋`.
@isnad1 id=eq.0h1v.s3.d87655749323 from=translated src=- shape=2e76f3a7 vocab=9b2a4278
-/
theorem qdagger_qminus (U : QSer) : qdagger (qminus U) = qminus (qdagger U) := by
  funext k h
  simp only [qdagger, qminus]
  split_ifs with hh
  · rw [show ((k : ℤ) + h - k * h) = ((h : ℤ) + k - h * k) by ring,
      show (((k - h : ℕ) : ℤ) + h - ((k - h : ℕ) : ℤ) * h) =
        ((h : ℤ) + ((k - h : ℕ) : ℤ)) - h * ((k - h : ℕ) : ℤ) by ring]
    exact qdagger_twist h k (U (k - h) h) hh
  · simp

private theorem sum_antidiagonal_assoc (n : ℕ) (F : ℕ → ℕ → ℕ → Coef) :
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
      F q.1 q.2 p.2 =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      F p.1 q.1 q.2 := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ ↦ ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
    (fun x _ ↦ ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) ?_ ?_ ?_ ?_ ?_
  all_goals rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩ hx
  all_goals simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hx ⊢
  all_goals first
    | rfl
    | (constructor <;> first | trivial | omega)
    | (obtain ⟨h1, h2⟩ := hx; subst h2; simp)

/-- The twisted product is associative.
@isnad1 id=eq.0h3v.s4.1075212c2a3d from=translated src=- shape=b8c031c3 vocab=ba3086e0
-/
theorem qmul_assoc (U V W : QSer) :
    qmul (qmul U V) W = qmul U (qmul V W) := by
  funext c h
  let K : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Coef := fun a b e x y z ↦
    qpow (-((a : ℤ) * (y : ℤ)) - (a : ℤ) * (z : ℤ) - (b : ℤ) * (z : ℤ)) *
      (U a x * (V b y * W e z))
  have hL : qmul (qmul U V) W c h = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c,
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.1,
      (fun a b e ↦ ∑ r ∈ Finset.HasAntidiagonal.antidiagonal h,
        ∑ s ∈ Finset.HasAntidiagonal.antidiagonal r.1, K a b e s.1 s.2 r.2) q.1 q.2 p.2 := by
    simp only [qmul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp ↦ ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q hq' ↦ ?_)
    refine Finset.sum_congr rfl (fun r hr ↦ ?_)
    refine Finset.sum_congr rfl (fun s hs ↦ ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq'
    simp only [K]
    rw [show -((q.1 : ℤ) * (s.2 : ℤ)) - (q.1 : ℤ) * (r.2 : ℤ) - (q.2 : ℤ) * (r.2 : ℤ)
        = -((p.1 : ℤ) * (r.2 : ℤ)) + -((q.1 : ℤ) * (s.2 : ℤ)) by rw [← hq']; push_cast; ring,
      qpow_add]
    ring
  have hR : qmul U (qmul V W) c h = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal c,
      ∑ q ∈ Finset.HasAntidiagonal.antidiagonal p.2,
      (fun a b e ↦ ∑ r ∈ Finset.HasAntidiagonal.antidiagonal h,
        ∑ s ∈ Finset.HasAntidiagonal.antidiagonal r.2, K a b e r.1 s.1 s.2) p.1 q.1 q.2 := by
    simp only [qmul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p hp ↦ ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun q hq' ↦ ?_)
    refine Finset.sum_congr rfl (fun r hr ↦ ?_)
    refine Finset.sum_congr rfl (fun s hs ↦ ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hs
    simp only [K, ← hs]
    rw [mul_left_comm (U _ _), ← mul_assoc, ← qpow_add, Nat.cast_add]
    congr 2; ring
  rw [hL, hR]
  refine (sum_antidiagonal_assoc c (fun a b e ↦ ∑ r ∈ Finset.HasAntidiagonal.antidiagonal h,
    ∑ s ∈ Finset.HasAntidiagonal.antidiagonal r.1, K a b e s.1 s.2 r.2)).trans ?_
  refine Finset.sum_congr rfl (fun p _ ↦ Finset.sum_congr rfl (fun q _ ↦ ?_))
  exact sum_antidiagonal_assoc h (fun x y z ↦ K p.1 q.1 q.2 x y z)

/-! ### Reciprocal substitution and dilations on series -/

/-- `recipSer` acts coefficientwise: `[xⁿ] fᵛ = v([xⁿ] f)`.
@isnad1 id=eq.0h2v.s10.5cd3d3dda4a9 from=translated src=- shape=8da935b0 vocab=fa0d8dcb
-/
theorem coeff_recipSer (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (recipSer f) = recipCoef (PowerSeries.coeff n f) :=
  PowerSeries.coeff_map _ _ _

/-- `recipSer` is multiplicative.
@isnad1 id=eq.0h2v.s6.f7e3fd5b063c from=translated src=- shape=a13ca989 vocab=10af646f
-/
theorem recipSer_mul (f g : Ser) : recipSer (f * g) = recipSer f * recipSer g := map_mul _ f g

/-- `recipSer` is additive on differences.-/
private theorem recipSer_sub (f g : Ser) : recipSer
    (f - g) = recipSer f - recipSer g := map_sub _ f g

/-- `recipSer 1 = 1`.-/
private theorem recipSer_one : recipSer (1 : Ser) = 1 := map_one _

/-- `recipSer` is semilinear over `recipCoef`.-/
private theorem recipSer_C_mul (a : Coef) (f : Ser) :
    recipSer (PowerSeries.C a * f) = PowerSeries.C (recipCoef a) * recipSer f := by
  rw [recipSer, map_mul, PowerSeries.map_C]; rfl

/-- `recipSer` is an involution.
@isnad1 id=eq.0h1v.s3.e74e0176244c from=translated src=- shape=47dcad53 vocab=da33864c
-/
theorem recipSer_recipSer (f : Ser) : recipSer (recipSer f) = f := by
  ext m; simp [coeff_recipSer, recipCoef_recipCoef]

private theorem scalar_X_pow (m : ℕ) : (scalar (RatFunc.X : RatFunc ℚ)) ^ m = qpow (m : ℤ) := by
  simp [scalar, qpow, AddMonoidAlgebra.single_pow, zpow_natCast]

private theorem scalar_X_inv_pow (m : ℕ) :
    (scalar (RatFunc.X : RatFunc ℚ)⁻¹) ^ m = qpow (-(m : ℤ)) := by
  simp [scalar, qpow, AddMonoidAlgebra.single_pow, zpow_neg, zpow_natCast, inv_pow]

private theorem scalar_X_mul_scalar_X_inv :
    scalar (RatFunc.X : RatFunc ℚ) * scalar (RatFunc.X : RatFunc ℚ)⁻¹ = 1 := by
  rw [← scalar_mul, mul_inv_cancel₀ RatFunc.X_ne_zero, scalar_one]

private theorem rescale_C (a b : Coef) :
    PowerSeries.rescale b (PowerSeries.C a) = PowerSeries.C a := by
  ext m
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_C]
  split_ifs with h <;> simp [h]

/-- `[xⁿ] S f = qⁿ [xⁿ] f`.
@isnad1 id=eq.0h2v.s10.2ae6038a4aa8 from=translated src=- shape=4e4ab89c vocab=dfe2013b
-/
theorem coeff_dilate (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (dilate f) = qpow (n : ℤ) * PowerSeries.coeff n f := by
  simp [dilate, PowerSeries.coeff_rescale, scalar_X_pow]

/-- `[xⁿ] S⁻¹ f = q⁻ⁿ [xⁿ] f`.
@isnad1 id=eq.0h2v.s10.fad779d50426 from=translated src=- shape=4afe012a vocab=e64ae0b2
-/
theorem coeff_codilate (f : Ser) (n : ℕ) :
    PowerSeries.coeff n (codilate f) = qpow (-(n : ℤ)) * PowerSeries.coeff n f := by
  simp [codilate, PowerSeries.coeff_rescale, scalar_X_inv_pow]

/-- The dilation is multiplicative.
@isnad1 id=eq.0h2v.s6.9f1ccfc5b823 from=translated src=- shape=a13ca989 vocab=bc853a67
-/
theorem dilate_mul (f g : Ser) : dilate (f * g) = dilate f * dilate g := map_mul _ _ _

/-- The dilation is linear over `Coef`.-/
private theorem dilate_C_mul (a : Coef) (f : Ser) :
    dilate (PowerSeries.C a * f) = PowerSeries.C a * dilate f := by
  simp only [dilate, map_mul, rescale_C]

/-- `S⁻¹ ∘ S = id`.
@isnad1 id=eq.0h1v.s3.26a621a3e994 from=translated src=- shape=47dcad53 vocab=cc9b3ac0
-/
theorem codilate_dilate (f : Ser) : codilate (dilate f) = f := by
  simp only [dilate, codilate, PowerSeries.rescale_rescale, scalar_X_mul_scalar_X_inv,
    PowerSeries.rescale_one, RingHom.id_apply]

/-- `S ∘ S⁻¹ = id`.
@isnad1 id=eq.0h1v.s3.4eb7042905e7 from=translated src=- shape=47dcad53 vocab=cc9b3ac0
-/
theorem dilate_codilate (f : Ser) : dilate (codilate f) = f := by
  simp only [dilate, codilate, PowerSeries.rescale_rescale, mul_comm (scalar RatFunc.X⁻¹),
    scalar_X_mul_scalar_X_inv, PowerSeries.rescale_one, RingHom.id_apply]

/-- The reciprocal substitution conjugates `S` to `S⁻¹`.
@isnad1 id=eq.0h1v.s3.591cb438e0db from=translated src=- shape=2e76f3a7 vocab=74c5d205
-/
theorem recipSer_dilate (f : Ser) : recipSer (dilate f) = codilate (recipSer f) := by
  ext m
  rw [coeff_recipSer, coeff_dilate, coeff_codilate, coeff_recipSer, map_mul, recipCoef_qpow]

/-- The dilation preserves congruence through degree `n`.
@isnad1 id=scongr.1h3v.s4.451ebbe31f3f from=translated src=- shape=ed8f0edd vocab=33ce1f84
-/
theorem SCongr.dilate {n : ℕ} {f g : Ser} (h : SCongr n f g) :
    SCongr n (SurfaceBlowup.dilate f) (SurfaceBlowup.dilate g) := fun m hm ↦ by
  rw [coeff_dilate, coeff_dilate, h m hm]

private theorem rescale_subst (r : Coef) (h f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.rescale r (h.subst f) = h.subst (PowerSeries.rescale r f) := by
  rw [PowerSeries.rescale_eq_subst, PowerSeries.rescale_eq_subst,
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
      (PowerSeries.HasSubst.smul_X' r)]

private theorem constantCoeff_codilate (f : Ser) :
    PowerSeries.constantCoeff (codilate f) = PowerSeries.constantCoeff f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_codilate]
  simp [qpow_zero]

private theorem dilate_expSer (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
    dilate (expSer f) = expSer (dilate f) :=
  rescale_subst _ _ _ hf

private theorem dilate_logSer (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    dilate (logSer g) = logSer (dilate g) := by
  rw [logSer, logSer, PowerSeries.logOf_eq, PowerSeries.logOf_eq, dilate,
    rescale_subst _ _ _ (by simp [hg]), map_sub, map_one]
  rfl

private theorem dilate_divisorTransform (w : ℕ → ℚ) (f : Ser) :
    dilate (divisorTransform w f) = divisorTransform w (dilate f) := by
  refine PowerSeries.ext fun n ↦ ?_
  simp only [coeff_dilate, divisorTransform, PowerSeries.coeff_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [map_mul, adamsCoef_qpow k (Nat.pos_of_mem_divisors hk), mul_smul_comm,
    ← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hk)]

private theorem dilate_pLog (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    dilate (pLog g) = pLog (dilate g) := by
  rw [pLog, pLog, ← dilate_logSer g hg]
  exact dilate_divisorTransform _ _

/-- The dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
@isnad1 id=eq.1h2v.s7.f1d637f0f192 from=translated src=- shape=a79f3323 vocab=d0744192
-/
theorem dilate_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    dilate (pPow w g) = pPow w (dilate g) := by
  rw [pPow, pPow, pExp, pExp, dilate_expSer _ (constantCoeff_plethSum _), plethSum_eq,
    plethSum_eq, dilate_divisorTransform, dilate_C_mul, dilate_pLog g hg]

/-- The inverse dilation commutes with the plethystic powers `P_w` (for `g(0) = 1`).
@isnad1 id=eq.1h2v.s7.b894fa4f89e1 from=translated src=- shape=a79f3323 vocab=cecf727e
-/
theorem codilate_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    codilate (pPow w g) = pPow w (codilate g) := by
  conv_lhs => rw [← dilate_codilate g]
  rw [← dilate_pPow w _ (by rw [constantCoeff_codilate, hg]), codilate_dilate]

/-! ### The Gauss twist -/

/-- The reciprocal substitution conjugates `Φ` to `Φ⁻¹`.
@isnad1 id=eq.0h1v.s3.aa88c85c9a46 from=translated src=- shape=2e76f3a7 vocab=8e433b69
-/
theorem recipSer_gaussPhi (f : Ser) : recipSer (gaussPhi f) = gaussPhiInv (recipSer f) := by
  ext n
  simp only [gaussPhi, gaussPhiInv, coeff_recipSer, PowerSeries.coeff_mk, map_mul,
    recipCoef_qpow, neg_neg]

/-- `Φ` commutes with the dilation.
@isnad1 id=eq.0h1v.s3.0f42bdd13571 from=translated src=- shape=2e76f3a7 vocab=0722c395
-/
theorem gaussPhi_dilate (f : Ser) : gaussPhi (dilate f) = dilate (gaussPhi f) := by
  ext n : 1
  simp only [gaussPhi, coeff_dilate, PowerSeries.coeff_mk, mul_left_comm]

/-- `Φ` is additive on differences.
@isnad1 id=eq.0h2v.s6.f597735b808e from=translated src=- shape=a13ca989 vocab=163b0dbe
-/
theorem gaussPhi_sub (f g : Ser) : gaussPhi (f - g) = gaussPhi f - gaussPhi g := by
  ext n
  simp only [gaussPhi, map_sub, mul_sub, PowerSeries.coeff_mk]

/-- For symmetric `V`, the Gauss twist conjugates `ρ̄(v V)` to `S⁻¹ ∘ ρ(V†) ∘ S`.
@isnad1 id=eq.1h2v.s5.bbd9c843532a from=translated src=- shape=cbcad50c vocab=16c86f62
-/
theorem gaussPhi_qactRecip_gaussPhiInv (V : QSer) (hV : ∀ c h : ℕ, V c h = V h c) (f : Ser) :
    gaussPhi (qactRecip (qrecip V) (gaussPhiInv f)) = codilate (qact (qdagger V) (dilate f)) := by
  have hL (a b c : ℤ) (x y : Coef) :
      qpow a * (qpow b * (x * (qpow c * y))) = qpow (a + b + c) * (x * y) := by
    rw [qpow_add, qpow_add]; ring
  have hR (a b c d : ℤ) (x y : Coef) :
      qpow a * (qpow b * (qpow c * x * (qpow d * y))) = qpow (a + b + c + d) * (x * y) := by
    rw [qpow_add, qpow_add, qpow_add]; ring
  refine PowerSeries.ext fun n ↦ ?_
  rw [coeff_codilate]
  simp only [gaussPhi, gaussPhiInv, qactRecip, qact, qrecip, qdagger, PowerSeries.coeff_mk,
    coeff_dilate]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← Finset.Nat.sum_antidiagonal_swap, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hr
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [hV r.2 r.1, hL, hR]
  congr 2
  have e1 := two_mul_tri (r.1 + r.2 + p.2)
  have e2 := two_mul_tri r.1
  have e3 := two_mul_tri r.2
  have e4 := two_mul_tri p.2
  have hn : n = r.1 + r.2 + p.2 := by omega
  subst hn
  push_cast at e1 ⊢
  linarith

/-! ### Diagonal substitution -/

/-- Diagonal substitution `x ↦ E_{1,1}` is multiplicative into the quantum torus.
@isnad1 id=eq.0h2v.s5.9c0cbef56106 from=translated src=- shape=3887891b vocab=f46e6249
-/
theorem qdiag_mul (f g : Ser) : qdiag (f * g) = qmul (qdiag f) (qdiag g) := by
  funext c h
  simp only [qmul, qdiag]
  by_cases hch : c = h
  · subst hch
    rw [ite_eq_left rfl, PowerSeries.coeff_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [Finset.sum_eq_single p]
    · rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      simp only [ite_true]
      rw [← hp, show (-(((chooseTwo (p.1 + p.2) : ℕ) : ℤ))) =
        -((p.1 : ℤ) * p.2) + (-(chooseTwo p.1 : ℤ) + -(chooseTwo p.2 : ℤ)) by
          rw [chooseTwo_add]; ring,
        qpow_add, qpow_add]
      ring
    · intro r _ hr
      by_cases h1 : p.1 = r.1
      · have h2 : p.2 ≠ r.2 := fun h2 ↦ hr (Prod.ext h1.symm h2.symm)
        simp [h2]
      · simp [h1]
    · intro hp'; exact absurd hp hp'
  · rw [ite_eq_right hch]
    symm
    refine Finset.sum_eq_zero fun p hp ↦ Finset.sum_eq_zero fun r hr ↦ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hr
    by_cases h1 : p.1 = r.1
    · have h2 : p.2 ≠ r.2 := by omega
      simp [h2]
    · simp [h1]

/-- Diagonal substitution sends `1` to the unit `E_{0,0}`.-/
private theorem qdiag_one : qdiag 1 = qone := by
  funext c h
  simp only [qdiag, qone, PowerSeries.coeff_one]
  by_cases hch : c = h
  · subst hch
    rcases eq_or_ne c 0 with rfl | hc
    · simp [chooseTwo, qpow_zero]
    · simp [hc]
  · simp only [ite_eq_right hch]
    split_ifs with h' <;> first | rfl | omega

/-- `qdiag(f)† = qdiag(S(v f))`.-/
private theorem qdagger_qdiag (f : Ser) : qdagger (qdiag f) = qdiag (dilate (recipSer f)) := by
  funext c h
  simp only [qdagger, qdiag]
  by_cases hch : c = h
  · subst hch
    simp only [ite_true, map_mul, recipCoef_qpow, coeff_dilate, coeff_recipSer]
    have e := two_mul_chooseTwo c
    rw [← mul_assoc, ← mul_assoc, ← qpow_add, ← qpow_add]
    congr 2
    linarith
  · simp [hch]

/-- If `S(v P_s) P_s ≡ 1` through degree `M`, then `qdiag(P_s) qdiag(P_s)† ≡ 1` through total
degree `2M + 1`.
@isnad1 id=qcongr.1h2v.s7.121854be6882 from=translated src=- shape=0d9eafae vocab=c97294ed
-/
theorem qcongr_qdiag_mul_qdagger (M s : ℕ)
    (h : SCongr M (dilate (recipSer (eulerSer (-1) s)) * eulerSer (-1) s) 1) :
    QCongr (2 * M + 1) (qmul (qdiag (eulerSer (-1) s)) (qdagger (qdiag (eulerSer (-1) s))))
      qone := by
  rw [qdagger_qdiag, ← qdiag_mul, mul_comm (eulerSer (-1) s), ← qdiag_one]
  exact h.qdiag

/-- The reciprocal substitution commutes with the plethystic powers, twisting the exponent by
`q ↦ q⁻¹`: `P_w(g)ᵛ = P_{v(w)}(gᵛ)` for `g(0) = 1`.
@isnad1 id=eq.1h2v.s8.2933b6ac6950 from=translated src=- shape=95a9c2a7 vocab=0ec19f55
-/
theorem recipSer_pPow (w : RatFunc ℚ) (g : Ser) (hg : PowerSeries.constantCoeff g = 1) :
    recipSer (pPow w g) = pPow (recipRat w) (recipSer g) := by
  have hexp (f : Ser) (hf : PowerSeries.constantCoeff f = 0) :
      recipSer (expSer f) = expSer (recipSer f) :=
    (PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
      (PowerSeries.exp Coef)).trans (by rw [PowerSeries.map_exp]; rfl)
  have hlog : recipSer (logSer g) = logSer (recipSer g) := by
    have h1 : recipSer (g - 1) = recipSer g - 1 := by rw [recipSer_sub, recipSer_one]
    unfold recipSer at h1 ⊢
    rw [logSer, logSer, PowerSeries.logOf_eq, PowerSeries.logOf_eq, ← h1]
    exact (PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hg]))
      (PowerSeries.log Coef)).trans (by rw [PowerSeries.map_log]; rfl)
  have hdt (u : ℕ → ℚ) (f : Ser) :
      recipSer (divisorTransform u f) = divisorTransform u (recipSer f) := by
    refine PowerSeries.ext fun n ↦ ?_
    simp only [coeff_recipSer, divisorTransform, PowerSeries.coeff_mk, map_sum, map_rat_smul]
    exact Finset.sum_congr rfl fun k hk ↦ by
      rw [recipCoef_adamsCoef k (Nat.pos_of_mem_divisors hk)]
  rw [pPow, pPow, pExp, pExp, hexp _ (constantCoeff_plethSum _), plethSum_eq, plethSum_eq, hdt,
    recipSer_C_mul, recipCoef_scalar, pLog, pLog, moebiusSum_eq, moebiusSum_eq, hdt, hlog]

/-! ### Scalars and congruences of series -/

/-- Multiplication by a nonzero scalar `scalar w` is injective on `Coef`.
@isnad1 id=eq.2h3v.s6.8bcf3367b29c from=translated src=- shape=c2dffc1c vocab=08778671
-/
theorem scalar_mul_left_cancel {w : RatFunc ℚ} (hw : w ≠ 0) {x y : Coef}
    (h : scalar w * x = scalar w * y) : x = y := by
  have := congrArg (scalar w⁻¹ * ·) h
  simp only [← mul_assoc, ← scalar_mul, inv_mul_cancel₀ hw, scalar_one, one_mul] at this
  exact this

/-- `scalar w * x = 0` forces `x = 0` when `w ≠ 0`.-/
theorem eq_zero_of_scalar_mul_eq_zero {w : RatFunc ℚ} (hw : w ≠ 0) {x : Coef}
    (h : scalar w * x = 0) : x = 0 :=
  scalar_mul_left_cancel hw (by rw [h, mul_zero])

/-- Congruence of series is reflexive.
@isnad1 id=scongr.0h2v.s3.2932202e7fb3 from=translated src=- shape=3105397a vocab=c05a3af8
-/
@[refl] theorem SCongr.refl (n : ℕ) (f : Ser) : SCongr n f f := fun _ _ ↦ rfl

/-- Equal series are congruent.
@isnad1 id=scongr.1h3v.s3.4032a7b8f3b0 from=translated src=- shape=f812b2a9 vocab=c05a3af8
-/
theorem SCongr.of_eq {n : ℕ} {f g : Ser} (h : f = g) : SCongr n f g := h ▸ SCongr.refl n f

/-- Congruence of series is symmetric.
@isnad1 id=scongr.1h3v.s3.f2f39b3f0f50 from=translated src=- shape=2b5f2a84 vocab=c05a3af8
-/
theorem SCongr.symm {n : ℕ} {f g : Ser} (h : SCongr n f g) : SCongr n g f :=
  fun i hi ↦ (h i hi).symm

/-- Congruence of series is transitive.
@isnad1 id=scongr.2h4v.s4.b4787e579f86 from=translated src=- shape=31ac16df vocab=c05a3af8
-/
theorem SCongr.trans {n : ℕ} {f g u : Ser} (h : SCongr n f g) (h' : SCongr n g u) :
    SCongr n f u :=
  fun i hi ↦ (h i hi).trans (h' i hi)

/-- Congruence through degree `n` implies congruence through any `m ≤ n`.
@isnad1 id=scongr.2h4v.s4.02eca37e4a7d from=translated src=- shape=10e2c0a9 vocab=e1985de7
-/
theorem SCongr.mono {n m : ℕ} {f g : Ser} (h : SCongr n f g) (hmn : m ≤ n) : SCongr m f g :=
  fun i hi ↦ h i (hi.trans hmn)

/-- Congruence of series is compatible with multiplication.
@isnad1 id=scongr.2h5v.s6.d2ace3b2cde2 from=translated src=- shape=745f8771 vocab=fd159cc5
-/
theorem SCongr.mul {n : ℕ} {f g u v : Ser} (h : SCongr n f g) (h' : SCongr n u v) :
    SCongr n (f * u) (g * v) := by
  intro i hi
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun x hx ↦ ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [h x.1 (by omega), h' x.2 (by omega)]

/-- Congruence of series is compatible with multiplication by a constant.
@isnad1 id=scongr.1h4v.s8.4f0b22655420 from=translated src=- shape=1a7cc8c8 vocab=620fe625
-/
theorem SCongr.C_mul {n : ℕ} {f g : Ser} (h : SCongr n f g) (a : Coef) :
    SCongr n (PowerSeries.C a * f) (PowerSeries.C a * g) := fun i hi ↦ by
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, h i hi]

/-- Congruence of series is compatible with powers.
@isnad1 id=scongr.1h4v.s6.2a0a15164cbf from=translated src=- shape=338157e2 vocab=15e7eb13
-/
theorem SCongr.pow {n : ℕ} {f g : Ser} (h : SCongr n f g) (p : ℕ) : SCongr n (f ^ p) (g ^ p) := by
  induction p with
  | zero => exact SCongr.refl n 1
  | succ p ih => rw [pow_succ, pow_succ]; exact ih.mul h

/-- Congruences can be cancelled by a series with constant term `1`.
@isnad1 id=scongr.2h4v.s8.4396d9048eca from=translated src=- shape=79922e3d vocab=aef4230c
-/
theorem SCongr.of_mul_right {n : ℕ} {f g u : Ser} (hu : PowerSeries.constantCoeff u = 1)
    (h : SCongr n (f * u) (g * u)) : SCongr n f g := by
  obtain ⟨v, hv⟩ :=
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by rw [hu]; exact isUnit_one)).exists_right_inv
  simpa [mul_assoc, hv] using h.mul (SCongr.refl n v)

private theorem scongr_subst (n : ℕ) (a : Ser) (f g : Ser)
    (hf : PowerSeries.constantCoeff f = 0) (hg : PowerSeries.constantCoeff g = 0)
    (h : SCongr n f g) : SCongr n (a.subst f) (a.subst g) := by
  have ht : PowerSeries.trunc (n+1) f = PowerSeries.trunc (n+1) g := by
    refine Polynomial.ext fun m ↦ ?_
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hm
    · exact h m (by omega)
    · rfl
  intro m hm
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hf),
    PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hg)]
  congr 1
  funext d
  congr 1
  have h1 := PowerSeries.trunc_trunc_pow f (n+1) d
  have h2 := PowerSeries.trunc_trunc_pow g (n+1) d
  rw [ht] at h1
  have := congrArg (fun p ↦ Polynomial.coeff p m) (h1.symm.trans h2)
  simpa [PowerSeries.coeff_trunc, show m < n + 1 by omega] using this

/-- `exp` preserves congruence through degree `n` (on series with zero constant term).
@isnad1 id=scongr.3h3v.s8.2a84edf89624 from=translated src=- shape=a700f512 vocab=e9609141
-/
theorem SCongr.expSer {n : ℕ} {f g : Ser} (hf : PowerSeries.constantCoeff f = 0)
    (hg : PowerSeries.constantCoeff g = 0) (h : SCongr n f g) :
    SCongr n (SurfaceBlowup.expSer f) (SurfaceBlowup.expSer g) :=
  scongr_subst n (PowerSeries.exp Coef) f g hf hg h

/-- `log` preserves congruence through degree `n` (on series with constant term `1`).
@isnad1 id=scongr.3h3v.s8.8c60fbcfa455 from=translated src=- shape=a700f512 vocab=379950b3
-/
theorem SCongr.logSer {n : ℕ} {u v : Ser} (hu : PowerSeries.constantCoeff u = 1)
    (hv : PowerSeries.constantCoeff v = 1) (huv : SCongr n u v) :
    SCongr n (SurfaceBlowup.logSer u) (SurfaceBlowup.logSer v) :=
  scongr_subst n (PowerSeries.log Coef) (u - 1) (v - 1) (by simp [hu]) (by simp [hv])
    fun m hm ↦ by simp [huv m hm]

end SurfaceBlowup
