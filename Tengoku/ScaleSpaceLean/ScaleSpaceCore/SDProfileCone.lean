/-
Copyright (c) 2026 Daniel Fagerström. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Fagerström
-/
import Tengoku.ScaleSpaceLean.ScaleSpaceCore.SDProfile

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `lem:admissible-cone`: the admissible exponents form a convex cone, and are continuous

Home: line:lem:admissible-cone

Moved from the spatial article's export (`SpatialLine.AdmissibleCone`, `ExponentContinuity`, at
`cone-v0.1`), statements unchanged up to the namespace.

The content is that all seven fields of `SDProfile` are stable under addition and under
multiplication by a nonnegative scalar, and that the exponent transports: the profile with data
`(a₁+a₂, k₁+k₂)` has exponent `F₁ + F₂`, and the one with data `(c a₁, c k₁)` has exponent
`c F₁`. Five fields are immediate; the two integrability conditions are the ones with content,
and they are exactly the transport statement in `ℝ≥0∞`, a sum of two finite things being finite.

## `ℝ≥0∞` first, and the one place `toReal` costs something

`SDProfile.exponentL` is a `lintegral`, so additivity in `k` needs **no integrability side
condition**: `lintegral_add_left'` asks only for `AEMeasurable` of one summand, which
`aemeasurable_restrict_of_antitoneOn` supplies from `k_antitone`. The classical argument would
first have to know both integrals finite; here finiteness is a conclusion.

The node's statement is about the **real** exponent, though, and `(x + y).toReal` is
`x.toReal + y.toReal` only when both are finite. That finiteness is `lem:quadratic-growth`,
routed through `lem:profile-integrability`: `SDProfile.exponentL_ne_top` below is the one step of
the file that leaves the elementary algebra.

## Continuity

The bound is the truncation of `lem:quadratic-growth` read with the frequency in a bounded
neighbourhood: for `|ω| ≤ M`,
`1 - cos(ωx) ≤ 2(1 ∨ M²)(1 ∧ x²)`,
whose `ν`-integral is finite by the Lévy condition, which is a field of `SymLevyPair`. So
`ω ↦ ∫ (1 - cos ωx) ν(dx)` is continuous by dominated convergence in `ℝ≥0∞`, the Gaussian term
is a polynomial, and `lem:quadratic-growth` makes the sum finite, so the `.toReal` is continuous
too.

twin: `CausalAdmissible.add`, `CausalAdmissible.smul` (`CausalCone`), the same construction over
the causal profile structure.
-/

namespace ScaleSpace

open MeasureTheory Set Filter
open scoped ENNReal Topology

/-! ## Measurability of a profile, on the three windows the fields use -/

/-- A profile is a.e. measurable on `(0,∞)`: it is antitone there.
@isnad1 id=aemeasur.0h1v.s4.af2a0913a568 from=translated src=- shape=d27af4e0 vocab=df39176d
-/
theorem SDProfile.aemeasurable_k (P : SDProfile) :
    AEMeasurable P.k (volume.restrict (Ioi (0 : ℝ))) :=
  aemeasurable_restrict_of_antitoneOn measurableSet_Ioi P.k_antitone

/-- The same on any subset of `(0,∞)`; used at `Ioo 0 1` and at `Ioi 1`, the two windows of the
integrability fields.
@isnad1 id=aemeasur.1h2v.s5.4d78f5fa3ca0 from=translated src=- shape=88e1088c vocab=bcd05040
-/
theorem SDProfile.aemeasurable_k_mono (P : SDProfile) {s : Set ℝ} (hs : s ⊆ Ioi (0 : ℝ)) :
    AEMeasurable P.k (volume.restrict s) :=
  P.aemeasurable_k.mono_measure (Measure.restrict_mono hs le_rfl)

/-! ## The two constructions -/

/-- **The sum of two admissible profiles**, with data `(a₁ + a₂, k₁ + k₂)`.-/
noncomputable def SDProfile.add (P₁ P₂ : SDProfile) : SDProfile where
  a := P₁.a + P₂.a
  k := fun x => P₁.k x + P₂.k x
  a_nonneg := add_nonneg P₁.a_nonneg P₂.a_nonneg
  k_nonneg := fun x hx => add_nonneg (P₁.k_nonneg x hx) (P₂.k_nonneg x hx)
  k_antitone := fun _ hx _ hy hxy =>
    add_le_add (P₁.k_antitone hx hy hxy) (P₂.k_antitone hx hy hxy)
  k_zero := by simp [P₁.k_zero, P₂.k_zero]
  integrable_near_zero := by
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
    have hm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (x * P₁.k x))
        (volume.restrict (Ioo (0 : ℝ) 1)) :=
      (aemeasurable_id.mul (P₁.aemeasurable_k_mono hsub)).ennreal_ofReal
    have hsplit : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * (P₁.k x + P₂.k x)))
        = (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P₁.k x))
          + ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P₂.k x) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have h1 : 0 ≤ x * P₁.k x := mul_nonneg hx0.le (P₁.k_nonneg x (hsub hx))
      have h2 : 0 ≤ x * P₂.k x := mul_nonneg hx0.le (P₂.k_nonneg x (hsub hx))
      rw [← ENNReal.ofReal_add h1 h2]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨P₁.integrable_near_zero, P₂.integrable_near_zero⟩
  integrable_at_top := by
    have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi zero_le_one
    have hm : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P₁.k x / x))
        (volume.restrict (Ioi (1 : ℝ))) :=
      ((P₁.aemeasurable_k_mono hsub).div aemeasurable_id).ennreal_ofReal
    have hsplit : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal ((P₁.k x + P₂.k x) / x))
        = (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P₁.k x / x))
          + ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P₂.k x / x) := by
      rw [← lintegral_add_left' hm]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hsub hx
      have h1 : 0 ≤ P₁.k x / x := div_nonneg (P₁.k_nonneg x (hsub hx)) hx0.le
      have h2 : 0 ≤ P₂.k x / x := div_nonneg (P₂.k_nonneg x (hsub hx)) hx0.le
      rw [← ENNReal.ofReal_add h1 h2]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.add_ne_top.mpr ⟨P₁.integrable_at_top, P₂.integrable_at_top⟩

/-- **A nonnegative multiple of an admissible profile**, with data `(c a, c k)`.-/
noncomputable def SDProfile.smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) : SDProfile where
  a := c * P.a
  k := fun x => c * P.k x
  a_nonneg := mul_nonneg hc P.a_nonneg
  k_nonneg := fun x hx => mul_nonneg hc (P.k_nonneg x hx)
  k_antitone := fun _ hx _ hy hxy => mul_le_mul_of_nonneg_left (P.k_antitone hx hy hxy) hc
  k_zero := by simp [P.k_zero]
  integrable_near_zero := by
    have hsub : Ioo (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) := fun _ hx => hx.1
    have hsplit : (∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * (c * P.k x)))
        = ENNReal.ofReal c * ∫⁻ x in Ioo (0 : ℝ) 1, ENNReal.ofReal (x * P.k x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hx.1
      have h1 : 0 ≤ x * P.k x := mul_nonneg hx0.le (P.k_nonneg x (hsub hx))
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.integrable_near_zero
  integrable_at_top := by
    have hsub : Ioi (1 : ℝ) ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi zero_le_one
    have hsplit : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (c * P.k x / x))
        = ENNReal.ofReal c * ∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (P.k x / x) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      have hx0 : (0 : ℝ) < x := hsub hx
      have h1 : 0 ≤ P.k x / x := div_nonneg (P.k_nonneg x (hsub hx)) hx0.le
      rw [← ENNReal.ofReal_mul hc]
      congr 1
      ring
    rw [hsplit]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.integrable_at_top

/--
@isnad1 id=eq.0h2v.s4.9dc6203bb6e8 from=translated src=- shape=88b36870 vocab=b681864e
-/
@[simp] theorem SDProfile.add_a (P₁ P₂ : SDProfile) : (P₁.add P₂).a = P₁.a + P₂.a := rfl

/--
@isnad1 id=eq.0h3v.s4.223e6b815a61 from=translated src=- shape=be92c776 vocab=e3569e2d
-/
@[simp] theorem SDProfile.add_k (P₁ P₂ : SDProfile) (x : ℝ) :
    (P₁.add P₂).k x = P₁.k x + P₂.k x := rfl

/--
@isnad1 id=eq.1h2v.s5.53b6430e8fdb from=translated src=- shape=5641ec63 vocab=4005d7fc
-/
@[simp] theorem SDProfile.smul_a (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) :
    (P.smul hc).a = c * P.a := rfl

/--
@isnad1 id=eq.1h3v.s5.03018856128a from=translated src=- shape=c3930857 vocab=adf6e12d
-/
@[simp] theorem SDProfile.smul_k (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    (P.smul hc).k x = c * P.k x := rfl

/-! ## Finiteness of the exponent -/

/-- **`lem:quadratic-growth` at a profile.** The exponent `eq:sd-profile` is finite at every
frequency, so `SDProfile.exponent`, a `.toReal`, is the real number the display writes.

Routed through `lem:profile-integrability`: the profile's data is a symmetric Lévy pair with the
same `exponentL`, and `SymLevyPair.exponentL_ne_top` is the growth bound.
@isnad1 id=ne.0h2v.s3.b47a02eb453a from=translated src=- shape=92158592 vocab=71ade2f3
-/
theorem SDProfile.exponentL_ne_top (P : SDProfile) (ω : ℝ) : P.exponentL ω ≠ ⊤ := by
  obtain ⟨Q, ha, hν, -⟩ := profile_integrability_pair P
  rw [exponentL_eq_of_profileMeasure P Q ha hν ω]
  exact Q.exponentL_ne_top ω

/-! ## Evenness of the exponent

`(-ω)² = ω²` and the cosine is even, so both integrands are unchanged. -/

/-- The exponent is even, in `ℝ≥0∞`.
@isnad1 id=eq.0h2v.s3.f8715202e1d0 from=translated src=- shape=3b878b1c vocab=6d134b00
-/
theorem SDProfile.exponentL_neg (Q : SDProfile) (ω : ℝ) :
    Q.exponentL (-ω) = Q.exponentL ω := by
  rw [SDProfile.exponentL, SDProfile.exponentL]
  congr 1
  · congr 1
    ring
  · refine lintegral_congr fun x => ?_
    rw [show -ω * x = -(ω * x) by ring, Real.cos_neg]

/-- The exponent is even.
@isnad1 id=eq.0h2v.s3.05185d665f53 from=translated src=- shape=5a76020b vocab=0e93b181
-/
theorem SDProfile.exponent_neg (Q : SDProfile) (ω : ℝ) : Q.exponent (-ω) = Q.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponent, Q.exponentL_neg]

/-! ## Additivity and homogeneity of the exponent -/

/-- The exponent is additive in the data, in `ℝ≥0∞` and with no side condition.
@isnad1 id=eq.0h3v.s4.91603df458fc from=translated src=- shape=46c14041 vocab=a9e02e0f
-/
theorem SDProfile.exponentL_add (P₁ P₂ : SDProfile) (ω : ℝ) :
    (P₁.add P₂).exponentL ω = P₁.exponentL ω + P₂.exponentL ω := by
  have hm : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₁.k x / x))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEMeasurable.ennreal_ofReal ?_
    have hc : AEMeasurable (fun x : ℝ => 1 - Real.cos (ω * x))
        (volume.restrict (Ioi (0 : ℝ))) := by
      fun_prop
    exact (hc.mul P₁.aemeasurable_k).div aemeasurable_id
  have hjump : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * (P₁.k x + P₂.k x) / x))
      = (∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₁.k x / x))
        + ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P₂.k x / x) := by
    rw [← lintegral_add_left' hm]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    have h1 : 0 ≤ (1 - Real.cos (ω * x)) * P₁.k x / x :=
      div_nonneg (mul_nonneg hcos (P₁.k_nonneg x hx)) hx0.le
    have h2 : 0 ≤ (1 - Real.cos (ω * x)) * P₂.k x / x :=
      div_nonneg (mul_nonneg hcos (P₂.k_nonneg x hx)) hx0.le
    rw [← ENNReal.ofReal_add h1 h2]
    congr 1
    ring
  have hgauss : ENNReal.ofReal ((P₁.a + P₂.a) * ω ^ 2)
      = ENNReal.ofReal (P₁.a * ω ^ 2) + ENNReal.ofReal (P₂.a * ω ^ 2) := by
    rw [← ENNReal.ofReal_add (mul_nonneg P₁.a_nonneg (sq_nonneg ω))
      (mul_nonneg P₂.a_nonneg (sq_nonneg ω))]
    congr 1
    ring
  simp only [SDProfile.exponentL, SDProfile.add_a, SDProfile.add_k]
  rw [hgauss, hjump]
  ring

/-- The exponent is homogeneous in the data, for a nonnegative scalar.
@isnad1 id=eq.1h3v.s5.a7b0dd885625 from=translated src=- shape=45430920 vocab=225f114b
-/
theorem SDProfile.exponentL_smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (ω : ℝ) :
    (P.smul hc).exponentL ω = ENNReal.ofReal c * P.exponentL ω := by
  have hjump : (∫⁻ x in Ioi (0 : ℝ),
        ENNReal.ofReal ((1 - Real.cos (ω * x)) * (c * P.k x) / x))
      = ENNReal.ofReal c
        * ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal ((1 - Real.cos (ω * x)) * P.k x / x) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : (0 : ℝ) < x := hx
    have hcos : 0 ≤ 1 - Real.cos (ω * x) := by linarith [Real.cos_le_one (ω * x)]
    have h1 : 0 ≤ (1 - Real.cos (ω * x)) * P.k x / x :=
      div_nonneg (mul_nonneg hcos (P.k_nonneg x hx)) hx0.le
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  have hgauss : ENNReal.ofReal (c * P.a * ω ^ 2)
      = ENNReal.ofReal c * ENNReal.ofReal (P.a * ω ^ 2) := by
    rw [← ENNReal.ofReal_mul hc]
    congr 1
    ring
  simp only [SDProfile.exponentL, SDProfile.smul_a, SDProfile.smul_k]
  rw [hgauss, hjump, mul_add]

/-- **The exponent is additive**: the profile with data `(a₁+a₂, k₁+k₂)` has exponent
`F₁ + F₂`.
@isnad1 id=eq.0h3v.s4.49ce9f1e0a47 from=translated src=- shape=be92c776 vocab=ad8635f4
-/
theorem SDProfile.exponent_add (P₁ P₂ : SDProfile) (ω : ℝ) :
    (P₁.add P₂).exponent ω = P₁.exponent ω + P₂.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponentL_add,
    ENNReal.toReal_add (P₁.exponentL_ne_top ω) (P₂.exponentL_ne_top ω)]
  rfl

/-- **The exponent is homogeneous**: the profile with data `(c a, c k)` has exponent `c F`.
@isnad1 id=eq.1h3v.s5.85157c14e7c2 from=translated src=- shape=c3930857 vocab=2b582878
-/
theorem SDProfile.exponent_smul (P : SDProfile) {c : ℝ} (hc : 0 ≤ c) (ω : ℝ) :
    (P.smul hc).exponent ω = c * P.exponent ω := by
  rw [SDProfile.exponent, SDProfile.exponentL_smul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc]
  rfl

/-! ## The node -/

/-- **`lem:admissible-cone`.** The admissible exponents are closed under addition and under
multiplication by a nonnegative scalar, and the correspondence with the data `(a,k)` is linear —
so they form a convex cone.

Stated existentially, as the skeleton states it: what has to hold is that a profile with the
summed data and the summed exponent *exists*, not that it is built by any particular
construction. The profile clause is asserted on `(0,∞)`, which is where a profile is a density;
`k 0` is a normalisation and both constructions preserve it.
@isnad1 id=and.1h3v.s7.b0c30c846127 from=translated src=- shape=a167bcb2 vocab=587dc33b
-/
theorem admissible_cone (P₁ P₂ : SDProfile) (c : ℝ) (hc : 0 ≤ c) :
    (∃ Q : SDProfile, Q.a = P₁.a + P₂.a ∧ (∀ x : ℝ, 0 < x → Q.k x = P₁.k x + P₂.k x) ∧
        ∀ ω : ℝ, Q.exponent ω = P₁.exponent ω + P₂.exponent ω) ∧
      (∃ Q : SDProfile, Q.a = c * P₁.a ∧ (∀ x : ℝ, 0 < x → Q.k x = c * P₁.k x) ∧
        ∀ ω : ℝ, Q.exponent ω = c * P₁.exponent ω) :=
  ⟨⟨P₁.add P₂, rfl, fun _ _ => rfl, fun ω => P₁.exponent_add P₂ ω⟩,
   ⟨P₁.smul hc, rfl, fun _ _ => rfl, fun ω => P₁.exponent_smul hc ω⟩⟩

/-! ## Continuity of the exponent -/

namespace SymLevyPair

/-- **The truncation bound with the frequency in a bounded set.** For `|ω| ≤ M`,
`1 - cos(ωx) ≤ 2(1 ∨ M²)(1 ∧ x²)`: the two regimes of the truncation, `1 - cos θ ≤ θ²/2` near
the origin and `1 - cos θ ≤ 2` beyond it.
@isnad1 id=le.1h3v.s6.c1dc47e12300 from=translated src=- shape=f65afacc vocab=7554d95f
-/
theorem one_sub_cos_mul_le {M ω x : ℝ} (hω : |ω| ≤ M) :
    1 - Real.cos (ω * x) ≤ 2 * max 1 (M ^ 2) * min 1 (x ^ 2) := by
  have hq : 1 - Real.cos (ω * x) ≤ (ω * x) ^ 2 / 2 := by
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ω * x)]
  have hb : 1 - Real.cos (ω * x) ≤ 2 := by
    nlinarith [Real.neg_one_le_cos (ω * x)]
  have hωM : ω ^ 2 ≤ M ^ 2 := by
    have h1 : |ω| ≤ M := hω
    have h2 : (0 : ℝ) ≤ M := le_trans (abs_nonneg ω) hω
    nlinarith [sq_abs ω, abs_nonneg ω]
  have hmax : ω ^ 2 ≤ max 1 (M ^ 2) := le_trans hωM (le_max_right _ _)
  have hmax1 : (1 : ℝ) ≤ max 1 (M ^ 2) := le_max_left _ _
  rcases le_total (x ^ 2) 1 with h | h
  · rw [min_eq_right h]
    nlinarith [sq_nonneg x, sq_nonneg ω]
  · rw [min_eq_left h]
    nlinarith

/-- The `ℝ≥0∞` jump term of `eq:levy-khintchine` is measurable in the space variable.
@isnad1 id=measurab.0h1v.s5.24484b6ff7ab from=translated src=- shape=c21b0598 vocab=77db8369
-/
theorem measurable_one_sub_cos (ω : ℝ) :
    Measurable fun x : ℝ => ENNReal.ofReal (1 - Real.cos (ω * x)) :=
  (measurable_const.sub
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).measurable)).ennreal_ofReal

/-- **The jump term is continuous in the frequency**, by dominated convergence in `ℝ≥0∞`.
@isnad1 id=continuo.0h1v.s5.3d33b932caad from=translated src=- shape=be94fb82 vocab=8074b2b2
-/
theorem continuous_jump (P : SymLevyPair) :
    Continuous fun ω : ℝ => ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ω * x)) ∂P.ν := by
  refine continuous_iff_continuousAt.2 fun ω₀ => ?_
  set M : ℝ := |ω₀| + 1 with hM
  have hMnn : (0 : ℝ) ≤ 2 * max 1 (M ^ 2) := by positivity
  refine tendsto_lintegral_filter_of_dominated_convergence
    (bound := fun x => ENNReal.ofReal (2 * max 1 (M ^ 2) * min 1 (x ^ 2)))
    (Filter.Eventually.of_forall fun ω => measurable_one_sub_cos ω) ?_ ?_ ?_
  · refine Filter.eventually_of_mem (Metric.ball_mem_nhds ω₀ one_pos) fun ω hω => ?_
    have habs : |ω| ≤ M := by
      have : |ω - ω₀| < 1 := by simpa [Real.dist_eq] using hω
      have := abs_sub_abs_le_abs_sub ω ω₀
      simp only [hM]
      linarith [abs_sub_abs_le_abs_sub ω ω₀]
    exact Filter.Eventually.of_forall fun x =>
      ENNReal.ofReal_le_ofReal (one_sub_cos_mul_le habs)
  · have hsplit : ∀ x : ℝ, ENNReal.ofReal (2 * max 1 (M ^ 2) * min 1 (x ^ 2))
        = ENNReal.ofReal (2 * max 1 (M ^ 2)) * ENNReal.ofReal (min 1 (x ^ 2)) := fun x => by
      rw [ENNReal.ofReal_mul hMnn]
    simp only [hsplit]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top P.ν_integrable
  · refine Filter.Eventually.of_forall fun x => ?_
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((continuous_const.sub (Real.continuous_cos.comp
        (continuous_id.mul continuous_const))).tendsto ω₀)

/-- **`eq:levy-khintchine` is continuous in the frequency**, as an `ℝ≥0∞`-valued function.
@isnad1 id=continuo.0h1v.s3.304baef7db49 from=translated src=- shape=7000f90d vocab=b8b57771
-/
theorem continuous_exponentL (P : SymLevyPair) : Continuous P.exponentL := by
  have h1 : Continuous fun ω : ℝ => ENNReal.ofReal (P.a * ω ^ 2) :=
    ENNReal.continuous_ofReal.comp (continuous_const.mul (continuous_pow 2))
  exact h1.add P.continuous_jump

/-- **The exponent of a symmetric Lévy pair is continuous.** `#print axioms` reduces to Lean
core: the finiteness is `lem:quadratic-growth` and the limit is dominated convergence, so
`prop:fourier-toolbox`(3) is not spent.
@isnad1 id=continuo.0h1v.s4.d99e22dd62ba from=translated src=- shape=8735051e vocab=4a61e9a1
-/
theorem continuous_exponent (P : SymLevyPair) : Continuous P.exponent := by
  refine continuous_iff_continuousAt.2 fun ω => ?_
  exact (ENNReal.tendsto_toReal (P.exponentL_ne_top ω)).comp
    (P.continuous_exponentL.continuousAt)

end SymLevyPair

/-- **The exponent of an admissible profile is continuous**, `eq:sd-profile` being
`eq:levy-khintchine` at the pair `lem:profile-integrability` produces.
@isnad1 id=continuo.0h1v.s4.26faa5c1618f from=translated src=- shape=8735051e vocab=d3321c8f
-/
theorem SDProfile.continuous_exponent (P : SDProfile) : Continuous P.exponent := by
  obtain ⟨Q, -, -, hQ⟩ := profile_integrability_pair P
  simpa [funext hQ] using Q.continuous_exponent

end ScaleSpace
