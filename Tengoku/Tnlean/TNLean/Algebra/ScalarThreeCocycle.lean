/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Tnlean.TNLean.Algebra.ProjectiveRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicative scalar 3-cocycles

This file isolates the scalar algebra of the fusion-tensor gauge freedom in
arXiv:2502.20257, equations `eq:scalar_fus_ten`, `eq:3-cocycle`, and
`eq:omegagauge`. It does not assert the existence of fusion tensors or attach
these scalars to a matrix product unitary.

For a group `G`, a scalar 3-cochain has values in `ℂˣ`. A scalar 2-cochain is
represented by the existing function type `ScalarCocycle G`; its name and
2-cocycle interpretation are unchanged.

## Main definitions

* `ScalarThreeCochain`: multiplicative scalar 3-cochains.
* `ScalarThreeCochain.IsCocycle`: the associativity 3-cocycle equation.
* `ScalarThreeCochain.IsNormalized`: triviality when any argument is the identity.
* `ScalarThreeCochain.coboundary`: the 2-cochain coboundary in `eq:omegagauge`.
* `ScalarThreeCochain.fusionGauge`: the scalar fusion-tensor gauge action.
* `ScalarThreeCochain.CohomologousTo`: equality up to a fusion gauge.
* `ScalarThreeCochain.IsTrivialGaugeClass`: triviality of the scalar gauge class.
-/

namespace TNLean.Algebra

variable {G : Type*} [Group G]

/-- A multiplicative scalar 3-cochain `G × G × G → ℂˣ`.

This is the scalar function denoted by `ω` in arXiv:2502.20257,
`eq:3-cocycle`.-/
abbrev ScalarThreeCochain (G : Type*) := G → G → G → Units ℂ

namespace ScalarCocycle

/-- A scalar 2-cochain is normalized when it is one whenever either argument
is the identity. This standard condition is sufficient for its coboundary to
preserve normalized 3-cochains; `isNormalized_coboundary_iff` records the exact
weaker condition.-/
def IsNormalized (β : ScalarCocycle G) : Prop :=
  (∀ g, β 1 g = 1) ∧ (∀ g, β g 1 = 1)

end ScalarCocycle

namespace ScalarThreeCochain

/-- The multiplicative scalar 3-cocycle equation

`ω(gh,k,l) ω(g,h,kl) = ω(g,h,k) ω(g,hk,l) ω(h,k,l)`

from arXiv:2502.20257, `eq:3-cocycle`.-/
def IsCocycle (ω : ScalarThreeCochain G) : Prop :=
  ∀ g h k l,
    ω (g * h) k l * ω g h (k * l) =
      ω g h k * ω g (h * k) l * ω h k l

/-- A scalar 3-cochain is normalized when it equals one whenever any argument
is the identity. This is the standing normalization convention following
arXiv:2502.20257, `eq:triv_omegas`.

**Local fix (repeated normalization case):** The source display repeats
`ω(g,h,1) = 1` three times. The three clauses below give the intended cases in
which the first, second, or third argument is the identity. See
`docs/paper-gaps/fbc25_three_cocycle_normalization_typo.tex`.-/
def IsNormalized (ω : ScalarThreeCochain G) : Prop :=
  (∀ h k, ω 1 h k = 1) ∧
    (∀ g k, ω g 1 k = 1) ∧
      (∀ g h, ω g h 1 = 1)

/-- The multiplicative 3-coboundary of a scalar 2-cochain:

`(dβ)(g,h,k) = β(g,hk) β(h,k) / (β(g,h) β(gh,k))`.

The factor order is exactly arXiv:2502.20257, `eq:omegagauge`, induced by the
fusion-tensor scalar freedom in `eq:scalar_fus_ten`.-/
def coboundary (β : ScalarCocycle G) : ScalarThreeCochain G :=
  fun g h k => (β g (h * k) * β h k) / (β g h * β (g * h) k)

/-- The fusion-tensor scalar gauge action from arXiv:2502.20257,
`eq:omegagauge`: `ω ↦ dβ · ω`.-/
def fusionGauge (β : ScalarCocycle G) (ω : ScalarThreeCochain G) :
    ScalarThreeCochain G :=
  fun g h k => coboundary β g h k * ω g h k

/-- The trivial scalar 2-cochain acts identically.
@isnad1 id=eq.0h2v.s5.632da6bc3a3a from=translated src=- shape=f53d27ba vocab=23bea6cb
-/
@[simp]
theorem fusionGauge_one (ω : ScalarThreeCochain G) :
    fusionGauge (fun _ _ => 1) ω = ω := by
  funext g h k
  simp [fusionGauge, coboundary]

/-- Successive fusion gauges multiply their scalar 2-cochains pointwise.
@isnad1 id=eq.0h4v.s6.693238baca21 from=translated src=- shape=ff6f031a vocab=33b6e038
-/
theorem fusionGauge_comp (β γ : ScalarCocycle G) (ω : ScalarThreeCochain G) :
    fusionGauge γ (fusionGauge β ω) = fusionGauge (β * γ) ω := by
  funext g h k
  simp only [fusionGauge, coboundary, Pi.mul_apply, div_eq_mul_inv, mul_inv_rev]
  simp only [mul_assoc, mul_comm, mul_left_comm]

/-- The coboundary of every scalar 2-cochain is a scalar 3-cocycle.
@isnad1 id=iscocycl.0h2v.s3.6dfee6a77998 from=translated src=- shape=ed10201d vocab=9d862320
-/
theorem isCocycle_coboundary (β : ScalarCocycle G) : IsCocycle (coboundary β) := by
  intro g h k l
  simp only [coboundary, mul_assoc]
  apply Units.ext
  push_cast
  field_simp

/-- The pointwise product of scalar 3-cocycles is a scalar 3-cocycle.
@isnad1 id=iscocycl.2h3v.s6.2d62c4d8636f from=translated src=- shape=1333e5f0 vocab=7b200025
-/
theorem IsCocycle.mul {ω η : ScalarThreeCochain G}
    (hω : IsCocycle ω) (hη : IsCocycle η) : IsCocycle (ω * η) := by
  intro g h k l
  simp only [Pi.mul_apply]
  calc
    _ = (ω (g * h) k l * ω g h (k * l)) *
        (η (g * h) k l * η g h (k * l)) := by ac_rfl
    _ = (ω g h k * ω g (h * k) l * ω h k l) *
        (η g h k * η g (h * k) l * η h k l) := by rw [hω, hη]
    _ = _ := by ac_rfl

/-- Fusion-tensor scalar gauge transformations preserve the 3-cocycle equation.
@isnad1 id=iscocycl.1h3v.s4.64bd9af31da2 from=translated src=- shape=c9bdb183 vocab=dc8e2db1
-/
theorem IsCocycle.fusionGauge {ω : ScalarThreeCochain G} (hω : IsCocycle ω)
    (β : ScalarCocycle G) : IsCocycle (fusionGauge β ω) :=
  (isCocycle_coboundary β).mul hω

/-- A scalar 2-cochain has normalized 3-coboundary exactly when its values on
both identity axes agree with one constant. Normalizing that constant to one is
sufficient but not necessary.
@isnad1 id=iff.0h2v.s6.033dd2ab02d2 from=translated src=- shape=62a8e818 vocab=db7ab35f
-/
theorem isNormalized_coboundary_iff (β : ScalarCocycle G) :
    IsNormalized (coboundary β) ↔
      ∃ c : Units ℂ, (∀ g, β 1 g = c) ∧ (∀ g, β g 1 = c) := by
  constructor
  · rintro ⟨hleft, hmiddle, -⟩
    refine ⟨β 1 1, fun g => ?_, fun g => ?_⟩
    · exact div_eq_one.mp (by simpa [coboundary] using hleft 1 g)
    · exact (div_eq_one.mp (by simpa [coboundary] using hmiddle g 1)).symm
  · rintro ⟨c, hleft, hright⟩
    refine ⟨fun h k => ?_, fun g k => ?_, fun g h => ?_⟩
    · simp [coboundary, hleft]
    · simp only [coboundary, one_mul, mul_one, hleft, hright]
      rw [mul_comm]
      simp
    · simp [coboundary, hright]

/-- A normalized scalar 2-cochain has normalized 3-coboundary.
@isnad1 id=isnormal.1h2v.s4.d0a25349882e from=translated src=- shape=b161458b vocab=bb14d5e5
-/
theorem isNormalized_coboundary {β : ScalarCocycle G}
    (hβ : β.IsNormalized) : IsNormalized (coboundary β) := by
  apply (isNormalized_coboundary_iff β).2
  exact ⟨1, hβ.1, hβ.2⟩

/-- Pointwise multiplication preserves normalized scalar 3-cochains.
@isnad1 id=isnormal.2h3v.s6.c5d0afc6d8f9 from=translated src=- shape=1333e5f0 vocab=b0f4fbc5
-/
theorem IsNormalized.mul {ω η : ScalarThreeCochain G}
    (hω : IsNormalized ω) (hη : IsNormalized η) : IsNormalized (ω * η) := by
  rcases hω with ⟨hω₁, hω₂, hω₃⟩
  rcases hη with ⟨hη₁, hη₂, hη₃⟩
  refine ⟨fun h k => ?_, fun g k => ?_, fun g h => ?_⟩
  · simp [hω₁, hη₁]
  · simp [hω₂, hη₂]
  · simp [hω₃, hη₃]

/-- A fusion gauge preserves normalization when its scalar 2-cochain is normalized.
@isnad1 id=isnormal.2h3v.s4.c158224ad394 from=translated src=- shape=c2c20cae vocab=0c8339ea
-/
theorem IsNormalized.fusionGauge {ω : ScalarThreeCochain G}
    (hω : IsNormalized ω) {β : ScalarCocycle G} (hβ : β.IsNormalized) :
    IsNormalized (fusionGauge β ω) :=
  (isNormalized_coboundary hβ).mul hω

/-- Two scalar 3-cochains are cohomologous when the first is obtained from the
second by the fusion-gauge action in arXiv:2502.20257, `eq:omegagauge`.-/
def CohomologousTo (ω η : ScalarThreeCochain G) : Prop :=
  ∃ β : ScalarCocycle G, fusionGauge β η = ω

namespace CohomologousTo

/-- Cohomologous-to is reflexive.
@isnad1 id=cohomolo.0h2v.s3.1bf3ec7bbf00 from=translated src=- shape=82448d51 vocab=b446895d
-/
theorem refl (ω : ScalarThreeCochain G) : CohomologousTo ω ω :=
  ⟨fun _ _ => 1, fusionGauge_one ω⟩

/-- Cohomologous-to is symmetric.
@isnad1 id=cohomolo.1h3v.s4.dcc38e3ef80a from=translated src=- shape=1a0a78f4 vocab=b446895d
-/
theorem symm {ω η : ScalarThreeCochain G} (h : CohomologousTo ω η) :
    CohomologousTo η ω := by
  obtain ⟨β, hβ⟩ := h
  refine ⟨β⁻¹, ?_⟩
  rw [← hβ, fusionGauge_comp, mul_inv_cancel]
  exact fusionGauge_one η

/-- Cohomologous-to is transitive.
@isnad1 id=cohomolo.2h4v.s4.04b3809023e4 from=translated src=- shape=5499c893 vocab=b446895d
-/
theorem trans {ω η θ : ScalarThreeCochain G}
    (hωη : CohomologousTo ω η) (hηθ : CohomologousTo η θ) :
    CohomologousTo ω θ := by
  obtain ⟨β, hβ⟩ := hωη
  obtain ⟨γ, hγ⟩ := hηθ
  refine ⟨γ * β, ?_⟩
  calc
    fusionGauge (γ * β) θ = fusionGauge β (fusionGauge γ θ) :=
      (fusionGauge_comp γ β θ).symm
    _ = fusionGauge β η := congrArg (fusionGauge β) hγ
    _ = ω := hβ

/-- Cohomologous-to is an equivalence relation.
@isnad1 id=equivale.0h1v.s3.e87cdc1338ba from=translated src=- shape=aa7e0af4 vocab=344a2afc
-/
theorem equivalence : Equivalence (CohomologousTo (G := G)) :=
  ⟨refl, symm, trans⟩

end CohomologousTo

/-- A scalar 3-cochain has trivial gauge class when it is cohomologous to
the constant cochain one.-/
def IsTrivialGaugeClass (ω : ScalarThreeCochain G) : Prop :=
  CohomologousTo ω (fun _ _ _ => 1)

end ScalarThreeCochain

end TNLean.Algebra
