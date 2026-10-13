/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.MeasureTheory.Group.Conjugation

/-!
# Precomposition with inversion on `Lp` of a group

A measure on a type with involutive inversion that is invariant under inversion — normalized Haar
measure on a compact group, for instance — makes `g ↦ g⁻¹` measure preserving, so precomposition
with it is a linear isometric equivalence of `Lp E p μ`. Inversion is an involution, so this
equivalence is its own inverse: an element of `Lp` vanishes exactly when its inverse-translate does.

The construction is `MeasureTheory.Lp.compMeasurePreservingₗᵢEquiv`
(`TauCeti/MeasureTheory/Function/Lp/CompMeasurePreservingEquiv.lean`) at the inverse pair
`Inv.inv`, `Inv.inv`; what this file adds is the interaction with the class functions of
`TauCeti/MeasureTheory/Group/Conjugation.lean` and the compatibility with the continuous functions
that supply the elements of `Lp` in practice.

The intended use is the change of variables `∫ f g⁻¹ dg = ∫ f g dg` in inner-product form: for `p`
equal to `2` this map preserves the inner product, which is what turns a statement about a function
into the corresponding statement about its inverse-translate.

## Main definitions

* `TauCeti.invLpₗᵢ`: precomposition with inversion, as a linear isometric equivalence of `Lp E p μ`.

## Main statements

* `TauCeti.invLpₗᵢ_apply`: it is precomposition with `Inv.inv`.
* `TauCeti.coeFn_invLpₗᵢ`: it is represented by `g ↦ f g⁻¹`.
* `TauCeti.invLpₗᵢ_invLpₗᵢ`: it is an involution.
* `TauCeti.invLpₗᵢ_mem_classFunctionLp` and `TauCeti.invLpₗᵢ_mem_classFunctionLp_iff`: it preserves
  the class functions, because inversion commutes with conjugation, and being an involution it
  reflects them too.
* `TauCeti.invLpₗᵢ_toLp`: on a continuous function it is precomposition with inversion.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {G E : Type*} [MeasurableSpace G] [NormedAddCommGroup E] {p : ℝ≥0∞}
  [Fact (1 ≤ p)] {μ : Measure G}
variable (𝕜 : Type*) [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

section Involution

variable [InvolutiveInv G] [MeasurableInv G] [μ.IsInvInvariant]

/-- **Precomposition with inversion on `Lp`**, for a measure invariant under inversion. It is a
linear isometric equivalence because `g ↦ g⁻¹` preserves `μ` and is its own inverse. -/
noncomputable def invLpₗᵢ : Lp E p μ ≃ₗᵢ[𝕜] Lp E p μ :=
  Lp.compMeasurePreservingₗᵢEquiv 𝕜 (Measure.measurePreserving_inv μ)
    (Measure.measurePreserving_inv μ) (.of_eq (funext inv_inv))

variable {𝕜}

/-- The inversion equivalence is precomposition with `Inv.inv`.

Not a `simp` lemma: unfolding to `Lp.compMeasurePreserving` dissolves the abstraction, and it
would take `TauCeti.invLpₗᵢ_invLpₗᵢ` out of simp normal form (the `simpNF` linter rejects the
pair). Use it to rewrite by hand where the underlying precomposition is wanted. -/
theorem invLpₗᵢ_apply (f : Lp E p μ) :
    invLpₗᵢ 𝕜 f = Lp.compMeasurePreserving Inv.inv (Measure.measurePreserving_inv μ) f :=
  Lp.compMeasurePreservingₗᵢEquiv_apply 𝕜 _ _ _ f

/-- The inverse-translate of a class of functions is represented by `g ↦ f g⁻¹`. -/
theorem coeFn_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 f =ᵐ[μ] fun g ↦ f g⁻¹ :=
  Lp.coeFn_compMeasurePreservingₗᵢEquiv 𝕜 (Measure.measurePreserving_inv μ)
    (Measure.measurePreserving_inv μ) _ f

/-- **Inverting twice is the identity.**  The two precompositions compose to precomposition with
`g ↦ (g⁻¹)⁻¹`, which is the identity on the nose. -/
@[simp]
theorem invLpₗᵢ_invLpₗᵢ (f : Lp E p μ) : invLpₗᵢ 𝕜 (invLpₗᵢ 𝕜 f) = f := by
  simpa only [invLpₗᵢ_apply] using
    Lp.compMeasurePreserving_comp_apply_of_ae_id (E := E) (p := p)
    (Measure.measurePreserving_inv μ) (Measure.measurePreserving_inv μ)
    (.of_eq (funext inv_inv)) f

/-- The inversion equivalence is its own inverse: it is an equivalence and an involution. -/
@[simp]
theorem invLpₗᵢ_symm : (invLpₗᵢ 𝕜 (E := E) (p := p) (μ := μ)).symm = invLpₗᵢ 𝕜 := by
  refine LinearIsometryEquiv.ext fun f ↦ ?_
  rw [LinearIsometryEquiv.symm_apply_eq, invLpₗᵢ_invLpₗᵢ]

end Involution

section ClassFunction

variable [Group G] [MeasurableInv G] [μ.IsInvInvariant] [MeasurableMul G]
  [SMulInvariantMeasure (ConjAct G) G μ]

end ClassFunction

section Continuous

variable [InvolutiveInv G] [MeasurableInv G] [μ.IsInvInvariant] [TopologicalSpace G]
  [ContinuousInv G] [CompactSpace G] [BorelSpace G] [SecondCountableTopologyEither G E]
  [IsFiniteMeasure μ]

/-- **On a continuous function, inversion on `Lp` is precomposition with inversion.** -/
theorem invLpₗᵢ_toLp (F : C(G, E)) :
    invLpₗᵢ 𝕜 (ContinuousMap.toLp p μ 𝕜 F) =
      ContinuousMap.toLp p μ 𝕜 (F.comp ⟨Inv.inv, continuous_inv⟩) := by
  rw [invLpₗᵢ_apply]
  exact Lp.compMeasurePreserving_toLp 𝕜 F ⟨Inv.inv, continuous_inv⟩
    (Measure.measurePreserving_inv μ)

end Continuous

end TauCeti
