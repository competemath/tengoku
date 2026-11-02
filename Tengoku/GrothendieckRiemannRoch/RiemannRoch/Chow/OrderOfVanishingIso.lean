/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.OrderOfVanishing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Order of vanishing under ring isomorphisms

This file supplies the algebraic naturality needed to transport scheme-theoretic principal
divisors across isomorphisms.  The first layer proves that the length-defined order is invariant
under an arbitrary ring equivalence by transporting the principal quotient and comparing module
lengths along a surjective scalar map.  The discrete-valuation factorization proof is retained as
an independent compatibility check.
-/

noncomputable section

namespace Ring

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The length-defined order is invariant under a ring equivalence.-/
theorem ord_map_ringEquiv (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let eAlg : R ≃ₐ[R] S := AlgEquiv.ofRingEquiv (f := e) (fun _ ↦ rfl)
  have hspan : Ideal.span {e x} = (Ideal.span {x}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQuot : (R ⧸ Ideal.span {x}) ≃ₐ[R] (S ⧸ Ideal.span {e x}) :=
    Ideal.quotientEquivAlg (Ideal.span {x}) (Ideal.span {e x}) eAlg hspan
  calc
    Ring.ord S (e x) = Module.length S (S ⧸ Ideal.span {e x}) := rfl
    _ = Module.length R (S ⧸ Ideal.span {e x}) :=
      (Module.length_eq_of_surjective (M := S ⧸ Ideal.span {e x})
        e.surjective).symm
    _ = Module.length R (R ⧸ Ideal.span {x}) :=
      eQuot.toLinearEquiv.length_eq.symm
    _ = Ring.ord R x := rfl

section DVR

variable [IsDomain R] [IsDomain S]
  [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]

/-- The additive valuation of a discrete valuation ring is invariant under a ring equivalence.-/
theorem addVal_map_ringEquiv (e : R ≃+* S) (x : R) :
    IsDiscreteValuationRing.addVal S (e x) = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · subst x
    simp [IsDiscreteValuationRing.addVal_zero]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  rw [map_mul, map_pow,
    IsDiscreteValuationRing.addVal_def' u hπ n]
  exact IsDiscreteValuationRing.addVal_def'
    (Units.map e.toMonoidHom u) (hπ.map e.toMulEquiv) n

/-- On discrete valuation rings, `ord_map_ringEquiv` also follows directly from uniformizer
factorization.-/
theorem ord_map_ringEquiv_of_dvr (e : R ≃+* S) (x : R) :
    Ring.ord S (e x) = Ring.ord R x := by
  rw [Ring.ord_eq_addVal, Ring.ord_eq_addVal, addVal_map_ringEquiv]

end DVR

section Domain

variable [IsDomain R] [IsDomain S]

theorem ordMonoidWithZeroHom_map_ringEquiv (e : R ≃+* S) (x : R) :
    Ring.ordMonoidWithZeroHom S (e x) = Ring.ordMonoidWithZeroHom R x := by
  by_cases hx : x = 0
  · subst x
    simp
  rw [Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr (e.map_ne_zero_iff.mpr hx)),
    Ring.ordMonoidWithZeroHom_eq_ord
      (mem_nonZeroDivisors_iff_ne_zero.mpr hx),
    ord_map_ringEquiv]

theorem ordFrac_map_ringEquiv
    {K L : Type*} [Field K] [Field L]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [Ring.KrullDimLE 1 R] [Ring.KrullDimLE 1 S]
    [Algebra R K] [Algebra S L]
    [IsFractionRing R K] [IsFractionRing S L]
    (eR : R ≃+* S) (eK : K ≃+* L)
    (hcompat : ∀ r : R,
      eK (algebraMap R K r) = algebraMap S L (eR r))
    (x : K) :
    Ring.ordFrac S (eK x) = Ring.ordFrac R x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  by_cases ha : a = 0
  · subst a
    simp
  simp only [map_div₀, hcompat]
  rw [Ring.ordFrac_eq_ord S (eR.map_ne_zero_iff.mpr ha),
    Ring.ordFrac_eq_ord R ha,
    Ring.ordFrac_eq_ord S (eR.map_ne_zero_iff.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hb)),
    Ring.ordFrac_eq_ord R (mem_nonZeroDivisors_iff_ne_zero.mp hb),
    ordMonoidWithZeroHom_map_ringEquiv,
    ordMonoidWithZeroHom_map_ringEquiv]

end Domain

end Ring

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A scheme isomorphism induces the contravariant isomorphism of function fields given by its
stalk map at the generic point.-/
noncomputable def functionFieldIsoOfIso (f : X ⟶ Y) [IsIso f] :
    Y.functionField ≅ X.functionField :=
  Y.presheaf.stalkCongr
      (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm) ≪≫
    asIso (f.stalkMap (genericPoint X))

/-- The function-field isomorphism induced by a scheme isomorphism is compatible with the local
stalk isomorphism and the canonical maps from a local ring to the function field.-/
theorem functionFieldIsoOfIso_algebraMap (f : X ⟶ Y) [IsIso f]
    (x : X) (r : Y.presheaf.stalk (f x)) :
    (functionFieldIsoOfIso f).commRingCatIsoToRingEquiv
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField r) =
      algebraMap (X.presheaf.stalk x) X.functionField
        ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv r) := by
  let hX : genericPoint X ⤳ x := (genericPoint_spec X).specializes trivial
  let hY : genericPoint Y ⤳ f x := (genericPoint_spec Y).specializes trivial
  let hη : f (genericPoint X) ⤳ genericPoint Y :=
    specializes_of_eq (genericPoint_eq_of_isOpenImmersion f)
  have htransport :
      (Y.presheaf.stalkCongr
          (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm)).hom
          (Y.presheaf.stalkSpecializes hY r) =
        Y.presheaf.stalkSpecializes (hX.map f.continuous) r := by
    change (Y.presheaf.stalkSpecializes hη)
        (Y.presheaf.stalkSpecializes hY r) =
      Y.presheaf.stalkSpecializes (hX.map f.continuous) r
    rw [← ConcreteCategory.comp_apply,
      TopCat.Presheaf.stalkSpecializes_comp]
  change (f.stalkMap (genericPoint X)).hom
      ((Y.presheaf.stalkCongr
          (.of_eq (genericPoint_eq_of_isOpenImmersion f).symm)).hom
        (Y.presheaf.stalkSpecializes hY r)) =
    X.presheaf.stalkSpecializes hX ((f.stalkMap x).hom r)
  rw [htransport]
  exact f.stalkSpecializes_stalkMap_apply (genericPoint X) x hX r

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

end AlgebraicGeometry.Scheme
