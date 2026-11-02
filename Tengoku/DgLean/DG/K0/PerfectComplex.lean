import Tengoku.DgLean.DG.Derived.PerfectThick
import Tengoku.DgLean.DG.K0.Compact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `K₀` of perfect complexes

Let `R` be a ring. The perfect objects of the derived category of `R`-modules
(`DG.IsPerfect R`, the objects isomorphic to a strictly bounded complex of finitely generated
projective modules) form a thick triangulated subcategory `D^perf(R)` (`DG.IsPerfect.isThick`).
This file proves that its Grothendieck group is the Grothendieck group `K₀(R)` of finitely
generated projective `R`-modules (`DG.ProjK0 R`):

  `K₀(D^perf(R)) ≃+ K₀(R)`,   `[X] ↦ χ(X)`,   `[P] ↤ [P]`,

where `χ(X) = Σₙ (-1)ⁿ [Kⁿ]` is the Euler characteristic of any perfect complex `K` representing
`X` (compare C. A. Weibel, *The K-book*, Chapter II, §9, on Euler characteristics of bounded
complexes).

## Main definitions and results

* `DG.IsPerfect.eulerChar X hX : DG.ProjK0 R`: the Euler characteristic of a perfect object,
  independent of the perfect complex representing it (`DG.IsPerfect.eulerChar_eq`), invariant
  under isomorphisms and additive on distinguished triangles (`DG.IsPerfect.eulerChar_obj₂`).
* `DG.IsPerfect.K0Equiv P hP : K₀(P) ≃+ DG.ProjK0 R` for any description `P` of the perfect
  objects (`hP : ∀ X, P X ↔ DG.IsPerfect R X`, with `P` a triangulated subcategory closed under
  isomorphisms). The flexibility in `P` allows to apply the result to other descriptions of the
  perfect objects, e.g. as the compact objects.
* `DG.perfectK0Equiv R : K₀(D^perf(R)) ≃+ DG.ProjK0 R`, with `DG.perfectK0Equiv_mk` and
  `DG.perfectK0Equiv_symm_mk`.
-/

open CategoryTheory Category Limits Pretriangulated ZeroObject

universe w u

namespace DG

variable {R : Type u} [Ring R] [_root_.HasDerivedCategory.{w} (ModuleCat.{u} R)]

namespace IsPerfect

/-! ### The Euler characteristic of a perfect object -/

/-- The Euler characteristic `χ(X) ∈ K₀(R)` of a perfect object of the derived category: the
Euler characteristic `Σₙ (-1)ⁿ [Kⁿ]` of a perfect complex `K` representing it.-/
noncomputable def eulerChar (X : _root_.DerivedCategory (ModuleCat.{u} R))
    (hX : IsPerfect R X) : ProjK0.{u} R :=
  hX.choose_spec.choose.eulerChar

/-- The Euler characteristic of a perfect object can be computed from any perfect complex
representing it.-/
theorem eulerChar_eq {X : _root_.DerivedCategory (ModuleCat.{u} R)} (hX : IsPerfect R X)
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsPerfectComplex K)
    (e : _root_.DerivedCategory.Q.obj K ≅ X) : eulerChar X hX = hK.eulerChar :=
  IsPerfectComplex.eulerChar_eq_of_iso_Q _ hK (hX.choose_spec.choose_spec.some ≪≫ e.symm)

/-- Isomorphic perfect objects have the same Euler characteristic.-/
theorem eulerChar_eq_of_iso {X Y : _root_.DerivedCategory (ModuleCat.{u} R)} (e : X ≅ Y)
    (hX : IsPerfect R X) (hY : IsPerfect R Y) : eulerChar X hX = eulerChar Y hY := by
  have hY' := hY
  obtain ⟨K, hK, ⟨e'⟩⟩ := hY'
  rw [eulerChar_eq hY hK e', eulerChar_eq hX hK (e' ≪≫ e.symm)]

/-- The Euler characteristic of a finitely generated projective module placed in degree `n`.-/
theorem eulerChar_singleFunctor_obj {M : ModuleCat.{u} R} (hM : IsFGProjective R M) (n : ℤ)
    (h : IsPerfect R ((_root_.DerivedCategory.singleFunctor (ModuleCat.{u} R) n).obj M)) :
    eulerChar _ h = n.negOnePow • ProjK0.mk M hM := by
  rw [eulerChar_eq h (IsPerfectComplex.single hM n) (singleFunctorObjIso n M).symm,
    IsPerfectComplex.eulerChar_single]

/-- **Additivity of the Euler characteristic**: `χ(Y) = χ(X) + χ(Z)` for a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` of perfect objects.-/
theorem eulerChar_obj₂ (T : Triangle (_root_.DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : IsPerfect R T.obj₁) (h₂ : IsPerfect R T.obj₂)
    (h₃ : IsPerfect R T.obj₃) :
    eulerChar T.obj₂ h₂ = eulerChar T.obj₁ h₁ + eulerChar T.obj₃ h₃ := by
  have h₁' := h₁
  have h₂' := h₂
  obtain ⟨K, hK, ⟨e₁⟩⟩ := h₁'
  obtain ⟨L, hL, ⟨e₂⟩⟩ := h₂'
  obtain ⟨g, ⟨e₃⟩⟩ := exists_iso_mappingCone T hT hK e₁ e₂
  rw [eulerChar_eq h₁ hK e₁, eulerChar_eq h₂ hL e₂, eulerChar_eq h₃ (hK.mappingCone g hL) e₃,
    hK.eulerChar_mappingCone g hL, add_sub_cancel]

/-! ### The comparison of Grothendieck groups -/

section K0

variable (P : ObjectProperty (_root_.DerivedCategory (ModuleCat.{u} R))) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms] (hP : ∀ X, P X ↔ IsPerfect R X)

/-- The homomorphism `K₀(D^perf(R)) →+ K₀(R)`, `[X] ↦ χ(X)`.-/
noncomputable def K0ToProjK0 : K0 P.FullSubcategory →+ ProjK0.{u} R :=
  K0.lift (fun X => eulerChar X.obj ((hP _).1 X.property)) (fun T hT =>
    eulerChar_obj₂ (P.ι.mapTriangle.obj T) (P.ι.map_distinguished T hT)
      ((hP _).1 T.obj₁.property) ((hP _).1 T.obj₂.property) ((hP _).1 T.obj₃.property))

omit [P.IsClosedUnderIsomorphisms] in
@[simp]
theorem K0ToProjK0_mk [P.IsClosedUnderIsomorphisms] (X : P.FullSubcategory) :
    K0ToProjK0 P hP (K0.mk X) = eulerChar X.obj ((hP _).1 X.property) :=
  K0.lift_mk _ _ X

end K0

end IsPerfect

end DG
