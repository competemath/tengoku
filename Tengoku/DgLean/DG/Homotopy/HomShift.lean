import Tengoku.DgLean.DG.Homotopy.Shift
import Tengoku.DgLean.DG.Module.HomShiftIso

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Morphisms into shifts in the homotopy category

Let `A` be a dg ring and `M`, `N` dg `A`-modules. Morphisms `M → N⟦n⟧` in the homotopy category
`DG.HomotopyCategory A` are the `n`-th cohomology of the Hom complex:

* `DG.HomotopyCategory.homShiftAddEquivCohomology M N n :
    Hom_{H(A)}(M, N⟦n⟧) ≃+ Hⁿ(HOM_A(M, N))`,

obtained by combining `Hom_{H(A)}(M, N⟦n⟧) ≃+ H⁰(HOM_A(M, N⟦n⟧))`
(`DG.HomotopyCategory.homAddEquivCohomology`) with the isomorphism of dg abelian groups
`HOM_A(M, N⟦n⟧) ≅ HOM_A(M, N)⟦n⟧` (`DG.DGModule.HOM.rightShiftEquiv`). The class of a morphism
of dg modules `f : M → N⟦n⟧` is sent to the class of the `n`-cocycle `f`
(`DG.HomotopyCategory.homShiftAddEquivCohomology_quotient_map`). Here `N⟦n⟧` is the shift in
the homotopy category, identified with the image of the shift of dg modules by
`(quotient A).commShiftIso n`.

On the level of dg modules, `DG.DGModule.HOM.homShiftAddEquivCocycles :
(M →ᵈᵍ[A] N⟦n⟧) ≃+ Zⁿ(HOM_A(M, N))`.
-/

open scoped DG

open CategoryTheory

universe v u

namespace DG

namespace DGModule.HOM

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (M N : Type*)
  [AddCommGroup M] [DGAddCommGroup M] [Module A M] [DGModule A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N] [DGModule A N]

/-- Morphisms of dg modules `M → N⟦n⟧` are the `n`-cocycles of the Hom complex `HOM_A(M, N)`
(as a dg abelian group).-/
noncomputable def homShiftAddEquivCocycles (n : ℤ) :
    (M →ᵈᵍ[A] Shift n N) ≃+ cocycles (HOM A M N) n :=
  (Cocycle.homShiftAddEquiv A M N n).trans (cocyclesAddEquiv A M N n)

/--
@isnad1 id=eq.0h5v.s11.f5192eb080f9 from=translated src=- shape=a858d1d5 vocab=d3178938
-/
@[simp]
theorem coe_homShiftAddEquivCocycles_apply (n : ℤ) (f : M →ᵈᵍ[A] Shift n N) :
    (homShiftAddEquivCocycles M N n f : HOM A M N) =
      DirectSum.of (fun k => Cochain A M N k) n (Cocycle.homShiftAddEquiv A M N n f) :=
  rfl

end DGModule.HOM

namespace HomotopyCategory

variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A] (M N : DGModuleCat.{v} A)

/-- Composition with an isomorphism, as an additive equivalence of Hom groups (auxiliary).-/
private def compIsoAddEquiv {X Y Z : HomotopyCategory.{v} A} (e : Y ≅ Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' f g := Preadditive.add_comp _ _ _ _ _ _

-- Unfolding the shift on `DGModuleCat` in the instance arguments of `HOM` is slow.
set_option maxHeartbeats 400000 in
/-- `Hom_{H(A)}(M, N⟦n⟧) ≃+ Hⁿ(HOM_A(M, N))`: morphisms into a shift in the homotopy category
are the cohomology of the Hom complex.-/
noncomputable def homShiftAddEquivCohomology (n : ℤ) :
    ((quotient A).obj M ⟶ ((quotient A).obj N)⟦n⟧) ≃+ cohomology (DGModule.HOM A M N) n :=
  (compIsoAddEquiv (((quotient A).commShiftIso n).app N)).symm.trans
    ((homAddEquivCohomology M ((shiftFunctor (DGModuleCat.{v} A) n).obj N)).trans
      (DGModule.HOM.cohomologyRightShiftAddEquiv A M N n 0 n (zero_add n)))

end HomotopyCategory

end DG
