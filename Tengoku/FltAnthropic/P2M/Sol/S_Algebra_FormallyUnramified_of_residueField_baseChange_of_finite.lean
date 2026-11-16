import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite
open scoped TensorProduct

open IsLocalRing

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
@isnad1 id=formally.1h2v.s7.1eac94e217dd from=translated src=- shape=b9474670 vocab=349db73c
-/
theorem solution (R S : Type*) [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (h : Algebra.FormallyUnramified (IsLocalRing.ResidueField R)
      (IsLocalRing.ResidueField R ⊗[R] S)) :
    Algebra.FormallyUnramified R S := by
  haveI : Module.Finite S Ω[S⁄R] := inferInstance
  haveI : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
  have e := KaehlerDifferential.tensorKaehlerEquivBase R (ResidueField R) S
    (ResidueField R ⊗[R] S)
  haveI : Subsingleton Ω[(ResidueField R ⊗[R] S)⁄(ResidueField R)] :=
    h.subsingleton_kaehlerDifferential
  haveI : Subsingleton (ResidueField R ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
  exact ⟨(IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[S⁄R])).mp inferInstance⟩
