import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_charZero_functionField_of_hom_spec_of_charZero

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

/--
@isnad1 id=charzero.0h3v.s6.117f69ae51c6 from=translated src=- shape=613fa9a1 vocab=27ff17ea
-/
theorem solution
    (X : Scheme.{0}) [IsIntegral X]
    (C : Type) [Field C] [CharZero C] (f : Spec (CommRingCat.of C) ⟶ X) :
    CharZero X.functionField := by

  haveI : CharZero ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    (RingHom.charZero_iff (ϕ := (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom)
      (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv.injective).1 inferInstance

  haveI : CharZero ↑Γ(X, ⊤) := (f.appTop).hom.charZero

  haveI := (Scheme.Opens.nonempty_iff (⊤ : X.Opens)).2 ⟨(inferInstance : Nonempty X).some, trivial⟩
  exact (RingHom.charZero_iff (X.germToFunctionField_injective ⊤)).1 inferInstance
