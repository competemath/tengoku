import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Algebra_etale_of_moduleFinite_of_flat_of_forall_isUnramifiedAt

set_option autoImplicit false

universe u

/--
@isnad1 id=etale.1h2v.s6.b461a4a2acd6 from=translated src=- shape=254130b5 vocab=028e33d3
-/
theorem solution
    (O : Type u) [CommRing O] [IsNoetherianRing O] (C : Type u) [CommRing C] [Algebra O C] [Module.Finite O C] [Module.Flat O C]
    (h : ∀ (Q : Ideal C) [Q.IsPrime], Algebra.IsUnramifiedAt O Q) :
    Algebra.Etale O C := by
  haveI : Algebra.FinitePresentation O C := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI : Algebra.FormallyUnramified O C :=
    Algebra.formallyUnramified_iff_forall.mpr fun q => h q.asIdeal
  exact Algebra.Etale.of_formallyUnramified_of_flat
