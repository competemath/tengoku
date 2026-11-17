import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_prod_vanishingIdeal_eq_of_pairwise_disjoint_of_support_eq_iSup

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

/--
@isnad1 id=eq.3h4v.s8.07ea8469f44e from=translated src=- shape=12bcb891 vocab=2d7a7173
-/
theorem solution
    {Y : Scheme.{u}} {ι : Type*} [Fintype ι] (Z : ι → Closeds Y)
    (hdisj : Pairwise fun i j => Disjoint (Z i) (Z j))
    (J : Y.IdealSheafData) (hrad : J.radical = J) (hsupp : J.support = ⨆ i, Z i) :
    ∏ i, Scheme.IdealSheafData.vanishingIdeal (Z i) = J := by
  classical

  have hmul : ∀ I K : Y.IdealSheafData, I ⊔ K = ⊤ → I * K = I ⊓ K := by
    intro I K h
    ext U : 2
    rw [Scheme.IdealSheafData.ideal_mul, Scheme.IdealSheafData.ideal_inf, Pi.mul_apply, Pi.inf_apply]
    apply Ideal.mul_eq_inf_of_coprime
    have := congrArg (fun L : Y.IdealSheafData => L.ideal U) h
    simpa [Scheme.IdealSheafData.ideal_sup, Scheme.IdealSheafData.ideal_top] using this

  have hcop : ∀ I K : Y.IdealSheafData, Disjoint I.support K.support → I ⊔ K = ⊤ := by
    intro I K h
    rw [← Scheme.IdealSheafData.support_eq_bot_iff, Scheme.IdealSheafData.support_sup]
    exact h.eq_bot
  have hsuppV : ∀ A : Closeds Y, (Scheme.IdealSheafData.vanishingIdeal A).support = A := fun A =>
    Closeds.ext (Scheme.IdealSheafData.coe_support_vanishingIdeal A)

  have key : ∀ s : Finset ι, ∏ i ∈ s, Scheme.IdealSheafData.vanishingIdeal (Z i) =
      Scheme.IdealSheafData.vanishingIdeal (s.sup Z) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.sup_insert, Scheme.IdealSheafData.vanishingIdeal_sup]
      apply hmul
      apply hcop
      rw [hsuppV, hsuppV, Finset.disjoint_sup_right]
      intro i hi
      exact hdisj (fun h => ha (h ▸ hi))
  rw [key, Finset.sup_univ_eq_iSup, ← hsupp, Scheme.IdealSheafData.vanishingIdeal_support, hrad]
