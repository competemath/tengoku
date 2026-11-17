import Tengoku.FltAnthropic.Definitions.Def_ArithFrobResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArithFrobResidue_orderOf_arithFrob_eq_finrank_of_inertia_eq_bot
open scoped Pointwise
attribute [local instance] Ideal.Quotient.field
/--
@isnad1 id=eq.2h5v.s9.51883832b52a from=translated src=- shape=1ad258cf vocab=a2fa66ce
-/
theorem solution
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    (hP : P.inertia G = ⊥)
    (σ : MulAction.stabilizer G P) (hσ : IsArithFrobAt A (σ : G) P) :
    orderOf (σ : G) = Module.finrank (A ⧸ P.under A) (B ⧸ P) :=
  ArithFrobResidue.orderOf_arithFrob_eq_finrank_of_inertia_eq_bot hP σ hσ
