import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_pi_surj_torsion

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

/--
@isnad1 id=ex.2h9v.s14.3d74e2018641 from=translated src=- shape=055e97c4 vocab=906a14e2
-/
theorem solution
    {E V : Type} [Fintype E] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) {n : ℕ} (hn : 0 < n) :
    ∀ t : P.JacPoints, n • t = 0 → ∃ u : ↥P.U, P.π u = t := by
  intro t ht
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective P.periodLattice t
  have hs : s ∈ P.U := by
    simp only [PeriodDatum.U, Submodule.mem_comap]
    refine (Submodule.mem_torsion_iff _).mpr
      ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    show (n : ℤ) • P.periodLattice.mkQ s = 0
    rw [natCast_zsmul]
    exact ht
  exact ⟨⟨s, hs⟩, rfl⟩
