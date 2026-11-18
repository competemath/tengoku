import Tengoku.FltAnthropic.Definitions.Def_ModularForm_AtkinLehnerDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_AtkinLehnerDatum_not_dvd_R_of_prime

set_option autoImplicit false

/--
@isnad1 id=not.1h3v.s4.3f56772aee5a from=translated src=- shape=ac26aedd vocab=937d1fd1
-/
theorem solution {M q : ℕ} (W : ModularForm.AtkinLehnerDatum M q) (hq : q.Prime) :
    ¬ q ∣ W.R := by
  intro ⟨c, hc⟩
  have h1 : (q : ℤ) ∣ 1 := ⟨W.a - (c : ℤ) * W.b, by
    have hb := W.bezout; rw [hc] at hb; push_cast at hb; linarith⟩
  have hq1 : q = 1 := by
    have := Int.isUnit_iff.mp (isUnit_of_dvd_one h1)
    omega
  exact absurd hq1 hq.one_lt.ne'
