import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MazurAdmissible_GaloisModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MazurAdmissible_natCard_eq_pow_filtLength.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
local notation α "^+" M:51 => FixedPoints.addSubgroup M α

namespace P2MW.S_MazurAdmissible_natCard_eq_pow_filtLength

set_option autoImplicit false

noncomputable section

open MazurAdmissible

/--
@isnad1 id=eq.1h4v.s5.9977c5ef3dce from=translated src=- shape=f0cb2074 vocab=04bac093
-/
theorem solution
    {M : Type*} [AddCommGroup M] {q : ℕ} (hq : q.Prime) {Φ : OpenAction M}
    (c : AdmissibleChain q Φ) : Nat.card M = q ^ filtLength c := by
  have h : ∀ i : Fin (c.n + 1), Nat.card (c.step i) = q ^ (i : ℕ) := by
    intro i
    induction i using Fin.induction with
    | zero => rw [c.hbot]; simp
    | succ i ih =>
      have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        ((c.step i.castSucc).addSubgroupOf (c.step i.succ))
      rw [c.hcard i, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (c.hmono i)).toEquiv, ih] at hmul
      rw [hmul, Fin.val_succ, pow_succ, mul_comm, Fin.val_castSucc]
  have htop := h (Fin.last c.n)
  rw [c.htop, AddSubgroup.card_top, Fin.val_last] at htop
  exact htop
