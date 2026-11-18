import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalRing_PrincipalUnits
import Tengoku.FltAnthropic.Theorems.Thm_IsDiscreteValuationRing_relIndex_principalUnits_succ

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDiscreteValuationRing_relIndex_principalUnits_add.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDiscreteValuationRing_relIndex_principalUnits_add

set_option autoImplicit false
open IsLocalRing

open IsLocalRing in
/--
@isnad1 id=eq.1h3v.s6.521425d71a18 from=translated src=- shape=fd55c21c vocab=89325c6b
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (principalUnits R (k + n)).relIndex (principalUnits R k) = Nat.card (IsLocalRing.ResidueField R) ^ n := by
  induction n with
  | zero => rw [add_zero, pow_zero, Subgroup.relIndex_self]
  | succ n ih =>
    rw [pow_succ, ← ih, ← add_assoc,
      ← IsDiscreteValuationRing.relIndex_principalUnits_succ (R := R) (k := k + n) (by omega), mul_comm]
    exact (Subgroup.relIndex_mul_relIndex _ _ _
      (principalUnits_antitone (Nat.le_succ _)) (principalUnits_antitone (Nat.le_add_right k n))).symm
