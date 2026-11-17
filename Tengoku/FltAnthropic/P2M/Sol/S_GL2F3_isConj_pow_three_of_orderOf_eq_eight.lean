import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GL2F3_isConj_pow_three_of_orderOf_eq_eight.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GL2F3_isConj_pow_three_of_orderOf_eq_eight
set_option autoImplicit false

namespace FltWs24
namespace GL2F3
abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
def X (M : M2) : M2 := !![0, M 0 1; -M 1 0, 0]

set_option maxHeartbeats 32000000 in
set_option maxRecDepth 20000 in
/--
@isnad1 id=and.0h4v.s12.19f5a1d14d0f from=translated src=- shape=e9e520d9 vocab=8d2a113d
-/
theorem key (a b c d : ZMod 3) :
    ((!![a, b; c, d] : M2) ^ 4 = -1 →
      X !![a, b; c, d] * !![a, b; c, d] = !![a, b; c, d] ^ 3 * X !![a, b; c, d] ∧
      (X !![a, b; c, d]).det ≠ 0 ∧ Matrix.trace (!![a, b; c, d] : M2) ≠ 0) ∧
    ((!![a, b; c, d] : M2) ^ 8 = 1 → (!![a, b; c, d] : M2) ^ 4 ≠ 1 → (!![a, b; c, d] : M2) ^ 4 = -1) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide

open Matrix in
/--
@isnad1 id=eq.1h1v.s9.fe0730ce473b from=translated src=- shape=295eb129 vocab=1e261cf4
-/
theorem coe_pow_four_eq_neg_one (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    ((g : M2)) ^ 4 = -1 := by
  have h8 : (g : M2) ^ 8 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hg, pow_orderOf_eq_one, Units.val_one]
  have h4 : (g : M2) ^ 4 ≠ 1 := by
    intro h
    have : g ^ 4 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
    exact absurd this (pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hg]; norm_num))
  have e : (g : M2) = !![(g : M2) 0 0, (g : M2) 0 1; (g : M2) 1 0, (g : M2) 1 1] := Matrix.eta_fin_two _
  rw [e] at h8 h4 ⊢
  exact (key _ _ _ _).2 h8 h4

/--
@isnad1 id=isconj.1h1v.s9.a33b5c5f222a from=translated src=- shape=bdfd3964 vocab=38e953b7
-/
theorem isConj_pow_three_of_orderOf_eq_eight (g : GL (Fin 2) (ZMod 3)) (hg : orderOf g = 8) :
    IsConj g (g ^ 3) := by
  have h4 := coe_pow_four_eq_neg_one g hg
  have e : (g : M2) = !![(g : M2) 0 0, (g : M2) 0 1; (g : M2) 1 0, (g : M2) 1 1] := Matrix.eta_fin_two _
  have hk := (key ((g : M2) 0 0) ((g : M2) 0 1) ((g : M2) 1 0) ((g : M2) 1 1)).1 (by rw [← e]; exact h4)
  rw [← e] at hk
  obtain ⟨hXM, hdet, -⟩ := hk

  let c : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mkOfDetNeZero (X (g : M2)) hdet
  refine isConj_iff.mpr ⟨c, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Units.ext
  show X (g : M2) * (g : M2) = ((g ^ 3 : GL (Fin 2) (ZMod 3)) : M2) * X (g : M2)
  rw [Units.val_pow_eq_pow_val]
  exact hXM

end FltWs24.GL2F3

/--
@isnad1 id=isconj.1h1v.s9.a33b5c5f222a from=translated src=- shape=bdfd3964 vocab=38e953b7
-/
theorem solution (g : GL (Fin 2) (ZMod 3))
    (hg : orderOf g = 8) : IsConj g (g ^ 3) :=
  FltWs24.GL2F3.isConj_pow_three_of_orderOf_eq_eight g hg
