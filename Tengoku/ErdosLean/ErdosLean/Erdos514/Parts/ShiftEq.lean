import Tengoku.ErdosLean.ErdosLean.Erdos514.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős #514 — Part: the Taylor-shift identity
`g z = g 0 + z * dslope g 0 z` (Mathlib `sub_smul_dslope`), valid for every function. -/

namespace Erdos514

/--
@isnad1 id=eq.0h3v.s5.51765bea3014 from=translated src=- shape=7481d789 vocab=929b02ec
-/
theorem shift_eq_add_mul (f : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    shift f n z = shift f n 0 + z * shift f (n + 1) z := by
  have h := sub_smul_dslope (shift f n) 0 z
  simp only [sub_zero, smul_eq_mul] at h
  rw [shift_succ, h]; ring

end Erdos514
