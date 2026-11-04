import Tengoku.ErdosLean.ErdosLean.Erdos514.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős #514 — Part: Taylor shifts of entire functions are entire
Induction on `n` with `Complex.differentiableOn_dslope` (removable singularity). -/

namespace Erdos514

/--
@isnad1 id=differen.1h2v.s7.cd06429171e7 from=translated src=- shape=78cb5312 vocab=dd31147b
-/
theorem shift_differentiable {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    Differentiable ℂ (shift f n) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [shift_succ, ← differentiableOn_univ,
      Complex.differentiableOn_dslope Filter.univ_mem]
    exact ih.differentiableOn

end Erdos514
