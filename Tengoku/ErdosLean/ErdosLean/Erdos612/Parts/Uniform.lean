import Tengoku.ErdosLean.ErdosLean.Erdos612.Statement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Erdős 612, part: the uniform reading implies the weak reading

The uniform constant works for every fixed `d`: a graph with `minDegree = d`, `2 ≤ d`,
`m ∣ d` satisfies the hypotheses of `DiamBoundUniform`.
-/

namespace Erdos612

/--
@isnad1 id=diamboun.1h3v.s3.e9fad0bd1d99 from=translated src=- shape=da6bb30e vocab=8153d1bc
-/
theorem diamBound_of_uniform {s m : ℕ} {c : ℝ} (h : DiamBoundUniform s m c) :
    DiamBound s m c := by
  obtain ⟨C, hC⟩ := h
  intro d hd hm
  refine ⟨C, fun n G _ hconn hcf hmin => ?_⟩
  have := hC n G hconn hcf (hmin ▸ hd) (hmin ▸ hm)
  rwa [hmin] at this

end Erdos612
