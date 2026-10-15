module

public import Tengoku

open scoped NNReal ENNReal

public section

namespace Metric
variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] {f : X → Y} {s C P : Set X}
  {t C' : Set Y} {K ε : ℝ≥0} {n : ℕ∞}

-- TODO: replace
/--
@isnad1 id=issepara.0h2v.s4.428f5de90d1e from=translated src=- shape=1fc3748b vocab=f5fb4a26
-/
protected alias IsSeparated.zero := isSeparated_zero

lemma _root_.AntilipschitzWith.injOn (hf : AntilipschitzWith K f) (hs : IsSeparated ε s) :
    s.InjOn f := fun x hx y hy hxy ↦ hs.eq hx hy <| by grw [hf _]; simp [hxy]

/--
@isnad1 id=issepara.2h6v.s5.77b60a645f30 from=translated src=- shape=ad7aed71 vocab=52dffb7f
-/
lemma IsSeparated.image_of_antilipschitzWith (hf : AntilipschitzWith K f)
    (hs : IsSeparated (K * ε) s) : IsSeparated ε (f '' s) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  refine lt_of_mul_lt_mul_left' (a := (K : ℝ≥0∞)) ?_
  grw [← hf _]
  exact hs hx hy (ne_of_apply_ne _ hxy)

end Metric
