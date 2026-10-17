import Tengoku.NavierStokesEuler.Euler.AngleMeanZeroPrimitive

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Bounded linear maps commute with the literal normalized angular integral. -/

noncomputable section

namespace EulerAngleMeanZeroPrimitive

open MeasureTheory ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/--
@isnad1 id=eq.1h5v.s8.0c1eeee7f478 from=translated src=- shape=a45ea08d vocab=af28cfc0
-/
theorem rawPrimitive_map (L : E →L[ℝ] F) (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    L (rawPrimitive f θ) = rawPrimitive (fun s => L (f s)) θ :=
  (L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 θ)).symm

/--
@isnad1 id=eq.1h6v.s8.c28f333932ad from=translated src=- shape=ed7df6fb vocab=c8b14ae1
-/
theorem primitive_map (L : E →L[ℝ] F) (P : ℝ) (f : ℝ → E) (hf : Continuous f) (θ : ℝ) :
    L (primitive P f θ) = primitive P (fun s => L (f s)) θ := by
  unfold primitive
  rw [map_sub,map_smul,← L.intervalIntegral_comp_comm
    ((rawPrimitive_continuous f hf).intervalIntegrable 0 P),rawPrimitive_map L f hf θ]
  simp only [rawPrimitive_map L f hf]

end EulerAngleMeanZeroPrimitive
