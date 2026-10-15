import Tengoku.NavierStokesEuler.Euler.LinearDuhamel

/-!
# Naturality of the actual Duhamel solution

A bounded linear map intertwining the coefficient operators also intertwines
the actual forced solutions. This follows from their differential equations
and uniqueness; no compatibility of the chosen homogeneous fundamental maps
is assumed. In particular it applies to inclusions and support-changing
spatial translations.
-/

noncomputable section

namespace EulerLinearDuhamel.Evolution

open Set ContinuousLinearMap EulerVolterraConvolution

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {T : ℝ} {hT : 0 ≤ T}
  {B : C(Icc (0 : ℝ) T,E →L[ℝ] E)}
  {D : C(Icc (0 : ℝ) T,F →L[ℝ] F)}
  (U : Evolution T hT B) (V : Evolution T hT D)
  (L : E →L[ℝ] F)
  (hL : ∀ t u, D t (L u) = L (B t u))

include hL

/-- Bounded linear intertwiners commute with the actual forced solution.
@isnad1 id=eq.2h10v.s12.a3be55da3264 from=translated src=- shape=4075fc96 vocab=f1021f7b
-/
theorem solution_map (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    V.solution (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) (L a₀) =
      L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (U.solution f a₀) := by
  ext t
  symm
  apply V.solution_unique _ _ (fun s => L (U.solutionReal f a₀ s)) _ _ t
  · intro s
    have hd := (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := E) (F := F) L).comp_hasDerivWithinAt
      (s : ℝ) (U.solution_derivative f a₀ s)
    change HasDerivWithinAt (fun r => L (U.solutionReal f a₀ r))
      (D s (L (U.solutionReal f a₀ s)) + L (f s)) (Icc (0 : ℝ) T) s
    simp only [map_add, solution, ContinuousMap.coe_mk] at hd
    rw [hL]
    convert hd using 1
    rfl
  · change L (U.solution f a₀ ⟨0,le_rfl,hT⟩) = L a₀
    rw [U.solution_initial]

/-- Pointwise form of the same identity, including both endpoints.
@isnad1 id=eq.2h11v.s11.06b9f4c78173 from=translated src=- shape=2e31f295 vocab=f1021f7b
-/
theorem solution_map_apply (f : C(Icc (0 : ℝ) T,E)) (a₀ : E)
    (t : Icc (0 : ℝ) T) :
    V.solution (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) (L a₀) t =
      L (U.solution f a₀ t) := by
  exact congrArg (fun p : C(Icc (0 : ℝ) T,F) => p t) (U.solution_map V L hL f a₀)

end EulerLinearDuhamel.Evolution
