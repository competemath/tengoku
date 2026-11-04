import Tengoku.EntropyConstrainedMissingMass.EntropyConstrainedMissingMass.CoefficientGeneratingFunctions
import Tengoku.Seed.Analysis.Calculus.Deriv.Mul
import Tengoku.Seed.Analysis.Calculus.Deriv.Add
import Tengoku.Seed.Analysis.Calculus.Deriv.Pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Coefficientwise differentiation of formal power series. Every resulting finite
coefficient identity is an ordinary real derivative statement. -/

set_option backward.isDefEq.respectTransparency false

namespace EntropyConstrainedMissingMass
noncomputable section
open PowerSeries

/-- A formal series of derivatives, defined by actual scalar derivatives of each coefficient.-/
def HasCoeffDerivAt (F : ℝ → PowerSeries ℝ) (D : PowerSeries ℝ) (a : ℝ) : Prop :=
  ∀ n : ℕ, HasDerivAt (fun r => coeff n (F r)) (coeff n D) a

namespace HasCoeffDerivAt
variable {F G : ℝ → PowerSeries ℝ} {D E : PowerSeries ℝ} {a : ℝ}

/--
@isnad1 id=hascoeff.0h2v.s4.cba354ea6b67 from=translated src=- shape=eaddce21 vocab=93ff46e1
-/
theorem const (F : PowerSeries ℝ) (a : ℝ) : HasCoeffDerivAt (fun _ => F) 0 a := by
  intro n
  simpa using hasDerivAt_const a (coeff n F)

/--
@isnad1 id=eq.2h4v.s4.b173943f89a4 from=translated src=- shape=4ca92697 vocab=5d95f6d9
-/
theorem unique (hD : HasCoeffDerivAt F D a) (hE : HasCoeffDerivAt F E a) : D = E := by
  apply PowerSeries.ext
  intro n
  exact (hD n).unique (hE n)

/--
@isnad1 id=hascoeff.2h5v.s6.b01113f57593 from=translated src=- shape=1abf636f vocab=e6389a18
-/
theorem add (hF : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a) :
    HasCoeffDerivAt (fun r => F r + G r) (D + E) a := by
  intro n
  simp only [map_add]
  exact (hF n).fun_add (hG n)

/--
@isnad1 id=hascoeff.2h5v.s6.390f83af9e6d from=translated src=- shape=1abf636f vocab=531177d3
-/
theorem sub (hF : HasCoeffDerivAt F D a) (hG : HasCoeffDerivAt G E a) :
    HasCoeffDerivAt (fun r => F r - G r) (D - E) a := by
  intro n
  simp only [map_sub]
  exact (hF n).fun_sub (hG n)

/--
@isnad1 id=hascoeff.2h4v.s5.62689a1afae0 from=translated src=- shape=57cf5ac4 vocab=c5894b23
-/
theorem congr_of_eventuallyEq (hF : HasCoeffDerivAt F D a)
    (hGF : G =ᶠ[nhds a] F) : HasCoeffDerivAt G D a := by
  intro n
  exact (hF n).congr_of_eventuallyEq (hGF.mono (fun _ h => congrArg (coeff n) h))

/-- A scalar coefficient can be differentiated inside the constant-series embedding.
@isnad1 id=hascoeff.1h3v.s6.0418a21992a5 from=translated src=- shape=065bbf3f vocab=58ea20cb
-/
theorem C {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d a) :
    HasCoeffDerivAt (fun r => PowerSeries.C (f r)) (PowerSeries.C d) a := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using hf
  · simpa [coeff_C, hn] using hasDerivAt_const a (0 : ℝ)

end HasCoeffDerivAt

/-- Every coefficient of the homogeneous generating series varies polynomially in its roots.
@isnad1 id=differen.0h1v.s7.8f73c0db0308 from=translated src=- shape=5896c694 vocab=7f15e586
-/
theorem differentiable_homogeneous3 (n : ℕ) :
    Differentiable ℝ (fun v : Fin 3 → ℝ => homogeneous3 (v 0) (v 1) (v 2) n) := by
  have h2 (n : ℕ) : Differentiable ℝ (fun v : Fin 3 → ℝ => homogeneous2 (v 0) (v 1) n) := by
    induction n with
    | zero => simp only [homogeneous2]; fun_prop
    | succ n ih =>
      simp only [homogeneous2]
      exact ((differentiable_apply 0).pow _).add ((differentiable_apply 1).mul ih)
  induction n with
  | zero => simp only [homogeneous3]; fun_prop
  | succ n ih =>
    simp only [homogeneous3]
    exact (h2 (n + 1)).add ((differentiable_apply 2).mul ih)

/-- A differentiable triple path induces actual derivatives for all generating coefficients.
@isnad1 id=ex.1h2v.s7.708c87a59f71 from=translated src=- shape=6da703f7 vocab=44b0bf00
-/
theorem exists_hasCoeffDerivAt_homogeneousSeries (q : ℝ → (Fin 3 → ℝ)) {a : ℝ}
    (hq : DifferentiableAt ℝ q a) :
    ∃ D, HasCoeffDerivAt (fun r => homogeneousSeries (q r 0) (q r 1) (q r 2)) D a := by
  refine ⟨mk (fun n => deriv (fun r => homogeneous3 (q r 0) (q r 1) (q r 2) n) a), ?_⟩
  intro n
  simp only [coeff_homogeneousSeries, coeff_mk]
  exact ((differentiable_homogeneous3 n).differentiableAt.comp a hq).hasDerivAt

end
end EntropyConstrainedMissingMass
