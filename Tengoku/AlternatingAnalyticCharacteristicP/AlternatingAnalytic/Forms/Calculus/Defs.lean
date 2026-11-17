import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Module.Alternating.Uncurry.Fin
import Tengoku.Seed.LinearAlgebra.Alternating.DomCoprod
import Tengoku.Seed.Analysis.Calculus.FDeriv.Defs
import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Forms.Calculus.Shuffle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ambient analytic forms on an open subset of a normed space

Chart-level definitions for the ambient differential calculus of Theorem 7.2. A `k`-form on a
normed space `P` is a map `η : P → Alt^k(P; K)`; it is *ambient analytic* on `U` when `j ∘ η` is
analytic on `U`, where `j : Alt^k(P; K) → Mult^k(P; K)` forgets alternation. The wedge product is
`shuffle` on values, the exterior derivative is `alternatizeUncurryFin` applied to the derivative
(formula (7.1)), and the pullback along `h` is `(η ∘ h) ∘ (Dh, …, Dh)`. These are the definitions
used in `Challenges/Thm7_2.lean`.
-/

namespace AlternatingAnalytic.Forms

variable {K : Type*} [NontriviallyNormedField K]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  {P' : Type*} [NormedAddCommGroup P'] [NormedSpace K P']

/-- Ambient analyticity of a `k`-form `η` on `U`: `j ∘ η` is analytic on `U`, where
`j : Alt^k(P; K) → Mult^k(P; K)` is the inclusion.-/
def IsAmbientAnalyticOn {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) (U : Set P) : Prop :=
  AnalyticOnNhd K (fun y => (η y).toContinuousMultilinearMap) U

/-- The algebraic shuffle product of two scalar alternating maps.-/
noncomputable def wedgeAlg {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    P [⋀^Fin (k + l)]→ₗ[K] K :=
  ((LinearMap.mul' K K).compAlternatingMap
    (μ.toAlternatingMap.domCoprod ν.toAlternatingMap)).domDomCongr finSumFinEquiv

/-- The shuffle product of continuous alternating maps is continuous.
@isnad1 id=continuo.0h6v.s8.ea69af8c6346 from=translated src=- shape=83bc9f41 vocab=e09f5116
-/
theorem continuous_wedgeAlg {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    Continuous (wedgeAlg μ ν) := by
  have h : ⇑(wedgeAlg μ ν) = fun v => ∑ σ : Equiv.Perm.ModSumCongr (Fin k) (Fin l),
      LinearMap.mul' K K (AlternatingMap.domCoprod.summand μ.toAlternatingMap ν.toAlternatingMap σ
        (v ∘ finSumFinEquiv)) := by
    funext v
    simp [wedgeAlg, AlternatingMap.domCoprod_apply, map_sum, Function.comp_def]
  rw [h]
  refine continuous_finsetSum _ fun σ _ => ?_
  induction σ using Quotient.inductionOn' with
  | h σ =>
    simp only [AlternatingMap.domCoprod.summand_mk'', smul_apply,
      MultilinearMap.domDomCongr_apply, MultilinearMap.domCoprod_apply, map_zsmul_unit,
      LinearMap.mul'_apply, Function.comp_apply]
    simp only [Units.smul_def, zsmul_eq_mul]
    exact continuous_const.mul
      ((μ.cont.comp (continuous_pi fun i => continuous_apply _)).mul
        (ν.cont.comp (continuous_pi fun i => continuous_apply _)))

/-- The wedge (shuffle) product `μ ∧ ν ∈ Alt^{k+l}(P; K)`.-/
noncomputable def wedge {k l : ℕ} (μ : P [⋀^Fin k]→L[K] K) (ν : P [⋀^Fin l]→L[K] K) :
    P [⋀^Fin (k + l)]→L[K] K :=
  { wedgeAlg μ ν with cont := continuous_wedgeAlg μ ν }

/-- The exterior derivative, formula (7.1).-/
noncomputable def extDeriv {k : ℕ} (η : P → P [⋀^Fin k]→L[K] K) (y : P) :
    P [⋀^Fin (k + 1)]→L[K] K :=
  ContinuousAlternatingMap.alternatizeUncurryFin (fderiv K η y)

/-- Pullback `h^*η = (η ∘ h) ∘ (Dh, …, Dh)`.-/
noncomputable def pullback {k : ℕ} (h : P' → P) (η : P → P [⋀^Fin k]→L[K] K) (y : P') :
    P' [⋀^Fin k]→L[K] K :=
  (η (h y)).compContinuousLinearMap (fderiv K h y)

end AlternatingAnalytic.Forms
