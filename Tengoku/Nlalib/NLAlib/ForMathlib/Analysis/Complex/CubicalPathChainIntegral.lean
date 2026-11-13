import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.CubicalPathChain
import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.Complex.CubicalCauchy
import Tengoku.Nlalib.NLAlib.ForMathlib.MeasureTheory.CurveIntegralConcat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Native integration of finite cornered contour chains

Actual composable path pieces determine a cubical cycle when their endpoints
close. Its finite signed integral equals the native integral of their finite
concatenation. Smoothness is imposed on each piece, allowing corners and
stationary derivatives at every join.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Finset Set MeasureTheory
open scoped unitInterval
namespace Complex

/-- Forgetting domain-subtype endpoints does not change the extended native path.
@isnad1 id=eq.0h4v.s9.880f3b4e80f3 from=translated src=- shape=5e3290fe vocab=33f88825
-/
theorem cubicalPath_toContinuousMap_extend {Ω : Set ℂ} {a b : Ω} (γ : Path a b) :
    (cubicalPath γ.toContinuousMap).extend = (γ.map continuous_subtype_val).extend := by
  ext t
  rfl

/-- The actual native curve integral of a domain-valued path agrees with
its cubical-path spelling, independently of integrability.
@isnad1 id=eq.0h5v.s9.277f3c62bb52 from=translated src=- shape=144d4429 vocab=b5ad849b
-/
theorem curveIntegral_cubicalPath_toContinuousMap {Ω : Set ℂ} {a b : Ω}
    (γ : Path a b) (ω : ℂ → ℂ →L[ℂ] ℂ) :
    curveIntegral ω (cubicalPath γ.toContinuousMap) =
      curveIntegral ω (γ.map continuous_subtype_val) := by
  simp only [curveIntegral_def, curveIntegralFun_def, cubicalPath_toContinuousMap_extend]

/-- Piecewise C1 regularity of the actual pieces gives the regularity needed
by all finite-chain contour theorems, without claiming smoothness at joins.
@isnad1 id=contdiff.2h5v.s10.5b1f78116689 from=translated src=- shape=c64f8e8d vocab=116e48b9
-/
theorem contDiffOn_cubicalPath_of_mem_support_pathChain {Ω : Set ℂ} {n : ℕ}
    (p : Fin (n + 1) → Ω) (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I)
    (q : C(I, Ω)) (hq : q ∈ (Cubical.pathChain p γ).support) :
    ContDiffOn ℝ 1 (cubicalPath q).extend I := by
  obtain ⟨i, rfl⟩ := Cubical.exists_piece_of_mem_support_pathChain p γ hq
  rw [cubicalPath_toContinuousMap_extend]
  exact hγ i

/-- The cubical chain integral equals the actual native integral of the
finite cornered concatenation, including the empty family.
@isnad1 id=eq.1h5v.s10.5b81a01067b5 from=translated src=- shape=82521401 vocab=401f8302
-/
theorem cubicalCurveIntegral_pathChain_eq_curveIntegral_concat {Ω : Set ℂ} {n : ℕ}
    (p : Fin (n + 1) → Ω) (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    (g : ℂ → ℂ)
    (hγ : ∀ i, CurveIntegrable (fun z => g z • ContinuousLinearMap.id ℂ ℂ)
      ((γ i).map continuous_subtype_val)) :
    cubicalCurveIntegral g (Cubical.pathChain p γ) =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ)
        ((Path.concat p γ).map continuous_subtype_val) := by
  rw [Path.map_concat, curveIntegral_concat _ _ hγ]
  simp only [Cubical.pathChain, map_sum, cubicalCurveIntegral,
    Finsupp.linearCombination_single, one_smul, curveIntegral_cubicalPath_toContinuousMap]

/-- Continuous scalar forms on the domain are actually integrable on every
C1 piece, so the finite native concatenation identity needs no supplied
integrability or smoothness at its corners.
atlas: gauss-remainder-contour-kernel (partial)
@isnad1 id=eq.2h5v.s10.d23ccdb15f95 from=translated src=- shape=e32046ed vocab=5a2a8b8f
-/
theorem cubicalCurveIntegral_pathChain_eq_of_contDiffOn {Ω : Set ℂ} {n : ℕ}
    (p : Fin (n + 1) → Ω) (γ : (i : Fin n) → Path (p i.castSucc) (p i.succ))
    {g : ℂ → ℂ} (hg : ContinuousOn g Ω)
    (hγ : ∀ i, ContDiffOn ℝ 1 ((γ i).map continuous_subtype_val).extend I) :
    cubicalCurveIntegral g (Cubical.pathChain p γ) =
      curveIntegral (fun z => g z • ContinuousLinearMap.id ℂ ℂ)
        ((Path.concat p γ).map continuous_subtype_val) := by
  apply cubicalCurveIntegral_pathChain_eq_curveIntegral_concat
  intro i
  apply (hg.smul continuousOn_const).curveIntegrable_of_contDiffOn (hγ i)
  intro t
  exact ((γ i) t).property

end Complex
