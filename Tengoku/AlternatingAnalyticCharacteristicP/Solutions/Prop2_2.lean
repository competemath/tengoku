import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.Analysis.Calculus.ContDiff.Defs
import Tengoku.Seed.Analysis.Analytic.Basic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Descent.AmbientAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Proposition 2.2

The four parts are `AlternatingAnalytic.exists_ambientMultilinearAction_rep`,
`contDiff_ambientMultilinearAction`, `analyticOnNhd_ambientMultilinearAction_comp` and
`ambientMultilinearAction_alternating` with
`isClosed_setOf_forall_mem_range_toContinuousMultilinearMap` (`Descent/AmbientAction.lean`).
-/

open scoped ContDiff

namespace AlternatingAnalyticChallenge.Prop2_2

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']

/-- The joint action `B(f, g)(m) = g ∘ m ∘ (f, …, f)` on continuous multilinear maps.-/
noncomputable def multilinearAction (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F' :=
  (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E) F F' v.2).comp
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => v.1))

/-- The joint action on multilinear maps is the diagonal of a
bounded `(k + 1)`-linear map.
@isnad1 id=ex.0h6v.s14.a352a4c2447d from=translated src=- shape=de169bfc vocab=dd8ba0d0
-/
theorem part1 (k : ℕ) :
    ∃ H : ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F'))
        (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
          ContinuousMultilinearMap K (fun _ : Fin k => E) F'),
      ∀ v, H (fun _ => v) = multilinearAction k v := by
  exact AlternatingAnalytic.exists_ambientMultilinearAction_rep k

/-- The joint action on multilinear maps is `C^ω`.
@isnad1 id=contdiff.0h6v.s11.6747142ff60c from=translated src=- shape=4c41c803 vocab=aa8b7a44
-/
theorem part2 (k : ℕ) :
    ContDiff K ω (multilinearAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) := by
  exact AlternatingAnalytic.contDiff_ambientMultilinearAction k

/-- The restriction of the joint action to alternating inputs is
analytic as a map into `L(Alt^k(E'; F), Mult^k(E; F'))`.
@isnad1 id=analytic.0h6v.s11.da02b29fe1c1 from=translated src=- shape=c4677b3e vocab=548166d9
-/
theorem part3 (k : ℕ) :
    AnalyticOnNhd K
      (fun v : (E →L[K] E') × (F →L[K] F') =>
        (multilinearAction k v).comp
          (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K :
            (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F))
      Set.univ := by
  exact AlternatingAnalytic.analyticOnNhd_ambientMultilinearAction_comp k

/-- Every value of the restricted action takes values in
`Alt^k(E; F')`, and the operators taking values in `Alt^k(E; F')` form a closed subset of
`L(Alt^k(E'; F), Mult^k(E; F'))`.
@isnad1 id=and.0h6v.s12.7329b64b9a31 from=translated src=- shape=7aed6baf vocab=214f2d34
-/
theorem part4 (k : ℕ) :
    (∀ (v : (E →L[K] E') × (F →L[K] F')) (m : E' [⋀^Fin k]→L[K] F),
      ∃ m' : E [⋀^Fin k]→L[K] F',
        m'.toContinuousMultilinearMap = multilinearAction k v m.toContinuousMultilinearMap) ∧
    IsClosed {T : (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E) F' |
      ∀ m, T m ∈ Set.range
        (ContinuousAlternatingMap.toContinuousMultilinearMap :
          (E [⋀^Fin k]→L[K] F') → ContinuousMultilinearMap K (fun _ : Fin k => E) F')} := by
  exact ⟨AlternatingAnalytic.ambientMultilinearAction_alternating k,
    AlternatingAnalytic.isClosed_setOf_forall_mem_range_toContinuousMultilinearMap k⟩

end AlternatingAnalyticChallenge.Prop2_2
