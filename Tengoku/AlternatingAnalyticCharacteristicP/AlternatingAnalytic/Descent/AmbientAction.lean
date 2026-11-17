import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Basic
import Tengoku.Seed.Analysis.Calculus.ContDiff.CPolynomial
import Tengoku.Seed.Analysis.Analytic.CPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ambient joint action on multilinear maps

For `f : E →L[K] E'` and `g : F →L[K] F'` the joint action sends a continuous multilinear map
`m` on `E'` to `g ∘ m ∘ (f, …, f)` on `E`. The action `(f, g) ↦ (m ↦ g ∘ m ∘ (f, …, f))` is the
diagonal of a bounded `(k + 1)`-linear map, hence continuously polynomial and `C^ω`; its
restriction to alternating inputs is analytic, with alternating values in a closed set. This is
Proposition 2.2.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace AlternatingAnalytic

variable {K : Type*} [NontriviallyNormedField K]
  {E E' F F' : Type*}
  [NormedAddCommGroup E] [NormedSpace K E] [NormedAddCommGroup E'] [NormedSpace K E']
  [NormedAddCommGroup F] [NormedSpace K F] [NormedAddCommGroup F'] [NormedSpace K F']

/-- The joint action `(f, g) ↦ (m ↦ g ∘ m ∘ (f, …, f))` on continuous multilinear maps.-/
def ambientMultilinearAction (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F' :=
  (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E) F F' v.2).comp
    (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k => v.1))

/-- The bounded `(k + 1)`-linear representative of the joint action on multilinear maps.-/
def ambientMultilinearActionRep (k : ℕ) :
    ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F'))
      (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
        ContinuousMultilinearMap K (fun _ : Fin k => E) F') := by
  let post : ((E →L[K] E') × (F →L[K] F')) →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F' :=
    (ContinuousLinearMap.compContinuousMultilinearMapL K (fun _ : Fin k => E) F F').comp
      (ContinuousLinearMap.snd K _ _)
  let postOp := (ContinuousLinearMap.compL K (ContinuousMultilinearMap K (fun _ : Fin k => E') F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E) F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E) F')).comp post
  let curried : ContinuousMultilinearMap K
      (fun _ : Fin k => (E →L[K] E') × (F →L[K] F'))
      (((E →L[K] E') × (F →L[K] F')) →L[K]
        (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
          ContinuousMultilinearMap K (fun _ : Fin k => E) F')) :=
    postOp.flip.compContinuousMultilinearMap
      ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear K
        (fun _ : Fin k => E) (fun _ : Fin k => E') F).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.fst K (E →L[K] E') (F →L[K] F')))
  exact ContinuousMultilinearMap.uncurryRight
    (𝕜 := K) (G := ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F')
    (Ei := fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F')) curried

/-- The representative evaluates to `g_k ∘ m ∘ (f_0, …, f_{k-1})`.
@isnad1 id=eq.0h9v.s13.107c269d0e8e from=translated src=- shape=1fc72588 vocab=070e31e7
-/
theorem ambientMultilinearActionRep_apply (k : ℕ)
    (h : Fin (k + 1) → (E →L[K] E') × (F →L[K] F'))
    (m : ContinuousMultilinearMap K (fun _ : Fin k => E') F) (x : Fin k → E) :
    ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x =
      (h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i)) :=
  rfl

/-- The diagonal of the representative is the joint action.
@isnad1 id=eq.0h7v.s13.933edeaeaca1 from=translated src=- shape=d841e616 vocab=d0b68b1f
-/
theorem ambientMultilinearActionRep_diag (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F') k (fun _ => v) =
      ambientMultilinearAction k v := by
  ext m x
  rfl

/-- The joint action on multilinear maps is the diagonal of a bounded `(k + 1)`-linear map.
@isnad1 id=ex.0h6v.s14.73aecf6f5e62 from=translated src=- shape=de169bfc vocab=c7ecb2d3
-/
theorem exists_ambientMultilinearAction_rep (k : ℕ) :
    ∃ H : ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F'))
        (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
          ContinuousMultilinearMap K (fun _ : Fin k => E) F'),
      ∀ v, H (fun _ => v) = ambientMultilinearAction k v :=
  ⟨ambientMultilinearActionRep k, ambientMultilinearActionRep_diag k⟩

/-- The joint action on multilinear maps is continuously polynomial at every point.
@isnad1 id=cpolynom.0h7v.s11.7330c185fc25 from=translated src=- shape=572b27f6 vocab=4937aa45
-/
theorem cpolynomialAt_ambientMultilinearAction (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    CPolynomialAt K (ambientMultilinearAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k)
      v := by
  let diagonal : ((E →L[K] E') × (F →L[K] F')) →L[K]
      (Fin (k + 1) → (E →L[K] E') × (F →L[K] F')) :=
    ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id K _
  have h := (ContinuousMultilinearMap.cpolynomialAt (𝕜 := K)
    (F := ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F')
    (f := ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F')
      k)).comp (diagonal.cpolynomialAt v)
  have e : (ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F') k ∘
      diagonal) = ambientMultilinearAction k := by
    funext w
    exact ambientMultilinearActionRep_diag k w
  rwa [e] at h

/-- The joint action on multilinear maps is `C^ω`.
@isnad1 id=contdiff.0h6v.s11.a001e1e6be8d from=translated src=- shape=4c41c803 vocab=64aeccd5
-/
theorem contDiff_ambientMultilinearAction (k : ℕ) :
    ContDiff K ω (ambientMultilinearAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) :=
  contDiff_iff_contDiffAt.mpr fun v => (cpolynomialAt_ambientMultilinearAction k v).contDiffAt

/-- The restriction of the joint action to alternating inputs is analytic everywhere.
@isnad1 id=analytic.0h6v.s11.44209ed10f56 from=translated src=- shape=c4677b3e vocab=8a90eee8
-/
theorem analyticOnNhd_ambientMultilinearAction_comp (k : ℕ) :
    AnalyticOnNhd K
      (fun v : (E →L[K] E') × (F →L[K] F') =>
        (ambientMultilinearAction k v).comp
          (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K :
            (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E') F))
      Set.univ := by
  intro v _
  let restrict : (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F') →L[K]
      ((E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E) F') :=
    (ContinuousLinearMap.compL K (E' [⋀^Fin k]→L[K] F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E') F)
    (ContinuousMultilinearMap K (fun _ : Fin k => E) F')).flip
      (ContinuousAlternatingMap.toContinuousMultilinearMapCLM K)
  exact (ContinuousLinearMap.analyticAt (𝕜 := K)
    (E := ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
      ContinuousMultilinearMap K (fun _ : Fin k => E) F')
    (F := (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E) F')
    restrict _).comp (cpolynomialAt_ambientMultilinearAction k v).analyticAt

/-- The joint action sends alternating maps to alternating maps.
@isnad1 id=ex.0h8v.s11.c73aaf5467b2 from=translated src=- shape=f7ebc83c vocab=7f6b8699
-/
theorem ambientMultilinearAction_alternating (k : ℕ) (v : (E →L[K] E') × (F →L[K] F'))
    (m : E' [⋀^Fin k]→L[K] F) :
    ∃ m' : E [⋀^Fin k]→L[K] F',
      m'.toContinuousMultilinearMap = ambientMultilinearAction k v m.toContinuousMultilinearMap :=
  ⟨v.2.compContinuousAlternatingMap (m.compContinuousLinearMap v.1), by ext x; rfl⟩

/-- Operators on alternating maps with alternating values form a closed set.
@isnad1 id=isclosed.0h6v.s12.5d786f9dc6d8 from=translated src=- shape=36cfeff6 vocab=56c59e1b
-/
theorem isClosed_setOf_forall_mem_range_toContinuousMultilinearMap (k : ℕ) :
    IsClosed {T : (E' [⋀^Fin k]→L[K] F) →L[K] ContinuousMultilinearMap K (fun _ : Fin k => E) F' |
      ∀ m, T m ∈ Set.range
        (ContinuousAlternatingMap.toContinuousMultilinearMap :
          (E [⋀^Fin k]→L[K] F') → ContinuousMultilinearMap K (fun _ : Fin k => E) F')} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun m =>
    ContinuousAlternatingMap.isClosed_range_toContinuousMultilinearMap.preimage
      (continuous_eval_const m)

end AlternatingAnalytic
