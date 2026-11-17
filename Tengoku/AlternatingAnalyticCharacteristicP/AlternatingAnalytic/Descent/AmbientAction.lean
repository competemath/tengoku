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

/-- The representative evaluates to `g_k ∘ m ∘ (f_0, …, f_{k-1})`.-/
theorem ambientMultilinearActionRep_apply (k : ℕ)
    (h : Fin (k + 1) → (E →L[K] E') × (F →L[K] F'))
    (m : ContinuousMultilinearMap K (fun _ : Fin k => E') F) (x : Fin k → E) :
    ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F') k h m x =
      (h (Fin.last k)).2 (m fun i => (h i.castSucc).1 (x i)) :=
  rfl

/-- The diagonal of the representative is the joint action.-/
theorem ambientMultilinearActionRep_diag (k : ℕ) (v : (E →L[K] E') × (F →L[K] F')) :
    ambientMultilinearActionRep (K := K) (E := E) (E' := E') (F := F) (F' := F') k (fun _ => v) =
      ambientMultilinearAction k v := by
  ext m x
  rfl

/-- The joint action on multilinear maps is the diagonal of a bounded `(k + 1)`-linear map.-/
theorem exists_ambientMultilinearAction_rep (k : ℕ) :
    ∃ H : ContinuousMultilinearMap K (fun _ : Fin (k + 1) => (E →L[K] E') × (F →L[K] F'))
        (ContinuousMultilinearMap K (fun _ : Fin k => E') F →L[K]
          ContinuousMultilinearMap K (fun _ : Fin k => E) F'),
      ∀ v, H (fun _ => v) = ambientMultilinearAction k v :=
  ⟨ambientMultilinearActionRep k, ambientMultilinearActionRep_diag k⟩

/-- The joint action on multilinear maps is continuously polynomial at every point.-/
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

/-- The joint action on multilinear maps is `C^ω`.-/
theorem contDiff_ambientMultilinearAction (k : ℕ) :
    ContDiff K ω (ambientMultilinearAction (K := K) (E := E) (E' := E') (F := F) (F' := F') k) :=
  contDiff_iff_contDiffAt.mpr fun v => (cpolynomialAt_ambientMultilinearAction k v).contDiffAt

/-- The restriction of the joint action to alternating inputs is analytic everywhere.-/
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

/-- The joint action sends alternating maps to alternating maps.-/
theorem ambientMultilinearAction_alternating (k : ℕ) (v : (E →L[K] E') × (F →L[K] F'))
    (m : E' [⋀^Fin k]→L[K] F) :
    ∃ m' : E [⋀^Fin k]→L[K] F',
      m'.toContinuousMultilinearMap = ambientMultilinearAction k v m.toContinuousMultilinearMap :=
  ⟨v.2.compContinuousAlternatingMap (m.compContinuousLinearMap v.1), by ext x; rfl⟩

/-- Operators on alternating maps with alternating values form a closed set.-/
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
