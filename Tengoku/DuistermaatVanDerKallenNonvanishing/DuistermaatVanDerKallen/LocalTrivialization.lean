import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.FiberDiffeomorph
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CriticalNeighborhood
import Tengoku.Seed.Analysis.Convex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Smooth local product trivializations constructed from the complete scalar
normalized-gradient transport, with the original Laurent evaluation as base. -/

open Set
open scoped Topology Manifold ContDiff

namespace DuistermaatVanDerKallen
noncomputable section

/-- A base set disjoint from the manuscript's two critical-value sets.-/
def GoodBase {d : ℕ} (f : MultiLaurent d) (D : Set ℂ) : Prop :=
  ∀ s ∈ D, s ∉
    ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f)

theorem GoodBase.segment {d : ℕ} {f : MultiLaurent d} {D : Set ℂ}
    (hD : GoodBase f D) (hc : Convex ℝ D) {s t : ℂ} (hs : s ∈ D) (ht : t ∈ D) :
    GoodSegment f s (t - s) := by
  intro u hu
  apply hD
  have h := hc.lineMap_mem hs ht hu
  simpa only [AffineMap.lineMap_apply_module', add_comm] using h

/-- Torus points lying over a specified base set.-/
def laurentTube {d : ℕ} (f : MultiLaurent d) (D : Set ℂ) : Set (Fin d → ℂ) :=
  {z | (∀ i, z i ≠ 0) ∧ laurentEval f z ∈ D}

theorem laurentTube_isOpen {d : ℕ} (f : MultiLaurent d) {D : Set ℂ}
    (hD : IsOpen D) : IsOpen (laurentTube f D) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hz' : ∀ᶠ y in 𝓝 z, ∀ i, y i ≠ 0 := by
    have ho : IsOpen {y : Fin d → ℂ | ∀ i, y i ≠ 0} := by
      simpa only [ofPred_forall, preimage_ofPred_eq] using
        (isOpen_iInter_of_finite (fun i : Fin d =>
          (isOpen_ne : IsOpen {a : ℂ | a ≠ 0}).preimage (continuous_apply i)))
    exact ho.mem_nhds hz.1
  have he := (laurentEval_contDiffAt f hz.1).continuousAt.preimage_mem_nhds (hD.mem_nhds hz.2)
  exact Filter.inter_mem hz' he

section ConvexTube
variable {d : ℕ} {f : MultiLaurent d} {D : Set ℂ} {b : ℂ}
variable (hD : GoodBase f D) (hc : Convex ℝ D) (hb : b ∈ D)

include hD hc hb in
theorem convexTransport_admissible (s : D) (z : LaurentFiber f b) :
    (s.val - b, z.val) ∈ admissibleSegmentParameters f := by
  refine ⟨z.property.1, ?_⟩
  change GoodSegment f (laurentEval f z.val) (s.val - b)
  rw [z.property.2]
  exact hD.segment hc hb s.property

include hD hc hb in
theorem convexTransportBack_admissible (y : laurentTube f D) :
    (b - laurentEval f y.val, y.val) ∈ admissibleSegmentParameters f :=
  ⟨y.property.1, hD.segment hc y.property.2 hb⟩

end ConvexTube

/-- An open torus preimage, carrying its usual open-submanifold structure.-/
def laurentTubeOpen {d : ℕ} (f : MultiLaurent d) (D : TopologicalSpace.Opens ℂ) :
    TopologicalSpace.Opens (Fin d → ℂ) :=
  ⟨laurentTube f D, laurentTube_isOpen f D.isOpen⟩

section SmoothTube
variable {d : ℕ} {f : MultiLaurent d} {D : TopologicalSpace.Opens ℂ} {b : ℂ}
variable (hD : GoodBase f D) (hc : Convex ℝ (D : Set ℂ)) (hb : b ∈ D)
variable [Fact (RegularLaurentValue f b)]

/-- Evaluation is smooth on the open tube.-/
theorem laurentTube_eval_contMDiff :
    ContMDiff (modelWithCornersSelf ℝ (Fin d → ℂ)) (modelWithCornersSelf ℝ ℂ) ∞
      (fun y : laurentTubeOpen f D => laurentEval f y.val) := by
  intro y
  exact contMDiffAt_subtype_iff.mpr
    (((laurentEval_contDiffAt f y.property.1).of_le le_top).contMDiffAt)

end SmoothTube

/-- A good base consists of regular values.-/
theorem GoodBase.regularValue {d : ℕ} {f : MultiLaurent d} {D : Set ℂ}
    (hD : GoodBase f D) {b : ℂ} (hb : b ∈ D) : RegularLaurentValue f b :=
  regularLaurentValue_of_not_critical f (fun h => hD b hb (Or.inl h))

/-- Closedness follows from proper-radius compactness, independently of the
common-radius finiteness theorem, which remains a separate obligation.-/
theorem laurentCriticalValues_isClosed {d : ℕ} (f : MultiLaurent d) :
    IsClosed (ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
      asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
        (laurentDifferentialNorm f)) :=
  criticalValues_union_isClosed _ _ _ (laurentOnAffineTorus_continuous f)
    (laurentDifferentialNorm_continuous f) (fun _ => norm_nonneg _)
    (laurentDifferentialNorm_nonneg f) (affineTorus_sublevel_isCompact d)

/-- The actual complement of the two manuscript critical-value sets is open.-/
def laurentGoodValues {d : ℕ} (f : MultiLaurent d) : TopologicalSpace.Opens ℂ :=
  ⟨(ordinaryCriticalValues (laurentOnAffineTorus f) (laurentDifferentialNorm f) ∪
    asymptoticCriticalValues (laurentOnAffineTorus f) (fun x => ‖x.val‖)
      (laurentDifferentialNorm f))ᶜ, (laurentCriticalValues_isClosed f).isOpen_compl⟩

theorem laurentGoodValues_good {d : ℕ} (f : MultiLaurent d) : GoodBase f (laurentGoodValues f) :=
  fun _ h => h

end
end DuistermaatVanDerKallen
