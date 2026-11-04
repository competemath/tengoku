import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Analysis.Calculus.ImplicitContDiff
import Tengoku.Seed.Topology.Covering.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Compact regular root loci project as covering spaces. This supplies the
topological covering step independently of its degree and orientation. -/

open Set
open scoped Topology
namespace DuistermaatVanDerKallen
noncomputable section

section Slice
variable {E : Type*} [TopologicalSpace E]
variable (P : E × ℂ → ℂ) (B : Set E) (ε : ℝ)

/-- Roots over a prescribed compact base, inside a closed coordinate disc.-/
abbrev CompactRootSpace := {q : E × ℂ // q.1 ∈ B ∧ ‖q.2‖ ≤ ε ∧ P q = 0}

def compactRootProjection (q : CompactRootSpace P B ε) : B := ⟨q.val.1, q.property.1⟩

variable (e : OpenPartialHomeomorph (E × ℂ) (ℂ × E))
variable (heq : ∀ q, e q = (P q, q.1))
variable (hdisc : ∀ q ∈ e.source, ‖q.2‖ ≤ ε)
variable (z : CompactRootSpace P B ε)

def compactRootChartInverse (b : B) : CompactRootSpace P B ε := by
  classical
  exact if hb : (0, b.val) ∈ e.target then
    ⟨e.symm (0, b.val), by
      have he := e.right_inv hb
      rw [heq] at he
      refine ⟨?_, hdisc _ (e.map_target hb), congrArg Prod.fst he⟩
      rw [show (e.symm (0, b.val)).1 = b.val from congrArg Prod.snd he]
      exact b.property⟩
  else z

/--
@isnad1 id=eq.3h7v.s9.cf3621c19e83 from=translated src=- shape=b1cdc76f vocab=20a81fdc
-/
theorem compactRootChartInverse_val {b : B} (hb : (0, b.val) ∈ e.target) :
    (compactRootChartInverse P B ε e heq hdisc z b).val = e.symm (0, b.val) := by
  simp only [compactRootChartInverse, dite_eq_left hb]

def compactRootChart : OpenPartialHomeomorph (CompactRootSpace P B ε) B where
  toFun := compactRootProjection P B ε
  invFun := compactRootChartInverse P B ε e heq hdisc z
  source := {q | q.val ∈ e.source}
  target := {b | (0, b.val) ∈ e.target}
  map_source' := by
    intro q hq
    have he : e q.val = (0, q.val.1) := by rw [heq, q.property.2.2]
    change (0, q.val.1) ∈ e.target
    rw [← he]
    exact e.map_source hq
  map_target' := by
    intro b hb
    change (compactRootChartInverse P B ε e heq hdisc z b).val ∈ e.source
    rw [compactRootChartInverse_val P B ε e heq hdisc z hb]
    exact e.map_target hb
  left_inv' := by
    intro q hq
    have he : e q.val = (0, q.val.1) := by rw [heq, q.property.2.2]
    have hb : (0, (compactRootProjection P B ε q).val) ∈ e.target := he ▸ e.map_source hq
    apply Subtype.ext
    rw [compactRootChartInverse_val P B ε e heq hdisc z hb]
    change e.symm (0, q.val.1) = q.val
    rw [← he, e.left_inv hq]
  right_inv' := by
    intro b hb
    apply Subtype.ext
    change (compactRootChartInverse P B ε e heq hdisc z b).val.1 = b.val
    rw [compactRootChartInverse_val P B ε e heq hdisc z hb]
    have he := e.right_inv hb
    rw [heq] at he
    exact congrArg Prod.snd he
  open_source := e.open_source.preimage continuous_subtype_val
  open_target := e.open_target.preimage (continuous_const.prodMk continuous_subtype_val)
  continuousOn_toFun := (continuous_subtype_val.fst.subtype_mk _).continuousOn
  continuousOn_invFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun b : {b : B | (0, b.val) ∈ e.target} =>
        e.symm (0, b.val.val)) :=
      e.symm.continuousOn.comp_continuous
        (continuous_const.prodMk (continuous_subtype_val.comp continuous_subtype_val))
        (fun b => b.property)
    have hv : Continuous (fun b : {b : B | (0, b.val) ∈ e.target} =>
        (compactRootChartInverse P B ε e heq hdisc z b.val).val) := by
      convert hc using 1
      funext b
      exact compactRootChartInverse_val P B ε e heq hdisc z b.property
    exact hv.subtype_mk _

end Slice

section Covering
variable {E : Type*} [NormedAddCommGroup E]
variable (P : E × ℂ → ℂ) (B : Set E) (ε : ℝ)

/-- Compactness uses the closed disc, before boundary exclusion is applied.
@isnad1 id=compacts.2h4v.s7.e417de01a751 from=translated src=- shape=ca555391 vocab=9bb3a7ee
-/
theorem compactSpace_compactRootSpace (hB : IsCompact B) (hP : Continuous P) :
    CompactSpace (CompactRootSpace P B ε) := by
  change CompactSpace ↥({q : E × ℂ | q.1 ∈ B ∧ ‖q.2‖ ≤ ε ∧ P q = 0})
  apply isCompact_iff_compactSpace.mp
  have h := (hB.prod (isCompact_closedBall (0 : ℂ) ε)).inter_right
    (isClosed_eq hP (continuous_const (y := (0 : ℂ))))
  have heq : {q : E × ℂ | q.1 ∈ B ∧ ‖q.2‖ ≤ ε ∧ P q = 0} =
      B ×ˢ Metric.closedBall (0 : ℂ) ε ∩ {q | P q = 0} := by
    ext q
    simp [Metric.mem_closedBall, dist_zero_right, and_assoc]
  rw [heq]
  exact h

variable [NormedSpace ℂ E] [CompleteSpace E]

/-- A regular root strictly inside the disc has a chart whose map is precisely
projection onto the prescribed base subset.
@isnad1 id=ex.3h5v.s10.908eedb42701 from=translated src=- shape=a0d261af vocab=b407b214
-/
theorem exists_compactRootChart (z : CompactRootSpace P B ε)
    (hz : ‖z.val.2‖ < ε) (hP : ContDiffAt ℂ 1 P z.val)
    (hinv : (fderiv ℂ P z.val ∘L .inr ℂ E ℂ).IsInvertible) :
    ∃ e : OpenPartialHomeomorph (CompactRootSpace P B ε) B,
      z ∈ e.source ∧ (e : CompactRootSpace P B ε → B) = compactRootProjection P B ε := by
  let φ := (hP.hasStrictFDerivAt (by decide)).implicitFunctionDataOfProdDomain hinv
  let e₀ := φ.toOpenPartialHomeomorph
  have heq₀ (q : E × ℂ) : e₀ q = (P q, q.1) := rfl
  let e := e₀.restrOpen {q : E × ℂ | ‖q.2‖ < ε}
    (isOpen_lt continuous_snd.norm continuous_const)
  have heq (q : E × ℂ) : e q = (P q, q.1) := heq₀ q
  have hdisc (q : E × ℂ) (hq : q ∈ e.source) : ‖q.2‖ ≤ ε := hq.2.le
  refine ⟨compactRootChart P B ε e heq hdisc z, ?_, rfl⟩
  exact ⟨φ.pt_mem_toOpenPartialHomeomorph_source, hz⟩

/-- The compact root projection is a covering map when all roots are interior
and regular in the selected coordinate. Its degree is not asserted here.
@isnad1 id=iscoveri.3h4v.s9.cb37c0a71c1c from=translated src=- shape=b661a823 vocab=73ab14cd
-/
theorem isCoveringMap_compactRootProjection (hB : IsCompact B) (hP : Continuous P)
    (hreg : ∀ z : CompactRootSpace P B ε, ‖z.val.2‖ < ε ∧
      ContDiffAt ℂ 1 P z.val ∧ (fderiv ℂ P z.val ∘L .inr ℂ E ℂ).IsInvertible) :
    IsCoveringMap (compactRootProjection P B ε) := by
  let := compactSpace_compactRootSpace P B ε hB hP
  have hc : Continuous (compactRootProjection P B ε) :=
    continuous_subtype_val.fst.subtype_mk _
  intro b
  apply IsEvenlyCovered.of_openPartialHomeomorph hc
  intro z _
  obtain ⟨hz, hd, hi⟩ := hreg z
  exact exists_compactRootChart P B ε z hz hd hi

end Covering

end
end DuistermaatVanDerKallen
