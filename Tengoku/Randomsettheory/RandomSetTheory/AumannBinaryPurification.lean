/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.AumannCaratheodoryImage
import Tengoku.Randomsettheory.RandomSetTheory.EffrosConvexHull
import Tengoku.Randomsettheory.RandomSetTheory.FiniteConvexificationDepth
import Tengoku.Randomsettheory.RandomSetTheory.WeightedPurification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Binary purification of Aumann expectations

For a compact nonempty Effros-measurable correspondence on a finite atomless
base, taking the pointwise convex join of each fibre with itself does not
change its Aumann expectation.  A measurable lifting writes every selection
of the join as a measurable weighted mixture of two selections of the
original fibre; weighted bang--bang purification then replaces that mixture
by a pointwise choice with the same vector integral.

This is the correspondence-level binary step needed to remove pointwise
convexification without postulating a separate purification axiom.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory Set TopologicalSpace

noncomputable section

namespace RandomSetTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- **Binary Aumann purification.**  On a finite atomless base, the Aumann
expectation of the pointwise self-convex-join equals that of the original
compact-valued correspondence.-/
theorem aumannExpectation_convexJoin_self_eq_of_atomless
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ) [FiniteDimensional ℝ E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    aumannExpectation μ (fun ω => convexJoin ℝ (S ω) (S ω)) =
      aumannExpectation μ S := by
  let P : Ω → Set ((E × E) × ℝ) := fun ω =>
    ((S ω ×ˢ S ω) ×ˢ Icc (0 : ℝ) 1)
  let φ : Ω × ((E × E) × ℝ) → E := fun q => convexJoinMap q.2
  have hSS : RandomSet.IsEffrosMeasurable (fun ω => S ω ×ˢ S ω) :=
    hS.prod hS (fun ω => (hcompact ω).isClosed)
      (fun ω => (hcompact ω).isClosed) hne hne
  have hP : RandomSet.IsEffrosMeasurable P := by
    exact hSS.prod
      (RandomSet.isEffrosMeasurable_const (Icc (0 : ℝ) 1))
      (fun ω => (hcompact ω).isClosed.prod (hcompact ω).isClosed)
      (fun _ => isClosed_Icc)
      (fun ω => (hne ω).prod (hne ω))
      (fun _ => nonempty_Icc.2 zero_le_one)
  have hPcompact : ∀ ω, IsCompact (P ω) := fun ω =>
    ((hcompact ω).prod (hcompact ω)).prod isCompact_Icc
  have hPne : ∀ ω, (P ω).Nonempty := fun ω =>
    ((hne ω).prod (hne ω)).prod (nonempty_Icc.2 zero_le_one)
  have hφmeas : Measurable φ := by
    exact continuous_convexJoinMap.measurable.comp measurable_snd
  have hφcont : ∀ ω, Continuous fun q => φ (ω, q) := fun _ =>
    continuous_convexJoinMap
  have hImage (ω : Ω) :
      (fun q => φ (ω, q)) '' P ω = convexJoin ℝ (S ω) (S ω) := by
    exact (convexJoin_eq_image (S ω) (S ω)).symm
  apply Set.Subset.antisymm
  · rintro z ⟨v, hv, rfl⟩
    let v' : Ω → E := hv.1.aestronglyMeasurable.mk v
    have hv'meas : Measurable v' :=
      hv.1.aestronglyMeasurable.measurable_mk
    have hvv' : v =ᵐ[μ] v' :=
      hv.1.aestronglyMeasurable.ae_eq_mk
    have hv'mem : ∀ᵐ ω ∂μ, v' ω ∈ (fun q => φ (ω, q)) '' P ω := by
      filter_upwards [hv.2, hvv'] with ω hvω heq
      rw [hImage]
      rwa [← heq]
    obtain ⟨T, hTmeas, hTmem, hφT⟩ :=
      exists_measurable_lifting_of_ae_mem_image
        hP hPcompact hPne hφmeas hφcont hv'meas hv'mem
    let x : Ω → E := fun ω => (T ω).1.1
    let y : Ω → E := fun ω => (T ω).1.2
    let a : Ω → ℝ := fun ω => (T ω).2
    have hxmeas : Measurable x := hTmeas.fst.fst
    have hymeas : Measurable y := hTmeas.fst.snd
    have hameas : Measurable a := hTmeas.snd
    have hxmem : ∀ ω, x ω ∈ S ω := fun ω => (hTmem ω).1.1
    have hymem : ∀ ω, y ω ∈ S ω := fun ω => (hTmem ω).1.2
    have ha0 : ∀ ω, 0 ≤ a ω := fun ω => (hTmem ω).2.1
    have ha1 : ∀ ω, a ω ≤ 1 := fun ω => (hTmem ω).2.2
    have hxint : Integrable x μ := by
      apply hg.mono' hxmeas.aestronglyMeasurable
      filter_upwards [] with ω
      exact hdom ω (x ω) (hxmem ω)
    have hyint : Integrable y μ := by
      apply hg.mono' hymeas.aestronglyMeasurable
      filter_upwards [] with ω
      exact hdom ω (y ω) (hymem ω)
    obtain ⟨q, hq, _hchoice, hqIntegral⟩ :=
      exists_binary_purification_of_integrableSelections_of_atomless
        μ hμ
        (S := S)
        (f := y) (g := x)
        ⟨hyint, Filter.Eventually.of_forall hymem⟩
        ⟨hxint, Filter.Eventually.of_forall hxmem⟩
        hameas (Filter.Eventually.of_forall ha0)
          (Filter.Eventually.of_forall ha1)
    refine ⟨q, hq, ?_⟩
    calc
      (∫ ω, q ω ∂μ) =
          ∫ ω, a ω • y ω + (1 - a ω) • x ω ∂μ := hqIntegral
      _ = ∫ ω, v ω ∂μ := by
        apply integral_congr_ae
        filter_upwards [hφT, hvv'] with ω hφTω hvv'ω
        calc
          a ω • y ω + (1 - a ω) • x ω = φ (ω, T ω) := by
            simp only [φ, convexJoinMap, AffineMap.lineMap_apply_module]
            abel
          _ = v' ω := hφTω
          _ = v ω := hvv'ω.symm
  · exact aumannExpectation_mono fun ω =>
      subset_convexJoin_left (hne ω)

/-- Every finite binary convexification stage has the same Aumann
expectation as the original correspondence.-/
theorem aumannExpectation_convexJoinIterate_eq_of_atomless
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ) [FiniteDimensional ℝ E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    ∀ n, aumannExpectation μ (fun ω => convexJoinIterate (S ω) n) =
      aumannExpectation μ S := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      let T : Ω → Set E := fun ω => convexJoinIterate (S ω) n
      have hT : RandomSet.IsEffrosMeasurable T :=
        effrosMeasurable_convexJoinIterate hS hcompact hne n
      have hTcompact : ∀ ω, IsCompact (T ω) := fun ω =>
        convexJoinIterate_compact (hcompact ω) n
      have hTne : ∀ ω, (T ω).Nonempty := fun ω =>
        convexJoinIterate_nonempty (hne ω) n
      have hTdom : ∀ ω, ∀ x ∈ T ω, ‖x‖ ≤ g ω := by
        intro ω x hx
        have hxball : x ∈ Metric.closedBall (0 : E) (g ω) :=
          convexJoinIterate_subset_convex
            (fun y hy => by
              simpa [Metric.mem_closedBall, dist_zero_right] using
                hdom ω y hy)
            (convex_closedBall (0 : E) (g ω)) n hx
        simpa [Metric.mem_closedBall, dist_zero_right] using hxball
      calc
        aumannExpectation μ (fun ω => convexJoinIterate (S ω) (n + 1)) =
            aumannExpectation μ (fun ω => convexJoin ℝ (T ω) (T ω)) := rfl
        _ = aumannExpectation μ T :=
          aumannExpectation_convexJoin_self_eq_of_atomless
            μ hμ hT hTcompact hTne hg hTdom
        _ = aumannExpectation μ S := ih

/-- **Finite-dimensional Aumann purification.**  On a finite atomless base,
pointwise closed convexification of a compact nonempty correspondence does
not change its Aumann expectation.  Carathéodory's theorem makes the
pointwise convexification finite (`finrank ℝ E + 1` binary stages), after
which `aumannExpectation_convexJoinIterate_eq_of_atomless` purifies each
stage.-/
theorem aumannExpectation_closedConvexHull_eq_of_atomless
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hμ : IsAtomlessMeasure μ) [FiniteDimensional ℝ E]
    {S : Ω → Set E} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    aumannExpectation μ (fun ω => closedConvexHull ℝ (S ω)) =
      aumannExpectation μ S := by
  have hfibers :
      (fun ω => closedConvexHull ℝ (S ω)) =
        fun ω => convexJoinIterate (S ω) (Module.finrank ℝ E + 1) := by
    funext ω
    exact
      (convexJoinIterate_finrank_add_one_eq_closedConvexHull
        (hcompact ω) (hne ω)).symm
  rw [hfibers]
  exact aumannExpectation_convexJoinIterate_eq_of_atomless
    μ hμ hS hcompact hne hg hdom (Module.finrank ℝ E + 1)

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
