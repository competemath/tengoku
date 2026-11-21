/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku.Randomsettheory.RandomSetTheory.CastaingRepresentation
import Tengoku.Randomsettheory.RandomSetTheory.MeasurableSupport
import Tengoku.Randomsettheory.RandomSetTheory.AumannExpectation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Measurable approximate support selections

For a compact-valued Effros-measurable correspondence, a Castaing
representation contains points arbitrarily close to every support maximizer.
Choosing the first point within `ε` of the support value gives a measurable
`ε`-maximizing selection.  An integrable envelope makes it an integrable
selection, removing any separate approximate-selection hypothesis from
applications to the Aumann expectation.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open Set Metric MeasureTheory TopologicalSpace
open scoped InnerProductSpace

noncomputable section

namespace RandomSetTheory

/-- The `n`th Castaing selection is within `ε` of maximizing direction `u`.-/
def SupportDenseCandidate
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (S : Ω → Set H) (f : ℕ → Ω → H) (u : H) (ε : ℝ)
    (n : ℕ) (ω : Ω) : Prop :=
  supportFunction (S ω) u - ε < ⟪u, f n ω⟫_ℝ

theorem exists_supportDenseCandidate
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : Ω → Set H} (hcompact : ∀ ω, IsCompact (S ω))
    (hne : ∀ ω, (S ω).Nonempty)
    {f : ℕ → Ω → H}
    (hclosure : ∀ ω, closure (Set.range fun n => f n ω) = S ω)
    (u : H) {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    ∃ n, SupportDenseCandidate S f u ε n ω := by
  obtain ⟨x, hx, hxmax⟩ := supportFunction_attains (hcompact ω) (hne ω) u
  let U : Set H := {y | supportFunction (S ω) u - ε < ⟪u, y⟫_ℝ}
  have hUopen : IsOpen U := isOpen_lt continuous_const (by fun_prop)
  have hxU : x ∈ U := by
    dsimp [U]
    rw [hxmax]
    linarith
  have hxclosure : x ∈ closure (Set.range fun n => f n ω) := by
    rw [hclosure ω]
    exact hx
  obtain ⟨y, hyU, hyRange⟩ :=
    (_root_.mem_closure_iff.mp hxclosure) U hUopen hxU
  obtain ⟨n, rfl⟩ := hyRange
  exact ⟨n, hyU⟩

/-- Canonical first Castaing point whose support value is `ε`-optimal.-/
def supportApproximateSelection
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) (ε : ℝ) (hε : 0 < ε) (ω : Ω) : H := by
  classical
  let f : ℕ → Ω → H := castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne
  exact f (Nat.find (exists_supportDenseCandidate hcompact hne
    (closure_range_castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne)
    u hε ω)) ω

theorem measurable_supportApproximateSelection
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) {ε : ℝ} (hε : 0 < ε) :
    Measurable (supportApproximateSelection hS hcompact hne u ε hε) := by
  classical
  let f : ℕ → Ω → H := castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne
  have hf : ∀ n, Measurable (f n) :=
    castaingRepresentation_measurable hS (fun ω => (hcompact ω).isClosed) hne
  have hsupport : Measurable (fun ω => supportFunction (S ω) u) :=
    measurable_supportFunction hS hcompact hne u
  have hp : ∀ n, MeasurableSet {ω | SupportDenseCandidate S f u ε n ω} := by
    intro n
    exact measurableSet_lt (hsupport.sub measurable_const) ((hf n).const_inner)
  have hexists : ∀ ω, ∃ n, SupportDenseCandidate S f u ε n ω :=
    exists_supportDenseCandidate hcompact hne
      (closure_range_castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne)
      u hε
  exact Measurable.find hf hp hexists

theorem supportApproximateSelection_mem
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    supportApproximateSelection hS hcompact hne u ε hε ω ∈ S ω := by
  classical
  exact castaingRepresentation_mem hS (fun ω => (hcompact ω).isClosed) hne _ ω

theorem supportFunction_sub_lt_inner_supportApproximateSelection
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    (u : H) {ε : ℝ} (hε : 0 < ε) (ω : Ω) :
    supportFunction (S ω) u - ε <
      ⟪u, supportApproximateSelection hS hcompact hne u ε hε ω⟫_ℝ := by
  classical
  exact Nat.find_spec (exists_supportDenseCandidate hcompact hne
    (closure_range_castaingRepresentation hS (fun ω => (hcompact ω).isClosed) hne)
    u hε ω)

/-- Under an integrable envelope, the canonical approximate maximizer is an
integrable selection.-/
theorem integrableSelection_supportApproximateSelection_of_envelope
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (u : H) {ε : ℝ} (hε : 0 < ε) :
    IsIntegrableSelection μ S
      (supportApproximateSelection hS hcompact hne u ε hε) := by
  constructor
  · apply hg.mono'
      (measurable_supportApproximateSelection hS hcompact hne u hε).aestronglyMeasurable
    filter_upwards [] with ω
    exact hdom ω _ (supportApproximateSelection_mem hS hcompact hne u hε ω)
  · filter_upwards [] with ω
    exact supportApproximateSelection_mem hS hcompact hne u hε ω

/-- Existential, implementation-independent form of the measurable
integrable approximate support-selection theorem.-/
theorem exists_integrable_supportApproximation
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (u : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Ω → H, IsIntegrableSelection μ S f ∧
      ∀ ω, supportFunction (S ω) u - ε < ⟪u, f ω⟫_ℝ := by
  exact ⟨supportApproximateSelection hS hcompact hne u ε hε,
    integrableSelection_supportApproximateSelection_of_envelope
      hS hcompact hne hg hdom u hε,
    supportFunction_sub_lt_inner_supportApproximateSelection
      hS hcompact hne u hε⟩

/-- The integral of an `ε`-maximizing selection loses at most
`μ(Ω) ε` compared with the integrated pointwise support.-/
theorem inner_integral_supportApproximateSelection_lower_bound
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (u : H) {ε : ℝ} (hε : 0 < ε) :
    (∫ ω, supportFunction (S ω) u ∂μ) - μ.real Set.univ * ε ≤
      ⟪u, ∫ ω, supportApproximateSelection hS hcompact hne u ε hε ω ∂μ⟫_ℝ := by
  let f := supportApproximateSelection hS hcompact hne u ε hε
  have hf : IsIntegrableSelection μ S f :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS hcompact hne hg hdom u hε
  have hsupport : Integrable (fun ω => supportFunction (S ω) u) μ :=
    integrable_supportFunction_of_envelope hS hcompact hne hg hdom u
  rw [← integral_inner hf.1 u]
  calc
    (∫ ω, supportFunction (S ω) u ∂μ) - μ.real Set.univ * ε =
        ∫ ω, supportFunction (S ω) u - ε ∂μ := by
      rw [integral_sub hsupport (integrable_const ε), integral_const]
      simp [smul_eq_mul]
    _ ≤ ∫ ω, ⟪u, f ω⟫_ℝ ∂μ := by
      apply integral_mono_ae (hsupport.sub (integrable_const ε)) (hf.1.const_inner u)
      filter_upwards [] with ω
      exact (supportFunction_sub_lt_inner_supportApproximateSelection
        hS hcompact hne u hε ω).le

/-- Exact support identity for the closure of the Aumann expectation, derived
from Castaing's theorem and approximate maximizing selections.  No exact
maximizing-selection hypothesis is required.-/
theorem supportFunction_closure_aumannExpectation_of_envelope
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    (hAcompact : IsCompact (closure (aumannExpectation μ S))) (u : H) :
    supportFunction (closure (aumannExpectation μ S)) u =
      ∫ ω, supportFunction (S ω) u ∂μ := by
  have hsupport : Integrable (fun ω => supportFunction (S ω) u) μ :=
    integrable_supportFunction_of_envelope hS hcompact hne hg hdom u
  have hfOne : IsIntegrableSelection μ S
      (supportApproximateSelection hS hcompact hne u 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS hcompact hne hg hdom u (by norm_num)
  have hAne : (closure (aumannExpectation μ S)).Nonempty :=
    (aumannExpectation_nonempty_of_selection hfOne).closure
  apply le_antisymm
  · obtain ⟨x, hx, hxEq⟩ := supportFunction_attains hAcompact hAne u
    rw [hxEq]
    apply closure_minimal _
        (isClosed_le (by fun_prop : Continuous fun x : H => ⟪u, x⟫_ℝ)
          continuous_const) hx
    intro y hy
    exact inner_le_integral_supportFunction_of_mem_aumannExpectation
      (Filter.Eventually.of_forall hcompact) u hsupport hy
  · apply le_of_forall_pos_le_add
    intro δ hδ
    let m : ℝ := μ.real Set.univ
    let ε : ℝ := δ / (m + 1)
    have hm : 0 ≤ m := measureReal_nonneg
    have hm1 : 0 < m + 1 := by linarith
    have hε : 0 < ε := div_pos hδ hm1
    have hmε : m * ε < δ := by
      calc
        m * ε < (m + 1) * ε := mul_lt_mul_of_pos_right (by linarith) hε
        _ = δ := by
          dsimp [ε]
          exact mul_div_cancel₀ δ (ne_of_gt hm1)
    have hlower := inner_integral_supportApproximateSelection_lower_bound
      hS hcompact hne hg hdom u hε
    have hmem :
        (∫ ω, supportApproximateSelection hS hcompact hne u ε hε ω ∂μ) ∈
          closure (aumannExpectation μ S) := by
      apply subset_closure
      exact ⟨supportApproximateSelection hS hcompact hne u ε hε,
        integrableSelection_supportApproximateSelection_of_envelope
          hS hcompact hne hg hdom u hε, rfl⟩
    have hinner := inner_le_supportFunction hAcompact hmem u
    dsimp [m] at hmε hlower
    linarith

/-- Exact support identity for the *raw* Aumann expectation, without assuming
that this expectation is closed or compact.

The integrable envelope makes its closure compact.  Since a nonempty set and
its closure have the same support function, the closed-target identity above
immediately yields the formula on the unclosed Aumann expectation itself.
This does not prove topological closedness of that expectation.-/
theorem supportFunction_aumannExpectation_of_envelope
    {Ω H : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] [Nonempty H]
    [FiniteDimensional ℝ H]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {S : Ω → Set H} (hS : RandomSet.IsEffrosMeasurable S)
    (hcompact : ∀ ω, IsCompact (S ω)) (hne : ∀ ω, (S ω).Nonempty)
    {g : Ω → ℝ} (hg : Integrable g μ)
    (hdom : ∀ ω, ∀ x ∈ S ω, ‖x‖ ≤ g ω) (u : H) :
    supportFunction (aumannExpectation μ S) u =
      ∫ ω, supportFunction (S ω) u ∂μ := by
  have hAcompact : IsCompact (closure (aumannExpectation μ S)) :=
    closure_aumannExpectation_compact_of_integrable_envelope hg
      (Filter.Eventually.of_forall hdom)
  have hf : IsIntegrableSelection μ S
      (supportApproximateSelection hS hcompact hne u 1 (by norm_num)) :=
    integrableSelection_supportApproximateSelection_of_envelope
      hS hcompact hne hg hdom u (by norm_num)
  have hAne : (aumannExpectation μ S).Nonempty :=
    aumannExpectation_nonempty_of_selection hf
  rw [← supportFunction_closure_eq hAcompact hAne u]
  exact supportFunction_closure_aumannExpectation_of_envelope
    hS hcompact hne hg hdom hAcompact u

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
