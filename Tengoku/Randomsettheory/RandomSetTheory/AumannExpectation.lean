/-
Copyright (c) 2026 Hugo Dunias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Dunias
-/
import Tengoku
import Tengoku.Randomsettheory.RandomSetTheory.Basic
import Tengoku.Randomsettheory.RandomSetTheory.SupportFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Aumann expectation through integrable selections

The Aumann expectation of a correspondence `S : Ω → Set E` is the set of
Bochner integrals of all its integrable selections.  This is the primary
definition used in random-set theory; support-function characterizations need
additional measurable-selection and closedness theorems and are therefore not
built into the definition.

The file proves the algebraic, order, convexity, almost-everywhere invariance,
and integrable-envelope properties that follow directly from selections.  The
finite-dimensional Lyapunov conclusion is exposed as an explicit property,
so no atomlessness theorem absent from mathlib is silently assumed.
-/
namespace Tengoku.Randomsettheory end Tengoku.Randomsettheory open Tengoku.Randomsettheory
open MeasureTheory
open Set
open scoped Pointwise InnerProductSpace

noncomputable section

namespace RandomSetTheory

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An integrable selection of a set-valued map.-/
def IsIntegrableSelection (μ : Measure Ω) (S : Ω → Set E) (f : Ω → E) : Prop :=
  Integrable f μ ∧ ∀ᵐ ω ∂μ, f ω ∈ S ω

/-- The Aumann expectation: all integrals of integrable selections.-/
def aumannExpectation (μ : Measure Ω) (S : Ω → Set E) : Set E :=
  {x | ∃ f : Ω → E, IsIntegrableSelection μ S f ∧ ∫ ω, f ω ∂μ = x}

/--
@isnad1 id=iff.0h5v.s6.4c49df619e86 from=translated src=- shape=7375f8d4 vocab=b0379447
-/
theorem mem_aumannExpectation_iff {μ : Measure Ω} {S : Ω → Set E} {x : E} :
    x ∈ aumannExpectation μ S ↔
      ∃ f : Ω → E, IsIntegrableSelection μ S f ∧ ∫ ω, f ω ∂μ = x :=
  Iff.rfl

/--
@isnad1 id=nonempty.1h5v.s5.6983ffc11be5 from=translated src=- shape=34e66937 vocab=1b3914f3
-/
theorem aumannExpectation_nonempty_of_selection {μ : Measure Ω} {S : Ω → Set E}
    {f : Ω → E} (hf : IsIntegrableSelection μ S f) :
    (aumannExpectation μ S).Nonempty := by
  exact ⟨∫ ω, f ω ∂μ, f, hf, rfl⟩

/--
@isnad1 id=le.1h5v.s6.92fed920c9b1 from=translated src=- shape=656e642f vocab=27efaeb5
-/
theorem aumannExpectation_mono_ae {μ : Measure Ω} {S T : Ω → Set E}
    (hST : ∀ᵐ ω ∂μ, S ω ⊆ T ω) :
    aumannExpectation μ S ⊆ aumannExpectation μ T := by
  rintro x ⟨f, hf, rfl⟩
  refine ⟨f, ⟨hf.1, ?_⟩, rfl⟩
  filter_upwards [hf.2, hST] with ω hfω hSTω
  exact hSTω hfω

/--
@isnad1 id=le.1h5v.s6.de06738a2b36 from=translated src=- shape=ab261f87 vocab=80942d5a
-/
theorem aumannExpectation_mono {μ : Measure Ω} {S T : Ω → Set E}
    (hST : ∀ ω, S ω ⊆ T ω) :
    aumannExpectation μ S ⊆ aumannExpectation μ T :=
  aumannExpectation_mono_ae (Filter.Eventually.of_forall hST)

/--
@isnad1 id=eq.1h5v.s6.f1edcff7b057 from=translated src=- shape=7045bdcf vocab=baa0bb0b
-/
theorem aumannExpectation_congr_ae {μ : Measure Ω} {S T : Ω → Set E}
    (hST : S =ᵐ[μ] T) : aumannExpectation μ S = aumannExpectation μ T := by
  apply Set.Subset.antisymm
  · exact aumannExpectation_mono_ae (hST.mono fun _ h => h.subset)
  · exact aumannExpectation_mono_ae (hST.symm.mono fun _ h => h.subset)

/--
@isnad1 id=eq.1h4v.s6.372bb9177378 from=translated src=- shape=57dff9a7 vocab=17628d17
-/
theorem aumannExpectation_singleton {μ : Measure Ω} {f : Ω → E}
    (hf : Integrable f μ) :
    aumannExpectation μ (fun ω => ({f ω} : Set E)) = {∫ ω, f ω ∂μ} := by
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hgf : g =ᵐ[μ] f := hg.2.mono fun ω hω => by simpa using hω
    simp [integral_congr_ae hgf]
  · intro hx
    have hx' : x = ∫ ω, f ω ∂μ := by simpa using hx
    subst x
    refine ⟨f, ⟨hf, ?_⟩, rfl⟩
    filter_upwards [] with ω
    simp

/--
@isnad1 id=eq.0h4v.s7.cc13eac509af from=translated src=- shape=1ce46af2 vocab=cca2c4a9
-/
theorem aumannExpectation_const_singleton {μ : Measure Ω} [IsFiniteMeasure μ]
    [CompleteSpace E]
    (x : E) :
    aumannExpectation μ (fun _ => ({x} : Set E)) = {μ.real Set.univ • x} := by
  rw [aumannExpectation_singleton (integrable_const x)]
  rw [MeasureTheory.integral_const]

/-- On a probability space, the Aumann expectation of a constant closed
convex set is the set itself.
@isnad1 id=eq.2h4v.s7.22a33c19e614 from=translated src=- shape=9cb48b8e vocab=8c121211
-/
theorem aumannExpectation_const {μ : Measure Ω} [IsProbabilityMeasure μ]
    [CompleteSpace E] {K : Set E} (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) :
    aumannExpectation μ (fun _ => K) = K := by
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, rfl⟩
    exact hKconv.integral_mem hKclosed hf.2 hf.1
  · intro x hx
    refine ⟨fun _ => x, ⟨integrable_const x, ?_⟩, ?_⟩
    · filter_upwards [] with ω
      exact hx
    · rw [MeasureTheory.integral_const]
      simp

/--
@isnad1 id=convex.1h4v.s7.8ada47393705 from=translated src=- shape=e60db30b vocab=6edc40ed
-/
theorem aumannExpectation_convex {μ : Measure Ω} {S : Ω → Set E}
    (hS : ∀ᵐ ω ∂μ, Convex ℝ (S ω)) : Convex ℝ (aumannExpectation μ S) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨f, hf, rfl⟩
  rcases hy with ⟨g, hg, rfl⟩
  refine ⟨fun ω => a • f ω + b • g ω,
    ⟨(hf.1.smul a).add (hg.1.smul b), ?_⟩, ?_⟩
  · filter_upwards [hf.2, hg.2, hS] with ω hfω hgω hSω
    exact hSω hfω hgω ha hb hab
  · calc
      (∫ ω, a • f ω + b • g ω ∂μ) =
          (∫ ω, a • f ω ∂μ) + ∫ ω, b • g ω ∂μ :=
        integral_add (hf.1.smul a) (hg.1.smul b)
      _ = a • (∫ ω, f ω ∂μ) + b • ∫ ω, g ω ∂μ := by
        rw [integral_smul, integral_smul]

/-! ## Support-function characterization -/

section SupportFunction

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Every integrable selection satisfies the integrated support inequality.
@isnad1 id=le.3h6v.s7.cc2ed1760c5b from=translated src=- shape=22a565b4 vocab=4ce43193
-/
theorem inner_integral_selection_le_integral_supportFunction
    [CompleteSpace H]
    {μ : Measure Ω} {S : Ω → Set H} {f : Ω → H}
    (hf : IsIntegrableSelection μ S f)
    (hcompact : ∀ᵐ ω ∂μ, IsCompact (S ω))
    (u : H) (hsupport : Integrable (fun ω => supportFunction (S ω) u) μ) :
    ⟪u, ∫ ω, f ω ∂μ⟫_ℝ ≤ ∫ ω, supportFunction (S ω) u ∂μ := by
  rw [← integral_inner hf.1 u]
  apply integral_mono_ae (hf.1.const_inner u) hsupport
  filter_upwards [hf.2, hcompact] with ω hfω hcompactω
  exact inner_le_supportFunction hcompactω hfω u

/-- Every point of the Aumann expectation lies below the integral of the
pointwise support functions.
@isnad1 id=le.3h6v.s7.a4d893b89701 from=translated src=- shape=30f510c5 vocab=bf1de8c1
-/
theorem inner_le_integral_supportFunction_of_mem_aumannExpectation
    [CompleteSpace H]
    {μ : Measure Ω} {S : Ω → Set H}
    (hcompact : ∀ᵐ ω ∂μ, IsCompact (S ω))
    (u : H) (hsupport : Integrable (fun ω => supportFunction (S ω) u) μ)
    {x : H} (hx : x ∈ aumannExpectation μ S) :
    ⟪u, x⟫_ℝ ≤ ∫ ω, supportFunction (S ω) u ∂μ := by
  rcases hx with ⟨f, hf, rfl⟩
  exact inner_integral_selection_le_integral_supportFunction
    hf hcompact u hsupport

/-- A measurable-selection hypothesis tailored to a direction: an integrable
selection realizes the pointwise support almost everywhere.-/
def HasIntegrableSupportSelection
    (μ : Measure Ω) (S : Ω → Set H) (u : H) : Prop :=
  ∃ f : Ω → H, IsIntegrableSelection μ S f ∧
    ∀ᵐ ω ∂μ, ⟪u, f ω⟫_ℝ = supportFunction (S ω) u

/-- A support-maximizing selection realizes the integrated support bound as a
point of the Aumann expectation.
@isnad1 id=ex.1h5v.s6.638576cda75d from=translated src=- shape=5be150ac vocab=8dce7403
-/
theorem exists_mem_aumannExpectation_inner_eq_integral_supportFunction
    [CompleteSpace H]
    {μ : Measure Ω} {S : Ω → Set H} {u : H}
    (hsel : HasIntegrableSupportSelection μ S u) :
    ∃ x ∈ aumannExpectation μ S,
      ⟪u, x⟫_ℝ = ∫ ω, supportFunction (S ω) u ∂μ := by
  rcases hsel with ⟨f, hf, hmax⟩
  refine ⟨∫ ω, f ω ∂μ, ⟨f, hf, rfl⟩, ?_⟩
  rw [← integral_inner hf.1 u]
  exact integral_congr_ae hmax

/-- Sharp Aumann support identity under the exact hypotheses needed by the
elementary proof: compactness of the Aumann expectation, integrability of the
pointwise support, and an integrable maximizing selection.
@isnad1 id=eq.5h5v.s7.316ed6df835f from=translated src=- shape=df7565fd vocab=686b9b64
-/
theorem supportFunction_aumannExpectation
    [CompleteSpace H]
    {μ : Measure Ω} {S : Ω → Set H}
    (hcompact : ∀ᵐ ω ∂μ, IsCompact (S ω))
    (hAcompact : IsCompact (aumannExpectation μ S))
    (hAne : (aumannExpectation μ S).Nonempty)
    (u : H) (hsupport : Integrable (fun ω => supportFunction (S ω) u) μ)
    (hsel : HasIntegrableSupportSelection μ S u) :
    supportFunction (aumannExpectation μ S) u =
      ∫ ω, supportFunction (S ω) u ∂μ := by
  obtain ⟨x, hx, hxEq⟩ :=
    exists_mem_aumannExpectation_inner_eq_integral_supportFunction hsel
  apply le_antisymm
  · obtain ⟨y, hy, hyEq⟩ := supportFunction_attains hAcompact hAne u
    rw [hyEq]
    exact inner_le_integral_supportFunction_of_mem_aumannExpectation
      hcompact u hsupport hy
  · rw [← hxEq]
    exact inner_le_supportFunction hAcompact hx u

end SupportFunction

/-! ## Lyapunov convexity -/

/-- A genuine atomlessness property: every measurable set of positive measure
contains a measurable subset of strictly intermediate measure.-/
def IsAtomlessMeasure (μ : Measure Ω) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → 0 < μ s →
    ∃ t : Set Ω, t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ μ t < μ s

/--
@isnad1 id=nullsing.1h2v.s4.1ee0a3a1204b from=translated src=- shape=bf4988ee vocab=269f8849
-/
theorem IsAtomlessMeasure.toNullSingletonClass
    [MeasurableSingletonClass Ω] {μ : Measure Ω} (hμ : IsAtomlessMeasure μ) :
    NullSingletonClass μ := by
  refine ⟨fun x => ?_⟩
  by_contra hne
  obtain ⟨t, hts, _, htpos, htlt⟩ :=
    hμ {x} (measurableSet_singleton x) (pos_iff_ne_zero.mpr hne)
  rcases Set.subset_singleton_iff_eq.mp hts with rfl | rfl
  · simp at htpos
  · exact lt_irrefl _ htlt

/-- A positive measurable set in an atomless measure space can be split
into two disjoint measurable pieces of positive measure.
@isnad1 id=ex.3h3v.s7.19e3c607a447 from=translated src=- shape=19511048 vocab=a982010a
-/
theorem IsAtomlessMeasure.exists_measurable_split
    {μ : Measure Ω} (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s) (hspos : 0 < μ s) :
    ∃ t : Set Ω,
      t ⊆ s ∧ MeasurableSet t ∧ 0 < μ t ∧ 0 < μ (s \ t) := by
  obtain ⟨t, hts, htmeas, htpos, htlt⟩ := hμ s hs hspos
  refine ⟨t, hts, htmeas, htpos, ?_⟩
  rw [measure_sdiff hts htmeas.nullMeasurableSet (ne_top_of_lt htlt)]
  exact tsub_pos_iff_lt.mpr htlt

/-- Restricting an atomless measure to a measurable set preserves
atomlessness.
@isnad1 id=isatomle.2h3v.s4.ba247d4ae199 from=translated src=- shape=a6a6750d vocab=2f6022cb
-/
theorem IsAtomlessMeasure.restrict
    {μ : Measure Ω} (hμ : IsAtomlessMeasure μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    IsAtomlessMeasure (μ.restrict s) := by
  intro A hA hApos
  have hAs : MeasurableSet (A ∩ s) := hA.inter hs
  have hApos' : 0 < μ (A ∩ s) := by
    simpa [Measure.restrict_apply hA] using hApos
  obtain ⟨t, htAs, htmeas, htpos, htlt⟩ := hμ (A ∩ s) hAs hApos'
  have hts : t ⊆ s := htAs.trans inter_subset_right
  refine ⟨t, htAs.trans inter_subset_left, htmeas, ?_, ?_⟩
  · simpa [Measure.restrict_apply htmeas, inter_eq_self_of_subset_left hts]
      using htpos
  · simpa [Measure.restrict_apply htmeas, Measure.restrict_apply hA,
      inter_eq_self_of_subset_left hts] using htlt

/-- Range of `A ↦ ∫ ω in A, f ω ∂μ` over measurable sets.-/
def measurableSetIntegralRange (μ : Measure Ω) (f : Ω → E) : Set E :=
  {x | ∃ A : Set Ω, MeasurableSet A ∧ ∫ ω in A, f ω ∂μ = x}

/--
@isnad1 id=mem.0h4v.s5.6649c896dc9e from=translated src=- shape=2b0b8088 vocab=3c780e8f
-/
theorem zero_mem_measurableSetIntegralRange (μ : Measure Ω) (f : Ω → E) :
    0 ∈ measurableSetIntegralRange μ f := by
  exact ⟨∅, MeasurableSet.empty, by simp⟩

/--
@isnad1 id=mem.0h4v.s5.eaa0acf456e4 from=translated src=- shape=17df5ca5 vocab=45aa2992
-/
theorem integral_mem_measurableSetIntegralRange (μ : Measure Ω) (f : Ω → E) :
    (∫ ω, f ω ∂μ) ∈ measurableSetIntegralRange μ f := by
  exact ⟨Set.univ, MeasurableSet.univ, by simp⟩

/-- The exact finite-dimensional conclusion supplied by Lyapunov's convexity
theorem.  It is separated from any particular atomlessness typeclass.-/
def HasLyapunovConvexity (μ : Measure Ω) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop :=
  ∀ f : Ω → E, Integrable f μ → Convex ℝ (measurableSetIntegralRange μ f)

/-- Lyapunov convexity transports backwards through a continuous linear
equivalence of target spaces.  This lets applications work with their natural
norm while proving Lyapunov in any convenient finite-dimensional Euclidean
realization.
@isnad1 id=haslyapu.1h5v.s6.47a81d86f865 from=translated src=- shape=05ae1418 vocab=a49614e4
-/
theorem HasLyapunovConvexity.of_continuousLinearEquiv
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Ω} (hF : HasLyapunovConvexity μ F)
    (e : E ≃L[ℝ] F) : HasLyapunovConvexity μ E := by
  intro f hf
  have hef : Integrable (fun ω => e (f ω)) μ :=
    (e.integrable_comp_iff).2 hf
  have hconv := hF (fun ω => e (f ω)) hef
  intro x hx y hy a b ha hb hab
  have hex : e x ∈ measurableSetIntegralRange μ (fun ω => e (f ω)) := by
    rcases hx with ⟨A, hA, rfl⟩
    refine ⟨A, hA, ?_⟩
    exact e.integral_comp_comm f
  have hey : e y ∈ measurableSetIntegralRange μ (fun ω => e (f ω)) := by
    rcases hy with ⟨B, hB, rfl⟩
    refine ⟨B, hB, ?_⟩
    exact e.integral_comp_comm f
  obtain ⟨C, hC, hCeq⟩ := hconv hex hey ha hb hab
  refine ⟨C, hC, ?_⟩
  apply e.injective
  calc
    e (∫ ω in C, f ω ∂μ) = ∫ ω in C, e (f ω) ∂μ :=
      (e.integral_comp_comm f).symm
    _ = a • e x + b • e y := hCeq
    _ = e (a • x + b • y) := by simp

/-- Lyapunov convexity is invariant under continuous linear equivalence of
the finite-dimensional target representation.
@isnad1 id=iff.0h5v.s6.801018244ac1 from=translated src=- shape=247204d0 vocab=a49614e4
-/
theorem hasLyapunovConvexity_continuousLinearEquiv_iff
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Ω} (e : E ≃L[ℝ] F) :
    HasLyapunovConvexity μ E ↔ HasLyapunovConvexity μ F := by
  constructor
  · intro hE
    exact hE.of_continuousLinearEquiv e.symm
  · intro hF
    exact hF.of_continuousLinearEquiv e

/--
@isnad1 id=ex.4h5v.s7.965ef1e57bfb from=translated src=- shape=f3faff96 vocab=35ad0d54
-/
theorem HasLyapunovConvexity.exists_setIntegral_eq_smul
    {μ : Measure Ω} (hμ : HasLyapunovConvexity μ E)
    {f : Ω → E} (hf : Integrable f μ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∃ A : Set Ω, MeasurableSet A ∧
      (∫ ω in A, f ω ∂μ) = a • ∫ ω, f ω ∂μ := by
  have hmem := hμ f hf
    (integral_mem_measurableSetIntegralRange μ f)
    (zero_mem_measurableSetIntegralRange μ f)
    ha0 (sub_nonneg.mpr ha1) (by ring)
  rcases hmem with ⟨A, hA, hEq⟩
  exact ⟨A, hA, by simpa using hEq⟩

/--
@isnad1 id=convex.1h4v.s6.ba34a6b0ae28 from=translated src=- shape=d4ea2bdb vocab=8478fd27
-/
theorem aumannExpectation_convex_of_lyapunov
    {μ : Measure Ω} (hμ : HasLyapunovConvexity μ E) (S : Ω → Set E) :
    Convex ℝ (aumannExpectation μ S) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨f, hf, rfl⟩
  rcases hy with ⟨g, hg, rfl⟩
  have hfg : Integrable (fun ω => f ω - g ω) μ := hf.1.sub hg.1
  obtain ⟨A, hA, hsplit⟩ :=
    hμ.exists_setIntegral_eq_smul hfg ha (by linarith)
  let q : Ω → E := fun ω => g ω + A.indicator (fun ω => f ω - g ω) ω
  have hqint : Integrable q μ :=
    hg.1.add (hfg.integrableOn.integrable_indicator hA)
  refine ⟨q, ⟨hqint, ?_⟩, ?_⟩
  · filter_upwards [hf.2, hg.2] with ω hfω hgω
    by_cases hω : ω ∈ A
    · simpa [q, Set.indicator_of_mem hω] using hfω
    · simpa [q, Set.indicator_of_notMem hω] using hgω
  · rw [show q = fun ω => g ω + A.indicator (fun ω => f ω - g ω) ω from rfl]
    rw [integral_add hg.1 (hfg.integrableOn.integrable_indicator hA)]
    rw [integral_indicator hA, hsplit, integral_sub hf.1 hg.1]
    have hb' : b = 1 - a := by linarith
    rw [hb']
    module

/--
@isnad1 id=convex.1h4v.s6.ddc7fa8b3cce from=translated src=- shape=6903c5d1 vocab=8a66f5ec
-/
theorem closure_aumannExpectation_convex_of_lyapunov
    {μ : Measure Ω} (hμ : HasLyapunovConvexity μ E) (S : Ω → Set E) :
    Convex ℝ (closure (aumannExpectation μ S)) :=
  (aumannExpectation_convex_of_lyapunov hμ S).closure

/-! ## Minkowski operations -/

/--
@isnad1 id=mem.2h7v.s7.4c70941b06d8 from=translated src=- shape=513ee652 vocab=1e0b7a89
-/
theorem add_mem_aumannExpectation {μ : Measure Ω} {S T : Ω → Set E}
    {x y : E} (hx : x ∈ aumannExpectation μ S)
    (hy : y ∈ aumannExpectation μ T) :
    x + y ∈ aumannExpectation μ (fun ω => S ω + T ω) := by
  rcases hx with ⟨f, hf, rfl⟩
  rcases hy with ⟨g, hg, rfl⟩
  refine ⟨fun ω => f ω + g ω, ⟨hf.1.add hg.1, ?_⟩, ?_⟩
  · filter_upwards [hf.2, hg.2] with ω hfω hgω
    exact Set.add_mem_add hfω hgω
  · exact integral_add hf.1 hg.1

/--
@isnad1 id=le.0h5v.s6.30bb1beb8c05 from=translated src=- shape=db0293c0 vocab=6bbc0822
-/
theorem aumannExpectation_add_subset {μ : Measure Ω} {S T : Ω → Set E} :
    aumannExpectation μ S + aumannExpectation μ T ⊆
      aumannExpectation μ (fun ω => S ω + T ω) := by
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact add_mem_aumannExpectation hx hy

/-- Exact hypothesis needed for the reverse Minkowski inclusion: every
integrable selection of the pointwise sum admits an integrable measurable
decomposition.  Measurable-selection theorems can be used later to construct
this property under standard closed-valued hypotheses.-/
def HasIntegrableMinkowskiDecomposition (μ : Measure Ω)
    (S T : Ω → Set E) : Prop :=
  ∀ f : Ω → E,
    IsIntegrableSelection μ (fun ω => S ω + T ω) f →
    ∃ g h : Ω → E,
      IsIntegrableSelection μ S g ∧ IsIntegrableSelection μ T h ∧
        f =ᵐ[μ] fun ω => g ω + h ω

/-- Aumann expectation is exactly Minkowski additive whenever integrable
selections of the pointwise sum can be decomposed measurably.
@isnad1 id=eq.1h5v.s6.1eaf3c584eaf from=translated src=- shape=8018befb vocab=6aa52248
-/
theorem aumannExpectation_add
    {μ : Measure Ω} {S T : Ω → Set E}
    (hdecomp : HasIntegrableMinkowskiDecomposition μ S T) :
    aumannExpectation μ (fun ω => S ω + T ω) =
      aumannExpectation μ S + aumannExpectation μ T := by
  apply Set.Subset.antisymm
  · rintro x ⟨f, hf, hfx⟩
    obtain ⟨g, h, hg, hh, hfgh⟩ := hdecomp f hf
    refine ⟨∫ ω, g ω ∂μ, ⟨g, hg, rfl⟩,
      ∫ ω, h ω ∂μ, ⟨h, hh, rfl⟩, ?_⟩
    calc
      (∫ ω, g ω ∂μ) + ∫ ω, h ω ∂μ =
          ∫ ω, g ω + h ω ∂μ := (integral_add hg.1 hh.1).symm
      _ = ∫ ω, f ω ∂μ := integral_congr_ae hfgh.symm
      _ = x := hfx
  · exact aumannExpectation_add_subset

/-- Exact translation by an integrable singleton-valued correspondence.
@isnad1 id=eq.1h5v.s7.f19b4def332d from=translated src=- shape=5f44acb1 vocab=0a8fe4d5
-/
theorem aumannExpectation_add_singleton {μ : Measure Ω}
    {S : Ω → Set E} {g : Ω → E} (hg : Integrable g μ) :
    aumannExpectation μ (fun ω => S ω + ({g ω} : Set E)) =
      aumannExpectation μ S + {∫ ω, g ω ∂μ} := by
  apply Set.Subset.antisymm
  · rintro x ⟨h, hh, rfl⟩
    let f : Ω → E := fun ω => h ω - g ω
    have hfmem : ∀ᵐ ω ∂μ, f ω ∈ S ω := by
      filter_upwards [hh.2] with ω hω
      rcases hω with ⟨s, hs, t, ht, hst⟩
      simp only [mem_singleton_iff] at ht
      subst t
      simp [f, ← hst, hs]
    have hf : IsIntegrableSelection μ S f := ⟨hh.1.sub hg, hfmem⟩
    refine ⟨∫ ω, f ω ∂μ, ⟨f, hf, rfl⟩,
      ∫ ω, g ω ∂μ, Set.mem_singleton _, ?_⟩
    change (∫ ω, f ω ∂μ) + (∫ ω, g ω ∂μ) = ∫ ω, h ω ∂μ
    rw [← integral_add hf.1 hg]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp [f]
  · rintro x ⟨a, ha, b, hb, rfl⟩
    simp only [mem_singleton_iff] at hb
    subst b
    have hgmem : (∫ ω, g ω ∂μ) ∈
        aumannExpectation μ (fun ω => ({g ω} : Set E)) := by
      rw [aumannExpectation_singleton hg]
      exact Set.mem_singleton _
    exact add_mem_aumannExpectation ha hgmem

/--
@isnad1 id=mem.1h6v.s7.cc1ae5831dce from=translated src=- shape=6c22889b vocab=48c5c54b
-/
theorem smul_mem_aumannExpectation {μ : Measure Ω} {S : Ω → Set E}
    (c : ℝ) {x : E} (hx : x ∈ aumannExpectation μ S) :
    c • x ∈ aumannExpectation μ (fun ω => c • S ω) := by
  rcases hx with ⟨f, hf, rfl⟩
  refine ⟨fun ω => c • f ω, ⟨hf.1.smul c, ?_⟩, ?_⟩
  · filter_upwards [hf.2] with ω hfω
    exact Set.smul_mem_smul_set hfω
  · exact integral_smul c f

/--
@isnad1 id=le.0h5v.s7.30b40048c7a6 from=translated src=- shape=9d846465 vocab=f24244a5
-/
theorem aumannExpectation_smul_subset {μ : Measure Ω} {S : Ω → Set E}
    (c : ℝ) :
    c • aumannExpectation μ S ⊆
      aumannExpectation μ (fun ω => c • S ω) := by
  rintro _ ⟨x, hx, rfl⟩
  exact smul_mem_aumannExpectation c hx

/--
@isnad1 id=eq.1h5v.s7.f18203ef9c8c from=translated src=- shape=593adb0f vocab=c44a1978
-/
theorem aumannExpectation_smul_of_ne {μ : Measure Ω} {S : Ω → Set E}
    (c : ℝ) (hc : c ≠ 0) :
    aumannExpectation μ (fun ω => c • S ω) =
      c • aumannExpectation μ S := by
  apply Set.Subset.antisymm
  · rintro y ⟨g, hg, rfl⟩
    let f : Ω → E := fun ω => c⁻¹ • g ω
    have hfmem : ∀ᵐ ω ∂μ, f ω ∈ S ω := by
      filter_upwards [hg.2] with ω hω
      rcases hω with ⟨x, hx, hcx⟩
      simpa [f, ← hcx, hc] using hx
    refine ⟨∫ ω, f ω ∂μ, ⟨f, ⟨hg.1.smul c⁻¹, hfmem⟩, rfl⟩, ?_⟩
    rw [integral_smul]
    simp [hc]
  · exact aumannExpectation_smul_subset c

/--
@isnad1 id=mem.1h4v.s6.ffa889deef42 from=translated src=- shape=dc23da75 vocab=d6fc4a5d
-/
theorem zero_mem_aumannExpectation {μ : Measure Ω} {S : Ω → Set E}
    (hzero : ∀ᵐ ω ∂μ, (0 : E) ∈ S ω) :
    0 ∈ aumannExpectation μ S := by
  refine ⟨fun _ => 0, ⟨integrable_zero _ _ _, hzero⟩, ?_⟩
  simp

/-! ## Integrable envelopes and compact closure -/

/-- Every integral of a selection is bounded by the integral of a common
integrable envelope.
@isnad1 id=le.3h6v.s7.c9af2ecdeda2 from=translated src=- shape=8aa7c523 vocab=780a3161
-/
theorem norm_le_integral_envelope_of_mem_aumannExpectation
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    {x : E} (hx : x ∈ aumannExpectation μ S) :
    ‖x‖ ≤ ∫ ω, g ω ∂μ := by
  rcases hx with ⟨f, hf, rfl⟩
  apply norm_integral_le_of_norm_le hg
  filter_upwards [hf.2, hdom] with ω hfω hdomω
  exact hdomω (f ω) hfω

/-- The same explicit envelope bound holds on the closure of the Aumann
expectation.
@isnad1 id=le.3h6v.s7.e1d182ba8289 from=translated src=- shape=2bca473a vocab=4d667457
-/
theorem norm_le_integral_envelope_of_mem_closure_aumannExpectation
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω)
    {x : E} (hx : x ∈ closure (aumannExpectation μ S)) :
    ‖x‖ ≤ ∫ ω, g ω ∂μ := by
  have hsub : aumannExpectation μ S ⊆
      {y : E | ‖y‖ ≤ ∫ ω, g ω ∂μ} := fun _ hy =>
    norm_le_integral_envelope_of_mem_aumannExpectation hg hdom hy
  exact closure_minimal hsub
    (isClosed_le continuous_norm continuous_const) hx

/--
@isnad1 id=isbounde.2h5v.s6.1a2fd404f59d from=translated src=- shape=8697adab vocab=4c3e4f6c
-/
theorem aumannExpectation_isBounded_of_integrable_envelope
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    Bornology.IsBounded (aumannExpectation μ S) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨∫ ω, g ω ∂μ, ?_⟩
  exact fun _ hx =>
    norm_le_integral_envelope_of_mem_aumannExpectation hg hdom hx

/--
@isnad1 id=iscompac.2h5v.s7.ebf1cd91ba26 from=translated src=- shape=dc06848c vocab=8ec6daf2
-/
theorem closure_aumannExpectation_compact_of_integrable_envelope
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    IsCompact (closure (aumannExpectation μ S)) :=
  (aumannExpectation_isBounded_of_integrable_envelope hg hdom).isCompact_closure

/--
@isnad1 id=and.3h5v.s8.641b345800e0 from=translated src=- shape=115eb916 vocab=10190a12
-/
theorem closure_aumannExpectation_compact_convex
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} {S : Ω → Set E} {g : Ω → ℝ}
    (hconv : ∀ᵐ ω ∂μ, Convex ℝ (S ω))
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    IsCompact (closure (aumannExpectation μ S)) ∧
      Convex ℝ (closure (aumannExpectation μ S)) :=
  ⟨closure_aumannExpectation_compact_of_integrable_envelope hg hdom,
    (aumannExpectation_convex hconv).closure⟩

/--
@isnad1 id=and.3h5v.s7.0d878b8baf0f from=translated src=- shape=71e79a88 vocab=df8a1fcb
-/
theorem closure_aumannExpectation_compact_convex_of_lyapunov
    [FiniteDimensional ℝ E]
    {μ : Measure Ω} (hμ : HasLyapunovConvexity μ E)
    {S : Ω → Set E} {g : Ω → ℝ}
    (hg : Integrable g μ)
    (hdom : ∀ᵐ ω ∂μ, ∀ x ∈ S ω, ‖x‖ ≤ g ω) :
    IsCompact (closure (aumannExpectation μ S)) ∧
      Convex ℝ (closure (aumannExpectation μ S)) :=
  ⟨closure_aumannExpectation_compact_of_integrable_envelope hg hdom,
    closure_aumannExpectation_convex_of_lyapunov hμ S⟩

/-- Convenience wrapper for the project's random-set structure.-/
def RandomSet.aumannExpectation [TopologicalSpace E]
    (μ : Measure Ω) (S : RandomSet Ω E) : Set E :=
  RandomSetTheory.aumannExpectation μ S

end RandomSetTheory
-- Tengoku: root names of this library moved to Tengoku.Randomsettheory so they do not collide with other libraries (generated)
