import Tengoku.NsP23.P23.Artin.Coefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace foundation in the direct finite monomial model

The trace below is the ordinary sum of the ranges of all `A`-linear maps
`Omega →ₗ[A] A`.  Its root-image description is proved afterwards from the
frozen root-dual generation theorem.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- The ordinary module trace: the sum of the ranges of all `A`-linear maps
from the canonical dual to the algebra.-/
def TraceSubmodule (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    Submodule (MonomialArtin k S) (MonomialArtin k S) :=
  ⨆ F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S, F.range

/-- Values of arbitrary canonical-dual maps.-/
def traceValueSet (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    Set (MonomialArtin k S) :=
  {v | ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (φ : Omega k S), F φ = v}

/-- Values of arbitrary canonical-dual maps on selected-root duals.-/
def rootTraceValueSet (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    Set (MonomialArtin k S) :=
  {v | ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      F (U (k := k) S (rootIndex S s hs)) = v}

/--
@isnad1 id=le.0h6v.s9.2cb1b1ab5838 from=translated src=- shape=dfa4cf27 vocab=7c2db424
-/
theorem trace_range_le (S : Finset (Normal a b c))
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S) :
    F.range ≤ TraceSubmodule k S :=
  le_iSup (fun G : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S ↦ G.range) F

/--
@isnad1 id=eq.0h5v.s7.1020356de168 from=translated src=- shape=2e0c51c3 vocab=30d57e5c
-/
theorem trace_eq_span_traceValueSet (S : Finset (Normal a b c)) :
    TraceSubmodule k S =
      Submodule.span (MonomialArtin k S) (traceValueSet k S) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro F
    rintro v ⟨φ, rfl⟩
    exact Submodule.subset_span ⟨F, φ, rfl⟩
  · apply Submodule.span_le.2
    rintro v ⟨F, φ, rfl⟩
    exact trace_range_le (k := k) S F ⟨φ, rfl⟩

/-- The ordinary trace equals the `A`-span of images of the selected-root
duals.  This is a theorem, not the definition of trace.
@isnad1 id=eq.0h5v.s7.899bd15e9f42 from=translated src=- shape=2e0c51c3 vocab=05a1785c
-/
theorem trace_eq_span_rootTraceValueSet (S : Finset (Normal a b c)) :
    TraceSubmodule k S =
      Submodule.span (MonomialArtin k S) (rootTraceValueSet k S) := by
  rw [trace_eq_span_traceValueSet]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro v ⟨F, φ, rfl⟩
    have hφ : φ ∈ Submodule.span (MonomialArtin k S) (rootDualSet k S) := by
      rw [rootDual_span_eq_top]
      trivial
    refine Submodule.span_induction
      (p := fun ψ _ ↦ F ψ ∈
        Submodule.span (MonomialArtin k S) (rootTraceValueSet k S))
      ?_ ?_ ?_ ?_ hφ
    · rintro ψ ⟨s, hs, rfl⟩
      exact Submodule.subset_span ⟨F, s, hs, rfl⟩
    · simp
    · intro x y _ _ ihx ihy
      rw [F.map_add]
      exact Submodule.add_mem _ ihx ihy
    · intro r x _ ihx
      rw [F.map_smul]
      exact Submodule.smul_mem _ r ihx
  · apply Submodule.span_mono
    rintro v ⟨F, s, hs, rfl⟩
    exact ⟨F, U (k := k) S (rootIndex S s hs), rfl⟩

/-- Each selected-root image has zero degree-zero coefficient in type greater
than one.  The proof uses a second incomparable root and exact coefficient
transport; it is specific to the direct finite model.
@isnad1 id=eq.4h7v.s10.9a73d88c67b9 from=translated src=- shape=f2e871c8 vocab=67c9aae5
-/
theorem rootTraceValue_constantCoeff_eq_zero (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
    (s : Normal a b c) (hs : s ∈ S) :
    constantCoeff (k := k) S hS
        (F (U (k := k) S (rootIndex S s hs))) = 0 := by
  classical
  have hex : ∃ r ∈ S, r ≠ s := by
    by_contra hn
    push_neg at hn
    have hsub : S ⊆ {s} := by
      intro r hr
      simp [hn r hr]
    have hc := Finset.card_le_card hsub
    simp at hc
    omega
  obtain ⟨r, hr, hrs⟩ := hex
  let ri := rootIndex S r hr
  let si := rootIndex S s hs
  have hndiv : ¬r ∣ s := hanti r hr s hs hrs
  have hann : X (k := k) S ri.1 ri.2 • U (k := k) S si = 0 :=
    (X_smul_rootDual_eq_zero_iff (k := k) S s hs ri).2 (by
      change ¬r ∣ s
      exact hndiv)
  have hzero : X (k := k) S ri.1 ri.2 * F (U (k := k) S si) = 0 := by
    calc
      X (k := k) S ri.1 ri.2 * F (U (k := k) S si) =
          X (k := k) S ri.1 ri.2 • F (U (k := k) S si) := by
            simp [smul_eq_mul]
      _ = F (X (k := k) S ri.1 ri.2 • U (k := k) S si) := by
            symm
            exact F.map_smul _ _
      _ = 0 := by rw [hann]; simp
  have hc := congrArg (coeffAt (k := k) S ri) hzero
  rw [coeffAt_X_mul (k := k) S ri (unitIndex S hS) ri] at hc
  · simpa [constantCoeff, si] using hc
  · simp [unitIndex]

/-- If every selected-root image has zero coefficient in a live variable,
then every trace element has zero coefficient there.
@isnad1 id=eq.7h7v.s10.1fd6cadae129 from=translated src=- shape=1ccf137f vocab=af2495aa
-/
theorem coeffAt_variable_eq_zero_of_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (e : Direction)
    (heS : e.generator ∈ standardFinset S)
    (hroot : ∀ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S ⟨e.generator, heS⟩
        (F (U (k := k) S (rootIndex S s hs))) = 0)
    (t : MonomialArtin k S) (ht : t ∈ TraceSubmodule k S) :
    coeffAt (k := k) S ⟨e.generator, heS⟩ t = 0 := by
  rw [trace_eq_span_rootTraceValueSet] at ht
  let Z : Submodule (MonomialArtin k S) (MonomialArtin k S) := {
    carrier := {v | constantCoeff (k := k) S hS v = 0 ∧
      coeffAt (k := k) S ⟨e.generator, heS⟩ v = 0}
    zero_mem' := by simp
    add_mem' := by
      rintro x y ⟨hx0, hxe⟩ ⟨hy0, hye⟩
      constructor
      · rw [map_add, hx0, hy0, add_zero]
      · rw [map_add, hxe, hye, add_zero]
    smul_mem' := by
      rintro u v ⟨hv0, hve⟩
      constructor
      · simpa [smul_eq_mul, constantCoeff_mul (k := k) S hS hdom] using
          congrArg (fun z : k ↦ constantCoeff (k := k) S hS u * z) hv0
      · simpa [smul_eq_mul] using
          coeffAt_mul_eq_zero_of_right (k := k) S hS hdom e heS u v hv0 hve
  }
  have hrootZ : rootTraceValueSet k S ⊆ Z := by
    rintro v ⟨F, s, hs, rfl⟩
    exact ⟨rootTraceValue_constantCoeff_eq_zero (k := k) S hS hcard hanti F s hs,
      hroot F s hs⟩
  have hspanZ : Submodule.span (MonomialArtin k S) (rootTraceValueSet k S) ≤ Z :=
    Submodule.span_le.2 hrootZ
  exact (hspanZ ht).2

/-- A trace occurrence of a live variable has a selected-root image with a
nonzero coefficient in that variable.
@isnad1 id=ex.6h6v.s10.bf7976d3990d from=translated src=- shape=8e5c5c85 vocab=d6fd7acd
-/
theorem exists_root_image_with_variable_coeff_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (e : Direction)
    (heS : e.generator ∈ standardFinset S)
    (htrace : X (k := k) S e.generator heS ∈ TraceSubmodule k S) :
    ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S ⟨e.generator, heS⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hz := coeffAt_variable_eq_zero_of_trace (k := k) S hS hcard hanti
    hdom e heS hn _ htrace
  have hone : coeffAt (k := k) S ⟨e.generator, heS⟩
      (X (k := k) S e.generator heS) = 1 := by
    simpa using coeffAt_X (k := k) S
      (⟨e.generator, heS⟩ : MonomialIndex S) ⟨e.generator, heS⟩
  rw [hone] at hz
  exact one_ne_zero hz

/--
@isnad1 id=ex.6h5v.s10.8a04d8bbeac1 from=translated src=- shape=b75e998c vocab=999cd311
-/
theorem exists_root_image_with_x_coeff_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.xGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.1) ∈ TraceSubmodule k S) :
    ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.xGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0 :=
  exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS hcard
    hanti hdom .x _ htrace

/--
@isnad1 id=ex.6h5v.s10.72b5aebc10c8 from=translated src=- shape=b75e998c vocab=3fee175b
-/
theorem exists_root_image_with_y_coeff_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.yGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.1) ∈ TraceSubmodule k S) :
    ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.yGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.2.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0 :=
  exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS hcard
    hanti hdom .y _ htrace

/--
@isnad1 id=ex.6h5v.s10.c5b80a6cbf1f from=translated src=- shape=b75e998c vocab=3fee175b
-/
theorem exists_root_image_with_z_coeff_of_mem_trace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S)
    (htrace : X (k := k) S Normal.zGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1) ∈ TraceSubmodule k S) :
    ∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.zGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0 :=
  exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS hcard
    hanti hdom .z _ htrace

/-- The three live variable basis vectors lie in the ordinary trace.-/
def VariablesInTrace (k : Type*) [Field k] (S : Finset (Normal a b c))
    (hlive : IsLiveTie S) : Prop :=
  X (k := k) S Normal.xGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.1) ∈ TraceSubmodule k S ∧
  X (k := k) S Normal.yGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.1) ∈ TraceSubmodule k S ∧
  X (k := k) S Normal.zGenerator
      ((mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1) ∈ TraceSubmodule k S

/-- Separate map/root witnesses sourcing the x, y, and z coefficients.-/
def VariableTraceSources (k : Type*) [Field k] (S : Finset (Normal a b c))
    (hlive : IsLiveTie S) : Prop :=
  (∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.xGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0) ∧
  (∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.yGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.2.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0) ∧
  (∃ (F : Omega k S →ₗ[MonomialArtin k S] MonomialArtin k S)
      (s : Normal a b c) (hs : s ∈ S),
      coeffAt (k := k) S
        ⟨Normal.zGenerator, (mem_standardFinset_iff_standardSet S _).2 hlive.2.2.1⟩
        (F (U (k := k) S (rootIndex S s hs))) ≠ 0)

/--
@isnad1 id=variable.6h5v.s6.75b874958795 from=translated src=- shape=7f07e35c vocab=cc716e6c
-/
theorem variableTraceSources_of_variablesInTrace
    (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : IsRootAntichain S)
    (hdom : IsLiveParameterDomain a b c) (hlive : IsLiveTie S) :
    VariablesInTrace k S hlive → VariableTraceSources k S hlive := by
  rintro ⟨hx, hy, hz⟩
  exact ⟨exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      hcard hanti hdom .x _ hx,
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      hcard hanti hdom .y _ hy,
    exists_root_image_with_variable_coeff_of_mem_trace (k := k) S hS
      hcard hanti hdom .z _ hz⟩

end

end P23.Artin
