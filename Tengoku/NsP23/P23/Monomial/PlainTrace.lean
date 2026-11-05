import Tengoku.NsP23.P23.Monomial.PlainCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Trace foundation in the direct finite monomial model

The trace below is the ordinary sum of the ranges of all `A`-linear maps
`PlainOmega →ₗ[A] A`.  Its root-image description is proved afterwards from the
Run29 root-dual generation theorem.
-/

namespace P23.Monomial

noncomputable section

variable {k : Type*} [Field k]

/-- The ordinary module trace: the sum of the ranges of all `A`-linear maps
from the canonical dual to the algebra.-/
def PlainTraceSubmodule (k : Type*) [Field k] (S : Finset PlainExp) :
    Submodule (PlainMonomialArtin k S) (PlainMonomialArtin k S) :=
  ⨆ F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S, F.range

/-- Values of arbitrary canonical-dual maps.-/
def plainTraceValueSet (k : Type*) [Field k] (S : Finset PlainExp) :
    Set (PlainMonomialArtin k S) :=
  {v | ∃ (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S)
      (φ : PlainOmega k S), F φ = v}

/-- Values of arbitrary canonical-dual maps on selected-root duals.-/
def plainRootTraceValueSet (k : Type*) [Field k] (S : Finset PlainExp) :
    Set (PlainMonomialArtin k S) :=
  {v | ∃ (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S)
      (s : PlainExp) (hs : s ∈ S),
      F (PU (k := k) S (plainRootIndex S s hs)) = v}

theorem plainTrace_range_le (S : Finset PlainExp)
    (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S) :
    F.range ≤ PlainTraceSubmodule k S :=
  le_iSup (fun G : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S ↦ G.range) F

theorem plainTrace_eq_span_plainTraceValueSet (S : Finset PlainExp) :
    PlainTraceSubmodule k S =
      Submodule.span (PlainMonomialArtin k S) (plainTraceValueSet k S) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro F
    rintro v ⟨φ, rfl⟩
    exact Submodule.subset_span ⟨F, φ, rfl⟩
  · apply Submodule.span_le.2
    rintro v ⟨F, φ, rfl⟩
    exact plainTrace_range_le (k := k) S F ⟨φ, rfl⟩

/-- The ordinary trace equals the `A`-span of images of the selected-root
duals.  This is a theorem, not the definition of trace.-/
theorem plainTrace_eq_span_rootTraceValueSet (S : Finset PlainExp) :
    PlainTraceSubmodule k S =
      Submodule.span (PlainMonomialArtin k S) (plainRootTraceValueSet k S) := by
  rw [plainTrace_eq_span_plainTraceValueSet]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro v ⟨F, φ, rfl⟩
    have hφ : φ ∈ Submodule.span (PlainMonomialArtin k S) (plainRootDualSet k S) := by
      rw [plainRootDual_span_eq_top]
      trivial
    refine Submodule.span_induction
      (p := fun ψ _ ↦ F ψ ∈
        Submodule.span (PlainMonomialArtin k S) (plainRootTraceValueSet k S))
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
    exact ⟨F, PU (k := k) S (plainRootIndex S s hs), rfl⟩

/-- Each selected-root image has zero degree-zero coefficient in type greater
than one.  The proof uses a second incomparable root and exact coefficient
transport; it is specific to the direct finite model.-/
theorem plainRootTraceValue_constantCoeff_eq_zero (S : Finset PlainExp)
    (hS : S.Nonempty) (hcard : 2 ≤ S.card) (hanti : PlainRootAntichain S)
    (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S)
    (s : PlainExp) (hs : s ∈ S) :
    plainConstantCoeff (k := k) S hS
        (F (PU (k := k) S (plainRootIndex S s hs))) = 0 := by
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
  let ri := plainRootIndex S r hr
  let si := plainRootIndex S s hs
  have hndiv : ¬plainDivides r s := fun hd => hrs (hanti r hr s hs hd)
  have hann : PX (k := k) S ri.1 ri.2 • PU (k := k) S si = 0 :=
    (PX_smul_plainRootDual_eq_zero_iff (k := k) S s hs ri).2 (by
      change ¬plainDivides r s
      exact hndiv)
  have hzero : PX (k := k) S ri.1 ri.2 * F (PU (k := k) S si) = 0 := by
    calc
      PX (k := k) S ri.1 ri.2 * F (PU (k := k) S si) =
          PX (k := k) S ri.1 ri.2 • F (PU (k := k) S si) := by
            simp [smul_eq_mul]
      _ = F (PX (k := k) S ri.1 ri.2 • PU (k := k) S si) := by
            symm
            exact F.map_smul _ _
      _ = 0 := by rw [hann]; simp
  have hc := congrArg (plainCoeffAt (k := k) S ri) hzero
  rw [plainCoeffAt_PX_mul (k := k) S ri (plainUnitIndex S hS) ri] at hc
  · simpa [plainConstantCoeff, si] using hc
  · simp [plainUnitIndex]

/-- If every selected-root image has zero coefficient in a live variable,
then every trace element has zero coefficient there.-/
theorem plain_variable_coeff_eq_zero_of_trace
    (S : Finset PlainExp) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : PlainRootAntichain S)
    (e : Fin 3)
    (heS : plainUnitVector e ∈ plainStandardFinset S)
    (hroot : ∀ (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S)
      (s : PlainExp) (hs : s ∈ S),
      plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩
        (F (PU (k := k) S (plainRootIndex S s hs))) = 0)
    (t : PlainMonomialArtin k S) (ht : t ∈ PlainTraceSubmodule k S) :
    plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩ t = 0 := by
  rw [plainTrace_eq_span_rootTraceValueSet] at ht
  let Z : Submodule (PlainMonomialArtin k S) (PlainMonomialArtin k S) := {
    carrier := {v | plainConstantCoeff (k := k) S hS v = 0 ∧
      plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩ v = 0}
    zero_mem' := by simp
    add_mem' := by
      rintro x y ⟨hx0, hxe⟩ ⟨hy0, hye⟩
      constructor
      · rw [map_add, hx0, hy0, add_zero]
      · rw [map_add, hxe, hye, add_zero]
    smul_mem' := by
      rintro u v ⟨hv0, hve⟩
      constructor
      · simpa [smul_eq_mul, plainConstantCoeff_mul (k := k) S hS] using
          congrArg (fun z : k ↦ plainConstantCoeff (k := k) S hS u * z) hv0
      · simpa [smul_eq_mul] using
          plainCoeffAt_mul_eq_zero_of_right (k := k) S hS e heS u v hv0 hve
  }
  have hrootZ : plainRootTraceValueSet k S ⊆ Z := by
    rintro v ⟨F, s, hs, rfl⟩
    exact ⟨plainRootTraceValue_constantCoeff_eq_zero (k := k) S hS hcard hanti F s hs,
      hroot F s hs⟩
  have hspanZ : Submodule.span (PlainMonomialArtin k S) (plainRootTraceValueSet k S) ≤ Z :=
    Submodule.span_le.2 hrootZ
  exact (hspanZ ht).2

/-- A trace occurrence of a live variable has a selected-root image with a
nonzero coefficient in that variable.-/
theorem plain_exists_root_image_with_variable_coeff_of_mem_trace
    (S : Finset PlainExp) (hS : S.Nonempty)
    (hcard : 2 ≤ S.card) (hanti : PlainRootAntichain S)
    (e : Fin 3)
    (heS : plainUnitVector e ∈ plainStandardFinset S)
    (htrace : PX (k := k) S (plainUnitVector e) heS ∈ PlainTraceSubmodule k S) :
    ∃ (F : PlainOmega k S →ₗ[PlainMonomialArtin k S] PlainMonomialArtin k S)
      (s : PlainExp) (hs : s ∈ S),
      plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩
        (F (PU (k := k) S (plainRootIndex S s hs))) ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hz := plain_variable_coeff_eq_zero_of_trace (k := k) S hS hcard hanti
    e heS hn _ htrace
  have hone : plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩
      (PX (k := k) S (plainUnitVector e) heS) = 1 := by
    simpa using plainCoeffAt_PX (k := k) S
      (⟨plainUnitVector e, heS⟩ : PlainMonomialIndex S) ⟨plainUnitVector e, heS⟩
  rw [hone] at hz
  exact one_ne_zero hz

end
end P23.Monomial
