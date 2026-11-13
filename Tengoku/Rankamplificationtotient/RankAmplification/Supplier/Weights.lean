import Tengoku.Rankamplificationtotient.RankAmplification.Supplier.Definitions
import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Exact supplier weights This module proves the finite combinatorial content behind Lemmas 10.7 and 10.9. -/

namespace RankAmplification

noncomputable instance LabelPartition.fintypeForWeights (J : ℕ) :
    Fintype (LabelPartition J) :=
  Fintype.ofFinite _

noncomputable instance SupplierDescriptor.fintypeForWeights
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)} :
    Fintype (SupplierDescriptor P x B) :=
  Fintype.ofFinite _

/-! ## Reindexing the numerical weights -/

/--
@isnad1 id=eq.0h6v.s6.30144547de2e from=translated src=- shape=5edb3af1 vocab=9a8fed87
-/
theorem supplierWeight_eq_fiberCard {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x d : ℕ) :
    supplierWeight P x d =
      ((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor = d).card := by
  rfl

/--
@isnad1 id=iff.0h6v.s5.692e894b1f7d from=translated src=- shape=3b644970 vocab=96310390
-/
theorem supplierWeight_pos_iff_mem_support {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x d : ℕ) :
    0 < supplierWeight P x d ↔ d ∈ supplierDivisorSupport P x := by
  classical
  change 0 < ((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor = d).card ↔
    d ∈ (allSupplierSystems P x).image SupplierSystem.selectedDivisor
  rw [Finset.card_pos]
  constructor
  · rintro ⟨s, hs⟩
    exact Finset.mem_image.mpr ⟨s, (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩
  · intro h
    obtain ⟨s, hs, hsd⟩ := Finset.mem_image.mp h
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, hsd⟩⟩

/--
@isnad1 id=mem.0h6v.s5.1aa06b50fd7f from=translated src=- shape=f611bc20 vocab=93610111
-/
theorem mem_allSupplierSystems {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) :
    s ∈ allSupplierSystems P x := by
  classical
  unfold allSupplierSystems
  simp

/--
@isnad1 id=eq.1h6v.s6.e40c5864de19 from=translated src=- shape=ab5c8b14 vocab=09230739
-/
theorem supplierDivisorWeight_eq_dividingSystemCard {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    supplierDivisorWeight P x N =
      ((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor ∣ N).card := by
  classical
  unfold supplierDivisorWeight supplierWeight
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext s
  simp [Nat.mem_divisors, hN]

/--
@isnad1 id=le.2h7v.s5.b751da30addb from=translated src=- shape=1a532e08 vocab=3993f720
-/
theorem one_le_supplierDivisorWeight_of_system {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} (s : SupplierSystem P x)
    (hN : N ≠ 0) (hdvd : s.selectedDivisor ∣ N) :
    1 ≤ supplierDivisorWeight P x N := by
  rw [supplierDivisorWeight_eq_dividingSystemCard P x N hN]
  exact Finset.card_pos.mpr
    ⟨s, Finset.mem_filter.mpr ⟨mem_allSupplierSystems s, hdvd⟩⟩

/-- The coverage conclusion of Lemma 10.7 from an explicit realization certificate.
@isnad1 id=le.1h8v.s5.2ff5cb9fe48d from=translated src=- shape=da5ce16a vocab=46e7ff0b
-/
theorem one_le_supplierDivisorWeight_of_realization {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} {s : SupplierSystem P x}
    (R : SupplierRealization (N := N) s) (hN : N ≠ 0) :
    1 ≤ supplierDivisorWeight P x N :=
  one_le_supplierDivisorWeight_of_system s hN R.systemSelectedDivisor_dvd

private theorem reciprocal_fiber_sum {α : Type*} [DecidableEq α]
    (S : Finset α) (g : α → ℕ) :
    (∑ d ∈ S.image g, ((S.filter fun a ↦ g a = d).card : ℚ) / d) =
      ∑ a ∈ S, 1 / (g a : ℚ) := by
  classical
  calc
    (∑ d ∈ S.image g, ((S.filter fun a ↦ g a = d).card : ℚ) / d) =
        ∑ d ∈ S.image g, ∑ a ∈ S.filter (fun a ↦ g a = d), 1 / (g a : ℚ) := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        (((S.filter fun a ↦ g a = d).card : ℚ) / d) =
            ∑ _a ∈ S.filter (fun a ↦ g a = d), 1 / (d : ℚ) := by
          simp [div_eq_mul_inv]
        _ = ∑ a ∈ S.filter (fun a ↦ g a = d), 1 / (g a : ℚ) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
    _ = ∑ a ∈ S, 1 / (g a : ℚ) :=
      Finset.sum_fiberwise_of_maps_to
        (fun a ha ↦ Finset.mem_image.mpr ⟨a, ha, rfl⟩) (fun a ↦ 1 / (g a : ℚ))

/--
@isnad1 id=eq.0h5v.s4.18caed166954 from=translated src=- shape=d4ac095d vocab=48dd58e9
-/
theorem supplierReciprocalMass_eq_systemMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    supplierReciprocalMass P x = supplierSystemReciprocalMass P x := by
  classical
  unfold supplierReciprocalMass supplierDivisorSupport supplierWeight
    supplierSystemReciprocalMass
  exact reciprocal_fiber_sum (allSupplierSystems P x) SupplierSystem.selectedDivisor

/-! ## Exact block-mass upper bound -/

/-- The reciprocal mass of all admissible descriptors for one fixed block.-/
noncomputable def descriptorReciprocalMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) (B : Finset (Fin J)) : ℚ :=
  ∑ d : SupplierDescriptor P x B, 1 / (d.selectedDivisor : ℚ)

/-- The product of independent descriptor masses for a fixed partition.-/
noncomputable def partitionDescriptorMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) (π : LabelPartition J) : ℚ :=
  ∏ B : π.Block, descriptorReciprocalMass P x B.1

/-- A partition together with arbitrary descriptors, before imposing distinct source bases.-/
abbrev RelaxedSupplierData {J y Y : ℕ} (P : LabelledPrimeDemands J y Y) (x : ℕ) :=
  Σ π : LabelPartition J, (B : π.Block) → SupplierDescriptor P x B.1

/-- Product reciprocal weight attached to relaxed block descriptors.-/
noncomputable def RelaxedSupplierData.reciprocalWeight
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (a : RelaxedSupplierData P x) : ℚ :=
  ∏ B : a.1.Block, 1 / ((a.2 B).selectedDivisor : ℚ)

/-- Total reciprocal mass of all relaxed supplier data.-/
noncomputable def relaxedSupplierReciprocalMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) : ℚ :=
  ∑ a : RelaxedSupplierData P x, a.reciprocalWeight

/-- Forget the distinct-base constraints of a supplier system.-/
def SupplierSystem.toRelaxedData {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) : RelaxedSupplierData P x :=
  ⟨s.partition, s.descriptor⟩

/--
@isnad1 id=injectiv.0h5v.s5.1205b8a06f86 from=translated src=- shape=8daa7dd7 vocab=d10e2487
-/
theorem SupplierSystem.toRelaxedData_injective {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} :
    Function.Injective (SupplierSystem.toRelaxedData :
      SupplierSystem P x → RelaxedSupplierData P x) := by
  intro s t h
  cases s
  cases t
  cases h
  rfl

/--
@isnad1 id=eq.0h6v.s5.b0c56e4801ef from=translated src=- shape=b2cf0157 vocab=b74921fb
-/
theorem SupplierSystem.reciprocalWeight_toRelaxedData {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.toRelaxedData.reciprocalWeight = 1 / (s.selectedDivisor : ℚ) := by
  classical
  change (∏ B : s.partition.Block, 1 / ((s.descriptor B).selectedDivisor : ℚ)) =
    1 / (s.selectedDivisor : ℚ)
  simp only [SupplierSystem.selectedDivisor, Nat.cast_prod, one_div]
  exact Finset.prod_inv_distrib fun B : s.partition.Block ↦
    ((s.descriptor B).selectedDivisor : ℚ)

set_option maxHeartbeats 800000 in
/--
@isnad1 id=eq.0h5v.s5.0930b81ecee4 from=translated src=- shape=c5999433 vocab=62b575af
-/
theorem relaxedSupplierReciprocalMass_eq_partitionSum {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    relaxedSupplierReciprocalMass P x =
      ∑ π : LabelPartition J, partitionDescriptorMass P x π := by
  classical
  rw [relaxedSupplierReciprocalMass, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro π hπ
  unfold partitionDescriptorMass descriptorReciprocalMass
    RelaxedSupplierData.reciprocalWeight
  exact (Fintype.prod_sum
    (κ := fun B : π.Block ↦ SupplierDescriptor P x B.1)
    fun (B : π.Block) (d : SupplierDescriptor P x B.1) ↦
      1 / (d.selectedDivisor : ℚ)).symm

/--
@isnad1 id=le.0h5v.s5.6e50ea519a04 from=translated src=- shape=c5999433 vocab=15df7173
-/
theorem supplierReciprocalMass_le_partitionDescriptorMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    supplierReciprocalMass P x ≤
      ∑ π : LabelPartition J, partitionDescriptorMass P x π := by
  classical
  rw [supplierReciprocalMass_eq_systemMass,
    ← relaxedSupplierReciprocalMass_eq_partitionSum]
  unfold supplierSystemReciprocalMass relaxedSupplierReciprocalMass
  calc
    (∑ s ∈ allSupplierSystems P x, 1 / (s.selectedDivisor : ℚ)) =
        ∑ s ∈ allSupplierSystems P x, s.toRelaxedData.reciprocalWeight := by
      apply Finset.sum_congr rfl
      intro s hs
      exact s.reciprocalWeight_toRelaxedData.symm
    _ = ∑ a ∈ (allSupplierSystems P x).image SupplierSystem.toRelaxedData,
          a.reciprocalWeight :=
      (Finset.sum_image SupplierSystem.toRelaxedData_injective.injOn).symm
    _ ≤ ∑ a : RelaxedSupplierData P x, a.reciprocalWeight := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro a ha
        simp
      · intro a ha hnot
        unfold RelaxedSupplierData.reciprocalWeight
        exact Finset.prod_nonneg fun B hB ↦ one_div_nonneg.mpr (Nat.cast_nonneg _)

/--
@isnad1 id=le.0h6v.s5.9ce6a09a7b2e from=translated src=- shape=d63a2954 vocab=cf666afe
-/
theorem descriptorReciprocalMass_nonneg {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) (B : Finset (Fin J)) :
    0 ≤ descriptorReciprocalMass P x B := by
  unfold descriptorReciprocalMass
  exact Finset.sum_nonneg fun d hd ↦ one_div_nonneg.mpr (Nat.cast_nonneg _)

/--
@isnad1 id=le.0h5v.s4.5d3f270a6bc9 from=translated src=- shape=05601c67 vocab=973ed3c2
-/
theorem supplierReciprocalMass_nonneg {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    0 ≤ supplierReciprocalMass P x := by
  unfold supplierReciprocalMass
  exact Finset.sum_nonneg fun d hd ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-! ## The exact large-divisor tail -/

/-- Reciprocal mass of supplier systems whose selected divisor exceeds `H`.-/
noncomputable def supplierSystemReciprocalTail {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) : ℚ :=
  ∑ s ∈ (allSupplierSystems P x).filter (H < ·.selectedDivisor),
    1 / (s.selectedDivisor : ℚ)

/--
@isnad1 id=eq.0h6v.s4.b366428bad1d from=translated src=- shape=a1d5184a vocab=a85253bc
-/
theorem supplierReciprocalTail_eq_systemTail {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    supplierReciprocalTail P x H = supplierSystemReciprocalTail P x H := by
  classical
  unfold supplierReciprocalTail supplierDivisorSupport supplierWeight
    supplierSystemReciprocalTail
  calc
    (∑ d ∈ ((allSupplierSystems P x).image SupplierSystem.selectedDivisor).filter (H < ·),
        (((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor = d).card : ℚ) / d) =
        ∑ d ∈ ((allSupplierSystems P x).image SupplierSystem.selectedDivisor).filter (H < ·),
          ∑ s ∈ (allSupplierSystems P x).filter (fun s ↦ s.selectedDivisor = d),
            1 / (s.selectedDivisor : ℚ) := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        ((((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor = d).card : ℚ) / d) =
            ∑ _s ∈ (allSupplierSystems P x).filter (fun s ↦ s.selectedDivisor = d),
              1 / (d : ℚ) := by simp [div_eq_mul_inv]
        _ = ∑ s ∈ (allSupplierSystems P x).filter (fun s ↦ s.selectedDivisor = d),
              1 / (s.selectedDivisor : ℚ) := by
            apply Finset.sum_congr rfl
            intro s hs
            rw [(Finset.mem_filter.mp hs).2]
    _ = ∑ s ∈ (allSupplierSystems P x).filter (H < ·.selectedDivisor),
          1 / (s.selectedDivisor : ℚ) := by
      rw [Finset.sum_fiberwise_eq_sum_filter]
      apply Finset.sum_congr
      · ext s
        simp [allSupplierSystems]
      · intro s hs
        rfl

/--
@isnad1 id=le.0h6v.s4.2c331de56e4d from=translated src=- shape=68982eb5 vocab=2685cc15
-/
theorem supplierReciprocalTail_nonneg {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    0 ≤ supplierReciprocalTail P x H := by
  unfold supplierReciprocalTail
  exact Finset.sum_nonneg fun d hd ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/--
@isnad1 id=le.0h6v.s4.88bdfe274f6a from=translated src=- shape=56aff6dd vocab=06defab9
-/
theorem supplierReciprocalTail_le_mass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    supplierReciprocalTail P x H ≤ supplierReciprocalMass P x := by
  classical
  rw [supplierReciprocalTail_eq_systemTail, supplierReciprocalMass_eq_systemMass]
  unfold supplierSystemReciprocalTail supplierSystemReciprocalMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    exact (Finset.mem_filter.mp hs).1
  · intro s hs hnot
    exact one_div_nonneg.mpr (Nat.cast_nonneg _)

/--
@isnad1 id=le.0h6v.s5.3548800e1adb from=translated src=- shape=de9e02ea vocab=d908a4c4
-/
theorem supplierReciprocalTail_le_partitionDescriptorMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    supplierReciprocalTail P x H ≤
      ∑ π : LabelPartition J, partitionDescriptorMass P x π :=
  (supplierReciprocalTail_le_mass P x H).trans
    (supplierReciprocalMass_le_partitionDescriptorMass P x)

/-- A genuinely `H`-dependent finite tail estimate, requiring no distributional input.
@isnad1 id=le.0h6v.s6.1dd485bde925 from=translated src=- shape=9739c47a vocab=49f2b909
-/
theorem supplierReciprocalTail_le_systemCount_div {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    supplierReciprocalTail P x H ≤
      (Fintype.card (SupplierSystem P x) : ℚ) / (H + 1) := by
  classical
  rw [supplierReciprocalTail_eq_systemTail]
  unfold supplierSystemReciprocalTail
  calc
    (∑ s ∈ (allSupplierSystems P x).filter (H < ·.selectedDivisor),
        1 / (s.selectedDivisor : ℚ)) ≤
        ∑ _s ∈ (allSupplierSystems P x).filter (H < ·.selectedDivisor),
          1 / ((H + 1 : ℕ) : ℚ) := by
      apply Finset.sum_le_sum
      intro s hs
      apply one_div_le_one_div_of_le (by positivity)
      exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_filter.mp hs).2
    _ = (((allSupplierSystems P x).filter (H < ·.selectedDivisor)).card : ℚ) /
          (H + 1) := by
      simp [div_eq_mul_inv]
    _ ≤ ((allSupplierSystems P x).card : ℚ) / (H + 1) := by
      gcongr
      exact Finset.filter_subset _ _
    _ = (Fintype.card (SupplierSystem P x) : ℚ) / (H + 1) := by
      simp [allSupplierSystems]

/--
@isnad1 id=le.0h6v.s8.1d082387d29f from=translated src=- shape=9739c47a vocab=37f90559
-/
theorem supplierReciprocalTail_le_relaxedSystemCount_div {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x H : ℕ) :
    supplierReciprocalTail P x H ≤
      (Fintype.card (RelaxedSupplierData P x) : ℚ) / (H + 1) := by
  refine (supplierReciprocalTail_le_systemCount_div P x H).trans ?_
  gcongr
  exact_mod_cast Fintype.card_le_of_injective
    (SupplierSystem.toRelaxedData : SupplierSystem P x → RelaxedSupplierData P x)
    SupplierSystem.toRelaxedData_injective

/-! ## Exact occurrence-count bound for the pointwise weight -/

/-- Source bases which divide `N` and support at least one admissible nonempty labelled block.-/
noncomputable def admissibleSourceOccurrenceBases {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) : Finset ℕ :=
  N.primeFactors.filter fun q ↦
    ∃ B : Finset (Fin J), B.Nonempty ∧
      ∃ d : SupplierDescriptor P x B, d.base = q

/-- The exact finite occurrence count used in the pointwise multiplicity bound.-/
noncomputable def admissibleSourceOccurrenceCount {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) : ℕ :=
  (admissibleSourceOccurrenceBases P x N).card

/-- The exact number of set partitions of the labelled index type.-/
noncomputable def labelledPartitionCount (J : ℕ) : ℕ :=
  Fintype.card (LabelPartition J)

/--
@isnad1 id=le.0h6v.s4.1a8d99b232ef from=translated src=- shape=1fadf3b9 vocab=4e7ca376
-/
theorem admissibleSourceOccurrenceCount_le_primeFactors {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) :
    admissibleSourceOccurrenceCount P x N ≤ N.primeFactors.card := by
  unfold admissibleSourceOccurrenceCount admissibleSourceOccurrenceBases
  exact Finset.card_filter_le _ _

/--
@isnad1 id=lt.1h7v.s5.27a3519fc79c from=translated src=- shape=5d697f7a vocab=b4654b94
-/
theorem admissibleSourceOccurrenceBase_gt_lowerCutoff {J y Y q : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    (hq : q ∈ admissibleSourceOccurrenceBases P x N) :
    y < q := by
  obtain ⟨B, hB, d, rfl⟩ := (Finset.mem_filter.mp hq).2
  exact d.base_gt_lowerCutoff hB

/-- The elementary product bound behind any logarithmic estimate for the occurrence count.
@isnad1 id=le.1h6v.s5.e3e9ad1b27fa from=translated src=- shape=13824005 vocab=328cfbbe
-/
theorem cutoffSucc_pow_admissibleSourceOccurrenceCount_le {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    (y + 1) ^ admissibleSourceOccurrenceCount P x N ≤ N := by
  classical
  let sources := admissibleSourceOccurrenceBases P x N
  have hsources : sources ⊆ N.primeFactors := by
    intro q hq
    exact (Finset.mem_filter.mp hq).1
  have hprodDvd : (∏ q ∈ sources, q) ∣ N :=
    (Finset.prod_dvd_prod_of_subset sources N.primeFactors id hsources).trans
      (Nat.prod_primeFactors_dvd N)
  calc
    (y + 1) ^ admissibleSourceOccurrenceCount P x N =
        ∏ _q ∈ sources, (y + 1) := by
      simp [sources, admissibleSourceOccurrenceCount]
    _ ≤ ∏ q ∈ sources, q := by
      apply Finset.prod_le_prod
      · exact fun q hq ↦ Nat.zero_le _
      · intro q hq
        exact Nat.succ_le_iff.mpr
          (admissibleSourceOccurrenceBase_gt_lowerCutoff (P := P) (x := x) (N := N) hq)
    _ ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hprodDvd

/-- An explicit replacement for the paper's informal relation `y = exp T`: the integer cutoff contains the exponential scale when `exp T ≤ y + 1`.-/
def HasExponentialCutoffScale (y : ℕ) (T : ℝ) : Prop :=
  Real.exp T ≤ (y + 1 : ℕ)

/--
@isnad1 id=le.2h7v.s5.ab0b1ee6a038 from=translated src=- shape=1931a036 vocab=6da41275
-/
theorem exp_occurrenceCount_mul_le_ambient {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) {T : ℝ} (hN : N ≠ 0)
    (hscale : HasExponentialCutoffScale y T) :
    Real.exp ((admissibleSourceOccurrenceCount P x N : ℝ) * T) ≤ N := by
  rw [Real.exp_nat_mul]
  calc
    Real.exp T ^ admissibleSourceOccurrenceCount P x N ≤
        ((y + 1 : ℕ) : ℝ) ^ admissibleSourceOccurrenceCount P x N := by
      gcongr
      simpa [HasExponentialCutoffScale] using hscale
    _ ≤ (N : ℝ) := by
      exact_mod_cast cutoffSucc_pow_admissibleSourceOccurrenceCount_le P x N hN

/--
@isnad1 id=le.4h7v.s6.d7d998c2de63 from=translated src=- shape=13df2399 vocab=75f8ea0e
-/
theorem occurrenceCount_le_log_two_mul_div_scale {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) {T : ℝ}
    (hN : 0 < N) (hNx : N ≤ 2 * x) (hT : 0 < T)
    (hscale : HasExponentialCutoffScale y T) :
    (admissibleSourceOccurrenceCount P x N : ℝ) ≤ Real.log (2 * x) / T := by
  apply (le_div_iff₀ hT).mpr
  calc
    (admissibleSourceOccurrenceCount P x N : ℝ) * T ≤ Real.log N :=
      (Real.le_log_iff_exp_le (by positivity)).mpr
        (exp_occurrenceCount_mul_le_ambient P x N hN.ne' hscale)
    _ ≤ Real.log (2 * x) := by
      apply Real.log_le_log
      · positivity
      · exact_mod_cast hNx

private theorem SupplierSystem.descriptorBase_mem_admissibleSourceOccurrenceBases
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    (s : SupplierSystem P x) (hN : N ≠ 0) (hdvd : s.selectedDivisor ∣ N)
    (B : s.partition.Block) :
    (s.descriptor B).base ∈ admissibleSourceOccurrenceBases P x N := by
  classical
  apply Finset.mem_filter.mpr
  constructor
  · apply Nat.mem_primeFactors.mpr
    exact ⟨(s.descriptor B).base_prime, (s.descriptor_base_dvd B).trans hdvd, hN⟩
  · exact ⟨B.1, s.partition.block_nonempty B, s.descriptor B, rfl⟩

/-- Supplier systems whose selected divisor divides the ambient integer.-/
abbrev DividingSupplierSystem {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) :=
  {s : SupplierSystem P x // s.selectedDivisor ∣ N}

/-- Partition and per-label source-base code for a dividing supplier system.-/
noncomputable def DividingSupplierSystem.labelBaseCode
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ} (hN : N ≠ 0)
    (s : DividingSupplierSystem P x N) :
    LabelPartition J ×
      (Fin J → {q // q ∈ admissibleSourceOccurrenceBases P x N}) :=
  ⟨s.1.partition, fun i ↦
    ⟨(s.1.descriptor (s.1.partition.blockOf i)).base,
      s.1.descriptorBase_mem_admissibleSourceOccurrenceBases hN s.2
        (s.1.partition.blockOf i)⟩⟩

/--
@isnad1 id=injectiv.1h6v.s6.e05c76d4ce03 from=translated src=- shape=e42000fb vocab=0e810263
-/
theorem DividingSupplierSystem.labelBaseCode_injective
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ} (hN : N ≠ 0) :
    Function.Injective (DividingSupplierSystem.labelBaseCode (P := P) (x := x) hN) := by
  rintro ⟨⟨π, descriptor, bases_injective⟩, hdvd⟩
    ⟨⟨ρ, otherDescriptor, otherBases_injective⟩, otherDvd⟩ hcode
  have hpartition : π = ρ := congrArg Prod.fst hcode
  have hfunctions := congrArg Prod.snd hcode
  dsimp [labelBaseCode] at hpartition hfunctions
  cases hpartition
  apply Subtype.ext
  dsimp
  have hdescriptor : descriptor = otherDescriptor := by
    funext B
    apply SupplierDescriptor.eq_of_base_eq
    obtain ⟨i, hi⟩ := π.block_nonempty B
    have hiCode := congrArg Subtype.val (congrFun hfunctions i)
    have hblock : π.blockOf i = B := π.block_eq_of_mem i B hi
    exact (congrArg (fun C ↦ (descriptor C).base) hblock).symm.trans <|
      hiCode.trans (congrArg (fun C ↦ (otherDescriptor C).base) hblock)
  cases hdescriptor
  rfl

/--
@isnad1 id=le.1h6v.s5.0dbe7996f19a from=translated src=- shape=0ff0aa02 vocab=b1fa0453
-/
theorem supplierDivisorWeight_le_partitionCount_mul_occurrenceCount_pow {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    supplierDivisorWeight P x N ≤
      labelledPartitionCount J * admissibleSourceOccurrenceCount P x N ^ J := by
  classical
  rw [supplierDivisorWeight_eq_dividingSystemCard P x N hN]
  have hcard := Fintype.card_le_of_injective
    (DividingSupplierSystem.labelBaseCode (P := P) (x := x) hN)
    (DividingSupplierSystem.labelBaseCode_injective (P := P) (x := x) hN)
  have hfilterCard :
      ((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor ∣ N).card =
        Fintype.card (DividingSupplierSystem P x N) := by
    let dividingSystems :=
      (allSupplierSystems P x).filter fun s ↦ s.selectedDivisor ∣ N
    let e : {s // s ∈ dividingSystems} ≃ DividingSupplierSystem P x N :=
      { toFun := fun s ↦ ⟨s.1, (Finset.mem_filter.mp s.2).2⟩
        invFun := fun s ↦ ⟨s.1, Finset.mem_filter.mpr ⟨mem_allSupplierSystems s.1, s.2⟩⟩
        left_inv := fun s ↦ by rfl
        right_inv := fun s ↦ by rfl }
    exact (Fintype.card_coe dividingSystems).symm.trans (Fintype.card_congr e)
  rw [hfilterCard]
  simpa [labelledPartitionCount, admissibleSourceOccurrenceCount] using hcard

/-- The paper's `max(1, W)^J` presentation of the same pointwise multiplicity estimate.
@isnad1 id=le.1h6v.s6.af3ebda03b86 from=translated src=- shape=1c1466a3 vocab=813e5a0b
-/
theorem supplierDivisorWeight_le_partitionCount_mul_maxOccurrenceCount_pow {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x N : ℕ) (hN : N ≠ 0) :
    supplierDivisorWeight P x N ≤
      labelledPartitionCount J * max 1 (admissibleSourceOccurrenceCount P x N) ^ J := by
  refine (supplierDivisorWeight_le_partitionCount_mul_occurrenceCount_pow P x N hN).trans ?_
  gcongr
  exact le_max_right _ _

end RankAmplification
