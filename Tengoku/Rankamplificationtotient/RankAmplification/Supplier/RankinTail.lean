import Tengoku.Rankamplificationtotient.RankAmplification.Supplier.Convolution
import Tengoku.Rankamplificationtotient.RankAmplification.Rankin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Supplier tails and finite Rankin encoding This module proves the finite combinatorial bridge used in the large-source estimates. -/

namespace RankAmplification

open Finset

noncomputable section

/-! ## Elementary smoothness and finite-fibre lemmas -/

theorem isSmooth_of_largestPrimeFactor_le {Y n : ℕ} (hn : n ≠ 0)
    (hlarge : largestPrimeFactor n ≤ Y) :
    IsSmooth Y n := by
  refine ⟨hn, ?_⟩
  intro p hp
  exact (Finset.le_sup (f := id) hp).trans
    ((le_max_right 1 ((primeSupport n).sup id)).trans hlarge)

theorem isSmooth_mul {Y m n : ℕ} (hm : IsSmooth Y m) (hn : IsSmooth Y n) :
    IsSmooth Y (m * n) := by
  refine ⟨Nat.mul_ne_zero hm.1 hn.1, ?_⟩
  intro p hp
  change p ∈ (m * n).primeFactors at hp
  rw [Nat.primeFactors_mul hm.1 hn.1] at hp
  exact (Finset.mem_union.mp hp).elim (hm.2 p) (hn.2 p)

theorem isSmooth_finset_prod {Y : ℕ} { α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (hf : ∀ a ∈ S, IsSmooth Y (f a)) :
    IsSmooth Y (∏ a ∈ S, f a) := by
  induction S using Finset.induction_on with
  | empty => simp [IsSmooth]
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha]
      exact isSmooth_mul (hf a (Finset.mem_insert_self a S))
        (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))

theorem one_le_orderedDivisorCount_two {m : ℕ} (hm : m ≠ 0) :
    1 ≤ orderedDivisorCount 2 m := by
  rw [orderedDivisorCount_two]
  exact Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm⟩⟩

theorem one_le_orderedDivisorCount_of_pos_rank {j m : ℕ}
    (hj : 0 < j) (hm : m ≠ 0) :
    1 ≤ orderedDivisorCount j m := by
  induction j with
  | zero => omega
  | succ j ih =>
      by_cases hjzero : j = 0
      · subst j
        rw [orderedDivisorCount_one hm]
      · rw [orderedDivisorCount_succ]
        exact (ih (Nat.pos_of_ne_zero hjzero)).trans <|
          Finset.single_le_sum (fun d hd ↦ Nat.zero_le _)
            (Nat.mem_divisors.mpr ⟨dvd_rfl, hm⟩)

/-- A finite reciprocal-sum encoding lemma.-/
@[nolint unusedArguments]
theorem finite_reciprocal_sum_le_tau_smooth_tail
    {α : Type*} [DecidableEq α] (S : Finset α) (code denominator : α → ℕ)
    (j R H X C : ℕ)
    (hcode : ∀ a ∈ S, code a ∈ finiteSmoothTailSet R H X)
    (hdenominator : ∀ a ∈ S, code a ≤ denominator a)
    (hfibre : ∀ m ∈ finiteSmoothTailSet R H X,
      (S.filter fun a ↦ code a = m).card ≤ C * orderedDivisorCount j m) :
    (∑ a ∈ S, 1 / (denominator a : ℝ)) ≤
      C * finiteTauSmoothReciprocalTail j R H X := by
  have hreciprocal : ∀ a ∈ S,
      1 / (denominator a : ℝ) ≤ 1 / (code a : ℝ) := by
    intro a ha
    have hcodePos : 0 < code a := by
      have hmem := mem_finiteSmoothTailSet.mp (hcode a ha)
      omega
    apply one_div_le_one_div_of_le
    · exact_mod_cast hcodePos
    · exact_mod_cast hdenominator a ha
  calc
    (∑ a ∈ S, 1 / (denominator a : ℝ)) ≤
        ∑ a ∈ S, 1 / (code a : ℝ) := by
      exact Finset.sum_le_sum fun a ha ↦ hreciprocal a ha
    _ = ∑ m ∈ finiteSmoothTailSet R H X,
        ∑ a ∈ S.filter (fun a ↦ code a = m), 1 / (code a : ℝ) := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun a ha ↦ hcode a ha)
        (fun a ↦ 1 / (code a : ℝ))
    _ = ∑ m ∈ finiteSmoothTailSet R H X,
        ((S.filter fun a ↦ code a = m).card : ℝ) / m := by
      apply Finset.sum_congr rfl
      intro m hm
      calc
        (∑ a ∈ S.filter (fun a ↦ code a = m), 1 / (code a : ℝ)) =
            ∑ _a ∈ S.filter (fun a ↦ code a = m), 1 / (m : ℝ) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [(Finset.mem_filter.mp ha).2]
        _ = ((S.filter fun a ↦ code a = m).card : ℝ) / m := by
          simp [div_eq_mul_inv]
    _ ≤ ∑ m ∈ finiteSmoothTailSet R H X,
        (C * orderedDivisorCount j m : ℕ) / (m : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmPos : 0 < (m : ℝ) := by
        exact_mod_cast Nat.zero_lt_of_lt (mem_finiteSmoothTailSet.mp hm).1
      exact div_le_div_of_nonneg_right (by exact_mod_cast hfibre m hm) hmPos.le
    _ = C * finiteTauSmoothReciprocalTail j R H X := by
      unfold finiteTauSmoothReciprocalTail
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      ring

/-- The ordinary divisor-weighted smooth tail dominates any finite encoding whose fibres are bounded by a constant: `τ₂(m) ≥ 1` supplies the missing weight.-/
theorem finite_reciprocal_sum_le_card_mul_divisor_smooth_tail
    {α : Type*} [DecidableEq α] (S : Finset α) (code denominator : α → ℕ)
    (R H X C : ℕ)
    (hcode : ∀ a ∈ S, code a ∈ finiteSmoothTailSet R H X)
    (hdenominator : ∀ a ∈ S, code a ≤ denominator a)
    (hcard : S.card ≤ C) :
    (∑ a ∈ S, 1 / (denominator a : ℝ)) ≤
      C * finiteTauSmoothReciprocalTail 2 R H X := by
  apply finite_reciprocal_sum_le_tau_smooth_tail S code denominator 2 R H X C
    hcode hdenominator
  intro m hm
  calc
    (S.filter fun a ↦ code a = m).card ≤ S.card := Finset.card_filter_le _ _
    _ ≤ C := hcard
    _ = C * 1 := by simp
    _ ≤ C * orderedDivisorCount 2 m := by
      gcongr
      exact one_le_orderedDivisorCount_two
        (Nat.ne_of_gt (Nat.zero_lt_of_lt (mem_finiteSmoothTailSet.mp hm).1))

/-- Rank-sensitive form of the constant-fibre estimate.-/
theorem finite_reciprocal_sum_le_card_mul_tau_smooth_tail
    {α : Type*} [DecidableEq α] (S : Finset α) (code denominator : α → ℕ)
    (j R H X C : ℕ) (hj : 0 < j)
    (hcode : ∀ a ∈ S, code a ∈ finiteSmoothTailSet R H X)
    (hdenominator : ∀ a ∈ S, code a ≤ denominator a)
    (hcard : S.card ≤ C) :
    (∑ a ∈ S, 1 / (denominator a : ℝ)) ≤
      C * finiteTauSmoothReciprocalTail j R H X := by
  apply finite_reciprocal_sum_le_tau_smooth_tail S code denominator j R H X C
    hcode hdenominator
  intro m hm
  calc
    (S.filter fun a ↦ code a = m).card ≤ S.card := Finset.card_filter_le _ _
    _ ≤ C := hcard
    _ = C * 1 := by simp
    _ ≤ C * orderedDivisorCount j m := by
      gcongr
      exact one_le_orderedDivisorCount_of_pos_rank hj
        (Nat.ne_of_gt (Nat.zero_lt_of_lt (mem_finiteSmoothTailSet.mp hm).1))

/-- A tail-to-census inequality with an explicit reciprocal cutoff.-/
theorem finiteTauSmoothReciprocalTail_two_le_count_div (R H X : ℕ) :
    finiteTauSmoothReciprocalTail 2 R H X ≤
      finiteDivisorWeightedSmoothCount R X / (H + 1) := by
  rw [finiteTauSmoothReciprocalTail, finiteDivisorWeightedSmoothCount_eq]
  simp_rw [orderedDivisorCount_two]
  calc
    (∑ m ∈ finiteSmoothTailSet R H X, (m.divisors.card : ℝ) / m) ≤
        ∑ m ∈ finiteSmoothTailSet R H X,
          (m.divisors.card : ℝ) / (H + 1) := by
      apply Finset.sum_le_sum
      intro m hm
      apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      · positivity
      · exact_mod_cast Nat.succ_le_iff.mpr (mem_finiteSmoothTailSet.mp hm).1
    _ ≤ ∑ m ∈ finiteSmoothSet R X,
        (m.divisors.card : ℝ) / (H + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (finiteSmoothTailSet_subset R H X)
      intro m hm hnot
      positivity
    _ = (∑ m ∈ finiteSmoothSet R X, (m.divisors.card : ℝ)) / (H + 1) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.sum_mul]

/-! ## The exact finite large-prime-transfer sum -/

/-- The finite sum occurring on the left of Proposition 10.20, with a general ambient numerator `W` (the paper takes `W = 2xZ`).-/
noncomputable def finiteLargePrimeTransfer (Z W : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc Z W.sqrt).filter Nat.Prime,
    finiteDivisorWeightedSmoothCount p (W / p ^ 2)

/-- Pointwise finite Rankin applied inside the large-prime transfer sum.-/
theorem finiteLargePrimeTransfer_le_rankin {Z W : ℕ} {sigma : ℝ}
    (hsigma : 0 ≤ sigma) :
    finiteLargePrimeTransfer Z W ≤
      ∑ p ∈ (Finset.Ioc Z W.sqrt).filter Nat.Prime,
        ((W / p ^ 2 : ℕ) : ℝ) ^ sigma *
          finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m)
            p (W / p ^ 2) (-sigma) := by
  unfold finiteLargePrimeTransfer
  apply Finset.sum_le_sum
  intro p hp
  simpa only [finiteDivisorWeightedSmoothCount] using
    finiteTauSmoothCount_le_rankin (j := 2) (R := p) (X := W / p ^ 2) hsigma

/-- An unconditional elementary majorant for the finite divisor-weighted smooth census.-/
theorem finiteDivisorWeightedSmoothCount_le_square (R X : ℕ) :
    finiteDivisorWeightedSmoothCount R X ≤ (X : ℝ) ^ 2 := by
  classical
  rw [finiteDivisorWeightedSmoothCount_eq]
  have hcard : (finiteSmoothSet R X).card ≤ X := by
    unfold finiteSmoothSet
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  calc
    (∑ m ∈ finiteSmoothSet R X, (m.divisors.card : ℝ)) ≤
        ∑ _m ∈ finiteSmoothSet R X, (X : ℝ) := by
      apply Finset.sum_le_sum
      intro m hm
      exact_mod_cast (Nat.card_divisors_le_self m).trans
        (mem_finiteSmoothSet.mp hm).2.1
    _ = ((finiteSmoothSet R X).card : ℝ) * X := by simp
    _ ≤ (X : ℝ) * X := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg X)
    _ = (X : ℝ) ^ 2 := by ring

/-! ## The source split for one supplier system -/

namespace SupplierDescriptor

/-- The `q - 1` coordinate of a type-(L) source; type-(P) sources contribute padding `1`.-/
def linearPredecessor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim (fun source ↦ source.natBase - 1) (fun _ ↦ 1)

/-- The selected linear base; type-(P) sources contribute `1`.-/
def linearSelectedPart {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim LinearDescriptor.natBase (fun _ ↦ 1)

/-- The exponent retained in the type-(P) part; it is zero for type-(L) sources.-/
def powerSelectedExponent {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim (fun _ ↦ 0) (fun source ↦ powerMultiplicity P B source.natBase + 1)

/-- The selected type-(P) prime power; type-(L) sources contribute `1`.-/
def powerSelectedPart {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.base ^ d.powerSelectedExponent

@[simp]
theorem selectedDivisor_eq_linearSelectedPart_mul_powerSelectedPart
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    d.selectedDivisor = d.linearSelectedPart * d.powerSelectedPart := by
  cases d <;> simp [selectedDivisor, linearSelectedPart, powerSelectedPart,
    powerSelectedExponent, base]

theorem linearPredecessor_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    0 < d.linearPredecessor := by
  cases d with
  | inl source =>
      exact Nat.sub_pos_of_lt source.base_prime.one_lt
  | inr source => simp [linearPredecessor]

theorem linearPredecessor_smooth {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) :
    IsSmooth Y d.linearPredecessor := by
  cases d with
  | inl source =>
      exact isSmooth_of_largestPrimeFactor_le
        (Nat.ne_of_gt (Nat.sub_pos_of_lt source.base_prime.one_lt)) source.smooth
  | inr source => simp [linearPredecessor, IsSmooth]

theorem linearPredecessor_le_selectedDivisor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) :
    d.linearPredecessor ≤ d.selectedDivisor := by
  cases d with
  | inl source =>
      simp [linearPredecessor, selectedDivisor]
  | inr source =>
      exact Nat.succ_le_iff.mpr (selectedDivisor_pos (Sum.inr source))

theorem linearSelectedPart_le_two_mul_predecessor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) :
    d.linearSelectedPart ≤ 2 * d.linearPredecessor := by
  cases d with
  | inl source =>
      simp only [linearSelectedPart, linearPredecessor, Sum.elim_inl]
      have hbase : 2 ≤ source.natBase := source.base_prime.two_le
      omega
  | inr source => simp [linearSelectedPart, linearPredecessor]

theorem powerSelectedExponent_le_card_add_one {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) :
    d.powerSelectedExponent ≤ B.card + 1 := by
  cases d with
  | inl source => simp [powerSelectedExponent]
  | inr source =>
      unfold powerSelectedExponent powerMultiplicity powerLabels
      simpa only [Sum.elim_inr] using Nat.add_le_add_right (Finset.card_filter_le B _) 1

theorem powerSelectedPart_le_Y_pow {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) :
    d.powerSelectedPart ≤ Y ^ d.powerSelectedExponent := by
  cases d with
  | inl source => simp [powerSelectedPart, powerSelectedExponent]
  | inr source =>
      exact pow_le_pow_left' source.base_le _

end SupplierDescriptor

namespace LabelPartition

/-- Every finite partition of `Fin J` has at most `J` nonempty blocks.-/
theorem block_card_le {J : ℕ} (pi : LabelPartition J) :
    Fintype.card pi.Block ≤ J := by
  classical
  let representative : pi.Block → Fin J := fun B ↦ B.1.min' (pi.block_nonempty B)
  have hinjective : Function.Injective representative := by
    intro B C h
    apply Subtype.ext
    apply pi.eq_of_overlap B.2 C.2
    · exact Finset.min'_mem B.1 (pi.block_nonempty B)
    · have hmem := Finset.min'_mem C.1 (pi.block_nonempty C)
      change representative C ∈ C.1 at hmem
      change representative B ∈ C.1
      rwa [h]
  simpa [representative] using Fintype.card_le_of_injective representative hinjective

/-- The block cardinalities sum to the cardinality of the label type.-/
theorem sum_block_card {J : ℕ} (pi : LabelPartition J) :
    (∑ B : pi.Block, B.1.card) = J := by
  classical
  have hpairwise : (pi.blocks : Set (Finset (Fin J))).PairwiseDisjoint id := by
    intro B hB C hC hne
    change Disjoint B C
    rw [Finset.disjoint_left]
    intro i hiB hiC
    exact hne (pi.eq_of_overlap hB hC hiB hiC)
  have hunion : pi.blocks.biUnion id = (Finset.univ : Finset (Fin J)) := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true]
    obtain ⟨B, hB, hi⟩ := pi.covers i
    exact ⟨B, hB, hi⟩
  have hcard := Finset.card_biUnion hpairwise
  rw [hunion] at hcard
  change (∑ B ∈ pi.blocks.attach, B.1.card) = J
  rw [Finset.sum_attach]
  simpa using hcard.symm

end LabelPartition

namespace SupplierSystem

/-- Product of all padded type-(L) predecessor coordinates.-/
def linearPredecessorProduct {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) : ℕ :=
  ∏ B : s.partition.Block, (s.descriptor B).linearPredecessor

/-- Product of the selected type-(L) bases.-/
def linearSelectedProduct {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) : ℕ :=
  ∏ B : s.partition.Block, (s.descriptor B).linearSelectedPart

/-- Product of the selected type-(P) prime powers.-/
def powerSelectedProduct {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) : ℕ :=
  ∏ B : s.partition.Block, (s.descriptor B).powerSelectedPart

theorem selectedDivisor_eq_linear_mul_power {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.selectedDivisor = s.linearSelectedProduct * s.powerSelectedProduct := by
  unfold selectedDivisor linearSelectedProduct powerSelectedProduct
  simp_rw [SupplierDescriptor.selectedDivisor_eq_linearSelectedPart_mul_powerSelectedPart]
  exact Finset.prod_mul_distrib

theorem linearPredecessorProduct_pos {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    0 < s.linearPredecessorProduct := by
  unfold linearPredecessorProduct
  exact Finset.prod_pos fun B hB ↦ (s.descriptor B).linearPredecessor_pos

theorem linearPredecessorProduct_smooth {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    IsSmooth Y s.linearPredecessorProduct := by
  unfold linearPredecessorProduct
  exact isSmooth_finset_prod Finset.univ
    (fun B : s.partition.Block ↦ (s.descriptor B).linearPredecessor)
    (fun B hB ↦ (s.descriptor B).linearPredecessor_smooth)

theorem linearPredecessorProduct_le_selectedDivisor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.linearPredecessorProduct ≤ s.selectedDivisor := by
  unfold linearPredecessorProduct selectedDivisor
  exact Finset.prod_le_prod (fun B hB ↦ Nat.zero_le _)
    (fun B hB ↦ (s.descriptor B).linearPredecessor_le_selectedDivisor)

theorem linearSelectedProduct_le_two_pow_mul_predecessor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.linearSelectedProduct ≤ 2 ^ J * s.linearPredecessorProduct := by
  unfold linearSelectedProduct linearPredecessorProduct
  calc
    (∏ B : s.partition.Block, (s.descriptor B).linearSelectedPart) ≤
        ∏ B : s.partition.Block, 2 * (s.descriptor B).linearPredecessor := by
      exact Finset.prod_le_prod (fun B hB ↦ Nat.zero_le _)
        (fun B hB ↦ (s.descriptor B).linearSelectedPart_le_two_mul_predecessor)
    _ = 2 ^ Fintype.card s.partition.Block *
        ∏ B : s.partition.Block, (s.descriptor B).linearPredecessor := by
      exact (Finset.pow_card_mul_prod (s := Finset.univ) (b := 2)).symm
    _ ≤ 2 ^ J * ∏ B : s.partition.Block,
        (s.descriptor B).linearPredecessor := by
      exact Nat.mul_le_mul_right _
        (pow_le_pow_right' (by norm_num) s.partition.block_card_le)

theorem sum_powerSelectedExponent_le_two_mul {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    (∑ B : s.partition.Block, (s.descriptor B).powerSelectedExponent) ≤ 2 * J := by
  calc
    (∑ B : s.partition.Block, (s.descriptor B).powerSelectedExponent) ≤
        ∑ B : s.partition.Block, (B.1.card + 1) := by
      exact Finset.sum_le_sum fun B hB ↦
        (s.descriptor B).powerSelectedExponent_le_card_add_one
    _ = J + Fintype.card s.partition.Block := by
      rw [Finset.sum_add_distrib, s.partition.sum_block_card]
      simp
    _ ≤ 2 * J := by
      simpa [two_mul] using Nat.add_le_add_left s.partition.block_card_le J

theorem one_le_upperCutoff_of_pos_rank {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (hJ : 0 < J) :
    1 ≤ Y := by
  let i : Fin J := ⟨0, hJ⟩
  exact (P.prime i).one_lt.le.trans (P.upper i)

/-- Exact paper-scale bound for the type-(P) part.-/
theorem powerSelectedProduct_le_upperCutoff_pow_two_mul {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.powerSelectedProduct ≤ Y ^ (2 * J) := by
  unfold powerSelectedProduct
  calc
    (∏ B : s.partition.Block, (s.descriptor B).powerSelectedPart) ≤
        ∏ B : s.partition.Block, Y ^ (s.descriptor B).powerSelectedExponent := by
      exact Finset.prod_le_prod (fun B hB ↦ Nat.zero_le _)
        (fun B hB ↦ (s.descriptor B).powerSelectedPart_le_Y_pow)
    _ = Y ^ (∑ B : s.partition.Block,
        (s.descriptor B).powerSelectedExponent) := by
      exact Finset.prod_pow_eq_pow_sum Finset.univ _ Y
    _ ≤ Y ^ (2 * J) := by
      by_cases hJ : J = 0
      · subst J
        have hcard : Fintype.card s.partition.Block = 0 :=
          Nat.eq_zero_of_le_zero s.partition.block_card_le
        letI : IsEmpty s.partition.Block := Fintype.card_eq_zero_iff.mp hcard
        simp
      · exact pow_le_pow_right'
          (one_le_upperCutoff_of_pos_rank P (Nat.pos_of_ne_zero hJ))
          s.sum_powerSelectedExponent_le_two_mul

/-- Every selected divisor is controlled by its smooth predecessor code and the explicit `2^J Y^(2J)` loss from the source split.-/
theorem selectedDivisor_le_encodingFactor_mul_predecessor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x) :
    s.selectedDivisor ≤
      (2 ^ J * Y ^ (2 * J)) * s.linearPredecessorProduct := by
  rw [s.selectedDivisor_eq_linear_mul_power]
  calc
    s.linearSelectedProduct * s.powerSelectedProduct ≤
        (2 ^ J * s.linearPredecessorProduct) * Y ^ (2 * J) := by
      exact Nat.mul_le_mul s.linearSelectedProduct_le_two_pow_mul_predecessor
        s.powerSelectedProduct_le_upperCutoff_pow_two_mul
    _ = (2 ^ J * Y ^ (2 * J)) * s.linearPredecessorProduct := by
      ac_rfl

theorem encodingFactor_pos {J y Y : ℕ} (P : LabelledPrimeDemands J y Y) :
    0 < 2 ^ J * Y ^ (2 * J) := by
  by_cases hJ : J = 0
  · subst J
    simp
  · exact Nat.mul_pos (pow_pos (by omega) _)
      (pow_pos (Nat.zero_lt_of_lt (one_le_upperCutoff_of_pos_rank P
        (Nat.pos_of_ne_zero hJ))) _)

theorem linearPredecessorProduct_le_two_mul_pow {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x)
    (hx : 0 < x) :
    s.linearPredecessorProduct ≤ (2 * x) ^ J := by
  unfold linearPredecessorProduct
  calc
    (∏ B : s.partition.Block, (s.descriptor B).linearPredecessor) ≤
        ∏ _B : s.partition.Block, 2 * x := by
      apply Finset.prod_le_prod
      · exact fun B hB ↦ Nat.zero_le _
      · intro B hB
        cases s.descriptor B with
        | inl source =>
            exact (Nat.sub_le _ _).trans source.base_le
        | inr source =>
            simp only [SupplierDescriptor.linearPredecessor, Sum.elim_inr]
            omega
    _ = (2 * x) ^ Fintype.card s.partition.Block := by simp
    _ ≤ (2 * x) ^ J := by
      exact pow_le_pow_right' (by omega) s.partition.block_card_le

/-- A selected-divisor tail element maps to the advertised finite smooth predecessor tail.-/
theorem linearPredecessorProduct_mem_finiteSmoothTailSet {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x H Hcode : ℕ} (s : SupplierSystem P x)
    (hx : 0 < x) (hlarge : H < s.selectedDivisor)
    (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H) :
    s.linearPredecessorProduct ∈ finiteSmoothTailSet Y Hcode ((2 * x) ^ J) := by
  rw [mem_finiteSmoothTailSet]
  refine ⟨?_, s.linearPredecessorProduct_le_two_mul_pow hx,
    s.linearPredecessorProduct_smooth⟩
  have hmul : (2 ^ J * Y ^ (2 * J)) * Hcode <
      (2 ^ J * Y ^ (2 * J)) * s.linearPredecessorProduct :=
    hscale.trans_lt <| hlarge.trans_le s.selectedDivisor_le_encodingFactor_mul_predecessor
  exact (Nat.mul_lt_mul_left (encodingFactor_pos P)).mp hmul

end SupplierSystem

/-! ## Supplier tail bounds -/

/-- Finite divisor-weighted smooth-tail bound for one labelled supplier family.-/
theorem supplierReciprocalTail_le_divisorSmoothTail {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ}
    (hx : 0 < x) (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        finiteTauSmoothReciprocalTail 2 Y Hcode ((2 * x) ^ J) := by
  classical
  rw [supplierReciprocalTail_eq_systemTail]
  unfold supplierSystemReciprocalTail
  push_cast
  let S := (allSupplierSystems P x).filter (H < ·.selectedDivisor)
  apply finite_reciprocal_sum_le_card_mul_divisor_smooth_tail S
    SupplierSystem.linearPredecessorProduct SupplierSystem.selectedDivisor
    Y Hcode ((2 * x) ^ J) (Fintype.card (SupplierSystem P x))
  · intro s hs
    exact s.linearPredecessorProduct_mem_finiteSmoothTailSet hx
      (Finset.mem_filter.mp hs).2 hscale
  · intro s hs
    exact s.linearPredecessorProduct_le_selectedDivisor
  · unfold S
    simpa [allSupplierSystems] using
      (Finset.card_filter_le (allSupplierSystems P x) (H < ·.selectedDivisor))

/-- Rank-sensitive supplier-tail encoding.-/
theorem supplierReciprocalTail_le_tauSmoothTail {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ}
    (hJ : 0 < J) (hx : 0 < x)
    (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        finiteTauSmoothReciprocalTail J Y Hcode ((2 * x) ^ J) := by
  classical
  rw [supplierReciprocalTail_eq_systemTail]
  unfold supplierSystemReciprocalTail
  push_cast
  let S := (allSupplierSystems P x).filter (H < ·.selectedDivisor)
  apply finite_reciprocal_sum_le_card_mul_tau_smooth_tail S
    SupplierSystem.linearPredecessorProduct SupplierSystem.selectedDivisor
    J Y Hcode ((2 * x) ^ J) (Fintype.card (SupplierSystem P x)) hJ
  · intro s hs
    exact s.linearPredecessorProduct_mem_finiteSmoothTailSet hx
      (Finset.mem_filter.mp hs).2 hscale
  · intro s hs
    exact s.linearPredecessorProduct_le_selectedDivisor
  · unfold S
    simpa [allSupplierSystems] using
      (Finset.card_filter_le (allSupplierSystems P x) (H < ·.selectedDivisor))

/-- The same supplier tail bounded by the finite divisor-weighted smooth census.-/
theorem supplierReciprocalTail_le_divisorSmoothCount {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ}
    (hx : 0 < x) (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        (finiteDivisorWeightedSmoothCount Y ((2 * x) ^ J) / (Hcode + 1)) := by
  exact (supplierReciprocalTail_le_divisorSmoothTail P hx hscale).trans <| by
    gcongr
    exact finiteTauSmoothReciprocalTail_two_le_count_div Y Hcode ((2 * x) ^ J)

/-- The supplier tail followed by the exact finite Rankin inequality.-/
theorem supplierReciprocalTail_le_rankin {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ} {delta : ℝ}
    (hx : 0 < x) (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H)
    (hHcode : 0 < Hcode) (hdelta : 0 ≤ delta) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        ((Hcode : ℝ) ^ (-delta) *
          finiteSmoothRpowSum (fun m ↦ orderedDivisorCount 2 m) Y ((2 * x) ^ J)
            (delta - 1)) := by
  exact (supplierReciprocalTail_le_divisorSmoothTail P hx hscale).trans <| by
    gcongr
    exact finiteTauSmoothReciprocalTail_le_rankin hHcode hdelta

/-- Moving-rank version followed by the finite weighted Rankin inequality.-/
theorem supplierReciprocalTail_le_tauRankin {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ} {delta : ℝ}
    (hJ : 0 < J) (hx : 0 < x)
    (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H)
    (hHcode : 0 < Hcode) (hdelta : 0 ≤ delta) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        ((Hcode : ℝ) ^ (-delta) *
          finiteSmoothRpowSum (fun m ↦ orderedDivisorCount J m) Y ((2 * x) ^ J)
            (delta - 1)) := by
  exact (supplierReciprocalTail_le_tauSmoothTail P hJ hx hscale).trans <| by
    gcongr
    exact finiteTauSmoothReciprocalTail_le_rankin hHcode hdelta

/-- The same rank-sensitive bridge with the paper's named Rankin exponent.-/
theorem supplierReciprocalTail_le_chosenTauRankin {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) {x H Hcode : ℕ}
    (hJ : 0 < J) (hx : 0 < x)
    (hscale : (2 ^ J * Y ^ (2 * J)) * Hcode ≤ H)
    (hHcode : 0 < Hcode) (hY : 1 < Y) (hu : 1 ≤ rankinU Hcode Y) :
    (supplierReciprocalTail P x H : ℝ) ≤
      Fintype.card (SupplierSystem P x) *
        (Real.exp (-rankinU Hcode Y * Real.log (rankinU Hcode Y)) *
          finiteSmoothRpowSum (fun m ↦ orderedDivisorCount J m) Y ((2 * x) ^ J)
            (rankinDelta Hcode Y - 1)) := by
  exact (supplierReciprocalTail_le_tauSmoothTail P hJ hx hscale).trans <| by
    gcongr
    exact finiteTauSmoothReciprocalTail_le_chosen_rankin hHcode hY hu

end

end RankAmplification
