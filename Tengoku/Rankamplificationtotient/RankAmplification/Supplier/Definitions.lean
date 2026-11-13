import Tengoku.Rankamplificationtotient.RankAmplification.Definitions
import Tengoku.Seed.Data.Nat.Factorization.Basic
import Tengoku.Seed.Data.Nat.GCD.BigOperators
import Tengoku.Seed.Data.Nat.Prime.Int

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Supplier systems This module formalizes the finite combinatorial objects in Definition 10.4. -/

namespace RankAmplification

/-! ## Labelled demands and blocks -/

/-- A labelled `J`-tuple of prime demands in the interval `(y, Y]`.-/
structure LabelledPrimeDemands (J y Y : ℕ) where
  /-- Numerical prime demanded by each label.-/
  value : Fin J → ℕ
  prime : ∀ i, Nat.Prime (value i)
  lower : ∀ i, y < value i
  upper : ∀ i, value i ≤ Y

/-- The product `D(B)` of all labelled demands in a block.-/
def blockDemandProduct {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) : ℕ :=
  ∏ i ∈ B, P.value i

/-- The full labelled demand product `D(P) = D(I)`.-/
def totalDemandProduct {J y Y : ℕ} (P : LabelledPrimeDemands J y Y) : ℕ :=
  blockDemandProduct P Finset.univ

/-- The labels in `B` whose numerical demand equals the proposed power-source base `q`.-/
def powerLabels {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) (q : ℕ) : Finset (Fin J) :=
  B.filter fun i ↦ P.value i = q

/-- The multiplicity `e_B = |E_B|` of labels supplied through a power source.-/
def powerMultiplicity {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) (q : ℕ) : ℕ :=
  (powerLabels P B q).card

/-- The residual demand product `D(B \ E_B)` which must divide `q - 1`.-/
def residualDemandProduct {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) (q : ℕ) : ℕ :=
  blockDemandProduct P (B \ powerLabels P B q)

theorem blockDemandProduct_pos {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) :
    0 < blockDemandProduct P B := by
  exact Finset.prod_pos fun i hi ↦ (P.prime i).pos

theorem demand_dvd_blockDemandProduct {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    {B : Finset (Fin J)} {i : Fin J} (hi : i ∈ B) :
    P.value i ∣ blockDemandProduct P B := by
  simpa [blockDemandProduct] using Finset.dvd_prod_of_mem P.value hi

/-- A finite partition of the label set.-/
structure LabelPartition (J : ℕ) where
  /-- Finite collection of partition blocks.-/
  blocks : Finset (Finset (Fin J))
  nonempty : ∀ B ∈ blocks, B.Nonempty
  covers : ∀ i : Fin J, ∃ B, B ∈ blocks ∧ i ∈ B
  eq_of_overlap : ∀ {B C : Finset (Fin J)} {i : Fin J},
    B ∈ blocks → C ∈ blocks → i ∈ B → i ∈ C → B = C

/-- A block bundled with its membership in a partition.-/
abbrev LabelPartition.Block {J : ℕ} (π : LabelPartition J) :=
  {B : Finset (Fin J) // B ∈ π.blocks}

theorem LabelPartition.block_nonempty {J : ℕ} (π : LabelPartition J) (B : π.Block) :
    B.1.Nonempty :=
  π.nonempty B.1 B.2

/-- The unique block containing a given label.-/
noncomputable def LabelPartition.blockOf {J : ℕ} (π : LabelPartition J) (i : Fin J) :
    π.Block := by
  classical
  exact ⟨Classical.choose (π.covers i), (Classical.choose_spec (π.covers i)).1⟩

theorem LabelPartition.mem_blockOf {J : ℕ} (π : LabelPartition J) (i : Fin J) :
    i ∈ (π.blockOf i).1 :=
  (Classical.choose_spec (π.covers i)).2

theorem LabelPartition.block_eq_of_mem {J : ℕ} (π : LabelPartition J) (i : Fin J)
    (B : π.Block) (hi : i ∈ B.1) :
    π.blockOf i = B := by
  apply Subtype.ext
  exact π.eq_of_overlap (π.blockOf i).2 B.2 (π.mem_blockOf i) hi

private theorem labelPartition_blocks_injective {J : ℕ} :
    Function.Injective (LabelPartition.blocks : LabelPartition J → Finset (Finset (Fin J))) := by
  intro π ρ h
  cases π
  cases ρ
  cases h
  rfl

instance labelPartitionFinite (J : ℕ) : Finite (LabelPartition J) :=
  Finite.of_injective LabelPartition.blocks labelPartition_blocks_injective

/-! ## Local descriptors -/

/-- A type-(L) descriptor.-/
structure LinearDescriptor {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x : ℕ) (B : Finset (Fin J)) where
  /-- Bounded prime base of the linear Euler factor.-/
  base : Fin (2 * x + 1)
  base_prime : Nat.Prime base
  demand_dvd : blockDemandProduct P B ∣ (base : ℕ) - 1
  smooth : largestPrimeFactor ((base : ℕ) - 1) ≤ Y

/-- A type-(P) descriptor.-/
structure PowerDescriptor {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (B : Finset (Fin J)) where
  /-- Bounded prime base of the power Euler factor.-/
  base : Fin (Y + 1)
  base_prime : Nat.Prime base
  occurs : (powerLabels P B base).Nonempty
  residual_dvd : residualDemandProduct P B base ∣ (base : ℕ) - 1
  smooth : largestPrimeFactor ((base : ℕ) - 1) ≤ Y

/-- Either one linear descriptor or one power descriptor for a block.-/
abbrev SupplierDescriptor {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x : ℕ) (B : Finset (Fin J)) :=
  LinearDescriptor P x B ⊕ PowerDescriptor P B

namespace LinearDescriptor

/-- The linear descriptor base viewed as a natural number.-/
def natBase {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : LinearDescriptor P x B) : ℕ :=
  d.base

theorem base_le {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : LinearDescriptor P x B) :
    d.natBase ≤ 2 * x :=
  Nat.lt_succ_iff.mp d.base.isLt

theorem demand_lt_base {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : LinearDescriptor P x B) {i : Fin J} (hi : i ∈ B) :
    P.value i < d.natBase := by
  have hdvd : P.value i ∣ d.natBase - 1 :=
    (demand_dvd_blockDemandProduct P hi).trans d.demand_dvd
  have hle : P.value i ≤ d.natBase - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt d.base_prime.one_lt) hdvd
  exact hle.trans_lt (Nat.sub_lt d.base_prime.pos Nat.zero_lt_one)

theorem base_gt_lowerCutoff {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : LinearDescriptor P x B) (hB : B.Nonempty) :
    y < d.natBase := by
  obtain ⟨i, hi⟩ := hB
  exact (P.lower i).trans (d.demand_lt_base hi)

private theorem base_injective {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} :
    Function.Injective (LinearDescriptor.base : LinearDescriptor P x B → Fin (2 * x + 1)) := by
  intro d e h
  cases d
  cases e
  cases h
  rfl

theorem eq_of_base_eq {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} {d e : LinearDescriptor P x B} (h : d.natBase = e.natBase) :
    d = e := by
  apply base_injective
  exact Fin.ext h

instance finite {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} : Finite (LinearDescriptor P x B) :=
  Finite.of_injective LinearDescriptor.base base_injective

end LinearDescriptor

namespace PowerDescriptor

/-- The power descriptor base viewed as a natural number.-/
def natBase {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} (d : PowerDescriptor P B) : ℕ :=
  d.base

theorem base_le {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} (d : PowerDescriptor P B) :
    d.natBase ≤ Y :=
  Nat.lt_succ_iff.mp d.base.isLt

theorem multiplicity_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} (d : PowerDescriptor P B) :
    0 < powerMultiplicity P B d.natBase := by
  exact Finset.card_pos.mpr d.occurs

theorem base_eq_demand {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} (d : PowerDescriptor P B) :
    ∃ i ∈ B, P.value i = d.natBase := by
  obtain ⟨i, hi⟩ := d.occurs
  exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩

theorem base_gt_lowerCutoff {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} (d : PowerDescriptor P B) :
    y < d.natBase := by
  obtain ⟨i, hi, hvalue⟩ := d.base_eq_demand
  simpa [hvalue] using P.lower i

private theorem base_injective {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} :
    Function.Injective (PowerDescriptor.base : PowerDescriptor P B → Fin (Y + 1)) := by
  intro d e h
  cases d
  cases e
  cases h
  rfl

theorem eq_of_base_eq {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} {d e : PowerDescriptor P B} (h : d.natBase = e.natBase) :
    d = e := by
  apply base_injective
  exact Fin.ext h

instance finite {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {B : Finset (Fin J)} : Finite (PowerDescriptor P B) :=
  Finite.of_injective PowerDescriptor.base base_injective

end PowerDescriptor

namespace SupplierDescriptor

theorem linear_power_base_ne {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (linear : LinearDescriptor P x B)
    (power : PowerDescriptor P B) :
    linear.natBase ≠ power.natBase := by
  obtain ⟨i, hi, hvalue⟩ := power.base_eq_demand
  have hlt := linear.demand_lt_base hi
  omega

instance finite {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} : Finite (SupplierDescriptor P x B) := by
  classical
  change Finite (LinearDescriptor P x B ⊕ PowerDescriptor P B)
  letI : Fintype (LinearDescriptor P x B) := Fintype.ofFinite _
  letI : Fintype (PowerDescriptor P B) := Fintype.ofFinite _
  infer_instance

/-- Prime base of either kind of supplier descriptor.-/
def base {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim LinearDescriptor.natBase PowerDescriptor.natBase

/-- Local divisor selected by either kind of supplier descriptor.-/
def selectedDivisor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim LinearDescriptor.natBase fun source ↦
    source.natBase ^ (powerMultiplicity P B source.natBase + 1)

/-- The exponent of the source base in the selected local divisor.-/
def selectedExponent {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) : ℕ :=
  d.elim (fun _ ↦ 1) fun source ↦ powerMultiplicity P B source.natBase + 1

theorem selectedDivisor_eq_pow {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    d.selectedDivisor = d.base ^ d.selectedExponent := by
  cases d <;> simp [selectedDivisor, base, selectedExponent]

theorem selectedExponent_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    0 < d.selectedExponent := by
  cases d <;> simp [selectedExponent]

theorem base_prime {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    Nat.Prime d.base := by
  cases d with
  | inl source => exact source.base_prime
  | inr source => exact source.base_prime

theorem base_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    0 < d.base :=
  d.base_prime.pos

theorem selectedDivisor_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    0 < d.selectedDivisor := by
  cases d with
  | inl source => exact source.base_prime.pos
  | inr source => exact pow_pos source.base_prime.pos _

theorem base_dvd_selectedDivisor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    d.base ∣ d.selectedDivisor := by
  cases d with
  | inl source => exact dvd_rfl
  | inr source => exact dvd_pow_self source.natBase (Nat.succ_ne_zero _)

theorem base_le_max {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    d.base ≤ max (2 * x) Y := by
  cases d with
  | inl source => exact source.base_le.trans (le_max_left _ _)
  | inr source => exact source.base_le.trans (le_max_right _ _)

theorem base_le_two_mul {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) (hY : Y ≤ 2 * x) :
    d.base ≤ 2 * x :=
  d.base_le_max.trans (max_le (le_rfl) hY)

theorem base_gt_lowerCutoff {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} (d : SupplierDescriptor P x B) (hB : B.Nonempty) :
    y < d.base := by
  cases d with
  | inl source => exact source.base_gt_lowerCutoff hB
  | inr source => exact source.base_gt_lowerCutoff

/-- For a fixed block and numerical source base, the admissible descriptor is unique.-/
theorem eq_of_base_eq {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    {B : Finset (Fin J)} {d e : SupplierDescriptor P x B} (h : d.base = e.base) :
    d = e := by
  cases d with
  | inl linear =>
      cases e with
      | inl other => exact congrArg Sum.inl (LinearDescriptor.eq_of_base_eq h)
      | inr power => exact False.elim (linear_power_base_ne linear power h)
  | inr power =>
      cases e with
      | inl linear => exact False.elim (linear_power_base_ne linear power h.symm)
      | inr other => exact congrArg Sum.inr (PowerDescriptor.eq_of_base_eq h)

theorem primeSupport_selectedDivisor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} {B : Finset (Fin J)} (d : SupplierDescriptor P x B) :
    primeSupport d.selectedDivisor = {d.base} := by
  cases d with
  | inl source => simpa [selectedDivisor, base, LinearDescriptor.natBase, primeSupport]
      using source.base_prime.primeFactors
  | inr source =>
      simpa [selectedDivisor, base, PowerDescriptor.natBase, primeSupport] using
        Nat.primeFactors_prime_pow (Nat.succ_ne_zero (powerMultiplicity P B source.natBase))
          source.base_prime

theorem eq_base_of_prime_dvd_selectedDivisor {J y Y p : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} {B : Finset (Fin J)}
    (d : SupplierDescriptor P x B) (hp : Nat.Prime p) (hdvd : p ∣ d.selectedDivisor) :
    p = d.base := by
  rw [d.selectedDivisor_eq_pow] at hdvd
  exact (Nat.prime_dvd_prime_iff_eq hp d.base_prime).mp (hp.dvd_of_dvd_pow hdvd)

end SupplierDescriptor

/-! ## Systems, realizations, and occurrence assignments -/

/-- A `Y`-admissible supplier system: a partition, one admissible descriptor per block, and pairwise-distinct source bases.-/
structure SupplierSystem {J y Y : ℕ} (P : LabelledPrimeDemands J y Y) (x : ℕ) where
  /-- Partition of the demand labels into source blocks.-/
  partition : LabelPartition J
  /-- Admissible local descriptor chosen for each block.-/
  descriptor : (B : partition.Block) → SupplierDescriptor P x B.1
  bases_injective : Function.Injective fun B ↦ (descriptor B).base

namespace SupplierSystem

/-- Product of the selected local divisors over all blocks.-/
def selectedDivisor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) : ℕ :=
  ∏ B : s.partition.Block, (s.descriptor B).selectedDivisor

theorem descriptor_selectedDivisor_dvd {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) (B : s.partition.Block) :
    (s.descriptor B).selectedDivisor ∣ s.selectedDivisor := by
  exact Finset.dvd_prod_of_mem (fun C : s.partition.Block ↦
    (s.descriptor C).selectedDivisor) (Finset.mem_univ B)

theorem descriptor_base_dvd {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) (B : s.partition.Block) :
    (s.descriptor B).base ∣ s.selectedDivisor :=
  (s.descriptor B).base_dvd_selectedDivisor.trans (s.descriptor_selectedDivisor_dvd B)

theorem selectedDivisor_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) :
    0 < s.selectedDivisor := by
  exact Finset.prod_pos fun B hB ↦ (s.descriptor B).selectedDivisor_pos

theorem base_ne_of_ne {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) {B C : s.partition.Block} (hBC : B ≠ C) :
    (s.descriptor B).base ≠ (s.descriptor C).base :=
  (s.bases_injective.ne hBC)

theorem descriptor_base_gt_lowerCutoff {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) (B : s.partition.Block) :
    y < (s.descriptor B).base :=
  (s.descriptor B).base_gt_lowerCutoff (s.partition.block_nonempty B)

theorem selectedDivisors_coprime {J y Y : ℕ} {P : LabelledPrimeDemands J y Y}
    {x : ℕ} (s : SupplierSystem P x) {B C : s.partition.Block} (hBC : B ≠ C) :
    Nat.Coprime (s.descriptor B).selectedDivisor (s.descriptor C).selectedDivisor := by
  rw [(s.descriptor B).selectedDivisor_eq_pow, (s.descriptor C).selectedDivisor_eq_pow]
  exact Nat.coprime_pow_primes _ _ (s.descriptor B).base_prime
    (s.descriptor C).base_prime (s.bases_injective.ne hBC)

theorem selectedDivisor_dvd_of_forall_descriptor_dvd {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} (s : SupplierSystem P x)
    (hdvd : ∀ B, (s.descriptor B).selectedDivisor ∣ N) :
    s.selectedDivisor ∣ N := by
  classical
  unfold selectedDivisor
  induction (Finset.univ : Finset s.partition.Block) using Finset.induction_on with
  | empty => simp
  | @insert B blocks hB ih =>
      rw [Finset.prod_insert hB]
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · exact Nat.Coprime.prod_right fun C hC ↦ s.selectedDivisors_coprime fun hBC ↦
          hB (hBC ▸ hC)
      · exact hdvd B
      · exact ih

/-- Every prime factor selected by a supplier system lies above the lower cutoff `y`.-/
theorem primeFactor_selectedDivisor_gt_lowerCutoff {J y Y p : ℕ}
    {P : LabelledPrimeDemands J y Y} {x : ℕ} (s : SupplierSystem P x)
    (hp : Nat.Prime p) (hdvd : p ∣ s.selectedDivisor) :
    y < p := by
  obtain ⟨B, hB, hpB⟩ :=
    (hp.prime.dvd_finsetProd_iff fun B : s.partition.Block ↦
      (s.descriptor B).selectedDivisor).mp hdvd
  have hbase := s.descriptor_base_gt_lowerCutoff B
  have heq := (s.descriptor B).eq_base_of_prime_dvd_selectedDivisor hp hpB
  simpa [heq] using hbase

private def code {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ}
    (s : SupplierSystem P x) :
    Σ π : LabelPartition J, (B : π.Block) → SupplierDescriptor P x B.1 :=
  ⟨s.partition, s.descriptor⟩

private theorem code_injective {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ} :
    Function.Injective (code : SupplierSystem P x →
      Σ π : LabelPartition J, (B : π.Block) → SupplierDescriptor P x B.1) := by
  intro s t h
  cases s
  cases t
  cases h
  rfl

instance finite {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ} :
    Finite (SupplierSystem P x) :=
  by
    classical
    letI : Fintype (LabelPartition J) := Fintype.ofFinite _
    letI (π : LabelPartition J) : Fintype π.Block := Fintype.ofFinite _
    letI (π : LabelPartition J) (B : π.Block) :
        Fintype (SupplierDescriptor P x B.1) := Fintype.ofFinite _
    exact Finite.of_injective code code_injective

noncomputable instance fintype {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x : ℕ} :
    Fintype (SupplierSystem P x) :=
  Fintype.ofFinite _

end SupplierSystem

/-- Exact prime-power divisibility `q^a ∥ N`.-/
def IsExactPrimePowerFactor (N q a : ℕ) : Prop :=
  0 < a ∧ q ^ a ∣ N ∧ ¬q ^ (a + 1) ∣ N

/-- A realization maps every block to the exact local prime power with its source base and requires the descriptor's selected divisor to divide that local factor.-/
structure SupplierRealization {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    (s : SupplierSystem P x) where
  /-- Exact exponent of the source prime attached to each block.-/
  exponent : s.partition.Block → ℕ
  exactFactor : ∀ B, IsExactPrimePowerFactor N (s.descriptor B).base (exponent B)
  selected_dvd : ∀ B, (s.descriptor B).selectedDivisor ∣
    (s.descriptor B).base ^ exponent B

namespace SupplierRealization

/-- Exact prime-power factor realized by one supplier block.-/
def localFactor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s)
    (B : s.partition.Block) : ℕ :=
  (s.descriptor B).base ^ R.exponent B

theorem exponent_pos {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s)
    (B : s.partition.Block) :
    0 < R.exponent B :=
  (R.exactFactor B).1

theorem localFactor_dvd {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s)
    (B : s.partition.Block) :
    R.localFactor B ∣ N :=
  (R.exactFactor B).2.1

theorem selectedDivisor_dvd_localFactor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} {s : SupplierSystem P x}
    (R : SupplierRealization (N := N) s) (B : s.partition.Block) :
    (s.descriptor B).selectedDivisor ∣ R.localFactor B :=
  R.selected_dvd B

theorem selectedExponent_le_exponent {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} {s : SupplierSystem P x}
    (R : SupplierRealization (N := N) s) (B : s.partition.Block) :
    (s.descriptor B).selectedExponent ≤ R.exponent B := by
  apply (Nat.pow_dvd_pow_iff_le_right (s.descriptor B).base_prime.one_lt).mp
  rw [← (s.descriptor B).selectedDivisor_eq_pow]
  exact R.selected_dvd B

theorem systemSelectedDivisor_dvd {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} {s : SupplierSystem P x}
    (R : SupplierRealization (N := N) s) :
    s.selectedDivisor ∣ N := by
  apply s.selectedDivisor_dvd_of_forall_descriptor_dvd
  intro B
  exact (R.selected_dvd B).trans (R.localFactor_dvd B)

/-- The canonical realization obtained from divisibility of the system divisor.-/
noncomputable def ofSystemDivisor {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} (s : SupplierSystem P x)
    (hN : N ≠ 0) (hdvd : s.selectedDivisor ∣ N) :
    SupplierRealization (N := N) s where
  exponent B := N.factorization (s.descriptor B).base
  exactFactor B := by
    have hselected : (s.descriptor B).selectedDivisor ∣ N :=
      (s.descriptor_selectedDivisor_dvd B).trans hdvd
    have hpow : (s.descriptor B).base ^ (s.descriptor B).selectedExponent ∣ N := by
      rwa [← (s.descriptor B).selectedDivisor_eq_pow]
    have hle : (s.descriptor B).selectedExponent ≤
        N.factorization (s.descriptor B).base :=
      ((s.descriptor B).base_prime.pow_dvd_iff_le_factorization hN).mp hpow
    refine ⟨(s.descriptor B).selectedExponent_pos.trans_le hle,
      ((s.descriptor B).base_prime.pow_dvd_iff_le_factorization hN).mpr le_rfl, ?_⟩
    intro hnext
    have himpossible : N.factorization (s.descriptor B).base + 1 ≤
        N.factorization (s.descriptor B).base :=
      ((s.descriptor B).base_prime.pow_dvd_iff_le_factorization hN).mp hnext
    omega
  selected_dvd B := by
    rw [(s.descriptor B).selectedDivisor_eq_pow]
    apply pow_dvd_pow
    have hselected : (s.descriptor B).selectedDivisor ∣ N :=
      (s.descriptor_selectedDivisor_dvd B).trans hdvd
    apply ((s.descriptor B).base_prime.pow_dvd_iff_le_factorization hN).mp
    rwa [← (s.descriptor B).selectedDivisor_eq_pow]

/-- For positive ambient integers, the paper's realization criterion is exact.-/
theorem nonempty_realization_iff_systemSelectedDivisor_dvd {J y Y : ℕ}
    {P : LabelledPrimeDemands J y Y} {x N : ℕ} (s : SupplierSystem P x) (hN : N ≠ 0) :
    Nonempty (SupplierRealization (N := N) s) ↔ s.selectedDivisor ∣ N := by
  constructor
  · rintro ⟨R⟩
    exact R.systemSelectedDivisor_dvd
  · exact fun hdvd ↦ ⟨ofSystemDivisor s hN hdvd⟩

theorem localFactor_injective {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s) :
    Function.Injective R.localFactor := by
  intro B C h
  have hp := (s.descriptor B).base_prime
  have hq := (s.descriptor C).base_prime
  have hpow := hp.pow_inj' hq (R.exponent_pos B).ne' (R.exponent_pos C).ne' h
  exact s.bases_injective hpow.1

end SupplierRealization

/-- The labelled occurrence assignment induced by a realization: each label is sent to its unique partition block, hence to that block's exact local factor.-/
structure OccurrenceAssignment {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s) where
  /-- Unique supplier block assigned to each demand label.-/
  source : Fin J → s.partition.Block
  label_mem : ∀ i, i ∈ (source i).1

namespace OccurrenceAssignment

/-- Realized local factor supplying a given demand label.-/
def localFactor {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} {R : SupplierRealization (N := N) s}
    (σ : OccurrenceAssignment R) (i : Fin J) : ℕ :=
  R.localFactor (σ.source i)

theorem source_eq {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} {R : SupplierRealization (N := N) s}
    (σ τ : OccurrenceAssignment R) (i : Fin J) :
    σ.source i = τ.source i := by
  apply Subtype.ext
  exact s.partition.eq_of_overlap (σ.source i).2 (τ.source i).2
    (σ.label_mem i) (τ.label_mem i)

theorem unique {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} {R : SupplierRealization (N := N) s}
    (σ τ : OccurrenceAssignment R) : σ = τ := by
  have hsource : σ.source = τ.source := funext fun i ↦ source_eq σ τ i
  cases σ
  cases τ
  cases hsource
  rfl

end OccurrenceAssignment

/-- The canonical occurrence assignment obtained from the unique-block operation.-/
noncomputable def SupplierRealization.occurrenceAssignment
    {J y Y : ℕ} {P : LabelledPrimeDemands J y Y} {x N : ℕ}
    {s : SupplierSystem P x} (R : SupplierRealization (N := N) s) :
    OccurrenceAssignment R where
  source := s.partition.blockOf
  label_mem := s.partition.mem_blockOf

/-! ## Finite weights -/

/-- The finite set of all admissible supplier systems for fixed labelled demands.-/
noncomputable def allSupplierSystems {J y Y : ℕ} (P : LabelledPrimeDemands J y Y) (x : ℕ) :
    Finset (SupplierSystem P x) := by
  classical
  exact Finset.univ

/-- The exact divisor weight `w_P(d)`: systems, rather than numerical divisors, are counted.-/
noncomputable def supplierWeight {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x d : ℕ) : ℕ := by
  classical
  exact ((allSupplierSystems P x).filter fun s ↦ s.selectedDivisor = d).card

/-- The finite numerical support of `w_P`.-/
noncomputable def supplierDivisorSupport {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x : ℕ) : Finset ℕ := by
  classical
  exact (allSupplierSystems P x).image SupplierSystem.selectedDivisor

/-- The formal divisor sum `F_P(N) = ∑_{d∣N} w_P(d)`.-/
noncomputable def supplierDivisorWeight {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, supplierWeight P x d

/-- The finite reciprocal mass `Λ(P) = ∑_d w_P(d)/d`.-/
noncomputable def supplierReciprocalMass {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x : ℕ) : ℚ :=
  ∑ d ∈ supplierDivisorSupport P x, (supplierWeight P x d : ℚ) / d

/-- The large-selected-divisor tail `Λ_{>H}(P) = ∑_{d>H} w_P(d)/d`.-/
noncomputable def supplierReciprocalTail {J y Y : ℕ} (P : LabelledPrimeDemands J y Y)
    (x H : ℕ) : ℚ :=
  ∑ d ∈ (supplierDivisorSupport P x).filter (H < ·), (supplierWeight P x d : ℚ) / d

/-- The equivalent system-indexed reciprocal sum, convenient for later reindexing arguments.-/
noncomputable def supplierSystemReciprocalMass {J y Y : ℕ}
    (P : LabelledPrimeDemands J y Y) (x : ℕ) : ℚ :=
  ∑ s ∈ allSupplierSystems P x, 1 / (s.selectedDivisor : ℚ)

end RankAmplification
