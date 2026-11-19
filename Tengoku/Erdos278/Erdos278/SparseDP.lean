import Tengoku.Erdos278.Erdos278.PrimeDP
import Tengoku.Erdos278.Erdos278.Components

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

/-- Only these pairs can ever be separated by a choice of residues.-/
def interactionPairs {r : ℕ} (n : Fin r → ℕ) : Finset (PairIndex r) :=
  univ.filter (fun p => 1 < (n p.1.1).gcd (n p.1.2))

def interactionVertices {r : ℕ} (n : Fin r → ℕ) : Finset (Fin r) :=
  (interactionPairs n).biUnion (fun p => {p.1.1, p.1.2})

theorem interaction_vertices_card {r : ℕ} (n : Fin r → ℕ) :
    (interactionVertices n).card ≤ 2 * (interactionPairs n).card :=
  interacting_vertices_bound _

theorem isolated_vertex_coprime {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) {i j : Fin r}
    (hi : i ∉ interactionVertices n) (hij : i ≠ j) :
    (n i).Coprime (n j) := by
  apply Nat.coprime_iff_gcd_eq_one.mpr
  by_contra h
  have hpos := Nat.gcd_pos_of_pos_left (n j) (hn i)
  have hg : 1 < (n i).gcd (n j) := by omega
  apply hi
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact mem_biUnion.mpr ⟨⟨(i,j), hlt⟩,
      by simpa [interactionPairs] using hg, by simp⟩
  · exact mem_biUnion.mpr ⟨⟨(j,i), hgt⟩,
      by simpa [interactionPairs, Nat.gcd_comm] using hg, by simp⟩

/-- Removing every isolated modulus preserves the objective up to an explicit
nonnegative factor, for every residue choice, including modulus one.-/
theorem isolated_vertices_factorization {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (a : Fin r → ℤ) :
    1 - density univ n a = (1 - density (interactionVertices n) n a) *
      ∏ i ∈ univ \ interactionVertices n, (1 - (1 : ℚ) / n i) := by
  have hu : interactionVertices n ∪ (univ \ interactionVertices n) = univ := by
    ext i; simp
  have hc : ∀ i ∈ interactionVertices n, ∀ j ∈ univ \ interactionVertices n,
      (n i).Coprime (n j) := by
    intro i hi j hj
    have hjn := (mem_sdiff.mp hj).2
    exact (isolated_vertex_coprime n hn hjn (fun he => hjn (he ▸ hi))).symm
  have hf := uncovered_component_factorization
    (interactionVertices n) (univ \ interactionVertices n)
    (disjoint_left.mpr (fun i hi hj => (mem_sdiff.mp hj).2 hi))
    n (fun i _ => hn i) a hc
  rw [hu, coprime_uncovered_product _ n (fun i _ => hn i) a
    (fun i hi j _ hij => isolated_vertex_coprime n hn (mem_sdiff.mp hi).2 hij)] at hf
  exact hf

/-- A maximum on the nonisolated vertices is already a maximum on all vertices.
The residues on isolated vertices can be chosen arbitrarily.-/
theorem isolated_optimum_lift {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) (a : Fin r → ℤ)
    (ha : ∀ x, density (interactionVertices n) n x ≤
      density (interactionVertices n) n a) :
    ∀ x, density univ n x ≤ density univ n a := by
  have hnonneg : 0 ≤ ∏ i ∈ univ \ interactionVertices n, (1 - (1 : ℚ) / n i) := by
    rw [← coprime_uncovered_product _ n (fun i _ => hn i) a
      (fun i hi j _ hij => isolated_vertex_coprime n hn (mem_sdiff.mp hi).2 hij)]
    exact sub_nonneg.mpr (density_bounds _ n (fun i _ => hn i) a).2
  intro x
  have hmul := mul_le_mul_of_nonneg_right (sub_le_sub_left (ha x) 1) hnonneg
  have hfa := isolated_vertices_factorization n hn a
  have hfx := isolated_vertices_factorization n hn x
  linarith

/-- A family of masks on m permitted edges has at most 2^m members.-/
theorem supported_masks_card_bound {r : ℕ}
    (R : Finset (SeparationMask r)) (E : SeparationMask r)
    (hE : ∀ H ∈ R, H ⊆ E) : R.card ≤ 2 ^ E.card := by
  calc
    _ ≤ E.powerset.card := card_le_card (fun H hH => mem_powerset.mpr (hE H hH))
    _ = _ := card_powerset E

theorem local_masks_supported {r : ℕ} (V : Finset (Fin r)) (b : ℕ)
    (E : SeparationMask r)
    (hV : ∀ p : PairIndex r, p.1.1 ∈ V → p.1.2 ∈ V → p ∈ E)
    (H : SeparationMask r) (hH : H ∈ localSeparationMasks V b) : H ⊆ E := by
  obtain ⟨f, _, rfl⟩ := mem_image.mp hH
  intro p hp
  obtain ⟨_, hi, hj, _⟩ := mem_filter.mp hp
  exact hV p hi hj

theorem local_masks_sparse_card_bound {r : ℕ} (V : Finset (Fin r)) (b : ℕ)
    (E : SeparationMask r)
    (hV : ∀ p : PairIndex r, p.1.1 ∈ V → p.1.2 ∈ V → p ∈ E) :
    (localSeparationMasks V b).card ≤ 2 ^ E.card :=
  supported_masks_card_bound _ E (local_masks_supported V b E hV)

theorem separation_dp_supported {r : ℕ}
    (choices : ℕ → Finset (SeparationMask r)) (k : ℕ) (E : SeparationMask r)
    (hE : ∀ t < k, ∀ H ∈ choices t, H ⊆ E)
    (H : SeparationMask r) (hH : H ∈ separationDP choices k) : H ⊆ E := by
  obtain ⟨f, hf, rfl⟩ := (separation_dp_exact choices k H).mp hH
  intro p hp
  obtain ⟨t, ht, hp⟩ := mem_biUnion.mp hp
  exact hE t (mem_range.mp ht) (f t) (hf t (mem_range.mp ht)) hp

theorem separation_dp_sparse_state_bound {r : ℕ}
    (choices : ℕ → Finset (SeparationMask r)) (k : ℕ) (E : SeparationMask r)
    (hE : ∀ t < k, ∀ H ∈ choices t, H ⊆ E) :
    (separationDP choices k).card ≤ 2 ^ E.card :=
  supported_masks_card_bound _ E (separation_dp_supported choices k E hE)

/-- All candidate transitions, including candidates discarded as duplicates.-/
theorem separation_total_sparse_candidate_bound {r : ℕ}
    (choices : ℕ → Finset (SeparationMask r)) (d : ℕ) (E : SeparationMask r)
    (hE : ∀ t < d, ∀ H ∈ choices t, H ⊆ E) :
    (∑ t ∈ range d, (separationDP choices t ×ˢ choices t).card) ≤
      d * 2 ^ (2 * E.card) := by
  calc
    _ ≤ ∑ _t ∈ range d, 2 ^ (2 * E.card) := by
      apply sum_le_sum
      intro t ht
      rw [card_product, two_mul, pow_add]
      exact Nat.mul_le_mul
        (separation_dp_sparse_state_bound choices t E
          (fun s hs => hE s (hs.trans (mem_range.mp ht))))
        (supported_masks_card_bound _ E (hE t (mem_range.mp ht)))
    _ = _ := by simp

/-- The finite enumeration used in finiteSeparationDP, exposed for counting.-/
noncomputable def finiteSeparationSchedule {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) (t : ℕ) : Finset (SeparationMask r) :=
  if ht : t < Fintype.card C then
    choices ((Fintype.equivFin C).symm ⟨t, ht⟩) else {∅}

noncomputable def finiteSeparationCandidateCount {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) : ℕ :=
  ∑ t ∈ range (Fintype.card C),
    (separationDP (finiteSeparationSchedule choices) t ×ˢ
      finiteSeparationSchedule choices t).card

theorem finite_schedule_supported {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) (E : SeparationMask r)
    (hE : ∀ c, ∀ H ∈ choices c, H ⊆ E) (t : ℕ)
    (H : SeparationMask r) (hH : H ∈ finiteSeparationSchedule choices t) : H ⊆ E := by
  classical
  by_cases ht : t < Fintype.card C
  · exact hE _ H (by simpa [finiteSeparationSchedule, ht] using hH)
  · have hh : H = ∅ := by simpa [finiteSeparationSchedule, ht] using hH
    simp [hh]

theorem finite_separation_dp_sparse_state_bound {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) (E : SeparationMask r)
    (hE : ∀ c, ∀ H ∈ choices c, H ⊆ E) :
    (finiteSeparationDP choices).card ≤ 2 ^ E.card :=
  separation_dp_sparse_state_bound (finiteSeparationSchedule choices) _ E
    (fun t _ => finite_schedule_supported choices E hE t)

theorem finite_separation_sparse_candidate_bound {r : ℕ} {C : Type*} [Fintype C]
    (choices : C → Finset (SeparationMask r)) (E : SeparationMask r)
    (hE : ∀ c, ∀ H ∈ choices c, H ⊆ E) :
    finiteSeparationCandidateCount choices ≤ Fintype.card C * 2 ^ (2 * E.card) :=
  separation_total_sparse_candidate_bound (finiteSeparationSchedule choices) _ E
    (fun t _ => finite_schedule_supported choices E hE t)

/-- A shared digit has a base greater than one dividing both input moduli.-/
theorem radix_support_interaction {r : ℕ} {β : Type*} [Fintype β]
    (n : Fin r → ℕ) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 2 ≤ b j) (hrep : ∀ i, radixModulus b (e i) = n i)
    (c : RadixCoordinate e) (p : PairIndex r)
    (hi : p.1.1 ∈ radixSupport e c) (hj : p.1.2 ∈ radixSupport e c) :
    p ∈ interactionPairs n := by
  have hdiv (i : Fin r) (h : c.2.val < e i c.1) : b c.1 ∣ n i := by
    rw [← hrep i]
    exact (dvd_pow_self (b c.1) (by omega : e i c.1 ≠ 0)).trans
      (Finset.dvd_lcm (mem_univ c.1))
  have hni : 0 < n p.1.1 := by
    rw [← hrep p.1.1]
    exact radix_modulus_pos b _ (fun j => lt_of_lt_of_le (by decide) (hb j))
  have hd := Nat.dvd_gcd
    (hdiv p.1.1 (mem_filter.mp hi).2) (hdiv p.1.2 (mem_filter.mp hj).2)
  have hbase := hb c.1
  exact mem_filter.mpr ⟨mem_univ _, lt_of_lt_of_le (by omega : 1 < b c.1)
    (Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ hni) hd)⟩

theorem radix_dp_sparse_state_bound {r : ℕ} {β : Type*} [Fintype β]
    (n : Fin r → ℕ) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 2 ≤ b j) (hrep : ∀ i, radixModulus b (e i) = n i) :
    (radixDP b e).card ≤ 2 ^ (interactionPairs n).card :=
  finite_separation_dp_sparse_state_bound _ _ (fun c =>
    local_masks_supported _ _ _ (radix_support_interaction n b e hb hrep c))

theorem radix_dp_sparse_candidate_bound {r : ℕ} {β : Type*} [Fintype β]
    (n : Fin r → ℕ) (b : β → ℕ) (e : Fin r → β → ℕ)
    (hb : ∀ j, 2 ≤ b j) (hrep : ∀ i, radixModulus b (e i) = n i) :
    finiteSeparationCandidateCount (fun c : RadixCoordinate e =>
      localSeparationMasks (radixSupport e c) (b c.1)) ≤
      radixCoordinateCount e * 2 ^ (2 * (interactionPairs n).card) := by
  simpa only [radix_coordinate_card] using
    finite_separation_sparse_candidate_bound
      (fun c : RadixCoordinate e => localSeparationMasks (radixSupport e c) (b c.1))
      (interactionPairs n) (fun c =>
        local_masks_supported _ _ _ (radix_support_interaction n b e hb hrep c))

/-- Number of graph/subset pairs inspected after isolated vertices are removed.
This is a cardinality bound, not a bit-cost analysis of objective evaluation.-/
theorem sparse_objective_candidate_bound {r : ℕ} (n : Fin r → ℕ)
    (R : Finset (SeparationMask r)) (hR : R.card ≤ 2 ^ (interactionPairs n).card) :
    (R ×ˢ (interactionVertices n).powerset).card ≤ 2 ^ (3 * (interactionPairs n).card) := by
  rw [card_product, card_powerset]
  calc
    _ ≤ 2 ^ (interactionPairs n).card * 2 ^ (2 * (interactionPairs n).card) :=
      Nat.mul_le_mul hR
        (Nat.pow_le_pow_right (by decide) (interaction_vertices_card n))
    _ = _ := by rw [← pow_add]; congr 1; omega

/-- Sparse bounds hold for every positive input, without a supplied radix certificate.
The prime representation establishes existence, not an efficient factorization.-/
theorem prime_dp_sparse_bounds {r : ℕ} (n : Fin r → ℕ) (hn : ∀ i, 0 < n i) :
    (primeDP n).card ≤ 2 ^ (interactionPairs n).card ∧
    finiteSeparationCandidateCount (fun c : RadixCoordinate (inputPrimeExponents n) =>
      localSeparationMasks (radixSupport (inputPrimeExponents n) c)
        (inputPrimeRadix n c.1)) ≤
      (∑ i, Nat.clog 2 (n i)) * 2 ^ (2 * (interactionPairs n).card) ∧
    (primeDP n ×ˢ (interactionVertices n).powerset).card ≤
      2 ^ (3 * (interactionPairs n).card) := by
  have hs : (primeDP n).card ≤ 2 ^ (interactionPairs n).card :=
    radix_dp_sparse_state_bound n _ _ (fun p => (input_radix_prime n p).two_le)
      (input_radix_representation n hn)
  refine ⟨hs, ?_, sparse_objective_candidate_bound n _ hs⟩
  exact (radix_dp_sparse_candidate_bound n _ _ (fun p => (input_radix_prime n p).two_le)
    (input_radix_representation n hn)).trans
    (Nat.mul_le_mul_right _ (prime_dp_coordinate_bound n hn))

end Erdos278
