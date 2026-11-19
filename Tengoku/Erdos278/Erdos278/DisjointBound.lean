import Tengoku.Erdos278.Erdos278.Density
import Tengoku.Erdos278.Erdos278.PrivateFactors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

theorem union_card_eq_iff_pairwise_disjoint {ι α : Type*}
    [DecidableEq ι] [DecidableEq α] (s : Finset ι) (t : ι → Finset α) :
    (s.biUnion t).card = ∑ i ∈ s, (t i).card ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (t i) (t j) := by
  constructor
  · induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
      intro h
      rw [Finset.biUnion_insert, Finset.sum_insert hk] at h
      have htail : (s.biUnion t).card ≤ ∑ i ∈ s, (t i).card := Finset.card_biUnion_le
      have hunion := Finset.card_union_le (t k) (s.biUnion t)
      have heqtail : (s.biUnion t).card = ∑ i ∈ s, (t i).card := by omega
      have hequnion : (t k ∪ s.biUnion t).card = (t k).card + (s.biUnion t).card := by omega
      have hdis := Finset.card_union_eq_card_add_card.mp hequnion
      have hhead (i : ι) (hi : i ∈ s) : Disjoint (t k) (t i) := by
        apply hdis.mono_right
        intro x hx
        exact Finset.mem_biUnion.mpr ⟨i, hi, hx⟩
      intro i hi j hj hij
      rcases Finset.mem_insert.mp hi with rfl | his
      · rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact (hij rfl).elim
        · exact hhead j hjs
      · rcases Finset.mem_insert.mp hj with rfl | hjs
        · exact (hhead i his).symm
        · exact ih heqtail i his j hjs hij
  · intro h
    exact Finset.card_biUnion h

theorem residue_disjoint_iff (L m n : ℕ) (hL : 0 < L)
    (hm : m ∣ L) (hn : n ∣ L) (a b : ℤ) :
    Disjoint (residueFinset L m a) (residueFinset L n b) ↔
      ¬ (a ≡ b [ZMOD m.gcd n]) := by
  constructor
  · intro hd hc
    obtain ⟨z, hzm, hzn⟩ := crt_two m n a b hc
    let w : ℤ := z % L
    have hLp : (0 : ℤ) < L := by exact_mod_cast hL
    have hwI : w ∈ Finset.Ico 0 (L : ℤ) :=
      Finset.mem_Ico.mpr ⟨Int.emod_nonneg _ hLp.ne', Int.emod_lt_of_pos _ hLp⟩
    have hwz : w ≡ z [ZMOD L] := Int.mod_modEq _ _
    have hwm : w ∈ residueFinset L m a := Finset.mem_filter.mpr
      ⟨hwI, (hwz.of_dvd (Int.natCast_dvd_natCast.mpr hm)).trans hzm⟩
    have hwn : w ∈ residueFinset L n b := Finset.mem_filter.mpr
      ⟨hwI, (hwz.of_dvd (Int.natCast_dvd_natCast.mpr hn)).trans hzn⟩
    exact Finset.disjoint_left.mp hd hwm hwn
  · intro hc
    apply Finset.disjoint_left.mpr
    intro w hwm hwn
    have hwma := (Finset.mem_filter.mp hwm).2
    have hwnb := (Finset.mem_filter.mp hwn).2
    exact hc ((hwma.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left m n))).symm.trans
      (hwnb.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right m n))))

theorem reciprocal_sum_as_card_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) (hn : ∀ i ∈ s, 0 < n i)
    (L : ℕ) (hL : 0 < L) (hd : ∀ i ∈ s, n i ∣ L) :
    (∑ i ∈ s, (1 : ℚ) / n i) =
      ((∑ i ∈ s, (residueFinset L (n i) (a i)).card : ℕ) : ℚ) / L := by
  rw [Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact (residue_ratio (n i) L (hn i hi) hL (hd i hi) (a i)).symm

theorem density_le_reciprocal_sum {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    density s n a ≤ ∑ i ∈ s, (1 : ℚ) / n i := by
  have hL : 0 < s.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i hi).ne'))
  rw [reciprocal_sum_as_card_sum s n a hn (s.lcm n) hL (fun _ hi => dvd_lcm hi)]
  unfold density coveredFinset
  apply (div_le_div_iff_of_pos_right (by exact_mod_cast hL)).mpr
  exact_mod_cast (Finset.card_biUnion_le (s := s)
    (t := fun i => residueFinset (s.lcm n) (n i) (a i)))

/-- Equality in the union bound is exactly pairwise incompatibility.
This is proved from cardinalities, not from cancellation of alternating sums.-/
theorem density_eq_reciprocal_sum_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    density s n a = ∑ i ∈ s, (1 : ℚ) / n i ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Compatible n a i j := by
  have hL : 0 < s.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i hi).ne'))
  have hLQ : ((s.lcm n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  have cancel (u v : ℕ) :
      (u : ℚ) / (s.lcm n : ℕ) = (v : ℚ) / (s.lcm n : ℕ) ↔ u = v := by
    constructor
    · intro h
      field_simp [hLQ] at h
      exact_mod_cast h
    · rintro rfl
      rfl
  rw [reciprocal_sum_as_card_sum s n a hn (s.lcm n) hL (fun _ hi => dvd_lcm hi)]
  unfold density coveredFinset
  rw [cancel, union_card_eq_iff_pairwise_disjoint]
  constructor
  · intro h i hi j hj hij
    exact (residue_disjoint_iff _ _ _ hL (dvd_lcm hi) (dvd_lcm hj) _ _).mp (h i hi j hj hij)
  · intro h i hi j hj hij
    exact (residue_disjoint_iff _ _ _ hL (dvd_lcm hi) (dvd_lcm hj) _ _).mpr (h i hi j hj hij)

theorem maximum_attains_union_bound_iff {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (n : ι → ℕ) (hn : ∀ i ∈ s, 0 < n i) :
    (∃ a, (∀ b, density s n b ≤ density s n a) ∧
      density s n a = ∑ i ∈ s, (1 : ℚ) / n i) ↔
      ∃ a, ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Compatible n a i j := by
  constructor
  · rintro ⟨a, _, ha⟩
    exact ⟨a, (density_eq_reciprocal_sum_iff s n hn a).mp ha⟩
  · rintro ⟨a, ha⟩
    have heq := (density_eq_reciprocal_sum_iff s n hn a).mpr ha
    refine ⟨a, ?_, heq⟩
    intro b
    rw [heq]
    exact density_le_reciprocal_sum s n hn b

/-- Arithmetic correctness of the reduction from disjoint feasibility for a
positive list to upper-bound attainment for pairwise distinct positive moduli.
Polynomial construction time and the external NP-hardness theorem are not
represented by this theorem.-/
theorem distinct_union_bound_reduction {r : ℕ} (n : Fin r → ℕ)
    (hn : ∀ i, 0 < n i) :
    ∃ m : Fin r → ℕ, (∀ i, 0 < m i) ∧ Function.Injective m ∧
      ((∃ a, ∀ i j, i ≠ j → ¬ Compatible n a i j) ↔
        ∃ a, (∀ b, density univ m b ≤ density univ m a) ∧
          density univ m a = ∑ i, (1 : ℚ) / m i) := by
  obtain ⟨m, hm, hinj, heq⟩ := distinct_moduli_preserving_compatibility n hn
  refine ⟨m, hm, hinj, ?_⟩
  rw [maximum_attains_union_bound_iff univ m (fun i _ => hm i)]
  simp only [mem_univ, forall_const]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i j hij hc => ha i j hij ((heq a i j).mp hc)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, fun i j hij hc => ha i j hij ((heq a i j).mpr hc)⟩

end Erdos278
