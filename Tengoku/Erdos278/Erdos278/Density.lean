import Tengoku.Erdos278.Erdos278.Core
import Tengoku.Seed.Data.Int.CardIntervalMod
import Tengoku.Seed.Combinatorics.Enumerative.InclusionExclusion
import Tengoku.Seed.Algebra.BigOperators.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset
variable {ι : Type*} [DecidableEq ι]

def residueFinset (L n : ℕ) (a : ℤ) : Finset ℤ :=
  (Ico 0 (L : ℤ)).filter (fun z => z ≡ a [ZMOD n])

noncomputable def coveredFinset (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) : Finset ℤ :=
  s.biUnion (fun i => residueFinset (s.lcm n) (n i) (a i))

/-- Exact fraction covered in one common period. Its asymptotic interpretation
is established separately in `AsymptoticDensity.lean`.-/
noncomputable def density (s : Finset ι) (n : ι → ℕ) (a : ι → ℤ) : ℚ :=
  (coveredFinset s n a).card / (s.lcm n : ℕ)

/-- Weighted clique inclusion-exclusion. The input relation has a reflexive
diagonal; only off-diagonal pairs impose nontrivial conditions.-/
noncomputable def graphValue (s : Finset ι) (n : ι → ℕ) (G : ι → ι → Prop) : ℚ := by
  classical
  exact ∑ t : s.powerset.filter (·.Nonempty),
    if (∀ i ∈ t.1, ∀ j ∈ t.1, G i j) then
      (-1 : ℚ) ^ (t.1.card + 1) / (t.1.lcm n : ℕ) else 0

theorem residue_card_mul (m k : ℕ) (hm : 0 < m) (a : ℤ) :
    (residueFinset (m * k) m a).card = k := by
  have hmQ : (m : ℚ) ≠ 0 := by positivity
  have heq : (((m * k : ℕ) : ℚ) - a) / (m : ℚ) =
      (k : ℚ) + (-(a : ℚ) / (m : ℚ)) := by
    push_cast
    field_simp
    ring
  have hcard := Int.Ico_filter_modEq_card 0 (m * k : ℕ)
    (r := (m : ℤ)) (by exact_mod_cast hm) a
  simp only [Int.cast_natCast, Int.cast_zero, zero_sub, heq,
    Int.ceil_natCast_add, add_sub_cancel_right, max_eq_left (Int.natCast_nonneg k)] at hcard
  exact_mod_cast hcard

theorem residue_ratio (m L : ℕ) (hm : 0 < m) (hL : 0 < L)
    (hd : m ∣ L) (a : ℤ) :
    ((residueFinset L m a).card : ℚ) / L = 1 / m := by
  obtain ⟨k, rfl⟩ := hd
  rw [residue_card_mul m k hm]
  have hmQ : (m : ℚ) ≠ 0 := by positivity
  have hkQ : (k : ℚ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hL
    exact_mod_cast this
  push_cast
  field_simp

theorem intersection_ratio (s t : Finset ι) (ht : t.Nonempty) (hts : t ⊆ s)
    (n : ι → ℕ) (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    ((t.inf' ht (fun i => residueFinset (s.lcm n) (n i) (a i))).card : ℚ) /
      (s.lcm n : ℕ) = if IsClique n a t then (1 : ℚ) / (t.lcm n : ℕ) else 0 := by
  classical
  have hL : 0 < s.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i hi).ne'))
  have htpos : 0 < t.lcm n := Nat.pos_of_ne_zero
    (Finset.lcm_ne_zero_iff.mpr (fun i hi => (hn i (hts hi)).ne'))
  by_cases hc : IsClique n a t
  · obtain ⟨z, hz⟩ := (generalized_crt t n a
      (fun i hi => (hn i (hts hi)).ne')).mpr hc
    have heq : t.inf' ht (fun i => residueFinset (s.lcm n) (n i) (a i)) =
        residueFinset (s.lcm n) (t.lcm n) z := by
      ext w
      simp only [Finset.mem_inf', residueFinset, mem_filter]
      constructor
      · intro h
        obtain ⟨i, hi⟩ := ht
        exact ⟨(h i hi).1, (solution_iff_modEq_lcm t n a hz w).mp
          (fun j hj => (h j hj).2)⟩
      · rintro ⟨hw, hcong⟩ i hi
        exact ⟨hw, (solution_iff_modEq_lcm t n a hz w).mpr hcong i hi⟩
    rw [ite_eq_left hc, heq]
    exact residue_ratio _ _ htpos hL (Finset.lcm_mono hts) z
  · have heq : t.inf' ht (fun i => residueFinset (s.lcm n) (n i) (a i)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro z hz
      apply hc
      apply (generalized_crt t n a (fun i hi => (hn i (hts hi)).ne')).mp
      refine ⟨z, fun i hi => ?_⟩
      exact (mem_filter.mp ((Finset.mem_inf' ht).mp hz i hi)).2
    simp [heq, hc]

/-- Theorem A: the actual finite-period density is the weighted clique value.-/
theorem density_eq_graphValue (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a : ι → ℤ) :
    density s n a = graphValue s n (Compatible n a) := by
  classical
  have hIE := Finset.inclusion_exclusion_card_biUnion s
    (fun i => residueFinset (s.lcm n) (n i) (a i))
  have hIEQ : ((coveredFinset s n a).card : ℚ) =
      ∑ t : s.powerset.filter (·.Nonempty),
        (-1 : ℚ) ^ (t.1.card + 1) *
          (t.1.inf' (mem_filter.mp t.2).2
            (fun i => residueFinset (s.lcm n) (n i) (a i))).card := by
    exact_mod_cast hIE
  unfold density
  rw [hIEQ, Finset.sum_div]
  unfold graphValue
  apply Finset.sum_congr rfl
  intro t _
  rw [mul_div_assoc, intersection_ratio s t.1 (mem_filter.mp t.2).2
    (mem_powerset.mp (mem_filter.mp t.2).1) n hn a]
  by_cases hc : IsClique n a t.1
  · rw [ite_eq_left hc]
    have hc' : ∀ i ∈ t.1, ∀ j ∈ t.1, Compatible n a i j := hc
    rw [ite_eq_left hc']
    ring
  · rw [ite_eq_right hc]
    have hc' : ¬ (∀ i ∈ t.1, ∀ j ∈ t.1, Compatible n a i j) := hc
    rw [ite_eq_right hc']
    simp

theorem density_eq_of_compatible (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (a b : ι → ℤ)
    (h : ∀ i j, Compatible n a i j ↔ Compatible n b i j) :
    density s n a = density s n b := by
  rw [density_eq_graphValue s n hn a, density_eq_graphValue s n hn b]
  congr 1
  funext i j
  exact propext (h i j)

def Realizable (n : ι → ℕ) (G : ι → ι → Prop) : Prop :=
  ∃ a : ι → ℤ, ∀ i j, G i j ↔ Compatible n a i j

/-- Theorem C, stated as equality of all attainable values, stronger than just
equality of the maxima.-/
theorem graph_optimization_exact (s : Finset ι) (n : ι → ℕ)
    (hn : ∀ i ∈ s, 0 < n i) (d : ℚ) :
    (∃ a, density s n a = d) ↔
      ∃ G, Realizable n G ∧ graphValue s n G = d := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Compatible n a, ⟨a, fun _ _ => Iff.rfl⟩,
      (density_eq_graphValue s n hn a).symm⟩
  · rintro ⟨G, ⟨a, ha⟩, hd⟩
    refine ⟨a, ?_⟩
    rw [density_eq_graphValue s n hn a]
    have heq : G = Compatible n a := funext (fun i => funext (fun j => propext (ha i j)))
    rwa [heq] at hd

end Erdos278
