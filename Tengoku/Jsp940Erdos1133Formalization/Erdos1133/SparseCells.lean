import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Sparse, separated packets for arbitrary finite node sets. The unit gap
between adjacent closed core intervals avoids endpoint double counting. -/

noncomputable section
open scoped BigOperators
open Finset Set

namespace Erdos1133

/-- Among finitely many residue classes, one retains at least the average
number of indices, with an exact integer inequality.
@isnad1 id=ex.1h2v.s6.02fe01a620e5 from=translated src=- shape=ee01b272 vocab=0432e2f3
-/
theorem exists_large_residue (s : Finset ℕ) (K : ℕ) (hK : 0 < K) :
    ∃ r < K, s.card ≤ K * (s.filter fun i => i % K = r).card := by
  classical
  obtain ⟨r, hr, hmax⟩ := (Finset.range K).exists_max_image
    (fun r => (s.filter fun i => i % K = r).card) (by simpa using Nat.ne_of_gt hK)
  refine ⟨r, Finset.mem_range.mp hr, ?_⟩
  have hsum := Finset.sum_le_sum (fun j hj => hmax j hj)
  have hpart : s.card = ∑ j ∈ Finset.range K, (s.filter fun i => i % K = j).card :=
    Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i hK))
  rw [hpart]
  simpa using hsum

/--
@isnad1 id=pairwise.0h3v.s8.86a3f578b72a from=translated src=- shape=8446ca80 vocab=e0aaa214
-/
theorem cell_cores_disjoint (Γ : Finset ℝ) (ρ : ℕ) (a : ℝ) :
    Pairwise (fun i j : ℕ => Disjoint
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*i)| ≤ ρ)
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*j)| ≤ ρ)) := by
  classical
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := abs_le.mp (Finset.mem_filter.mp hxi).2
  have hj := abs_le.mp (Finset.mem_filter.mp hxj).2
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hcast : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
    push_cast at hi hj
    nlinarith
  · have hcast : (j : ℝ) + 1 ≤ i := by exact_mod_cast hji
    push_cast at hi hj
    nlinarith

/-- A genuine counting bound: all closed cores are disjoint, so every dense
core consumes at least `2ρ+2` distinct nodes.
@isnad1 id=other.0h4v.s8.c63abe1b5a36 from=translated src=- shape=571f2878 vocab=308ab135
-/
theorem sparse_cells_count (Γ : Finset ℝ) (ρ m : ℕ) (a : ℝ) :
    let good := (Finset.range m).filter fun (i : ℕ) =>
      (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*(i : ℝ))| ≤ ρ).card ≤ 2*ρ+1
    (2*ρ+2) * m ≤ Γ.card + (2*ρ+2) * good.card := by
  classical
  let cell : ℕ → Finset ℝ := fun i =>
    Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*i)| ≤ ρ
  let good := (Finset.range m).filter fun i => (cell i).card ≤ 2*ρ+1
  let bad := (Finset.range m) \ good
  change (2*ρ+2) * m ≤ Γ.card + (2*ρ+2) * good.card
  have hd : (↑bad : Set ℕ).PairwiseDisjoint cell := fun i _ j _ hij =>
    cell_cores_disjoint Γ ρ a hij
  have hsubset : bad.biUnion cell ⊆ Γ := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp hxi).1
  have hcard : ∑ i ∈ bad, (cell i).card ≤ Γ.card := by
    rw [← Finset.card_biUnion hd]
    exact Finset.card_le_card hsubset
  have hbad : (2*ρ+2)*bad.card ≤ Γ.card := by
    have hsum := Finset.sum_le_sum (s := bad) (fun i hi =>
      show 2*ρ+2 ≤ (cell i).card from by
        have hin := Finset.mem_sdiff.mp hi
        have hn : ¬ (cell i).card ≤ 2*ρ+1 := by
          intro hh
          exact hin.2 (Finset.mem_filter.mpr ⟨hin.1, hh⟩)
        omega)
    have hh : (2*ρ+2)*bad.card ≤ ∑ i ∈ bad, (cell i).card := by
      simpa [mul_comm] using hsum
    exact hh.trans hcard
  have hpartition : bad.card + good.card = m := by
    dsimp [bad]
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
    have hle : good.card ≤ m := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range m)
    change m - good.card + good.card = m
    exact Nat.sub_add_cancel hle
  nlinarith

/-- Reindexing a large residue class by its quotient makes the spacing scale
appear directly in the integer indices used by the packet tail estimates.
@isnad1 id=ex.1h5v.s8.13b6a4472f0f from=translated src=- shape=b4dac9ec vocab=303e1d15
-/
theorem packed_sparse_cells (Γ : Finset ℝ) (ρ m K : ℕ) (hK : 0 < K) (a : ℝ) :
    ∃ r < K, ∃ s : Finset ℤ,
      (∀ j ∈ s, ∃ i < m, j = (i / K : ℕ) ∧ i % K = r) ∧
      (2*ρ+2)*m ≤ Γ.card + (2*ρ+2)*K*s.card ∧
      ∀ j ∈ s, (Γ.filter fun x =>
        |x - (a + (2*ρ+1 : ℕ)*((K : ℝ)*j+r))| ≤ ρ).card ≤ 2*ρ+1 := by
  classical
  let good := (Finset.range m).filter fun (i : ℕ) =>
    (Γ.filter fun x => |x - (a + (2*ρ+1 : ℕ)*(i : ℝ))| ≤ ρ).card ≤ 2*ρ+1
  obtain ⟨r, hr, hlarge⟩ := exists_large_residue good K hK
  let chosen := good.filter fun i => i % K = r
  let s : Finset ℤ := chosen.image fun i => (i / K : ℕ)
  have hmod (i : ℕ) (hi : i ∈ chosen) : i % K = r := (Finset.mem_filter.mp hi).2
  have hdiv (i : ℕ) (hi : i ∈ chosen) : K * (i / K) + r = i := by
    have hh := Nat.mod_add_div i K
    rw [hmod i hi] at hh
    omega
  have hs : s.card = chosen.card := by
    apply Finset.card_image_iff.mpr
    intro i hi j hj he
    change (i / K : ℤ) = (j / K : ℤ) at he
    have he' : i / K = j / K := by exact_mod_cast he
    have hi' := hdiv i hi
    have hj' := hdiv j hj
    rw [he'] at hi'
    omega
  refine ⟨r, hr, s, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1,
      rfl, hmod i hi⟩
  · have hc := sparse_cells_count Γ ρ m a
    change (2*ρ+2)*m ≤ Γ.card + (2*ρ+2)*good.card at hc
    change good.card ≤ K * chosen.card at hlarge
    rw [hs]
    nlinarith
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have hid : (K : ℝ) * (i / K : ℕ) + r = i := by exact_mod_cast hdiv i hi
    simpa only [Int.cast_natCast, hid] using
      (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2

/-- Arbitrary node sets of cardinality at most `2N` have a linear number of
sparse cores. Their centers are indexed with the exact spacing needed by the
packet estimates, and stay two spacing lengths away from the period seam.
@isnad1 id=ex.1h2v.s9.9c8009033a32 from=translated src=- shape=c465348c vocab=fe90fe05
-/
theorem separated_sparse_cells (ρ K : ℕ) (hK : 0 < K) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Γ : Finset ℝ,
      Γ.card ≤ 2*N →
      ∃ s : Finset ℤ, ∃ c : ℤ → ℝ,
        s.Nonempty ∧ η*(N : ℝ) ≤ s.card ∧
        (∀ i j : ℤ, ((2*ρ+1)*K : ℕ) * |((j-i : ℤ) : ℝ)| = |c j-c i|) ∧
        (∀ j ∈ s, -(N : ℝ) + 2*((2*ρ+1)*K : ℕ) ≤ c j ∧
          c j ≤ N - 2*((2*ρ+1)*K : ℕ)) ∧
        (∀ j ∈ s, (Γ.filter fun x => |x-c j| ≤ ρ).card ≤ 2*ρ+1) ∧
        (∀ i j : ℤ, c j-c i = ((2*ρ+1)*K : ℕ)*((j-i : ℤ) : ℝ)) := by
  classical
  let L : ℕ := 2*ρ+1
  let D : ℕ := L*K
  have hL : 0 < L := by dsimp [L]; omega
  have hD : 0 < D := Nat.mul_pos hL hK
  let B : ℕ := 4*(L+1)*D + (L+1)*L
  let N₀ : ℕ := B + 2*D + 1
  refine ⟨1/((L+1)*D : ℕ), by positivity, N₀, ?_⟩
  intro N hN Γ hΓ
  have hB : B ≤ N := by dsimp [N₀] at hN; omega
  have hNpos : 0 < N := by dsimp [N₀] at hN; omega
  have h4D : 4*D ≤ 2*N := by dsimp [N₀] at hN; omega
  let m : ℕ := (2*N-4*D)/L
  let a : ℝ := -(N : ℝ) + 2*D
  obtain ⟨r, hr, s, hw, hc, hsp⟩ := packed_sparse_cells Γ ρ m K hK a
  let c : ℤ → ℝ := fun j => a + L*((K : ℝ)*j+r)
  have hfloor : 2*N ≤ L*m + 4*D + L := by
    have hm : (2*N-4*D)%L + L*m = 2*N-4*D := Nat.mod_add_div _ _
    have hmod := Nat.mod_lt (2*N-4*D) hL
    have hsub := Nat.sub_add_cancel h4D
    omega
  have hlinear : N ≤ (L+1)*D*s.card := by
    change (L+1)*m ≤ Γ.card + (L+1)*K*s.card at hc
    have hh := Nat.mul_le_mul_left L hc
    have hf := Nat.mul_le_mul_left (L+1) hfloor
    have hg := Nat.mul_le_mul_left L hΓ
    dsimp [D, B] at hB hf ⊢
    nlinarith
  have hsn : s.Nonempty := Finset.card_pos.mp (by
    by_contra hn
    have hz : s.card = 0 := by omega
    rw [hz, mul_zero] at hlinear
    omega)
  refine ⟨s, c, hsn, ?_, ?_, ?_, ?_, ?_⟩
  · have hlin : (N : ℝ) ≤ ((L+1)*D : ℕ)*(s.card : ℝ) := by exact_mod_cast hlinear
    have hp : (0 : ℝ) < ((L+1)*D : ℕ) := by positivity
    rw [one_div, mul_comm]
    change (N : ℝ) / ((L+1)*D : ℕ) ≤ s.card
    exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hlin)
  · intro i j
    have he : c j-c i = (D : ℝ)*((j-i : ℤ) : ℝ) := by
      dsimp [c, D]
      push_cast
      ring
    have habs : |(D : ℝ)| = D := abs_of_nonneg (Nat.cast_nonneg D)
    rw [he, abs_mul, habs]
  · intro j hj
    obtain ⟨i, hi, hji, hmod⟩ := hw j hj
    have hind : K*(i/K)+r = i := by
      have hd := Nat.mod_add_div i K
      rw [hmod] at hd
      omega
    have hjcast : (K : ℝ)*(j : ℝ)+r = i := by
      rw [hji]
      exact_mod_cast hind
    have he : c j = a + (L : ℝ)*i := by dsimp [c]; rw [hjcast]
    have him : (L : ℝ)*i ≤ L*m := by
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hi.le) (Nat.cast_nonneg _)
    have hmN : L*m ≤ 2*N-4*D := Nat.mul_div_le _ _
    have hmN' : (L : ℝ)*m ≤ 2*(N : ℝ)-4*D := by
      have hnat : L*m+4*D ≤ 2*N := by omega
      have hnatr : (L : ℝ)*m+4*D ≤ 2*N := by exact_mod_cast hnat
      linarith
    rw [he]
    change -(N : ℝ)+2*D ≤ a+(L : ℝ)*i ∧ a+(L : ℝ)*i ≤ N-2*D
    dsimp [a]
    constructor
    · have hpos : (0 : ℝ) ≤ (L : ℝ)*i := by positivity
      linarith
    · linarith
  · exact hsp
  · intro i j
    dsimp [c, L]
    push_cast
    ring

/-- Leaving a `2D` margin at both ends prevents collisions across every
nonzero translate of the period, not just the immediately adjacent copy.
@isnad1 id=le.4h5v.s7.07d17208d292 from=translated src=- shape=7333b88f vocab=cd4582a6
-/
theorem center_gap_across_period {N D a b : ℝ} (hN : 0 ≤ N)
    (ha : -N+2*D ≤ a ∧ a ≤ N-2*D)
    (hb : -N+2*D ≤ b ∧ b ≤ N-2*D) (q : ℤ) (hq : q ≠ 0) :
    4*D ≤ |b-a+2*N*q| := by
  rcases lt_or_gt_of_ne hq with hq | hq
  · have hqi : q ≤ -1 := by omega
    have hq' : (q : ℝ) ≤ -1 := by exact_mod_cast hqi
    have hshift : 2*N*(q : ℝ) ≤ -2*N := by nlinarith
    have hs : 4*D ≤ -(b-a+2*N*q) := by linarith [ha.1, hb.2]
    exact hs.trans (neg_le_abs _)
  · have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hshift : 2*N ≤ 2*N*(q : ℝ) := by nlinarith
    have hs : 4*D ≤ b-a+2*N*q := by linarith [ha.2, hb.1]
    exact hs.trans (le_abs_self _)

end Erdos1133
