import Tengoku.Twinprime.TwinPrime.Analytic.DyadicIntervalCover
import Tengoku.Twinprime.TwinPrime.Analytic.DyadicStaircase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Geometry of dyadic staircase corrections

Distinct tree nodes of equal height are disjoint. Their left halves are
therefore disjoint, while an antitone boundary makes their correction
intervals disjoint in the reverse order. All endpoints remain in the given
finite domains, including empty correction intervals.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- Internal tree nodes whose left children have height `ℓ`.-/
def dyadicStaircaseLevel (M k ℓ : ℕ) : Finset (ℕ × ℕ) :=
  (dyadicTreeBlocks M k).filter fun p => p.2 = ℓ + 1

/-- The endpoint formula agrees with the explicit level-indexed half length.
@isnad1 id=eq.1h4v.s6.eea1cd4551d9 from=translated src=- shape=a4f7d996 vocab=347a6c54
-/
theorem dyadicStaircaseLevel_halfLength (M k ℓ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicStaircaseLevel M k ℓ) :
    (2 : ℕ) ^ (p.2 - 1) = 2 ^ ℓ := by
  rw [(mem_filter.mp hp).2]
  simp

/-- Equal-height tree nodes are either identical or separated in their
natural left-to-right order.
@isnad1 id=or.4h4v.s7.5d7fd2a8d9f4 from=translated src=- shape=af375470 vocab=79839eca
-/
theorem dyadicTreeBlocks_same_height_separated (M k : ℕ) (p q : ℕ × ℕ)
    (hp : p ∈ dyadicTreeBlocks M k) (hq : q ∈ dyadicTreeBlocks M k)
    (hh : p.2 = q.2) (hne : p ≠ q) :
    p.1 + 2 ^ p.2 ≤ q.1 ∨ q.1 + 2 ^ q.2 ≤ p.1 := by
  induction k generalizing M with
  | zero =>
      have hp' : p = (M, 0) := by simpa [dyadicTreeBlocks] using hp
      have hq' : q = (M, 0) := by simpa [dyadicTreeBlocks] using hq
      exact (hne (hp'.trans hq'.symm)).elim
  | succ k ih =>
      rcases mem_insert.mp hp with hp | hp
      · subst p
        rcases mem_insert.mp hq with hq | hq
        · exact (hne hq.symm).elim
        · rcases mem_union.mp hq with hq | hq
          · have h := (mem_dyadicTreeBlocks_bounds M k q hq).2.2
            dsimp only at hh
            omega
          · have h := (mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k q hq).2.2
            dsimp only at hh
            omega
      · rcases mem_insert.mp hq with hq | hq
        · subst q
          rcases mem_union.mp hp with hp | hp
          · have h := (mem_dyadicTreeBlocks_bounds M k p hp).2.2
            dsimp only at hh
            omega
          · have h := (mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k p hp).2.2
            dsimp only at hh
            omega
        · rcases mem_union.mp hp with hp | hp <;> rcases mem_union.mp hq with hq | hq
          · exact ih M hp hq
          · exact Or.inl ((mem_dyadicTreeBlocks_bounds M k p hp).2.1.trans
              (mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k q hq).1)
          · exact Or.inr ((mem_dyadicTreeBlocks_bounds M k q hq).2.1.trans
              (mem_dyadicTreeBlocks_bounds (M + 2 ^ k) k p hp).1)
          · exact ih (M + 2 ^ k) hp hq

/--
@isnad1 id=disjoint.4h4v.s7.49b5d0c49694 from=translated src=- shape=763a0657 vocab=0ccf98a2
-/
theorem dyadicTreeBlocks_same_height_disjoint (M k : ℕ) (p q : ℕ × ℕ)
    (hp : p ∈ dyadicTreeBlocks M k) (hq : q ∈ dyadicTreeBlocks M k)
    (hh : p.2 = q.2) (hne : p ≠ q) :
    Disjoint (Ico p.1 (p.1 + 2 ^ p.2)) (Ico q.1 (q.1 + 2 ^ q.2)) := by
  apply disjoint_left.mpr
  intro n hn hn'
  have h1 := mem_Ico.mp hn
  have h2 := mem_Ico.mp hn'
  rcases dyadicTreeBlocks_same_height_separated M k p q hp hq hh hne with h | h <;> omega

/--
@isnad1 id=le.1h4v.s6.858632caf866 from=translated src=- shape=977aab8e vocab=95e64635
-/
theorem dyadicStaircaseLevel_half_le_length (M k ℓ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicStaircaseLevel M k ℓ) :
    2 ^ (p.2 - 1) ≤ (2 : ℕ) ^ p.2 := by
  have hh := (mem_filter.mp hp).2
  rw [hh]
  simp only [Nat.add_sub_cancel, pow_succ]
  omega

/-- The left-child intervals lie in the whole first-factor domain.
@isnad1 id=and.1h4v.s7.90294904b828 from=translated src=- shape=bbc816b4 vocab=f78a8f4b
-/
theorem dyadicStaircaseLevel_left_valid (M k ℓ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicStaircaseLevel M k ℓ) :
    M ≤ p.1 ∧ p.1 ≤ p.1 + 2 ^ (p.2 - 1) ∧
      p.1 + 2 ^ (p.2 - 1) ≤ M + 2 ^ k := by
  have hb := mem_dyadicTreeBlocks_bounds M k p (mem_filter.mp hp).1
  have hhalf := dyadicStaircaseLevel_half_le_length M k ℓ p hp
  exact ⟨hb.1, Nat.le_add_right _ _, (Nat.add_le_add_left hhalf _).trans hb.2.1⟩

/-- The two arguments at which a correction evaluates the boundary are
members of the whole first-factor domain, in the indicated order.
@isnad1 id=and.1h4v.s8.a7eb094db278 from=translated src=- shape=3c9215f4 vocab=6d321037
-/
theorem dyadicStaircaseLevel_endpoint_mem (M k ℓ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicStaircaseLevel M k ℓ) :
    (p.1 + 2 ^ p.2 - 1) ∈ Ico M (M + 2 ^ k) ∧
      (p.1 + 2 ^ (p.2 - 1) - 1) ∈ Ico M (M + 2 ^ k) ∧
        p.1 + 2 ^ (p.2 - 1) - 1 ≤ p.1 + 2 ^ p.2 - 1 := by
  have hb := mem_dyadicTreeBlocks_bounds M k p (mem_filter.mp hp).1
  have hh := (mem_filter.mp hp).2
  have hpos : 0 < (2 : ℕ) ^ ℓ := by positivity
  have hhalf : 2 ^ (p.2 - 1) = (2 : ℕ) ^ ℓ := by rw [hh]; simp
  have hwhole : 2 ^ p.2 = (2 : ℕ) ^ ℓ + 2 ^ ℓ := by rw [hh, pow_succ]; omega
  simp only [mem_Ico]
  omega

/-- Left children of distinct nodes at one correction level are disjoint.
@isnad1 id=disjoint.3h5v.s7.41bf30c90d15 from=translated src=- shape=95b392db vocab=3ea8c075
-/
theorem dyadicStaircaseLevel_left_disjoint (M k ℓ : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ dyadicStaircaseLevel M k ℓ) (q : ℕ × ℕ)
    (hq : q ∈ dyadicStaircaseLevel M k ℓ) (hne : p ≠ q) :
    Disjoint (Ico p.1 (p.1 + 2 ^ (p.2 - 1)))
      (Ico q.1 (q.1 + 2 ^ (q.2 - 1))) := by
  have hd := dyadicTreeBlocks_same_height_disjoint M k p q
    (mem_filter.mp hp).1 (mem_filter.mp hq).1
    ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) hne
  exact hd.mono (Ico_subset_Ico le_rfl (Nat.add_le_add_left
    (dyadicStaircaseLevel_half_le_length M k ℓ p hp) _))
    (Ico_subset_Ico le_rfl (Nat.add_le_add_left
      (dyadicStaircaseLevel_half_le_length M k ℓ q hq) _))

/-- An antitone boundary gives valid correction intervals in the whole
second-factor domain. The correction is allowed to be empty.
@isnad1 id=and.3h7v.s8.c14a3108cb8c from=translated src=- shape=fc683b1a vocab=02d83c87
-/
theorem dyadicStaircaseLevel_correction_valid (M k ℓ N j : ℕ) (F : ℕ → ℕ)
    (hF : AntitoneOn F (Set.Ico M (M + 2 ^ k)))
    (hbound : ∀ m ∈ Ico M (M + 2 ^ k), N ≤ F m ∧ F m ≤ N + 2 ^ j)
    (p : ℕ × ℕ) (hp : p ∈ dyadicStaircaseLevel M k ℓ) :
    N ≤ F (p.1 + 2 ^ p.2 - 1) ∧
      F (p.1 + 2 ^ p.2 - 1) ≤ F (p.1 + 2 ^ (p.2 - 1) - 1) ∧
        F (p.1 + 2 ^ (p.2 - 1) - 1) ≤ N + 2 ^ j := by
  obtain ⟨hr, hl, hle⟩ := dyadicStaircaseLevel_endpoint_mem M k ℓ p hp
  exact ⟨(hbound _ hr).1, hF (mem_Ico.mp hl) (mem_Ico.mp hr) hle, (hbound _ hl).2⟩

/-- Corrections at one level are pairwise disjoint, in reverse first-factor
order. Only antitonicity is needed for this assertion.
@isnad1 id=disjoint.4h6v.s8.7c7dd64b0b1c from=translated src=- shape=f8023e53 vocab=d3df8000
-/
theorem dyadicStaircaseLevel_correction_disjoint (M k ℓ : ℕ) (F : ℕ → ℕ)
    (hF : AntitoneOn F (Set.Ico M (M + 2 ^ k)))
    (p : ℕ × ℕ) (hp : p ∈ dyadicStaircaseLevel M k ℓ)
    (q : ℕ × ℕ) (hq : q ∈ dyadicStaircaseLevel M k ℓ) (hne : p ≠ q) :
    Disjoint
      (Ico (F (p.1 + 2 ^ p.2 - 1)) (F (p.1 + 2 ^ (p.2 - 1) - 1)))
      (Ico (F (q.1 + 2 ^ q.2 - 1)) (F (q.1 + 2 ^ (q.2 - 1) - 1))) := by
  obtain ⟨hpr, hpl, _⟩ := dyadicStaircaseLevel_endpoint_mem M k ℓ p hp
  obtain ⟨hqr, hql, _⟩ := dyadicStaircaseLevel_endpoint_mem M k ℓ q hq
  have hp0 : 0 < (2 : ℕ) ^ (p.2 - 1) := by positivity
  have hq0 : 0 < (2 : ℕ) ^ (q.2 - 1) := by positivity
  have hsep := dyadicTreeBlocks_same_height_separated M k p q
    (mem_filter.mp hp).1 (mem_filter.mp hq).1
    ((mem_filter.mp hp).2.trans (mem_filter.mp hq).2.symm) hne
  apply disjoint_left.mpr
  intro n hn hn'
  have hn1 := mem_Ico.mp hn
  have hn2 := mem_Ico.mp hn'
  rcases hsep with hpq | hqp
  · have hf := hF (mem_Ico.mp hpr) (mem_Ico.mp hql)
      (show p.1 + 2 ^ p.2 - 1 ≤ q.1 + 2 ^ (q.2 - 1) - 1 by omega)
    omega
  · have hf := hF (mem_Ico.mp hqr) (mem_Ico.mp hpl)
      (show q.1 + 2 ^ q.2 - 1 ≤ p.1 + 2 ^ (p.2 - 1) - 1 by omega)
    omega

end TwinPrime.Analytic
