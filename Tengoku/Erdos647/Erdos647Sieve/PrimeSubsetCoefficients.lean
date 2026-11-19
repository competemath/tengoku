/-
Elementary coefficients as sums over subsets of INDEX sets.
New implementation source; not compiled in the assistant environment.
No positivity or distinctness of weight values is assumed. Distinctness is
required only of the enumerating indices. Accepted source files are unchanged.
-/
import Tengoku.Erdos647.Erdos647Sieve.Bonferroni

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false
open scoped BigOperators

noncomputable section
namespace Erdos647Sieve
open Bonferroni

/-- The insertion recurrence for the degree-q subset sum.-/
theorem sum_powersetCard_succ_insert (s : Finset ℕ) (a : ℕ)
    (ha : a ∉ s) (w : ℕ → ℝ) (q : ℕ) :
    (∑ S ∈ (insert a s).powersetCard (q + 1), ∏ p ∈ S, w p) =
      (∑ S ∈ s.powersetCard (q + 1), ∏ p ∈ S, w p) +
        w a * (∑ S ∈ s.powersetCard q, ∏ p ∈ S, w p) := by
  classical
  have hnot : ∀ {S : Finset ℕ}, S ⊆ s → a ∉ S := by
    intro S hS haS
    exact ha (hS haS)
  have hdisj : Disjoint (s.powersetCard (q + 1))
      ((s.powersetCard q).image (insert a)) := by
    apply Finset.disjoint_left.mpr
    intro S hS hImage
    obtain ⟨T, _hT, hTS⟩ := Finset.mem_image.mp hImage
    have haS : a ∈ S := by
      rw [← hTS]
      exact Finset.mem_insert_self a T
    exact hnot (Finset.mem_powersetCard.mp hS).1 haS
  have hinj : Set.InjOn (insert a) (s.powersetCard q : Set (Finset ℕ)) := by
    intro S hS T hT hEq
    have haS : a ∉ S := hnot (Finset.mem_powersetCard.mp hS).1
    have haT : a ∉ T := hnot (Finset.mem_powersetCard.mp hT).1
    apply Finset.ext
    intro p
    by_cases hpa : p = a
    · subst p
      simp only [haS, haT]
    · have hm : p ∈ insert a S ↔ p ∈ insert a T := by rw [hEq]
      simpa only [Finset.mem_insert, hpa, false_or] using hm
  rw [Finset.powersetCard_succ_insert ha q, Finset.sum_union hdisj,
    Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  exact Finset.prod_insert (hnot (Finset.mem_powersetCard.mp hS).1)

/-- Any duplicate-free enumeration of indices gives the same subset polynomial.
The real values w(i) may coincide or be negative.-/
theorem elementary_map_eq_sum_powersetCard : ∀ (l : List ℕ), l.Nodup →
    ∀ (w : ℕ → ℝ) (q : ℕ), elementary (l.map w) q =
      ∑ S ∈ l.toFinset.powersetCard q, ∏ p ∈ S, w p := by
  classical
  intro l
  induction l with
  | nil =>
      intro _hl w q
      cases q with
      | zero => simp
      | succ q =>
          have he : (∅ : Finset ℕ).powersetCard (q + 1) = ∅ :=
            Finset.powersetCard_eq_empty.mpr (by simp)
          simp [elementary, he]
  | cons a l ih =>
      intro hl w q
      have ha : a ∉ l.toFinset := by
        simpa only [List.mem_toFinset] using (List.nodup_cons.mp hl).1
      have hnodup : l.Nodup := (List.nodup_cons.mp hl).2
      cases q with
      | zero => simp
      | succ q =>
          simp only [List.map_cons, elementary, List.toFinset_cons]
          rw [sum_powersetCard_succ_insert l.toFinset a ha w q,
            ih hnodup w (q + 1), ih hnodup w q]

/-- Exact finite-index form, preserving repeated weight values.-/
theorem elementary_toList_eq_sum_powersetCard (s : Finset ℕ)
    (w : ℕ → ℝ) (q : ℕ) :
    elementary (s.toList.map w) q =
      ∑ S ∈ s.powersetCard q, ∏ p ∈ S, w p := by
  classical
  simpa only [Finset.toList_toFinset] using
    elementary_map_eq_sum_powersetCard s.toList s.nodup_toList w q

/-- Enumeration order is irrelevant; indices, not weight values, are compared.-/
theorem elementary_map_eq_of_toFinset_eq (l₁ l₂ : List ℕ)
    (h₁ : l₁.Nodup) (h₂ : l₂.Nodup) (hset : l₁.toFinset = l₂.toFinset)
    (w : ℕ → ℝ) (q : ℕ) :
    elementary (l₁.map w) q = elementary (l₂.map w) q := by
  rw [elementary_map_eq_sum_powersetCard l₁ h₁ w q,
    elementary_map_eq_sum_powersetCard l₂ h₂ w q, hset]

end Erdos647Sieve
end
