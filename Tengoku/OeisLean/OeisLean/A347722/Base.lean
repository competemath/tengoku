/-
OEIS A347722: the base case `D n 0 = h n`.

`D n 0` counts the idempotent maps on `Fin n`. Sorting them by their set `A` of fixed points,
the maps with fixed-point set `A` are exactly those that fix `A` pointwise and send every other
point into `A`, so there are `|A| ^ (n - |A|)` of them.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Nat.Choose.Sum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.D_zero` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.Base

open Finset

/-- The idempotent maps with fixed-point set `A` form a product: a point of `A` goes to itself,
any other point goes anywhere in `A`.
@isnad1 id=eq.0h2v.s7.38299ef0c395 from=translated src=- shape=947bb586 vocab=2c8df924
-/
theorem fiber_eq {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun g : Fin n → Fin n => Idem g ∧ (univ.filter fun v => g v = v) = A)
      = Fintype.piFinset (fun v => if v ∈ A then {v} else A) := by
  ext g
  simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hI, rfl⟩ v
    by_cases hv : g v = v
    · simp [hv]
    · simp [hv, hI v]
  · intro H
    have h1 : ∀ v ∈ A, g v = v := fun v hv => by simpa [hv] using H v
    have h2 : ∀ v, v ∉ A → g v ∈ A := fun v hv => by simpa [hv] using H v
    refine ⟨fun v => ?_, ?_⟩
    · have hgv : g v ∈ A := by
        by_cases hv : v ∈ A
        · rw [h1 v hv]; exact hv
        · exact h2 v hv
      exact h1 _ hgv
    · ext v
      simp only [mem_filter, mem_univ, true_and]
      refine ⟨fun e => ?_, h1 v⟩
      by_contra hv
      exact hv (e ▸ h2 v hv)

/-- There are `|A| ^ (n - |A|)` idempotent maps with fixed-point set `A`.
@isnad1 id=eq.0h2v.s7.eb71e47023a2 from=translated src=- shape=7cacafc4 vocab=faceb0e8
-/
theorem card_fiber {n : ℕ} (A : Finset (Fin n)) :
    (univ.filter fun g : Fin n → Fin n => Idem g ∧ (univ.filter fun v => g v = v) = A).card
      = A.card ^ (n - A.card) := by
  rw [fiber_eq, Fintype.card_piFinset]
  have : ∀ v : Fin n, (if v ∈ A then ({v} : Finset (Fin n)) else A).card
      = if v ∈ A then 1 else A.card := fun v => by split_ifs <;> simp
  simp only [this]
  have hc : (univ.filter fun v : Fin n => v ∉ A) = Aᶜ := by ext v; simp
  rw [prod_ite, prod_const_one, one_mul, prod_const, hc, card_compl, Fintype.card_fin]

/-- The number of idempotent maps on `Fin n`.
@isnad1 id=eq.0h1v.s5.37209f7e2968 from=translated src=- shape=3c9c0c8c vocab=b7781779
-/
theorem card_idem (n : ℕ) :
    (univ.filter fun g : Fin n → Fin n => Idem g).card = h n := by
  rw [card_eq_sum_card_fiberwise (f := fun g : Fin n → Fin n => univ.filter fun v => g v = v)
    (t := (univ : Finset (Fin n)).powerset) (fun g _ => by simp)]
  simp only [filter_filter, card_fiber]
  rw [sum_powerset_apply_card (fun k => k ^ (n - k))]
  simp [h]

end A347722.Base

namespace A347722

/-- With no point constrained, `D n 0` counts all idempotent maps on `n` points, and there are
`h n = ∑ k, C(n,k) k^(n-k)` of them.
@isnad1 id=eq.0h1v.s3.48b7a4420190 from=translated src=- shape=53eb01b5 vocab=1c699846
-/
theorem D_zero (n : ℕ) : D n 0 = h n := by
  rw [← Base.card_idem]
  unfold D
  congr 1
  apply Finset.filter_congr
  intro g _
  simp

end A347722

