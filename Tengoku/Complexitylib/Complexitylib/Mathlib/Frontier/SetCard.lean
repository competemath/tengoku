/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Tengoku

/-!
# Counting a finite set by its fibers

Two `Set.ncard` forms of the familiar `Finset` estimates, upstreaming candidates:

* `Set.ncard_le_mul_ncard_image`: if every fiber of `f` on `s` has at most `n` elements, then
  `s` has at most `n` times as many elements as its image.
* `Set.ncard_le_sum_ncard_fiber`: a set on which a natural-number function takes values below
  `T` has at most as many elements as the sum of its fibers over `0, ..., T - 1`.
-/

@[expose] public section

namespace Set

variable {α β : Type*}

/-- A finite set whose fibers under `f` have at most `n` elements has at most `n` times as many
elements as its image.
@isnad1 id=le.2h5v.s6.290615fd3bc8 from=translated src=- shape=23c6f7e9 vocab=7881900b
-/
theorem ncard_le_mul_ncard_image {s : Set α} (hs : s.Finite) (f : α → β) (n : ℕ)
    (h : ∀ b, (s ∩ f ⁻¹' {b}).ncard ≤ n) : s.ncard ≤ n * (f '' s).ncard := by
  classical
  lift s to Finset α using hs
  rw [ncard_coe_finset, ← Finset.coe_image, ncard_coe_finset]
  refine Finset.card_le_mul_card_image s n fun b _ => ?_
  convert h b using 1
  rw [← ncard_coe_finset]
  congr 1
  ext a
  simp

/-- A finite set on which `f` takes values below `T` is no larger than the sum of its fibers
over `0, ..., T - 1`.
@isnad1 id=le.2h4v.s6.733d5ffb900d from=translated src=- shape=1b4f4b58 vocab=9bc076bb
-/
theorem ncard_le_sum_ncard_fiber {s : Set α} (hs : s.Finite) (f : α → ℕ) (T : ℕ)
    (hf : ∀ a ∈ s, f a < T) :
    s.ncard ≤ ∑ t ∈ Finset.range T, (s ∩ f ⁻¹' {t}).ncard := by
  classical
  lift s to Finset α using hs
  rw [ncard_coe_finset,
    Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range T)
      fun a ha => Finset.mem_range.mpr (hf a ha)]
  refine Finset.sum_le_sum fun t _ => le_of_eq ?_
  rw [← ncard_coe_finset]
  congr 1
  ext a
  simp

/-- If `f` is determined by `g` on `s`, then `f` takes at most as many values on `s` as `g`.
@isnad1 id=le.2h6v.s6.c5449c9298e9 from=translated src=- shape=279922e8 vocab=bda8c867
-/
theorem ncard_image_le_ncard_image_of_determines {γ : Type*} {s : Set α} (hs : s.Finite)
    (f : α → β) (g : α → γ) (h : ∀ a ∈ s, ∀ b ∈ s, g a = g b → f a = f b) :
    (f '' s).ncard ≤ (g '' s).ncard := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀⟩
  · simp
  have : Nonempty α := ⟨a₀⟩
  refine ncard_le_ncard_of_injOn (fun y => g (Function.invFunOn f s y)) ?_ ?_ (hs.image g)
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨_, Function.invFunOn_mem ⟨a, ha, rfl⟩, rfl⟩
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    rw [← Function.invFunOn_eq (f := f) ⟨a, ha, rfl⟩, ← Function.invFunOn_eq (f := f) ⟨b, hb, rfl⟩]
    exact h _ (Function.invFunOn_mem ⟨a, ha, rfl⟩) _ (Function.invFunOn_mem ⟨b, hb, rfl⟩) hab

end Set
