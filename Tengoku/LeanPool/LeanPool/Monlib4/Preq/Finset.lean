/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!

# finset

In this file we provide some elementary results for summations

-/

@[expose] public section

namespace Finset

open scoped BigOperators

/--
@isnad1 id=eq.0h8v.s6.cfec20771433 from=translated src=- shape=02329493 vocab=ee49a909
-/
theorem sum_rotate {α β γ ζ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ} {u : Finset ζ}
    {f : α → γ → ζ → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z =
      ∑ z ∈ u, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h8v.s6.a81a0d4c3eb7 from=translated src=- shape=91eda8ad vocab=ee49a909
-/
theorem sum_3_comm {α β γ ζ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ} {u : Finset ζ}
    {f : α → γ → ζ → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z =
      ∑ z ∈ u, ∑ y ∈ t, ∑ x ∈ s, f x y z := by
  rw [Finset.sum_rotate]
  congr
  ext
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h10v.s6.2d044fa9ec95 from=translated src=- shape=97d3b6a0 vocab=ee49a909
-/
theorem sum_4_rotate {α β γ ζ ε : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {f : α → γ → ζ → ε → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w =
      ∑ w ∈ v, ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, f x y z w := by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_rotate]

/--
@isnad1 id=eq.0h10v.s6.b149da96ba88 from=translated src=- shape=5540d9a0 vocab=ee49a909
-/
theorem sum_sum_comm_sum {α β γ ζ ε : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {f : α → γ → ζ → ε → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w =
      ∑ x ∈ s, ∑ y ∈ t, ∑ w ∈ v, ∑ z ∈ u, f x y z w := by
  congr
  ext x
  congr
  ext y
  nth_rw 2 [Finset.sum_comm]

/--
@isnad1 id=eq.0h8v.s6.7f268ebf336e from=translated src=- shape=ca074e2c vocab=ee49a909
-/
theorem sum_sum_sum {β α γ ζ : Type _} [AddCommMonoid β] {s : Finset γ} {t : Finset α}
    {g : Finset ζ} {f : γ → α → ζ → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ g, f x y z =
      ∑ z ∈ g, ∑ x ∈ s, ∑ y ∈ t, f x y z := by
  symm
  rw [Finset.sum_comm]
  congr
  ext
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h10v.s6.75592b281652 from=translated src=- shape=a7aa0de1 vocab=ee49a909
-/
theorem sum_4_swap_2 {β α γ ζ ε : Type _} [AddCommMonoid β] {s : Finset γ} {t : Finset α}
    {u : Finset ζ} {v : Finset ε} {f : γ → α → ζ → ε → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w =
      ∑ z ∈ u, ∑ w ∈ v, ∑ x ∈ s, ∑ y ∈ t, f x y z w := by
  rw [Finset.sum_rotate]
  congr
  ext
  rw [sum_rotate]

/--
@isnad1 id=eq.0h12v.s7.0ca69ff8bba4 from=translated src=- shape=9ac99cbd vocab=ee49a909
-/
theorem sum_5_rotate {α β γ ζ ε κ : Type _} [AddCommMonoid β] {s : Finset α} {t : Finset γ}
    {u : Finset ζ} {v : Finset ε} {k : Finset κ} {f : α → γ → ζ → ε → κ → β} :
    ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, ∑ vz ∈ k, f x y z w vz =
      ∑ vz ∈ k, ∑ x ∈ s, ∑ y ∈ t, ∑ z ∈ u, ∑ w ∈ v, f x y z w vz := by
  nth_rw 2 [Finset.sum_comm]
  congr
  ext x
  rw [Finset.sum_4_rotate]

end Finset

/--
@isnad1 id=iff.0h4v.s5.e36bb4381ba0 from=translated src=- shape=2938d055 vocab=e3b0c442
-/
theorem Forall.rotate {α β γ : Sort _} {p : α → β → γ → Prop} :
    (∀ (x : α) (y : β) (z : γ), p x y z) ↔ ∀ (z : γ) (x : α) (y : β), p x y z :=
  ⟨fun h _ _ _ => h _ _ _, fun h _ _ _ => h _ _ _⟩

/--
@isnad1 id=iff.0h5v.s5.4a461c29af83 from=translated src=- shape=41569231 vocab=e3b0c442
-/
theorem forall_forall_comm {α β γ ζ : Sort _} {p : α → β → γ → ζ → Prop} :
    (∀ (x : α) (y : β) (z : γ) (w : ζ), p x y z w) ↔ ∀ (x : α) (z : γ) (y : β) (w : ζ), p x y z w :=
  ⟨fun h _ _ _ _ => h _ _ _ _, fun h _ _ _ _ => h _ _ _ _⟩

/--
@isnad1 id=eq.0h4v.s6.67fd1ff5c81b from=translated src=- shape=ac14e2ef vocab=c80a58e2
-/
theorem Finset.sum_product_univ {β α γ : Type _} [AddCommMonoid β] [Fintype α] [Fintype γ]
    {f : γ × α → β} : ∑ x : γ × α, f x = ∑ x : γ, ∑ y : α, f (x, y) :=
  Finset.sum_product _ _ _
