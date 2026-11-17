import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Function_exists_eq_apply_sub_of_sum_range_minimalPeriod_eq_zero

set_option autoImplicit false

namespace Function
export _root_.Function (minimalPeriod_apply_iterate minimalPeriod_pos_iff_mem_periodicPts iterate_succ_apply' iterate_add_apply iterate_zero_apply isPeriodicPt_minimalPeriod minimalPeriod IsPeriodicPt iterate_eq_iterate_iff_of_lt_minimalPeriod)
open _root_.Function
namespace OrbitPrimitive

variable {X : Type*} (f : X → X) (hf : ∀ x : X, 0 < minimalPeriod f x)

def rel (x y : X) : Prop := ∃ k : ℕ, f^[k] x = y

include hf in
theorem rel_symm {x y : X} (h : rel f x y) : rel f y x := by
  obtain ⟨k, rfl⟩ := h

  refine ⟨minimalPeriod f x * k - k, ?_⟩
  have hper : IsPeriodicPt f (minimalPeriod f x) x := isPeriodicPt_minimalPeriod f x
  have h1 : f^[minimalPeriod f x * k - k] (f^[k] x) = f^[minimalPeriod f x * k] x := by
    rw [← iterate_add_apply, Nat.sub_add_cancel (Nat.le_mul_of_pos_left k (hf x))]
  rw [h1]
  exact (hper.mul_const k).eq

theorem rel_refl (x : X) : rel f x x := ⟨0, rfl⟩

theorem rel_trans {x y z : X} (h₁ : rel f x y) (h₂ : rel f y z) : rel f x z := by
  obtain ⟨k, rfl⟩ := h₁
  obtain ⟨l, rfl⟩ := h₂
  exact ⟨l + k, by rw [iterate_add_apply]⟩

def orbitSetoid (hf : ∀ x : X, 0 < minimalPeriod f x) : Setoid X where
  r := rel f
  iseqv := ⟨rel_refl f, rel_symm f hf, rel_trans f⟩

noncomputable def base (x : X) : X := (Quotient.mk (orbitSetoid f hf) x).out

theorem rel_base (x : X) : rel f (base f hf x) x := by
  have h : Quotient.mk (orbitSetoid f hf) (base f hf x) = Quotient.mk (orbitSetoid f hf) x := Quotient.out_eq _
  exact Quotient.exact (s := orbitSetoid f hf) h

open Classical in

noncomputable def idx (x : X) : ℕ := Nat.find (rel_base f hf x)

end OrbitPrimitive

end Function
