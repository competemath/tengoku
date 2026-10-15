/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
module

public import Tengoku

/-!
# Basic supremum and `rpow` lemmas for `ENNReal`

This file collects auxiliary lemmas about suprema, indexed suprema, and real
powers of `ENNReal`-valued functions used throughout the formalization of the
Prékopa–Leindler, Brunn–Minkowski, and isoperimetric inequalities.
-/

@[expose] public section

/-- The sum of two bounded indexed suprema in `ENNReal` equals the
indexed supremum of the pointwise sums.
@isnad1 id=eq.2h6v.s7.26d538f3e336 from=translated src=- shape=e51d54cf vocab=0be1b4a7
-/
lemma biSup_add_biSup
    {ι κ : Sort*}
    {p : ι → Prop} {q : κ → Prop} (hp : ∃ i, p i) (hq : ∃ j, q j)
    {f : ι → ENNReal} {g : κ → ENNReal} :
    (⨆ i, ⨆ _ : p i, f i) + (⨆ j, ⨆ _ : q j, g j) =
    (⨆ i, ⨆ j, ⨆ _ : p i, ⨆ _ : q j, f i + g j) := by
  apply le_antisymm
  · calc
      (⨆ x, ⨆ _ : p x, f x) + (⨆ y, ⨆ _ : q y, g y)
          = ⨆ x, ⨆ _ : p x, (f x + (⨆ y, ⨆ _ : q y, g y)) := by apply ENNReal.biSup_add' hp
      _ ≤ (⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, f x + g y) := by
        apply iSup₂_le
        intro x hx
        calc
          f x + (⨆ y, ⨆ _ : q y, g y) = ⨆ y, ⨆ _ : q y, (f x + g y) := by
            apply ENNReal.add_biSup' hq
          _ ≤ ⨆ x, ⨆ _ : p x, (⨆ y, ⨆ _ : q y, (f x + g y)) := by
            apply le_iSup₂ x hx
          _ = ⨆ x, ⨆ y, ⨆ _ : p x, ⨆ _ : q y, (f x + g y) := by
            apply iSup_congr; intro; exact iSup_comm
  simp only [iSup_le_iff]
  intro i j hi hj
  calc
    f i + g j ≤ (⨆ i, ⨆ (_ : p i), f i) + g j := by gcongr; apply le_iSup₂ i hi
    _ ≤ (⨆ i, ⨆ (_ : p i), f i) + ⨆ j, ⨆ (_ : q j), g j := by gcongr; apply le_iSup₂ j hj

/-- A nonzero `ENNReal`-valued function on `ℝ` has a nonzero supremum.
@isnad1 id=ne.1h1v.s5.a76591dab382 from=translated src=- shape=f537d880 vocab=8f6c5351
-/
lemma iSup_nonzero_of_nonzero {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  intro h
  apply hf_nonzero
  ext x
  simpa using le_iSup f x |>.trans_eq h

/-- The supremum of `min a n` over `n : ℕ` recovers `a`.
@isnad1 id=eq.0h1v.s4.f027d26f47e2 from=translated src=- shape=371487bd vocab=95225d22
-/
lemma iSup_min_nat (a : ENNReal) : ⨆ (n : ℕ), min a n = a := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt (by simp)
  intro w hw
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hw.trans_le le_top).ne
  exact ⟨n, by simp_all⟩

/-- The supremum of `min (f x) n` over a parameter is bounded by `n`, hence not `⊤`.
@isnad1 id=ne.0h3v.s5.3c5c013cc22f from=translated src=- shape=6f6be0c8 vocab=00c639db
-/
lemma iSup_min_nat_ne_top {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ := by
  apply ne_of_lt
  rw [iSup_lt_iff]
  use n
  exact ⟨ENNReal.natCast_lt_top n, fun x ↦ min_le_right (f x) ↑n⟩

/-- `rpow` by a positive real commutes with suprema in `ENNReal`.
@isnad1 id=eq.1h3v.s6.57a3e5d127ab from=translated src=- shape=e034b5a1 vocab=e981ebc9
-/
lemma iSup_rpow_of_pos {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup f
