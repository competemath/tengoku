/-
Copyright (c) 2026 Jonathan Ho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Ho
-/
/-
Vendored from `Vilin97/lean-pool` revision
`9c296f447f48f3242df5e65e0b6120ddffcd79a7`, file
`LeanPool/Isoperimetric/Basic.lean`.
-/
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic supremum and `rpow` lemmas for `ENNReal`

This file collects auxiliary lemmas about suprema, indexed suprema, and real
powers of `ENNReal`-valued functions used throughout the formalization of the
Prékopa–Leindler, Brunn–Minkowski, and isoperimetric inequalities.
-/
namespace Tengoku.MahlerHansenCograph end Tengoku.MahlerHansenCograph open Tengoku.MahlerHansenCograph
/-- The sum of two bounded indexed suprema in `ENNReal` equals the
indexed supremum of the pointwise sums.
@isnad1 id=eq.2h6v.s7.fa8912bc4d2f from=translated src=- shape=e51d54cf vocab=0be1b4a7
-/
lemma _root_.Tengoku.MahlerHansenCograph.biSup_add_biSup
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
@isnad1 id=ne.1h1v.s5.e5fc720aacfa from=translated src=- shape=f537d880 vocab=8f6c5351
-/
lemma _root_.Tengoku.MahlerHansenCograph.iSup_nonzero_of_nonzero {f : ℝ → ENNReal} (hf_nonzero : f ≠ 0) : iSup f ≠ 0 := by
  intro h
  apply hf_nonzero
  ext x
  simpa using le_iSup f x |>.trans_eq h

/-- The supremum of `min a n` over `n : ℕ` recovers `a`.
@isnad1 id=eq.0h1v.s5.c33f90bafc79 from=translated src=- shape=371487bd vocab=95225d22
-/
lemma _root_.Tengoku.MahlerHansenCograph.iSup_min_nat (a : ENNReal) : ⨆ (n : ℕ), min a n = a := by
  apply iSup_eq_of_forall_le_of_forall_lt_exists_gt (by simp)
  intro w hw
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hw.trans_le le_top).ne
  exact ⟨n, by simp_all⟩

/-- The supremum of `min (f x) n` over a parameter is bounded by `n`, hence not `⊤`.
@isnad1 id=ne.0h3v.s5.8342d00e4780 from=translated src=- shape=6f6be0c8 vocab=00c639db
-/
lemma _root_.Tengoku.MahlerHansenCograph.iSup_min_nat_ne_top {ι : Sort*} (n : ℕ) (f : ι → ENNReal) :
    iSup (fun x ↦ min (f x) n) ≠ ⊤ := by
  apply ne_of_lt
  rw [iSup_lt_iff]
  use n
  exact ⟨ENNReal.natCast_lt_top n, fun x ↦ min_le_right (f x) ↑n⟩

/-- `rpow` by a positive real commutes with suprema in `ENNReal`.
@isnad1 id=eq.1h3v.s6.780cf1aec5b5 from=translated src=- shape=e034b5a1 vocab=e981ebc9
-/
lemma _root_.Tengoku.MahlerHansenCograph.iSup_rpow_of_pos {ι : Sort*} {r : ℝ} (hr : r > 0) (f : ι → ENNReal) :
    (⨆ (i : ι), f i) ^ r = ⨆ (i : ι), f i ^ r :=
  (ENNReal.orderIsoRpow r hr).map_iSup f
-- Tengoku: root names of this library moved to Tengoku.MahlerHansenCograph so they do not collide with other libraries (generated)
