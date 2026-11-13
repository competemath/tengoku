/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Upstream/Debate/Misc/If.lean`: removed 7 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

@[expose] public section
namespace Tengoku.AisafetyAtlas end Tengoku.AisafetyAtlas open Tengoku.AisafetyAtlas 
-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

/-!
A few if utilities
-/

/-- ↑x ≤ ↑y ↔ y → x
@isnad1 id=iff.0h4v.s5.abaf1245f6be from=translated src=- shape=03a1abb6 vocab=f6621d84
-/
lemma Tengoku.AisafetyAtlas.ite_le_ite_iff (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    (@ite _ x dx (1:ℝ) 0) ≤ (@ite _ y dy 1 0) ↔ x → y := by
  by_cases h : x
  repeat { by_cases l : y; repeat { simp only [h, l, ite_true, ite_false]; norm_num }}

/--
@isnad1 id=iff.0h4v.s5.6ddc81499547 from=translated src=- shape=ca95f7a5 vocab=003f4253
-/
lemma Tengoku.AisafetyAtlas.ite_one_zero_congr (x y : Prop) {dx : Decidable x} {dy : Decidable y} :
    @ite _ x dx (1:ℝ) 0 = @ite _ y dy (1:ℝ) 0 ↔ (x ↔ y) := by
  by_cases h : x
  repeat { by_cases l : y; repeat simp [h, l] }

/--
@isnad1 id=iff.0h2v.s4.98dd2f5c6dd7 from=translated src=- shape=47b10ebb vocab=003f4253
-/
lemma Tengoku.AisafetyAtlas.ite_one_zero_ne_zero (x : Prop) {dx : Decidable x} : @ite _ x dx (1:ℝ) 0 ≠ 0 ↔ x := by
  by_cases h : x; repeat { simp only [h, if_true, if_false]; norm_num }

/--
@isnad1 id=eq.0h3v.s6.bad24c3b77f3 from=translated src=- shape=fbb697e2 vocab=bc76f6fc
-/
lemma Tengoku.AisafetyAtlas.ite_and_one_zero (x y : Prop) {d : Decidable (x ∧ y)} :
    @ite _ (x ∧ y) d (1:ℝ) 0 =
      (@ite _ x (Classical.dec _) (1:ℝ) 0) * (@ite _ y (Classical.dec _) 1 0) := by
  rw [ite_zero_mul_ite_zero, one_mul]
  congr

/--
@isnad1 id=le.0h2v.s4.7d6b773a041e from=translated src=- shape=60cdae67 vocab=f6621d84
-/
lemma Tengoku.AisafetyAtlas.ite_one_zero_nonneg {x : Prop} {d : Decidable x} : 0 ≤ @ite _ x d (1:ℝ) 0 := by
  split_ifs; repeat norm_num
-- Tengoku: root names of this library moved to Tengoku.AisafetyAtlas so they do not collide with other libraries (generated)
