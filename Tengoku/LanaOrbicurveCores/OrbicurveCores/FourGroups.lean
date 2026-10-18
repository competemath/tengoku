/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Core
import Tengoku.LanaOrbicurveCores.OrbicurveCores.FrickeRigidity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Takeuchi's four `(1;∞)`-groups, explicitly

Explicit generating pairs `(Aᵢ, Bᵢ)` in `SL(2, ℝ)` with trace triples

| case | `(tr A, tr B, tr AB)` | `A` | `B` |
|---|---|---|---|
| I | `(√5, 2√5, 5)` | `[[4, 1], [-1, 1]]/√5` | `[[3, 2], [8, 7]]/√5` |
| II | `(√6, 2√3, 3√2)` | `[[5, 1], [-1, 1]]/√6` | `[[2, 1], [5, 4]]/√3` |
| III | `(2√2, 2√2, 4)` | `[[3, 1], [1, 1]]/√2` | `[[1, 1], [1, 3]]/√2` |
| IV | `(3, 3, 3)` | `[[2, 1], [1, 1]]` | `[[0, -1], [1, 3]]` |

The numbering follows [Sijs] Table 1. By Fricke rigidity (`exists_conj_of_tr_eq`), any pair
with one of these trace triples, up to sign, is simultaneously `GL(2, ℝ)`-conjugate to
`(±Aᵢ, ±Bᵢ)`. With `takeuchi_one_infty` this gives:

* `OrbicurveCores.takeuchi_one_infty_conj`: an arithmetic `(1;∞)`-group is, up to Nielsen moves,
  signs and `GL(2, ℝ)`-conjugacy, one of the four explicit groups;
* `OrbicurveCores.canLift27_group_conj`: the same for `(1;∞)`-groups without core, assuming
  `MargulisOneInfty`.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The element `c • M` of `SL(2, ℝ)` for an integer matrix `M` of determinant `n > 0`, with
`c = 1/√n`. -/
noncomputable def scaledSL (n : ℕ) (hn : 0 < n) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M.det = n) : SL(2, ℝ) :=
  ⟨(Real.sqrt n)⁻¹ • M, by
    rw [det_smul, hM, Fintype.card_fin, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp⟩

/-- Case I: `A = [[4, 1], [-1, 1]]/√5`. -/
noncomputable def pairIA : SL(2, ℝ) := scaledSL 5 (by norm_num) !![4, 1; -1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case I: `B = [[3, 2], [8, 7]]/√5`. -/
noncomputable def pairIB : SL(2, ℝ) := scaledSL 5 (by norm_num) !![3, 2; 8, 7]
  (by simp [det_fin_two]; norm_num)
/-- Case II: `A = [[5, 1], [-1, 1]]/√6`. -/
noncomputable def pairIIA : SL(2, ℝ) := scaledSL 6 (by norm_num) !![5, 1; -1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case II: `B = [[2, 1], [5, 4]]/√3`. -/
noncomputable def pairIIB : SL(2, ℝ) := scaledSL 3 (by norm_num) !![2, 1; 5, 4]
  (by simp [det_fin_two]; norm_num)
/-- Case III: `A = [[3, 1], [1, 1]]/√2`. -/
noncomputable def pairIIIA : SL(2, ℝ) := scaledSL 2 (by norm_num) !![3, 1; 1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case III: `B = [[1, 1], [1, 3]]/√2`. -/
noncomputable def pairIIIB : SL(2, ℝ) := scaledSL 2 (by norm_num) !![1, 1; 1, 3]
  (by simp [det_fin_two]; norm_num)
/-- Case IV: `A = [[2, 1], [1, 1]]`. -/
noncomputable def pairIVA : SL(2, ℝ) := scaledSL 1 (by norm_num) !![2, 1; 1, 1]
  (by simp [det_fin_two]; norm_num)
/-- Case IV: `B = [[0, -1], [1, 3]]`. -/
noncomputable def pairIVB : SL(2, ℝ) := scaledSL 1 (by norm_num) !![0, -1; 1, 3]
  (by simp [det_fin_two])

/-- The four explicit pairs. -/
noncomputable def takeuchiPair : Fin 4 → SL(2, ℝ) × SL(2, ℝ)
  | 0 => (pairIA, pairIB)
  | 1 => (pairIIA, pairIIB)
  | 2 => (pairIIIA, pairIIIB)
  | 3 => (pairIVA, pairIVB)

lemma div_sqrt_eq_sqrt {t n X : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (h : t ^ 2 = X * n) :
    t / Real.sqrt n = Real.sqrt X := by
  have hX : 0 ≤ X := by
    by_contra hX; push Not at hX; nlinarith [sq_nonneg t]
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq hX (by positivity), div_mul_div_comm,
    Real.mul_self_sqrt hn.le, eq_div_iff hn.ne', ← h]
  ring

lemma div_sqrt_mul_sqrt_eq_sqrt {t n k X : ℝ} (ht : 0 ≤ t) (hn : 0 < n) (hk : 0 < k)
    (h : t ^ 2 = X * (n * k)) : t / (Real.sqrt n * Real.sqrt k) = Real.sqrt X := by
  rw [← Real.sqrt_mul hn.le]
  exact div_sqrt_eq_sqrt ht (by positivity) h

end OrbicurveCores
