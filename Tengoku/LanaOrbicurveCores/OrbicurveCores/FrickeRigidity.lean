/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Tengoku.LanaOrbicurveCores.OrbicurveCores.Fricke

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fricke rigidity: a pair in `SL(2, ℝ)` is determined by its trace triple

If `A, B ∈ SL(2, ℝ)` with `|tr A| > 2` (so `A` is hyperbolic) and `tr [A, B] ≠ 2` (the pair is
irreducible), then the triple `(tr A, tr B, tr AB)` determines the pair `(A, B)` up to
simultaneous conjugation by `GL(2, ℝ)` (`OrbicurveCores.exists_conj_of_tr_eq`).

Proof: conjugate `A` to `D = diag(λ, λ⁻¹)` with `λ = (x + √(x² - 4))/2`. Then
`B ~ [[a, b], [c, d]]` where `a + d = y` and `λa + λ⁻¹d = z` determine `a, d`, and
`bc = ad - 1 ≠ 0` because `tr [A, B] = 2 - bc(λ - λ⁻¹)²`. Conjugating by `diag(t, 1)`, which
fixes `D`, rescales `b` and leaves `bc` unchanged.

This is the classical fact behind [Sijs] Lemma 1.1.1 ("these traces determine `Γ` up to
conjugacy").
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The larger eigenvalue `(x + √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigBig (x : ℝ) : ℝ := (x + Real.sqrt (x ^ 2 - 4)) / 2

/-- The smaller eigenvalue `(x - √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigSmall (x : ℝ) : ℝ := (x - Real.sqrt (x ^ 2 - 4)) / 2

section eig

variable {x : ℝ} (hx : 4 < x ^ 2)
include hx

omit hx in
lemma eig_sum : eigBig x + eigSmall x = x := by unfold eigBig eigSmall; ring

lemma eig_prod : eigBig x * eigSmall x = 1 := by
  unfold eigBig eigSmall
  have := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 by linarith)
  linear_combination (-1 / 4 : ℝ) * this

lemma eig_sub_pos : 0 < eigBig x - eigSmall x := by
  unfold eigBig eigSmall
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < x ^ 2 - 4 by linarith)
  linarith

lemma eig_ne : eigBig x ≠ eigSmall x := sub_ne_zero.mp (eig_sub_pos hx).ne'

end eig

/-- The normal form of the second matrix: `[[a, 1], [ad - 1, d]]` with
`a = (z - μy)/(λ - μ)`, `d = (λy - z)/(λ - μ)`. -/
noncomputable def normalB (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (z - eigSmall x * y) / (eigBig x - eigSmall x)
  let d := (eigBig x * y - z) / (eigBig x - eigSmall x)
  !![a, 1; a * d - 1, d]

/-- The Fricke polynomial in normal form: for `D = diag(l, m)` with `lm = 1` and
`C = [[a, b], [c, d]]` with `det C = 1`, `x² + y² + z² - xyz - 4 = -bc (l - m)²` where
`x = l + m`, `y = a + d`, `z = la + md`. -/
lemma fricke_normal {l m a b c d : ℝ} (hprod : l * m = 1) (hdet : a * d - b * c = 1) :
    (l + m) ^ 2 + (a + d) ^ 2 + (l * a + m * d) ^ 2 - (l + m) * (a + d) * (l * a + m * d) - 4 =
      -(b * c) * (l - m) ^ 2 := by
  linear_combination (4 - (a + d) ^ 2) * hprod - (l - m) ^ 2 * hdet

end OrbicurveCores
