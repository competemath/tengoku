/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku

/- This is from the Sphere Pack project, so might not actually be for mathlib.-/

-- Maybe this belongs in NumberTheory/ModularForms/SlashActions.lean, next to ModularForm.mul_slash

/-! # SlashActions -/

@[expose] public section

local notation "GL(" n ", " R ")" "⁺" => @Matrix.GLPos (Fin n) R (instDecidableEqFin n)
  (Fin.fintype n) Real.linearOrderedCommRing

open ModularForm MatrixGroups UpperHalfPlane

/- Looks like the way to fix the errors is to replace each GL(n, ℝ)⁺ with
  `@Matrix.GLPos (Fin 2) ℝ (instDecidableEqFin 2) (Fin.fintype 2) Real.linearOrderedCommRing :
  Subgroup (GL (Fin 2) ℝ)`... but it's just so ugly!
-/

/-- Slash action under -I₂ as a GL(n, ℝ)⁺ matrix. See `ModularForm.slash_neg_one'` for the SL(2, ℤ)
version.
@isnad1 id=eq.1h2v.s8.0f26a88f8ef4 from=translated src=- shape=0003c6db vocab=1981641b
-/
theorem ModularForm.slash_neg_one {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : (GL (Fin 2) ℝ)) =
    f ∣[k] (1 : (GL (Fin 2) ℝ)) := by simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]

/-- Slash action under -I₂ as a SL(2, ℤ) matrix. See `ModularForm.slash_neg_one` for the GL(n, ℝ)⁺
version.
@isnad1 id=eq.1h2v.s8.f07f95b9c077 from=translated src=- shape=f65fe986 vocab=754c0584
-/
theorem ModularForm.slash_neg_one' {k : ℤ} (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ)) := by simp [SL_slash_def, denom, hk.neg_one_zpow]

/-- See `ModularForm.slash_neg'` for the version where `g` is a SL(2, ℤ) matrix.
@isnad1 id=eq.1h3v.s8.540aeba4d3c9 from=translated src=- shape=93482d88 vocab=1981641b
-/
theorem ModularForm.slash_neg {k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]

/-- See `ModularForm.slash_neg` for the version where `g` is a GL(n, ℝ)⁺ matrix.
@isnad1 id=eq.1h3v.s7.38534ac7dd33 from=translated src=- shape=5849ee71 vocab=754c0584
-/
theorem ModularForm.slash_neg' {k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) :
    f ∣[k] (-g) = f ∣[k] g := by
  rw [SL_slash, ← slash_neg _ _ hk]
  congr
  ext
  simp
