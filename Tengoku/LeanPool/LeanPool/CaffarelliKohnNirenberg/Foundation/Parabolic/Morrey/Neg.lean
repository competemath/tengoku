/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Basic

/-!
# Neg

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- Negation leaves the parabolic Morrey seminorm invariant.
@isnad1 id=eq.0h3v.s4.37a951ef6395 from=translated src=- shape=7de1fec5 vocab=86b93f67
-/
theorem morreyNorm_neg (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => -f z) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_neg]

/-- Absolute value leaves the parabolic Morrey seminorm invariant.
@isnad1 id=eq.0h3v.s4.341504be26b0 from=translated src=- shape=7de1fec5 vocab=982fde69
-/
theorem morreyNorm_abs (p q : ℝ) (f : ParabolicPoint → ℝ) :
    morreyNorm p q (fun z => |f z|) = morreyNorm p q f := by
  simp only [morreyNorm, morreyCell, cylinderPowerIntegral, abs_abs]

end CKN.Foundation.Parabolic.Morrey
