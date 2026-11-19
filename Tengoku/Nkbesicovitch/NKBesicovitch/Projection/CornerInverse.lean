/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerCode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Reconstructing a corner from its code

The first line, last-line intercept, and corner code determine the full corner.
The inverse has the two nonzero factors `a-b` and `b-a` required by equation (30)
of the supplied manuscript.
-/

@[expose] public section

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Recover a corner from its first line, last intercept, and code.-/
noncomputable def cornerFromCode (a b c κ : ℝ) (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    CornerCoordinates m :=
  let ξ₃ := (a - b)⁻¹ • (z - κ • atHeight c g)
  let ξ₂ := (b - a)⁻¹ • (x + b • ξ₃ - atHeight a g)
  (lineAt a (atHeight a g) ξ₂, (g.2, ξ₃))

/--
@isnad1 id=eq.0h8v.s5.e234400c4250 from=translated src=- shape=aa9ad5bd vocab=866103a8
-/
theorem first_cornerFromCode (a b c κ : ℝ) (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    cornerFirst a (cornerFromCode a b c κ g x z) = g := by
  simp [cornerFirst, cornerFromCode, atHeight_lineAt, lineAt_atHeight]

/--
@isnad1 id=eq.1h8v.s7.34a751f817db from=translated src=- shape=019b5ef9 vocab=b3d7ef76
-/
theorem last_cornerFromCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) :
    cornerLast b (cornerFromCode a b c κ g x z) =
      (x, (a - b)⁻¹ • (z - κ • atHeight c g)) := by
  dsimp only [cornerLast, cornerFromCode]
  rw [atHeight_lineAt, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm), one_smul]
  simp [lineAt]

/--
@isnad1 id=eq.1h8v.s5.dd73cd0f65d3 from=translated src=- shape=3e309e4a vocab=5639fc96
-/
theorem cornerCode_cornerFromCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (g : Line m) (x z : EuclideanSpace ℝ (Fin m)) : cornerCode a b c κ
      (cornerFromCode a b c κ g x z) = z := by
  rw [cornerCode, first_cornerFromCode]
  change κ • atHeight c g + (a - b) • ((a - b)⁻¹ • (z - κ • atHeight c g)) = z
  rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab), one_smul]
  module

/--
@isnad1 id=eq.1h6v.s5.05fcee577799 from=translated src=- shape=1988ace8 vocab=a8abaede
-/
theorem cornerFromCode_cornerCode {a b : ℝ} (hab : a ≠ b) (c κ : ℝ)
    (p : CornerCoordinates m) :
    cornerFromCode a b c κ (cornerFirst a p) (cornerLast b p).1 (cornerCode a b c κ p) = p := by
  have h₃ : (a - b)⁻¹ • (cornerCode a b c κ p - κ • atHeight c (cornerFirst a p)) = p.2.2 := by
    simp [cornerCode, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab)]
  have h₂ : (b - a)⁻¹ • ((cornerLast b p).1 + b • p.2.2 -
      atHeight a (cornerFirst a p)) = p.1.2 := by
    rw [atHeight_cornerFirst]
    have he : (cornerLast b p).1 + b • p.2.2 - atHeight a p.1 = (b - a) • p.1.2 := by
      unfold cornerLast lineAt atHeight
      module
    rw [he, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab.symm), one_smul]
  dsimp only [cornerFromCode]
  rw [h₃, h₂, atHeight_cornerFirst, lineAt_atHeight]
  rfl

/--
@isnad1 id=continuo.0h5v.s8.59032a3d6377 from=translated src=- shape=9c1eeb13 vocab=d345f372
-/
theorem continuous_cornerFromCode (a b c κ : ℝ) :
    Continuous (fun p : Line m × (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) ↦
      cornerFromCode a b c κ p.1 p.2.1 p.2.2) := by
  unfold cornerFromCode lineAt atHeight
  fun_prop

end NKBesicovitch.Projection
