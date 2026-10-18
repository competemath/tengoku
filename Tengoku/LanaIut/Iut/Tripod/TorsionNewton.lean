/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku.LanaIut.Iut.Torsion.Count
import Tengoku.LanaIut.Iut.Tripod.Legendre
import Tengoku
import Tengoku.Seed.NumberTheory.NumberField.Completion.FinitePlace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Torsion points on an integral model are almost integral

Let `W : y² = x³ + a₂x² + a₄x + a₆` be a Weierstrass curve over a number field `K` and `w` a
finite place of `K` at which `a₂, a₄, a₆` are integral. If `P = (x, y)` is an affine point with
`n • P = 0` (`n ≥ 1`), then `|n|_w² · |x|_w ≤ 1` (`Iut.TorsionNewton.apply_x_le`): the
`x`-coordinate is a root of the division polynomial `ΨSqₙ` (`Iut.Torsion.smul_eq_zero_iff_ΨSq`),
whose leading coefficient is `n²` and whose other coefficients are integral, and a dominant-term
(Newton polygon) argument bounds the root. In particular the `x`-coordinates of torsion points of
order prime to the residue characteristic are integral.
-/

namespace Iut.TorsionNewton

open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

/-- The ultrametric inequality for finite sums: if every term has `|·|_w ≤ B` and `B ≥ 0`,
so does the sum. -/
lemma apply_sum_le {ι : Type*} (s : Finset ι) (f : ι → K) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, w (f i) ≤ B) : w (∑ i ∈ s, f i) ≤ B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hB]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (FinitePlace.add_le w _ _).trans (max_le (hf i (Finset.mem_insert_self _ _))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The subring of `w`-integral elements. -/
def integers : Subring K where
  carrier := {z | w z ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul] at ha hb ⊢
    exact mul_le_one₀ ha (apply_nonneg w b) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (FinitePlace.add_le w a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

lemma mem_integers {z : K} : z ∈ integers w ↔ w z ≤ 1 := Iff.rfl

/-- The integral model of `W` over the `w`-integral elements. -/
def intModel (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) : WeierstrassCurve (integers w) :=
  ⟨⟨W.a₁, h₁⟩, ⟨W.a₂, h₂⟩, ⟨W.a₃, h₃⟩, ⟨W.a₄, h₄⟩, ⟨W.a₆, h₆⟩⟩

lemma intModel_map (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1) (h₃ : w W.a₃ ≤ 1)
    (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) :
    (intModel w W h₁ h₂ h₃ h₄ h₆).map (integers w).subtype = W := rfl

/-- The coefficients of the division polynomials of an integral model are integral. -/
lemma apply_coeff_ΨSq_le_one (W : Affine K) (h₁ : w W.a₁ ≤ 1) (h₂ : w W.a₂ ≤ 1)
    (h₃ : w W.a₃ ≤ 1) (h₄ : w W.a₄ ≤ 1) (h₆ : w W.a₆ ≤ 1) (n : ℤ) (k : ℕ) :
    w ((W.ΨSq n).coeff k) ≤ 1 := by
  rw [← intModel_map w W h₁ h₂ h₃ h₄ h₆, map_ΨSq, coeff_map]
  exact ((intModel w W h₁ h₂ h₃ h₄ h₆).ΨSq n).coeff k |>.2

end Iut.TorsionNewton

/-! ### Legendre curves with a non-integral parameter -/

namespace Iut.TorsionNewton

open WeierstrassCurve WeierstrassCurve.Affine NumberField Iut.Tripod
open scoped Classical

variable {K : Type*} [Field K] [NumberField K] (w : FinitePlace K)

end Iut.TorsionNewton
