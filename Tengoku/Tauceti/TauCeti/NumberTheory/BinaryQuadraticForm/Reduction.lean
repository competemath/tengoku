/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.GroupTheory.GroupAction.Stabilizer
public import Tengoku.Tauceti.TauCeti.NumberTheory.BinaryQuadraticForm.Root
public import Tengoku.Tauceti.TauCeti.NumberTheory.HurwitzClassNumber
import Tengoku.Tauceti.TauCeti.Algebra.QuadraticDiscriminant
import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Tengoku.Tauceti.TauCeti.Analysis.Complex.UpperHalfPlane.Rho
import Tengoku.Tauceti.TauCeti.NumberTheory.Modular.Stabilizer

/-!
# The Hurwitz class number counts classes of forms

For `D ≠ 0` the Hurwitz class number `TauCeti.hurwitzClassNumber D` is *defined* as a weighted
count of the reduced forms of discriminant `-D`. This file proves that it is the weighted count of
the `SL(2, ℤ)`-classes of positive definite integral binary quadratic forms of discriminant `-D`,
each class weighted by `2 / |Stab|`, where `Stab` is the stabiliser in `SL(2, ℤ)` of any form in
the class: `-1` acts trivially on forms, so `|Stab| / 2` is the order of the stabiliser in
`PSL(2, ℤ)`, and the weight is `1/2` on the classes of multiples of `x² + y²`, `1/3` on those of
multiples of `x² + x y + y²`, and `1` on all others.

The reduction theory is transported to the upper half-plane by the root map
`TauCeti.BinaryQuadraticForm.root`, which sends `f = a x² + b x y + c y²` to the root
`τ = (-b + i √D) / (2 a)` of `a τ² + b τ + c`, and which is injective and `SL(2, ℤ)`-equivariant.
Since `re τ = -b / (2 a)` and `|τ|² = c / a`, the conditions defining a reduced form say exactly
that `τ` lies in the part of the fundamental domain `𝒟` left of its boundary identifications: the
points of `𝒟` with `re τ < 1/2` which, on the unit circle, have `re τ ≤ 0`. Every orbit of
`SL(2, ℤ)` on `ℍ` meets that region in exactly one point
(`TauCeti.ModularGroup.exists_smul_mem_fd_left` and
`TauCeti.ModularGroup.orbit_mk_injOn_fd_left`), so every class of forms contains exactly one
reduced form. The stabiliser of a form is that of its root, and for a reduced form `f` the root `τ`
lies in `𝒟`: the stabiliser has order `4` when `τ = i`, that is for the forms `⟨a, 0, a⟩`, order
`6` when `τ = ρ`, that is for the forms `⟨a, a, a⟩`, and order `2` otherwise, the corner `ρ + 1`
of `𝒟` having real part `1/2`. So `2 / |Stab|` is the weight `TauCeti.reducedFormWeight` of the
reduced form in the class.

## Main results

* `TauCeti.BinaryQuadraticForm.isReducedForm_iff_root_mem`: a positive definite form is reduced
  exactly when its root lies in `𝒟`, has real part `< 1/2`, and has real part `≤ 0` if it lies on
  the unit circle.
* `TauCeti.BinaryQuadraticForm.root_eq_I_iff` and `TauCeti.BinaryQuadraticForm.root_eq_ρ_iff`: the
  forms with root `i` are the `⟨a, 0, a⟩`, those with root `ρ` the `⟨a, a, a⟩`.
* `TauCeti.BinaryQuadraticForm.reducedFormWeight_eq_two_div_card_stabilizer`: the weight of a
  reduced form is `2 / |Stab|`.
* `TauCeti.BinaryQuadraticForm.exists_smul_isReducedForm` and
  `TauCeti.BinaryQuadraticForm.orbit_mk_injOn_isReducedForm`: every class of positive definite
  forms of discriminant `-D` contains exactly one reduced form (Cohen, §5.3).
* `TauCeti.BinaryQuadraticForm.orbit_mk_reducedForms_bijective`: so the reduced forms of
  discriminant `-D` are in bijection with the classes, and there are finitely many classes
  (`TauCeti.BinaryQuadraticForm.finite_orbitRel_quotient_posDef`).
* `TauCeti.hurwitzClassNumber_eq_finsum`: for `D ≠ 0`, `H D` is the sum over the classes of
  `2 / |Stab|`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.3.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §8.
* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327.
-/

public section

open MulAction UpperHalfPlane
open scoped MatrixGroups Modular

namespace TauCeti

namespace BinaryQuadraticForm

variable {D : ℕ} [NeZero D]

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `|re τ| ≤ 1/2` exactly when
`|b| ≤ a`, as `re τ = -b / (2 a)`. -/
theorem abs_re_root_le_half_iff (f : posDef D) : |(root f).re| ≤ 1 / 2 ↔ |f.1.b| ≤ f.1.a := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, abs_div, abs_neg, abs_of_pos ha, div_le_iff₀ ha, one_div_mul_eq_div,
    mul_div_cancel_left₀ _ two_ne_zero]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `re τ < 1/2` exactly when
`-a < b`. -/
theorem re_root_lt_half_iff (f : posDef D) : (root f).re < 1 / 2 ↔ -f.1.a < f.1.b := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, div_lt_iff₀ ha, one_div_mul_eq_div, mul_div_cancel_left₀ _ two_ne_zero, neg_lt]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `re τ ≤ 0` exactly when
`0 ≤ b`. -/
theorem re_root_nonpos_iff (f : posDef D) : (root f).re ≤ 0 ↔ 0 ≤ f.1.b := by
  have ha : (0 : ℝ) < 2 * f.1.a := by have := (mem_posDef.1 f.2).2; positivity
  rw [re_root, div_le_iff₀ ha, zero_mul, neg_nonpos]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` has `|τ|² ≥ 1` exactly when
`a ≤ c`, as `|τ|² = c / a`. -/
theorem one_le_normSq_root_iff (f : posDef D) : 1 ≤ Complex.normSq (root f) ↔ f.1.a ≤ f.1.c := by
  have ha : (0 : ℝ) < f.1.a := mod_cast (mem_posDef.1 f.2).2
  rw [normSq_root, one_le_div ha]
  norm_cast

/-- The root `τ` of a positive definite form `a x² + b x y + c y²` lies on the unit circle exactly
when `a = c`. -/
theorem norm_root_eq_one_iff (f : posDef D) : ‖(root f : ℂ)‖ = 1 ↔ f.1.a = f.1.c := by
  have ha : (0 : ℝ) < f.1.a := mod_cast (mem_posDef.1 f.2).2
  rw [Complex.norm_def, Real.sqrt_eq_one, normSq_root, div_eq_one_iff_eq ha.ne', eq_comm]
  norm_cast

/-- **A form is reduced exactly when its root is in the left part of `𝒟`**: the root
`τ = (-b + i √D) / (2 a)` of a positive definite form `a x² + b x y + c y²` lies in `𝒟`, has
`re τ < 1/2`, and has `re τ ≤ 0` if `|τ| = 1`. This is the region of
`TauCeti.ModularGroup.orbit_mk_injOn_fd_left` and `TauCeti.ModularGroup.exists_smul_mem_fd_left`:
`|b| ≤ a` is `|re τ| ≤ 1/2`, `a ≤ c` is `|τ| ≥ 1`, and the sign conditions of a reduced form rule
out the right vertical edge and the part of the unit arc right of `i`. -/
theorem isReducedForm_iff_root_mem (f : posDef D) :
    IsReducedForm f.1 ↔
      root f ∈ 𝒟 ∧ (root f).re < 1 / 2 ∧ (‖(root f : ℂ)‖ = 1 → (root f).re ≤ 0) := by
  simp only [isReducedForm_iff, ModularGroup.fd, Set.mem_ofPred_eq, one_le_normSq_root_iff,
    abs_re_root_le_half_iff, re_root_lt_half_iff, norm_root_eq_one_iff, re_root_nonpos_iff]
  grind [(mem_posDef.1 f.2).2]

/-- The root of a positive definite form is `i` exactly for the multiples `⟨a, 0, a⟩` of
`x² + y²`. -/
@[simp]
theorem root_eq_I_iff (f : posDef D) : root f = I ↔ f.1.b = 0 ∧ f.1.a = f.1.c := by
  -- `a i² + b i + c = b i + (c - a)`
  rw [eq_comm, eq_root_iff]
  convert ofReal_mul_add_eq_zero_iff I (m := f.1.b) (n := f.1.c - f.1.a) using 1
  · push_cast [coe_I, Complex.I_sq]
    ring_nf
  · norm_cast
    omega

/-- The root of a positive definite form is `ρ = (-1 + i √3) / 2` exactly for the multiples
`⟨a, a, a⟩` of `x² + x y + y²`. -/
@[simp]
theorem root_eq_ρ_iff (f : posDef D) : root f = ρ ↔ f.1.a = f.1.b ∧ f.1.b = f.1.c := by
  -- `a ρ² + b ρ + c = (b - a) (ρ + 1) + (c - b)`, as `ρ² = -ρ - 1`
  rw [eq_comm, eq_root_iff]
  convert ofReal_mul_add_eq_zero_iff ((1 : ℝ) +ᵥ ρ) (m := f.1.b - f.1.a) (n := f.1.c - f.1.b)
    using 1
  · push_cast [coe_vadd_one_ρ, ρ_sq]
    ring_nf
  · norm_cast
    omega

end BinaryQuadraticForm

open BinaryQuadraticForm

end TauCeti
