/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# The complexification of a real normed space

For a real normed space `X`, the complexification `X_ℂ = X ⊕ i X` is the complex vector space of
formal sums `x + i y` with `x y : X`, where `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`.
It is the standard device for applying complex-analytic spectral theory to operators on a real
Banach space: a bounded real operator `T` extends to the complex-linear operator
`T_ℂ (x + i y) = T x + i T y`.

There are many equivalent complex norms on `X_ℂ`; this file uses the *Taylor norm*

`‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖`,

that is, `‖x + i y‖ = sup_θ ‖cos θ • x - sin θ • y‖`.  With this norm the passage from `X` to
`X_ℂ` loses no constants:

* the embedding `x ↦ x + i 0` is an isometry (`TauCeti.Complexification.norm_ofReal`);
* the real and imaginary parts are bounded by the norm, and the norm by their sum
  (`norm_re_le`, `norm_im_le`, `norm_le_norm_re_add_norm_im`), so `X_ℂ` carries the product
  topology and is complete whenever `X` is;
* the complexification of a bounded operator has the same operator norm
  (`ContinuousLinearMap.norm_complexify`).

Together with `ContinuousLinearMap.complexify_comp`, the last point means that an operator-norm
estimate for real operators, such as a growth bound `‖S t‖ ≤ M e^{ω t}` for a family of operators
or a bound `‖Rⁿ‖ ≤ C` on the powers of one operator, holds verbatim for their complexifications.
(On a real Hilbert space the Taylor norm is in general not the Hilbert norm `√(‖x‖² + ‖y‖²)`; the
two are equivalent.)

## Main declarations

* `TauCeti.Complexification`: the complexification of a real vector space, with its complex
  module structure.
* `TauCeti.Complexification.ofReal`, `TauCeti.Complexification.re_add_I_smul_im`: the real
  embedding, and the decomposition `z = re z + i im z`.
* `TauCeti.Complexification.norm_le_iff`: the characterization of the Taylor norm by bounds on the
  real parts of rotations.
* `TauCeti.Complexification.instNormedSpace`, `TauCeti.Complexification.instCompleteSpace`: the
  complex normed space structure, complete when `X` is.
* `TauCeti.Complexification.equivProd`: `X_ℂ` is real-linearly homeomorphic to `X × X`.
* `ContinuousLinearMap.complexify`: the complex-linear extension of a bounded real operator, with
  `ContinuousLinearMap.norm_complexify` and the bundled
  `ContinuousLinearMap.complexifyAlgHom`.
* `TauCeti.Complexification.ext_ofReal`: complex-linear maps out of `X_ℂ` are determined on `X`,
  so `T.complexify` is the unique complex-linear extension of `T`.

## References

* G. A. Muñoz, Y. Sarantopoulos, A. Tonge, *Complexifications of real Banach spaces,
  polynomials and multilinear maps*, Studia Math. 134 (1999), 1–33.
-/

public section

noncomputable section

open Set

namespace TauCeti

/-- The complexification `X ⊕ i X` of a real vector space `X`: an element with real part `re` and
imaginary part `im` stands for the formal sum `re + i im`. -/
@[ext]
structure Complexification (X : Type*) where
  /-- The real part of an element of the complexification. -/
  re : X
  /-- The imaginary part of an element of the complexification. -/
  im : X

namespace Complexification

section Module

variable {X : Type*} [AddCommGroup X]

instance : Zero (Complexification X) := ⟨⟨0, 0⟩⟩

instance : Add (Complexification X) := ⟨fun z w ↦ ⟨z.re + w.re, z.im + w.im⟩⟩

instance : Neg (Complexification X) := ⟨fun z ↦ ⟨-z.re, -z.im⟩⟩

instance : Sub (Complexification X) := ⟨fun z w ↦ ⟨z.re - w.re, z.im - w.im⟩⟩

instance : SMul ℕ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

instance : SMul ℤ (Complexification X) := ⟨fun n z ↦ ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Complexification X).re = 0 := (rfl)
@[simp] theorem zero_im : (0 : Complexification X).im = 0 := (rfl)
@[simp] theorem add_re (z w : Complexification X) : (z + w).re = z.re + w.re := (rfl)
@[simp] theorem add_im (z w : Complexification X) : (z + w).im = z.im + w.im := (rfl)
@[simp] theorem neg_re (z : Complexification X) : (-z).re = -z.re := (rfl)
@[simp] theorem neg_im (z : Complexification X) : (-z).im = -z.im := (rfl)
@[simp] theorem sub_re (z w : Complexification X) : (z - w).re = z.re - w.re := (rfl)
@[simp] theorem sub_im (z w : Complexification X) : (z - w).im = z.im - w.im := (rfl)

instance : AddCommGroup (Complexification X) :=
  Function.Injective.addCommGroup (fun z : Complexification X ↦ (z.re, z.im))
    (fun _ _ h ↦ by
      simp only [Prod.mk.injEq] at h
      exact Complexification.ext h.1 h.2)
    (rfl) (fun _ _ ↦ (rfl)) (fun _ ↦ (rfl)) (fun _ _ ↦ (rfl)) (fun _ _ ↦ (rfl))
    (fun _ _ ↦ (rfl))

/-- The embedding `x ↦ x + i 0` of a real vector space into its complexification. -/
def ofReal (x : X) : Complexification X := ⟨x, 0⟩

@[simp] theorem ofReal_re (x : X) : (ofReal x).re = x := (rfl)
@[simp] theorem ofReal_im (x : X) : (ofReal x).im = 0 := (rfl)

variable [Module ℝ X]

/-- Complex scalars act by `(a + b i) • (x + i y) = (a x - b y) + i (b x + a y)`. -/
instance : SMul ℂ (Complexification X) :=
  ⟨fun c z ↦ ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩⟩

@[simp]
theorem smul_re (c : ℂ) (z : Complexification X) : (c • z).re = c.re • z.re - c.im • z.im :=
  (rfl)

@[simp]
theorem smul_im (c : ℂ) (z : Complexification X) : (c • z).im = c.im • z.re + c.re • z.im :=
  (rfl)

instance : Module ℂ (Complexification X) where
  one_smul z := by ext <;> simp
  mul_smul c d z := by ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;>
    module
  smul_zero c := by ext <;> simp
  smul_add c z w := by ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul c d z := by ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re,
    Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_re (r : ℝ) (z : Complexification X) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, smul_re, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

/-- Real scalars act componentwise. -/
@[simp]
theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, smul_im, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

/-- Every element of the complexification is `re + i im`. -/
theorem re_add_I_smul_im (z : Complexification X) :
    ofReal z.re + Complex.I • ofReal z.im = z := by
  ext <;> simp

/-- Complex-linear maps out of the complexification agree once they agree on real vectors. -/
theorem ext_ofReal {E : Type*} [AddCommGroup E] [Module ℂ E]
    {f g : Complexification X →ₗ[ℂ] E} (h : ∀ x, f (ofReal x) = g (ofReal x)) : f = g := by
  ext z
  rw [← re_add_I_smul_im z, map_add, map_add, map_smul, map_smul, h, h]

end Module

section Norm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Taylor norm `‖z‖ = ⨆ w ∈ 𝕋, ‖Re (w • z)‖` on the complexification. -/
instance : Norm (Complexification X) := ⟨fun z ↦ ⨆ w : Circle, ‖((w : ℂ) • z).re‖⟩

theorem norm_def (z : Complexification X) : ‖z‖ = ⨆ w : Circle, ‖((w : ℂ) • z).re‖ := (rfl)

variable (X)

variable {X}

variable (X)

variable {X}

end Norm

end Complexification

end TauCeti

namespace ContinuousLinearMap

open TauCeti TauCeti.Complexification

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

variable (X Y)

variable {X Y}

end ContinuousLinearMap
