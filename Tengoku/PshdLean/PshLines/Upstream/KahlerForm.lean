/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
Modifications: adapted documentation and wrapped declarations in the PshLines namespace.
Source: https://github.com/zblore/csd-lean4/blob/c63273eceeb1c36c937eccfdf24795043666204f/CsdLean4/Mathlib/Analysis/InnerProductSpace/KahlerForm.lean
-/
module

public import Tengoku.Seed.Analysis.InnerProductSpace.Basic
public import Tengoku.Seed.Analysis.InnerProductSpace.Orthogonal
public import Tengoku.Seed.Analysis.Complex.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The flat Hermitian fundamental form

On a complex inner-product space, this file defines `J u = i • u`,
`g u v = re ⟪u,v⟫`, and `ω u v = im ⟪u,v⟫`. It proves real bilinearity,
alternation, compatibility with `J`, positivity, and invariance under complex
linear isometries. The inner product is conjugate-linear in its first slot.

These are statements about a vector space. No projective manifold, global
Kähler metric, Fubini–Study identification, or volume comparison is constructed.
The upstream declaration names are retained for traceability.
-/

@[expose] public section

namespace PshLines

namespace Kahler

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The complex structure `J`**: multiplication by `i`. Squares to `-1`
(`complexStructure_involutive`).-/
def complexStructure (u : E) : E := Complex.I • u

/-- **The Riemannian metric `g`**: the real part of the Hermitian inner product, `g u v = re ⟪u, v⟫`.
Symmetric (`metric_comm`) and positive-definite (`metric_self`, `= ‖u‖²`).-/
def metric (u v : E) : ℝ := (inner ℂ u v).re

/-- **The fundamental 2-form `ω`**: the imaginary part of the Hermitian inner product,
`ω u v = im ⟪u, v⟫`. Alternating `ℝ`-bilinear (the pointwise Kähler form).-/
def fundamentalForm (u v : E) : ℝ := (inner ℂ u v).im

/--
@isnad1 id=eq.0h2v.s6.f2636b8ac007 from=translated src=- shape=f565ff3e vocab=cfaaada5
-/
@[simp] theorem complexStructure_apply (u : E) : complexStructure u = Complex.I • u := rfl

/-- **`J² = -1`**: the fundamental relation of a complex structure. `J (J u) = i • (i • u) = -u`.
@isnad1 id=eq.0h2v.s5.3ffcde807eaf from=translated src=- shape=4a248773 vocab=1d15c343
-/
@[simp] theorem complexStructure_involutive (u : E) :
    complexStructure (complexStructure u) = -u := by
  simp only [complexStructure, smul_smul, Complex.I_mul_I, neg_smul, one_smul]

/-! ### `ω` is an alternating `ℝ`-bilinear form -/

/-- `ω u u = 0`: the fundamental form is alternating (`⟪u,u⟫` is real).
@isnad1 id=eq.0h2v.s4.0e2a7710a3b9 from=translated src=- shape=05c2fa88 vocab=1b0af063
-/
@[simp] theorem fundamentalForm_self (u : E) : fundamentalForm u u = 0 := by
  simp only [fundamentalForm, ← RCLike.im_to_complex, inner_self_im]

/-- `ω u v = -ω v u`: antisymmetry, from `⟪v,u⟫ = conj ⟪u,v⟫`.
@isnad1 id=eq.0h3v.s5.4b03fbc4f940 from=translated src=- shape=236eea68 vocab=b6158fda
-/
theorem fundamentalForm_antisymm (u v : E) :
    fundamentalForm u v = - fundamentalForm v u := by
  simp only [fundamentalForm, ← RCLike.im_to_complex]
  exact inner_im_symm u v

/-- `ω` is additive in the left argument.
@isnad1 id=eq.0h4v.s6.f0a2eeb15f2e from=translated src=- shape=28689fb3 vocab=c913738c
-/
theorem fundamentalForm_add_left (u u' v : E) :
    fundamentalForm (u + u') v = fundamentalForm u v + fundamentalForm u' v := by
  simp only [fundamentalForm, inner_add_left, Complex.add_im]

/-- `ω` is `ℝ`-homogeneous in the left argument (`r : ℝ` acting through `ℂ`). With additivity and
antisymmetry this makes `ω` an alternating `ℝ`-bilinear form.
@isnad1 id=eq.0h4v.s6.9f3cb3871e76 from=translated src=- shape=9fb0ae74 vocab=e7ce7a1c
-/
theorem fundamentalForm_real_smul_left (r : ℝ) (u v : E) :
    fundamentalForm ((r : ℂ) • u) v = r * fundamentalForm u v := by
  simp only [fundamentalForm, inner_smul_left, Complex.conj_ofReal, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-! ### The Kähler triple: `g`, `ω`, `J` compatibility -/

/-- **J-compatibility `ω u v = g (J u) v`.** The fundamental form is the metric precomposed with the
complex structure: `im ⟪u, v⟫ = re ⟪i • u, v⟫`. This is the defining relation tying `ω`, `g`, `J`.
@isnad1 id=eq.0h3v.s5.a74de297a1b1 from=translated src=- shape=50aef465 vocab=2d78bd4a
-/
theorem fundamentalForm_eq_metric_complexStructure (u v : E) :
    fundamentalForm u v = metric (complexStructure u) v := by
  simp only [fundamentalForm, metric, complexStructure, inner_smul_left, Complex.conj_I,
    neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg]

/-- **The metric is recovered from `ω` and `J`: `g u v = ω u (J v)`.** `re ⟪u, v⟫ = im ⟪u, i • v⟫`.
The dual Kähler-triple relation.
@isnad1 id=eq.0h3v.s5.f5bcc5f86a22 from=translated src=- shape=b0ce878e vocab=2d78bd4a
-/
theorem metric_eq_fundamentalForm_complexStructure (u v : E) :
    metric u v = fundamentalForm u (complexStructure v) := by
  simp only [metric, fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im]

/-! ### `J` is an isometry — `ω` is a `(1,1)`-form -/

/-- `J` preserves the Hermitian inner product: `⟪J u, J v⟫ = ⟪u, v⟫` (since `conj i · i = 1`).
@isnad1 id=eq.0h3v.s5.c308cd0d8bec from=translated src=- shape=ff1092e5 vocab=007c2151
-/
theorem inner_complexStructure (u v : E) :
    inner ℂ (complexStructure u) (complexStructure v) = inner ℂ u v := by
  show inner ℂ (Complex.I • u) (Complex.I • v) = inner ℂ u v
  rw [inner_smul_left, inner_smul_right, Complex.conj_I, ← mul_assoc, neg_mul,
    Complex.I_mul_I, neg_neg, one_mul]

/-- `J` is a `g`-isometry: `g (J u) (J v) = g u v`.
@isnad1 id=eq.0h3v.s5.1769a224e96b from=translated src=- shape=093c3531 vocab=c2558596
-/
theorem metric_complexStructure (u v : E) :
    metric (complexStructure u) (complexStructure v) = metric u v := by
  simp only [metric, inner_complexStructure]

/-- `ω` is `J`-invariant: `ω (J u) (J v) = ω u v`, i.e. `ω` is a `(1,1)`-form.
@isnad1 id=eq.0h3v.s5.ac822f4b7d8f from=translated src=- shape=093c3531 vocab=b9fcc877
-/
theorem fundamentalForm_complexStructure (u v : E) :
    fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v := by
  simp only [fundamentalForm, inner_complexStructure]

/-! ### Positivity / taming, and the metric's positive-definiteness -/

/-- `g u u = ‖u‖²`: the metric is positive-definite.
@isnad1 id=eq.0h2v.s5.1c7e9a0bf509 from=translated src=- shape=01f2e461 vocab=1ff22a68
-/
@[simp] theorem metric_self (u : E) : metric u u = ‖u‖ ^ 2 := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `g` is symmetric.
@isnad1 id=eq.0h3v.s4.725bbde53167 from=translated src=- shape=893c1bdf vocab=0993755a
-/
theorem metric_comm (u v : E) : metric u v = metric v u := by
  simp only [metric, ← RCLike.re_to_complex]
  exact inner_re_symm u v

/-- **Positivity / taming `ω u (J u) = ‖u‖²`.** The fundamental form paired with the complex structure
recovers the squared norm — so `(u, v) ↦ ω u (J v) = g u v` is positive-definite, the taming condition
that makes `ω` a *positive* `(1,1)`-form (the compatible almost-Kähler structure).
@isnad1 id=eq.0h2v.s5.44831e5abc04 from=translated src=- shape=b16ac153 vocab=33588497
-/
@[simp] theorem fundamentalForm_complexStructure_self (u : E) :
    fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 := by
  simp only [fundamentalForm, complexStructure, inner_smul_right, Complex.I_mul_im,
    ← RCLike.re_to_complex]
  exact inner_self_eq_norm_sq u

/-- `ω u (J u) > 0` for `u ≠ 0`: strict positivity of the taming form.
@isnad1 id=lt.1h2v.s5.3f2e683a3c6c from=translated src=- shape=9deb8484 vocab=c1d2367c
-/
theorem fundamentalForm_complexStructure_self_pos {u : E} (hu : u ≠ 0) :
    0 < fundamentalForm u (complexStructure u) := by
  rw [fundamentalForm_complexStructure_self]
  exact pow_pos (norm_pos_iff.mpr hu) 2

/-! ### The capstone -/

/-- The flat Hermitian triple satisfies the complex-structure, compatibility,
invariance, and squared-norm identities. No projective identification is asserted.
@isnad1 id=and.0h3v.s7.f3ddb01e1b0d from=translated src=- shape=66fa9578 vocab=c7ba4b2d
-/
theorem fubiniStudy_pointwise_kahler_compatibility (u v : E) :
    complexStructure (complexStructure u) = -u
    ∧ fundamentalForm u v = metric (complexStructure u) v
    ∧ metric u v = fundamentalForm u (complexStructure v)
    ∧ fundamentalForm (complexStructure u) (complexStructure v) = fundamentalForm u v
    ∧ fundamentalForm u (complexStructure u) = ‖u‖ ^ 2 :=
  ⟨complexStructure_involutive u, fundamentalForm_eq_metric_complexStructure u v,
    metric_eq_fundamentalForm_complexStructure u v,
    fundamentalForm_complexStructure u v, fundamentalForm_complexStructure_self u⟩

/-! ### Orthogonal complements are invariant under the complex structure -/

/-- Multiplication by `i` preserves the orthogonal complement of a complex span.
@isnad1 id=mem.1h3v.s8.30c925c190ae from=translated src=- shape=55509589 vocab=ef40b3f5
-/
theorem complexStructure_mem_orthogonal {ψ v : E}
    (hv : v ∈ (Submodule.span ℂ {ψ})ᗮ) :
    complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  simp only [complexStructure, inner_smul_right, hv u hu, mul_zero]

/-- The orthogonal complement of a complex span is `J`-invariant.
@isnad1 id=mem.1h3v.s8.30c925c190ae from=translated src=- shape=55509589 vocab=ef40b3f5
-/
theorem tangent_complexStructure_invariant (ψ : E) :
    ∀ v ∈ (Submodule.span ℂ {ψ})ᗮ, complexStructure v ∈ (Submodule.span ℂ {ψ})ᗮ :=
  fun _ hv => complexStructure_mem_orthogonal hv

/-! ### Invariance under complex linear isometries -/

/-- A `ℂ`-linear isometry preserves the metric `g`.
@isnad1 id=eq.0h4v.s8.a89ce461e86f from=translated src=- shape=0024bc64 vocab=2efc0557
-/
theorem metric_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v := by
  simp only [metric, f.inner_map_map]

/-- A `ℂ`-linear isometry preserves the fundamental form `ω`.
@isnad1 id=eq.0h4v.s8.d75ee4c526ad from=translated src=- shape=0024bc64 vocab=cc4ef4f4
-/
theorem fundamentalForm_linearIsometryEquiv (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    fundamentalForm (f u) (f v) = fundamentalForm u v := by
  simp only [fundamentalForm, f.inner_map_map]

/-- A complex linear isometry preserves the real metric and fundamental form.
@isnad1 id=and.0h4v.s9.c56cc1c9ccc6 from=translated src=- shape=1fadcf43 vocab=4b22710f
-/
theorem kahler_structure_isometry_invariant (f : E ≃ₗᵢ[ℂ] E) (u v : E) :
    metric (f u) (f v) = metric u v ∧ fundamentalForm (f u) (f v) = fundamentalForm u v :=
  ⟨metric_linearIsometryEquiv f u v, fundamentalForm_linearIsometryEquiv f u v⟩

end Kahler

end PshLines
