/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceySparseInterface
import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.QuadraticHilbertMaximalMeasurable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-radius test operators for the Krause--Lacey argument

The genuine maximal truncation is naturally `ENNReal`-valued until its
almost-everywhere finiteness is known.  To apply the finite sparse-maximal
lemma without any circular finiteness assumption, we first take a finite
maximum of sharp truncations.  Its value is an ordinary nonnegative real,
embedded in `ℂ`, and this module verifies the exact sublinearity required by
the sparse framework.
-/

open Function MeasureTheory Set
open scoped ENNReal NNReal

namespace QuadraticCarleson
namespace KrauseLaceyFiniteRadiusAdapter

open QuadraticHilbertMaximalMeasurable

set_option autoImplicit false

noncomputable section

/-- Finite maximum of sharp quadratic truncation norms, before embedding it
as a test-operator output.-/
def finiteRadiusQuadraticHilbertMaxNNNorm
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) : NNReal :=
  s.sup fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊

/-- The finite sharp-truncation maximum as a complex-valued test operator.
Its values lie on the nonnegative real axis.-/
def finiteRadiusQuadraticHilbertMaxTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) : TestOperator :=
  fun f x ↦ ((finiteRadiusQuadraticHilbertMaxNNNorm lam s f x : ℝ) : ℂ)

/--
@isnad1 id=eq.0h4v.s5.113f4f98c54c from=translated src=- shape=88ca513f vocab=0b25fde2
-/
@[simp] theorem norm_finiteRadiusQuadraticHilbertMaxTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) (f : L0Infinity) (x : ℝ) :
    ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖ =
      finiteRadiusQuadraticHilbertMaxNNNorm lam s f x := by
  rw [finiteRadiusQuadraticHilbertMaxTestOperator, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  exact NNReal.coe_nonneg _

/-- The finite-radius maximum is subadditive.
@isnad1 id=le.0h5v.s5.c0574bfc79d7 from=translated src=- shape=5966e80a vocab=9456825f
-/
theorem finiteRadiusQuadraticHilbertMaxNNNorm_add_le
    (lam : ℝ) (s : Finset densePositiveRadii) (f g : L0Infinity) (x : ℝ) :
    finiteRadiusQuadraticHilbertMaxNNNorm lam s (L0Infinity.add f g) x ≤
      finiteRadiusQuadraticHilbertMaxNNNorm lam s f x +
        finiteRadiusQuadraticHilbertMaxNNNorm lam s g x := by
  classical
  unfold finiteRadiusQuadraticHilbertMaxNNNorm
  apply Finset.sup_le
  intro ε hε
  calc
    ‖quadraticHilbertTrunc lam ε.1.1 (L0Infinity.add f g) x‖₊ =
        ‖quadraticHilbertTrunc lam ε.1.1 f x +
          quadraticHilbertTrunc lam ε.1.1 g x‖₊ := by
      apply congrArg nnnorm
      simpa only [quadraticHilbertTruncTestOperator] using
        quadraticHilbertTrunc_add lam ε.1.2 f g x
    _ ≤ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊ +
        ‖quadraticHilbertTrunc lam ε.1.1 g x‖₊ := nnnorm_add_le _ _
    _ ≤ (s.sup fun δ ↦ ‖quadraticHilbertTrunc lam δ.1.1 f x‖₊) +
        s.sup fun δ ↦ ‖quadraticHilbertTrunc lam δ.1.1 g x‖₊ := add_le_add
      (Finset.le_sup (s := s)
        (f := fun δ ↦ ‖quadraticHilbertTrunc lam δ.1.1 f x‖₊) hε)
      (Finset.le_sup (s := s)
        (f := fun δ ↦ ‖quadraticHilbertTrunc lam δ.1.1 g x‖₊) hε)

/-- Complex homogeneity of the finite-radius maximum.
@isnad1 id=eq.0h5v.s6.53fe98e1f6c9 from=translated src=- shape=8116597e vocab=05f1fdc8
-/
theorem finiteRadiusQuadraticHilbertMaxNNNorm_smul
    (lam : ℝ) (s : Finset densePositiveRadii) (c : ℂ)
    (f : L0Infinity) (x : ℝ) :
    finiteRadiusQuadraticHilbertMaxNNNorm lam s (L0Infinity.smul c f) x =
      ‖c‖₊ * finiteRadiusQuadraticHilbertMaxNNNorm lam s f x := by
  classical
  unfold finiteRadiusQuadraticHilbertMaxNNNorm
  calc
    (s.sup fun ε ↦
        ‖quadraticHilbertTrunc lam ε.1.1 (L0Infinity.smul c f) x‖₊) =
        s.sup fun ε ↦ ‖c * quadraticHilbertTrunc lam ε.1.1 f x‖₊ := by
      apply Finset.sup_congr rfl
      intro ε hε
      apply congrArg nnnorm
      simpa only [quadraticHilbertTruncTestOperator] using
        quadraticHilbertTrunc_smul lam ε.1.2 c f x
    _ = s.sup fun ε ↦ ‖c‖₊ * ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊ := by
      congr 1
      funext ε
      rw [nnnorm_mul]
    _ = ‖c‖₊ * (s.sup fun ε ↦
        ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊) :=
      (NNReal.mul_finset_sup ‖c‖₊ s
        (fun ε ↦ ‖quadraticHilbertTrunc lam ε.1.1 f x‖₊)).symm

/-- Every finite-radius maximal quadratic truncation is a genuine sublinear
operator on the project's bounded compact-support test-function space.
@isnad1 id=issublin.0h2v.s4.7fcd624d3252 from=translated src=- shape=6e7ccef6 vocab=5cbe1184
-/
theorem finiteRadiusQuadraticHilbertMaxTestOperator_isSublinear
    (lam : ℝ) (s : Finset densePositiveRadii) :
    IsSublinear (finiteRadiusQuadraticHilbertMaxTestOperator lam s) := by
  constructor
  · intro f g x
    simp only [norm_finiteRadiusQuadraticHilbertMaxTestOperator]
    exact_mod_cast finiteRadiusQuadraticHilbertMaxNNNorm_add_le lam s f g x
  · intro c f x
    simp only [norm_finiteRadiusQuadraticHilbertMaxTestOperator]
    rw [finiteRadiusQuadraticHilbertMaxNNNorm_smul]
    rfl

/-- Every selected radius is dominated pointwise by the finite-radius test
operator.
@isnad1 id=le.1h5v.s8.ab3260d92efc from=translated src=- shape=010bc45e vocab=e1d6aee1
-/
theorem quadraticHilbertTrunc_enorm_le_finiteRadiusTestOperator
    (lam : ℝ) (s : Finset densePositiveRadii) {ε : densePositiveRadii}
    (hε : ε ∈ s) (f : L0Infinity) (x : ℝ) :
    ‖quadraticHilbertTrunc lam ε.1.1 f x‖ₑ ≤
      ENNReal.ofReal ‖finiteRadiusQuadraticHilbertMaxTestOperator lam s f x‖ := by
  rw [norm_finiteRadiusQuadraticHilbertMaxTestOperator,
    ENNReal.ofReal_coe_nnreal]
  exact_mod_cast Finset.le_sup (s := s)
    (f := fun δ ↦ ‖quadraticHilbertTrunc lam δ.1.1 f x‖₊) hε

end
end KrauseLaceyFiniteRadiusAdapter
end QuadraticCarleson
