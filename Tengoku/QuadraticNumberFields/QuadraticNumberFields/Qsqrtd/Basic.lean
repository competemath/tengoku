/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.Seed.Algebra.QuadraticAlgebra.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
import Tengoku.Seed.RingTheory.Int.Basic
import Tengoku.Seed.RingTheory.Trace.Basic
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.QuadraticNumberFields.QNFMathlib.Algebra.Squarefree.Basic
import Tengoku.QuadraticNumberFields.QNFMathlib.Algebra.QuadraticAlgebra.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic Definitions for Quadratic Number Fields

This file defines the concept of a quadratic number field as a degree-2 extension of `ℚ`,
builds the concrete model `ℚ(√d)` as `QuadraticAlgebra ℚ d 0`, and proves basic properties
including norm, trace, and field/number field instances.

## Main Definitions

* `Qsqrtd d`: The quadratic algebra `QuadraticAlgebra ℚ d 0`, representing `ℚ(√d)`.
* `Qsqrtd.norm`: The norm `N(x) = x · x̄ = x.re² - d · x.im²`.

The predicate "K is a quadratic extension of ℚ" is provided by mathlib as
`Algebra.IsQuadraticExtension ℚ K`.

## Main Results

* `QuadraticField.instNumberField`: Any project-level quadratic field is a number field.
* `Qsqrtd.instIsQuadraticExtension`: `ℚ(√d)/ℚ` is a degree-2 extension.
* `not_isSquare_ratCast_of_squarefree_ne_one`: squarefree integer parameters
  with `d ≠ 1` give genuine quadratic fields.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
/-- The quadratic field `ℚ(√d)` as a type alias for `QuadraticAlgebra ℚ d 0`.-/
abbrev _root_.Tengoku.QuadraticNumberFields.Qsqrtd (d : ℚ) : Type := QuadraticAlgebra ℚ d 0

/-- Notation for the quadratic field `Qsqrtd d = ℚ(√d)`.-/
local notation "ℚ√" d => Qsqrtd d

namespace Tengoku.QuadraticNumberFields.Qsqrtd

open QuadraticAlgebra

variable {d : ℚ}

/-- The trace in `Q(√d)` is `x.re + x̄.re`.
@isnad1 id=eq.0h2v.s8.51cfa6c2dfd0 from=translated src=- shape=e67e59d1 vocab=f6dfe7bc
-/
@[simp] theorem trace_eq_re_add_re_star (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = x.re + (star x).re := by
  -- The trace is the matrix trace of left multiplication, so we just
  -- read off the two diagonal entries from the explicit `2 × 2` matrix.
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis d 0),
    QuadraticAlgebra.leftMulMatrix_eq, Matrix.trace_fin_two_of]
  simp

/-- In the model `Q(√d) = QuadraticAlgebra ℚ d 0`, the trace is `2 * re`.
@isnad1 id=eq.0h2v.s8.e56f05527811 from=translated src=- shape=a63f308d vocab=f54bca66
-/
theorem trace_eq_two_re (x : Qsqrtd d) :
    Algebra.trace ℚ (Qsqrtd d) x = 2 * x.re := by
  -- In `QuadraticAlgebra ℚ d 0`, conjugation fixes the real part.
  rw [trace_eq_re_add_re_star]
  simp
  ring

/-- The norm of an element `x : Q(√d)`, defined as `N(x) = x · x̄ = x.re² - d · x.im²`.-/
abbrev norm {d : ℚ} (x : Qsqrtd d) : ℚ := QuadraticAlgebra.norm x

/-- The norm on `Q(√d)` as a `MonoidHom` to `ℚ`.-/
abbrev normHom (d : ℚ) : Qsqrtd d →* ℚ :=
  QuadraticAlgebra.norm

/-- `normHom` evaluates to the quadratic norm.
@isnad1 id=eq.0h2v.s6.677619bfe43d from=translated src=- shape=151cf303 vocab=b38a2b37
-/
theorem normHom_apply (d : ℚ) (x : Qsqrtd d) :
    normHom d x = Qsqrtd.norm x :=
  rfl

/-- The norm on the unit group of `Q(√d)`, as a `MonoidHom` to `ℚˣ`.-/
abbrev normUnitsHom (d : ℚ) : (Qsqrtd d)ˣ →* ℚˣ :=
  Units.map (normHom d)

/-- Coercing `normUnitsHom` back to `ℚ` gives the quadratic norm of the
underlying unit.
@isnad1 id=eq.0h2v.s7.0d0cc780d298 from=translated src=- shape=cbccf160 vocab=8a3355eb
-/
theorem normUnitsHom_coe (d : ℚ) (u : (Qsqrtd d)ˣ) :
    ((normUnitsHom d u : ℚˣ) : ℚ) = Qsqrtd.norm (u : Qsqrtd d) := by
  simp [normUnitsHom, normHom]

/-- `Q(√0)` is not reduced because `√0² = 0` but `√0 ≠ 0`.
@isnad1 id=not.0h0v.s6.b109b988148f from=translated src=- shape=f4d8664b vocab=77ac2836
-/
 lemma zero_not_isReduced : ¬ IsReduced (Qsqrtd (0 : ℚ)) := by
  intro ⟨h⟩
  -- When `d = 0`, the element `ε = ⟨0, 1⟩` satisfies `ε² = 0`,
  -- so it is a nonzero nilpotent.
  have hnil : IsNilpotent (⟨0, 1⟩ : Qsqrtd 0) :=
    ⟨2, by ext <;> simp [pow_succ, pow_zero, QuadraticAlgebra.mk_mul_mk]⟩
  have hne : (⟨0, 1⟩ : Qsqrtd 0) ≠ 0 := by
    intro heq
    exact one_ne_zero (congr_arg QuadraticAlgebra.im heq)
  exact hne (h _ hnil)

/-- `Q(√0)` is not a field (it has nilpotents).
@isnad1 id=not.0h0v.s4.116ecfc1f9ad from=translated src=- shape=f4d8664b vocab=f436df56
-/
lemma zero_not_isField : ¬ IsField (Qsqrtd (0 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  exact zero_not_isReduced (inferInstance : IsReduced (Qsqrtd (0 : ℚ)))

/-- `Q(√1) ≅ ℚ × ℚ` is not a field (it has zero divisors).
@isnad1 id=not.0h0v.s4.9e50e5fa51a6 from=translated src=- shape=f4d8664b vocab=f436df56
-/
 lemma one_not_isField : ¬ IsField (Qsqrtd (1 : ℚ)) := by
  intro hF
  haveI := hF.isDomain
  -- For `d = 1`, the standard factorization
  -- `(1 + √1) (1 - √1) = 1 - (√1)^2 = 0` gives zero divisors.
  have hprod : (⟨1, 1⟩ : Qsqrtd 1) * ⟨1, -1⟩ = 0 := by
    ext <;> simp
  have hne : (⟨1, 1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  have hne' : (⟨1, -1⟩ : Qsqrtd 1) ≠ 0 := by
    intro h
    exact one_ne_zero (congr_arg QuadraticAlgebra.re h)
  rcases mul_eq_zero.mp hprod with h | h <;> contradiction

/-- Bridge: `¬ IsSquare d` implies the technical `Fact` needed by
`QuadraticAlgebra.instField`.
@isnad1 id=fact.0h1v.s5.e7155f260716 from=translated src=- shape=e63ba786 vocab=df1b4ba6
-/
instance instFact_of_not_isSquare (d : ℚ) [Fact (¬ IsSquare d)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ d + 0 * r) :=
  -- For `b = 0`, the field criterion for `QuadraticAlgebra ℚ d b`
  -- reduces to saying that `X^2 - d` has no rational root.
  ⟨by intro r hr; exact (Fact.out : ¬ IsSquare d) ⟨r, by nlinarith [hr]⟩⟩

/-- The two `ℚ`-algebra structures on `Qsqrtd d` give the same `ℚ`-dimension.

Coordinate proofs use `QuadraticAlgebra.instAlgebra`. Some number-field APIs use
`DivisionRing.toRatAlgebra`, so this lemma transfers finrank statements between them.
@isnad1 id=eq.0h1v.s7.e522d063ba9c from=translated src=- shape=ec1eb768 vocab=ed114e7c
-/
theorem finrank_ratAlgebra_eq_finrank_quadraticAlgebra (d : ℚ)
    [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) =
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ QuadraticAlgebra.instAlgebra) := by
  symm
  refine @Algebra.finrank_eq_of_equiv_equiv ℚ (Qsqrtd d) _ _
    QuadraticAlgebra.instAlgebra ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra
    (RingEquiv.refl ℚ) (RingEquiv.refl (Qsqrtd d)) ?_
  exact RingHom.ext_rat _ _

section RatAlgebra

attribute [local instance] DivisionRing.toRatAlgebra

/-- The `DivisionRing.toRatAlgebra` version of the finrank computation for `Qsqrtd d`.
@isnad1 id=eq.0h1v.s6.ed5713e32c1b from=translated src=- shape=7db9b3c3 vocab=0321f66a
-/
theorem finrank_ratAlgebra_eq_two (d : ℚ) [Fact (¬ IsSquare d)] :
    @Module.finrank ℚ (Qsqrtd d) _ _
      (@Algebra.toModule ℚ (Qsqrtd d) _ _ DivisionRing.toRatAlgebra) = 2 := by
  rw [finrank_ratAlgebra_eq_finrank_quadraticAlgebra]
  exact QuadraticAlgebra.finrank_eq_two d 0

/-- `Qsqrtd d` is quadratic over `ℚ` for the `DivisionRing.toRatAlgebra` structure.
@isnad1 id=isquadra.0h1v.s5.d975098996c9 from=translated src=- shape=66c81b7c vocab=a31b83b6
-/
instance instRatAlgebraIsQuadraticExtension (d : ℚ) [Fact (¬ IsSquare d)] :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd d) where
  finrank_eq_two' := finrank_ratAlgebra_eq_two d

end RatAlgebra

/-- Ring-level core of the generator relation, independent of any `Algebra ℚ`
instance. If `d` is not a square, `φ : Qsqrtd d ≃+* Qsqrtd d'` is a ring
isomorphism fixing the scalar `⟨d, 0⟩`, then writing `φ ⟨0, 1⟩ = ⟨a, b⟩` we have
`a = 0`, `b ≠ 0`, and `d = d' * b²`.

Being stated for `≃+*` (rather than `≃ₐ[ℚ]`), this sidesteps the `Algebra ℚ`
instance diamond on `Qsqrtd`, so it serves call sites that elaborate against
either the canonical or the `Field` algebra instance.
@isnad1 id=and.2h3v.s9.ca5c59fa9e3f from=translated src=- shape=2f4e338f vocab=a26a98df
-/
theorem ringEquiv_param_rel {d d' : ℚ} (hd : ¬ IsSquare d)
    (φ : Qsqrtd d ≃+* Qsqrtd d') (hfix : φ ⟨d, 0⟩ = ⟨d, 0⟩) :
    (φ ⟨0, 1⟩).re = 0 ∧ (φ ⟨0, 1⟩).im ≠ 0 ∧ d = d' * (φ ⟨0, 1⟩).im ^ 2 := by
  set a := (φ ⟨0, 1⟩).re
  set b := (φ ⟨0, 1⟩).im
  -- `⟨0, 1⟩² = ⟨d, 0⟩` and `φ` fixes `⟨d, 0⟩`, so `(φ ⟨0,1⟩)² = ⟨d, 0⟩`.
  have hε_sq : (⟨0, 1⟩ : Qsqrtd d) * ⟨0, 1⟩ = ⟨d, 0⟩ := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hφ_sq : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = ⟨d, 0⟩ := by rw [← map_mul, hε_sq, hfix]
  have hφ_eta : φ ⟨0, 1⟩ = ⟨a, b⟩ := by ext <;> rfl
  -- Comparing coordinates gives `a² + d'·b² = d` and `2ab = 0`.
  have hre : a ^ 2 + d' * b ^ 2 = d := by
    have := congr_arg QuadraticAlgebra.re hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
    simp at this
    nlinarith
  have him : 2 * a * b = 0 := by
    have := congr_arg QuadraticAlgebra.im hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
    simp at this
    linarith
  -- `b ≠ 0`, else `a² = d` makes `d` a square; then `2ab = 0` forces `a = 0`.
  have hb : b ≠ 0 := by
    intro hb0
    simp [hb0] at hre
    exact hd ⟨a, by nlinarith⟩
  have ha : a = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact absurd h hb
  exact ⟨ha, hb, by nlinarith [hre, ha]⟩

/-- The generator relation behind every `ℚ`-algebra equivalence of standard
models. If `d` is not a square and `φ : Qsqrtd d ≃ₐ[ℚ] Qsqrtd d'`, then writing
`φ ⟨0, 1⟩ = ⟨a, b⟩` we have `a = 0`, `b ≠ 0`, and `d = d' * b²`; i.e. the two
parameters differ by the rational square `b²`.

This is the `Algebra` version of `ringEquiv_param_rel`: `φ.commutes` proves
`⟨d, 0⟩ = algebraMap d`. Used by `param_unique` and
`algEquiv_iff_isSquareRatio`.
@isnad1 id=and.1h3v.s9.d4e47813794f from=translated src=- shape=1312e70d vocab=7f146b07
-/
theorem algEquiv_param_rel {d d' : ℚ} (hd : ¬ IsSquare d)
    (φ : Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') :
    (φ ⟨0, 1⟩).re = 0 ∧ (φ ⟨0, 1⟩).im ≠ 0 ∧ d = d' * (φ ⟨0, 1⟩).im ^ 2 :=
  ringEquiv_param_rel hd φ.toRingEquiv <| by
    have hleft : (⟨d, 0⟩ : Qsqrtd d) = algebraMap ℚ (Qsqrtd d) d :=
      (QuadraticAlgebra.algebraMap_eq (R := ℚ) (a := d) (b := 0) d).symm
    have hright : (⟨d, 0⟩ : Qsqrtd d') = algebraMap ℚ (Qsqrtd d') d :=
      (QuadraticAlgebra.algebraMap_eq (R := ℚ) (a := d') (b := 0) d).symm
    simp [hleft, hright]

end Tengoku.QuadraticNumberFields.Qsqrtd

/-! ## Integer Parameter Lemmas -/

/-- For a squarefree integer `d ≠ 1`, `d` is not a perfect square in `ℤ`.
@isnad1 id=not.2h1v.s4.7c013f299898 from=translated src=- shape=04eb94a6 vocab=a97af9b3
-/
lemma _root_.Tengoku.QuadraticNumberFields.not_isSquare_int_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare d := by
  intro hsq
  rcases eq_one_of_squarefree_isSquare hd hsq with rfl | rfl <;> simp_all

/-- For a squarefree integer `d ≠ 1`, `(d : ℚ)` is not a perfect square in `ℚ`.
@isnad1 id=not.2h1v.s4.8233c3183f19 from=translated src=- shape=9196607b vocab=4482373f
-/
lemma _root_.Tengoku.QuadraticNumberFields.not_isSquare_ratCast_of_squarefree_ne_one {d : ℤ}
    (hd : Squarefree d) (h1 : d ≠ 1) : ¬ IsSquare ((d : ℤ) : ℚ) := by
  intro hsqQ
  exact not_isSquare_int_of_squarefree_ne_one hd h1 (Rat.isSquare_intCast_iff.mp hsqQ)

/-- Bridge squarefree integer parameters to the field-level non-square condition.
@isnad1 id=fact.0h1v.s4.6f04dedfd846 from=translated src=- shape=17fda95b vocab=f5d14b00
-/
instance _root_.Tengoku.QuadraticNumberFields.instFact_not_isSquare_ratCast_of_squarefree_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
  ⟨not_isSquare_ratCast_of_squarefree_ne_one
    (d := d) (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩

/-! ### Coordinate lemmas

The coefficient of the canonical generator `√d` in `x : Qsqrtd (d : ℚ)`, and
companion lemmas for conjugation-fixed / conjugation-negated elements. -/

variable {d : ℤ}

/-- The coefficient of `√d` in `x : Qsqrtd (d : ℚ)`, extracted via the standard basis.-/
noncomputable def _root_.Tengoku.QuadraticNumberFields.imPartRatio (x : Qsqrtd (d : ℚ)) : ℚ :=
  (QuadraticAlgebra.basis (d : ℚ) 0).repr x (1 : Fin 2)

/-- `imPartRatio` is exactly the `im` coordinate.
@isnad1 id=eq.0h2v.s4.1e567a4f82b1 from=translated src=- shape=e8a0f1b4 vocab=c9d60a1b
-/
theorem _root_.Tengoku.QuadraticNumberFields.imPartRatio_eq_im (x : Qsqrtd (d : ℚ)) : imPartRatio x = x.im := by
  simp [imPartRatio, QuadraticAlgebra.basis]

/-- If `x` is negated by conjugation, then it is a rational multiple of `√d`,
and that multiple is exactly `imPartRatio x`.-/
theorem _root_.Tengoku.QuadraticNumberFields.eq_imPartRatio_smul_sqrt_of_star_neg {x : Qsqrtd (d : ℚ)} (hx : star x = -x) :
    x = (imPartRatio x : ℚ) • (⟨0, 1⟩ : Qsqrtd (d : ℚ)) := by
  have hre : x.re = 0 := by
    have hre_star : (star x).re = x.re := by simp [QuadraticAlgebra.re_star]
    have hre_neg : (-x).re = -x.re := by simp
    rw [hx] at hre_star
    rw [hre_neg] at hre_star
    linarith
  have him : (imPartRatio x : ℚ) = x.im := by simp [imPartRatio, QuadraticAlgebra.basis]
  simpa [hre, him] using (QuadraticAlgebra.mk_eta x).symm

/-- If `x` is fixed by conjugation, then it is the rational scalar `x.re`,
viewed in `K` via `x.re • (1 : Qsqrtd (d : ℚ))`.-/
theorem _root_.Tengoku.QuadraticNumberFields.eq_re_smul_one_of_star_self {x : Qsqrtd (d : ℚ)} (hx : star x = x) :
    x = (x.re : ℚ) • (1 : Qsqrtd (d : ℚ)) := by
  have him : x.im = 0 := by
    have him_star : (star x).im = -x.im := by simp [QuadraticAlgebra.im_star]
    rw [hx] at him_star
    linarith
  apply QuadraticAlgebra.ext
  · simp [QuadraticAlgebra.re_one]
  · simp [him, QuadraticAlgebra.im_one]

/-- A conjugation-fixed element of `ℚ(√d)` is the scalar `x.re`, embedded by
`algebraMap`.-/
theorem _root_.Tengoku.QuadraticNumberFields.eq_algebraMap_re_of_star_self {x : Qsqrtd (d : ℚ)} (hx : star x = x) :
    x = algebraMap ℚ (Qsqrtd (d : ℚ)) x.re :=
  (eq_re_smul_one_of_star_self hx).trans (Algebra.algebraMap_eq_smul_one x.re).symm

/-! ### Wedge and `ℤ`-smul coordinate lemmas

The alternating wedge `imPartRatio (u v̄ − v ū)` and the `re`/`im` coordinates of an
integer scalar multiple, used by the Cox norm-form machinery.  These are pure
coordinate facts about `Qsqrtd (d : ℚ)`. -/

/-- The `re` coordinate of an integer scalar multiple.
@isnad1 id=eq.0h3v.s6.13c0ce9033f9 from=translated src=- shape=cb9c2c0d vocab=f66db35d
-/
theorem _root_.Tengoku.QuadraticNumberFields.re_zsmul (n : ℤ) (z : Qsqrtd (d : ℚ)) : (n • z).re = (n : ℚ) * z.re := by
  rw [zsmul_eq_mul]
  simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

/-- The `im` coordinate of an integer scalar multiple.
@isnad1 id=eq.0h3v.s6.aae35ba59f70 from=translated src=- shape=cb9c2c0d vocab=ed89f4b8
-/
theorem _root_.Tengoku.QuadraticNumberFields.im_zsmul (n : ℤ) (z : Qsqrtd (d : ℚ)) : (n • z).im = (n : ℚ) * z.im := by
  rw [zsmul_eq_mul]
  simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

/-- The wedge `imPartRatio (u v̄ − v ū)` in coordinates: it is `2 (uᵢ vᵣ − uᵣ vᵢ)`,
a bilinear alternating form of the `re`/`im` coordinates.
@isnad1 id=eq.0h3v.s7.0dc930632658 from=translated src=- shape=43bd27c1 vocab=f1741205
-/
theorem _root_.Tengoku.QuadraticNumberFields.imPartRatio_wedge (u v : Qsqrtd (d : ℚ)) :
    imPartRatio (u * star v - v * star u) =
      2 * ((u.im : ℚ) * v.re - u.re * v.im) := by
  rw [imPartRatio_eq_im]
  simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star]
  ring

/-- Multiplying both wedge arguments by `x` scales the wedge by the field norm
`x.re² − d·x.im²` of `x`.
@isnad1 id=eq.0h4v.s9.cbee41c339ef from=translated src=- shape=cec29b38 vocab=10954ab5
-/
theorem _root_.Tengoku.QuadraticNumberFields.imPartRatio_wedge_mul_left (x u v : Qsqrtd (d : ℚ)) :
    imPartRatio (x * u * star (x * v) - x * v * star (x * u)) =
      ((x.re : ℚ) ^ 2 - (d : ℚ) * x.im ^ 2) * imPartRatio (u * star v - v * star u) := by
  rw [imPartRatio_wedge, imPartRatio_wedge]
  simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
  ring
-- Tengoku: 1 notation(s) of this module made local so they do not change other libraries (generated)
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
