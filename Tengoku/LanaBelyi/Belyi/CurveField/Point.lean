/-
Copyright (c) 2026 The Belyi project contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Belyi project contributors
-/
import Tengoku.LanaBelyi.Belyi.CurveField.Residue
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.FieldTheory.Minpoly.Field

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic points of a curve

An algebraic point `x ∈ X(ℚ̄)` of the curve with function field `K` is a place `P` of `K`
together with a field embedding `σ : κ(P) → ℚ̄ := AlgebraicClosure ℚ`
(`Belyi.CurveField.QbarPoint`). This is `Hom(Spec ℚ̄, X)` for the regular proper model `X`
of the curve; it includes the embedding of the constant field of `K`.

The value of a function `f ∈ O_P` at `x` is `f(x) := σ(f mod 𝔪_P) ∈ ℚ̄`
(`Belyi.CurveField.QbarPoint.eval`), and the field of definition of `x` is the number field
`σ(κ(P)) ⊆ ℚ̄` (`Belyi.CurveField.QbarPoint.fieldOf`), of degree `deg x = deg P`.

## Main definitions and results

* `Belyi.CurveField.QbarPoint K`, `QbarPoint.eval`, `QbarPoint.fieldOf`, `QbarPoint.deg`.
* ring-homomorphism lemmas for `eval`; `QbarPoint.eval_eq_zero_iff`:
  `f(x) = 0 ↔ ord_P f > 0` for `f ≠ 0`.
* `QbarPoint.deg_eq : x.deg = x.P.deg`, `QbarPoint.eval_mem_fieldOf`.
* `QbarPoint.finite_setOf_mem`: finitely many points lie over a finite set of places.
* `QbarPoint.exists_P_eq`: every place carries a point.
-/

open IsLocalRing

namespace Belyi.CurveField

/-- An algebraic point of the curve with function field `K`: a place `P` of `K` together with
an embedding of its residue field into `ℚ̄ = AlgebraicClosure ℚ`. -/
structure QbarPoint (K : Type*) [Field K] [CharZero K] where
  /-- The place (closed point of the regular proper model) underlying the point. -/
  P : Place K
  /-- The embedding of the residue field `κ(P)` into `ℚ̄`. -/
  σ : P.ResidueField →+* AlgebraicClosure ℚ

namespace QbarPoint

variable {K : Type*} [Field K] [CharZero K] (x : QbarPoint K)

/--
@isnad1 id=eq.2h3v.s11.0c7503b2cad0 from=translated src=- shape=155dcf96 vocab=abf45198
-/
theorem ext' {x y : QbarPoint K} (hP : x.P = y.P)
    (hσ : ∀ a : x.P.1, x.σ (x.P.residue a) = y.σ (y.P.residue ⟨a.1, hP ▸ a.2⟩)) : x = y := by
  obtain ⟨P, σ⟩ := x
  obtain ⟨Q, τ⟩ := y
  obtain rfl : P = Q := hP
  simp only [mk.injEq, heq_eq_eq, true_and]
  ext b
  obtain ⟨a, rfl⟩ := P.residue_surjective b
  exact hσ a

/-- The value `f(x) ∈ ℚ̄` of a function `f` regular at the point `x`. -/
noncomputable def eval (f : K) (hf : f ∈ x.P.1) : AlgebraicClosure ℚ :=
  x.σ (x.P.residue ⟨f, hf⟩)

variable {f g : K}

/--
@isnad1 id=eq.0h2v.s6.be5dea968d6c from=translated src=- shape=e3ba5d2a vocab=54323d08
-/
@[simp]
theorem eval_zero : x.eval 0 x.P.1.zero_mem = 0 := by
  simp [eval, show (⟨0, x.P.1.zero_mem⟩ : x.P.1) = 0 from rfl]

/--
@isnad1 id=eq.0h2v.s6.d177040163cd from=translated src=- shape=e3ba5d2a vocab=2ae11198
-/
@[simp]
theorem eval_one : x.eval 1 x.P.1.one_mem = 1 := by
  simp [eval, show (⟨1, x.P.1.one_mem⟩ : x.P.1) = 1 from rfl]

/--
@isnad1 id=eq.2h4v.s7.bd24feddbd45 from=translated src=- shape=1983bd7e vocab=72d7874f
-/
theorem eval_add (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f + g) (x.P.1.add_mem _ _ hf hg) = x.eval f hf + x.eval g hg := by
  simp only [eval, ← map_add]
  rfl

/--
@isnad1 id=eq.2h4v.s7.ac1c2604979a from=translated src=- shape=1983bd7e vocab=1f2ea58c
-/
theorem eval_mul (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f * g) (x.P.1.mul_mem _ _ hf hg) = x.eval f hf * x.eval g hg := by
  simp only [eval, ← map_mul]
  rfl

/--
@isnad1 id=eq.1h3v.s7.511c1b1fca4e from=translated src=- shape=31d5b154 vocab=cce86574
-/
theorem eval_neg (hf : f ∈ x.P.1) : x.eval (-f) (x.P.1.neg_mem _ hf) = -x.eval f hf := by
  simp only [eval, ← map_neg]
  rfl

/--
@isnad1 id=eq.2h4v.s7.7fab302a3339 from=translated src=- shape=1983bd7e vocab=8b1eefc3
-/
theorem eval_sub (hf : f ∈ x.P.1) (hg : g ∈ x.P.1) :
    x.eval (f - g) (sub_mem hf hg) = x.eval f hf - x.eval g hg := by
  simp only [eval, ← map_sub]
  rfl

/--
@isnad1 id=eq.1h4v.s7.41db25150c47 from=translated src=- shape=1614dae6 vocab=70c547d9
-/
theorem eval_pow (hf : f ∈ x.P.1) (n : ℕ) :
    x.eval (f ^ n) (pow_mem hf n) = x.eval f hf ^ n := by
  simp only [eval, ← map_pow]
  rfl

/-- The value only depends on the function (proof irrelevance, stated for rewriting).
@isnad1 id=eq.2h4v.s7.99f8f097a8b9 from=translated src=- shape=9d81f38c vocab=353d0890
-/
theorem eval_congr {f g : K} (h : f = g) (hf : f ∈ x.P.1) :
    x.eval f hf = x.eval g (h ▸ hf) := by
  subst h; rfl

/--
@isnad1 id=eq.0h3v.s5.f9c05d76499e from=translated src=- shape=29d8fb61 vocab=7cc27e80
-/
@[simp]
theorem eval_ratCast (q : ℚ) : x.eval (q : K) (x.P.ratCast_mem q) = (q : AlgebraicClosure ℚ) := by
  rw [eval, Place.residue_mk_ratCast, map_ratCast]

/--
@isnad1 id=eq.0h3v.s7.07b78d6b2b86 from=translated src=- shape=f026f86f vocab=9bb28b63
-/
@[simp]
theorem eval_algebraMap (q : ℚ) :
    x.eval (algebraMap ℚ K q) (x.P.algebraMap_mem q) = algebraMap ℚ (AlgebraicClosure ℚ) q :=
  x.eval_ratCast q

/--
@isnad1 id=iff.1h3v.s10.384b6ee2c87f from=translated src=- shape=80794d8b vocab=805cdcf6
-/
theorem eval_eq_zero_iff_mem_maximalIdeal (hf : f ∈ x.P.1) :
    x.eval f hf = 0 ↔ (⟨f, hf⟩ : x.P.1) ∈ maximalIdeal x.P.1 := by
  rw [eval, map_eq_zero_iff _ x.σ.injective, Place.residue_eq_zero_iff]

section IsCurveField

variable [IsCurveField K]

/-- A nonzero regular function vanishes at `x` iff it has positive order at `x.P`.
@isnad1 id=iff.2h3v.s7.37d0caed4ecf from=translated src=- shape=74c6da44 vocab=c2ebe647
-/
theorem eval_eq_zero_iff (hf : f ∈ x.P.1) (hf0 : f ≠ 0) :
    x.eval f hf = 0 ↔ 0 < x.P.ord f := by
  rw [eval_eq_zero_iff_mem_maximalIdeal, x.P.ord_pos_iff_mem_maximalIdeal (a := ⟨f, hf⟩) hf0]

/--
@isnad1 id=iff.1h3v.s7.85506269777a from=translated src=- shape=8e0a8dae vocab=c2ebe647
-/
theorem eval_eq_zero_iff' (hf : f ∈ x.P.1) : x.eval f hf = 0 ↔ f = 0 ∨ 0 < x.P.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  · simp [x.eval_eq_zero_iff hf hf0, hf0]

omit [IsCurveField K] in
/--
@isnad1 id=eq.2h3v.s7.ad1fe8acf86c from=translated src=- shape=4ee53613 vocab=ac1e2ffa
-/
theorem eval_inv (hf : f ∈ x.P.1) (hfi : f⁻¹ ∈ x.P.1) :
    x.eval f⁻¹ hfi = (x.eval f hf)⁻¹ := by
  rcases eq_or_ne f 0 with rfl | hf0
  · have h0 : ∀ h, x.eval 0 h = 0 := fun _ ↦ x.eval_zero
    simp only [inv_zero, h0]
  refine (eq_inv_of_mul_eq_one_left ?_)
  rw [← x.eval_mul hfi hf, x.eval_congr (inv_mul_cancel₀ hf0), eval_one]

end IsCurveField

/-- The field of definition `σ(κ(P)) ⊆ ℚ̄` of the point `x`. -/
noncomputable def fieldOf : IntermediateField ℚ (AlgebraicClosure ℚ) :=
  x.σ.toRatAlgHom.fieldRange

/--
@isnad1 id=mem.1h3v.s7.0c7c825f3821 from=translated src=- shape=20a59bf9 vocab=1363405f
-/
theorem eval_mem_fieldOf (hf : f ∈ x.P.1) : x.eval f hf ∈ x.fieldOf :=
  ⟨x.P.residue ⟨f, hf⟩, rfl⟩

/-- The residue field of `x.P` is isomorphic to the field of definition of `x`. -/
noncomputable def residueFieldEquiv : x.P.ResidueField ≃ₐ[ℚ] x.fieldOf :=
  x.σ.toRatAlgHom.equivFieldRange

/-- The degree `[ℚ(x) : ℚ]` of the point `x`. -/
noncomputable def deg : ℕ := Module.finrank ℚ x.fieldOf

section IsCurveField

variable [IsCurveField K]

omit [IsCurveField K] in
/--
@isnad1 id=eq.0h2v.s5.af88f3dd1879 from=translated src=- shape=2f9f940f vocab=d8ece7f1
-/
theorem deg_eq : x.deg = x.P.deg :=
  x.residueFieldEquiv.toLinearEquiv.finrank_eq.symm

/--
@isnad1 id=lt.0h2v.s5.e8d0820179ad from=translated src=- shape=4d54d531 vocab=d6530dcc
-/
theorem deg_pos : 0 < x.deg := x.deg_eq ▸ x.P.deg_pos

/-- Every place carries an algebraic point.
@isnad1 id=ex.0h2v.s5.8521293fdf42 from=translated src=- shape=39e54df0 vocab=39b50af6
-/
theorem exists_P_eq (P : Place K) : ∃ x : QbarPoint K, x.P = P :=
  ⟨⟨P, (IsAlgClosed.lift (R := ℚ) (S := P.ResidueField) (M := AlgebraicClosure ℚ)).toRingHom⟩,
    rfl⟩

end IsCurveField

end QbarPoint

end Belyi.CurveField
