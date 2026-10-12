/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.mvPolynomialX`, the matrix of variables, and `Matrix.eval_det_mvPolynomialX` occur in the
-- statements and proofs below; this module also supplies `MvPolynomial.eval`.
public import Tengoku
-- The `GL` notation, the coercion of an element of `GL n k` to a matrix,
-- `Matrix.GeneralLinearGroup.det` and `Matrix.GeneralLinearGroup.det_ne_zero`.

/-!
# Polynomial and rational functions on the general linear group

Two subalgebras of the `k`-valued functions on `GL n k`: the functions given by a polynomial in the
matrix entries, and those given by such a polynomial divided by a power of the determinant.  They
are the coordinate-level bookkeeping behind the polynomial and rational representations of
`GL n ℂ`, where a representation is polynomial or rational exactly when all of its matrix
coefficients lie in one of them.

The rational condition is stated multiplicatively, as `det ^ m * f` being polynomial, so that no
inverse is taken and it lives over an arbitrary commutative ring, as the polynomial condition does
over an arbitrary commutative semiring;
`TauCeti.Matrix.GeneralLinearGroup.mem_rationalFunctions_iff_inv` is the equivalent `(det ^ m)⁻¹`
form over a field.

Over a finite field every function on the finite set `GL n k` is the evaluation of a polynomial in
the matrix entries, so `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions k n` is then the whole
function algebra and the distinction between the two collapses.  Consumers for which the distinction
is the point work over an infinite field.

## Main definitions

* `TauCeti.Matrix.GeneralLinearGroup.polynomialFunctions`,
  `TauCeti.Matrix.GeneralLinearGroup.rationalFunctions`: the two subalgebras of `GL (Fin n) k → k`.

## Main results

* `TauCeti.Matrix.GeneralLinearGroup.det_zpow_mem_rationalFunctions`: every integral power of the
  determinant is a rational function.
* `TauCeti.Matrix.GeneralLinearGroup.exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions`
  and its field form
  `TauCeti.Matrix.GeneralLinearGroup.exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions`: a
  finite family of rational functions admits a common denominator.
-/

public section

open Matrix MvPolynomial

universe u w

namespace TauCeti

namespace Matrix.GeneralLinearGroup

section CommSemiring

variable {k : Type u} [CommSemiring k] {n : ℕ}

variable (k n) in
/-- **The polynomial functions on `GL n k`**: those `f : GL (Fin n) k → k` obtained by evaluating a
polynomial in the matrix entries, that is, the range of the algebra map sending the variable indexed
by `(i, j)` to the `(i, j)` entry. -/
noncomputable def polynomialFunctions : Subalgebra k (GL (Fin n) k → k) :=
  (MvPolynomial.aeval fun p : Fin n × Fin n =>
    fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) p.1 p.2).range

end CommSemiring

section CommRing

variable {k : Type u} [CommRing k] {n : ℕ}

/-- Evaluating the generic determinant at the entries of `g` gives `det g`. -/
@[simp]
theorem eval_entries_det_mvPolynomialX (g : GL (Fin n) k) :
    MvPolynomial.eval (fun p : Fin n × Fin n => (g : Matrix (Fin n) (Fin n) k) p.1 p.2)
        (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det
      = (g : Matrix (Fin n) (Fin n) k).det := by
  rw [_root_.Matrix.eval_det_mvPolynomialX]
  congr 1

variable (k n)

/-- **The rational functions on `GL n k`**: those `f : GL (Fin n) k → k` some determinant power of
which is polynomial in the matrix entries.  Stated multiplicatively, as `det ^ m * f` being
polynomial, so that no inverse is taken and the definition makes sense over a commutative ring;
`TauCeti.Matrix.GeneralLinearGroup.mem_rationalFunctions_iff_inv` is the form with `(det ^ m)⁻¹`
over a field. -/
noncomputable def rationalFunctions : Subalgebra k (GL (Fin n) k → k) where
  carrier := {f | ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ g : GL (Fin n) k,
    (g : Matrix (Fin n) (Fin n) k).det ^ m * f g
      = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P}
  mul_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨P₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_mul, ← hP₁ g, ← hP₂ g, pow_add, Pi.mul_apply]
    ring
  one_mem' := ⟨1, 0, fun g => by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨P₁, m₁, hP₁⟩ ⟨P₂, m₂, hP₂⟩
    refine ⟨(_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ m₂ * P₁
      + (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ m₁ * P₂, m₁ + m₂, fun g => ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, eval_entries_det_mvPolynomialX, ← hP₁ g,
      ← hP₂ g, pow_add, Pi.add_apply]
    ring
  zero_mem' := ⟨0, 0, fun g => by simp⟩
  algebraMap_mem' c := ⟨C c, 0, fun g => by simp⟩

variable {k n}

/-- **Membership in the rational functions**: `f` is rational exactly when some determinant power
`det ^ m` makes `det ^ m * f` the evaluation of a polynomial in the matrix entries. -/
theorem mem_rationalFunctions {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k, (g : Matrix (Fin n) (Fin n) k).det ^ m * f g
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P :=
  Iff.rfl

/-- **A finite family of rational functions has a common denominator**: a single determinant power
and a family of numerator polynomials express every member of the family. -/
theorem exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions {ι : Type w} [Finite ι]
    {f : ι → GL (Fin n) k → k} (hf : ∀ i, f i ∈ rationalFunctions k n) :
    ∃ (P : ι → MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ (i : ι) (g : GL (Fin n) k),
      (g : Matrix (Fin n) (Fin n) k).det ^ m * f i g
        = MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) (P i) := by
  have : Fintype ι := Fintype.ofFinite ι
  choose P m hPm using fun i => mem_rationalFunctions.mp (hf i)
  refine ⟨fun i => (_root_.Matrix.mvPolynomialX (Fin n) (Fin n) k).det ^ (Finset.univ.sup m - m i)
    * P i, Finset.univ.sup m, fun i g => ?_⟩
  have hle : m i ≤ Finset.univ.sup m := Finset.le_sup (Finset.mem_univ i)
  rw [map_mul, map_pow, eval_entries_det_mvPolynomialX, ← hPm i g, ← mul_assoc, ← pow_add]
  congr 2
  omega

end CommRing

section Field

variable {k : Type u} [Field k] {n : ℕ}

/-- Over a field, membership in the rational functions is the expected statement that `f` is a
polynomial in the matrix entries divided by a power of the determinant. -/
theorem mem_rationalFunctions_iff_inv {f : GL (Fin n) k → k} :
    f ∈ rationalFunctions k n ↔ ∃ (P : MvPolynomial (Fin n × Fin n) k) (m : ℕ),
      ∀ g : GL (Fin n) k, f g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ *
        MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) P := by
  rw [mem_rationalFunctions]
  refine exists_congr fun P => exists_congr fun m => forall_congr' fun g => ?_
  have hdet : (g : Matrix (Fin n) (Fin n) k).det ^ m ≠ 0 :=
    pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [eq_comm, eq_inv_mul_iff_mul_eq₀ hdet, eq_comm]

/-- **A finite family of rational functions has a common denominator**, in the form with the
determinant power inverted.  This is what lets the coordinate form of rationality carry a single
exponent for the whole matrix. -/
theorem exists_forall_eq_inv_mul_of_forall_mem_rationalFunctions {ι : Type w} [Finite ι]
    {f : ι → GL (Fin n) k → k} (hf : ∀ i, f i ∈ rationalFunctions k n) :
    ∃ (P : ι → MvPolynomial (Fin n × Fin n) k) (m : ℕ), ∀ (i : ι) (g : GL (Fin n) k),
      f i g = ((g : Matrix (Fin n) (Fin n) k).det ^ m)⁻¹ *
        MvPolynomial.eval (fun p => (g : Matrix (Fin n) (Fin n) k) p.1 p.2) (P i) := by
  obtain ⟨P, m, hPm⟩ := exists_forall_det_pow_mul_eq_of_forall_mem_rationalFunctions hf
  refine ⟨P, m, fun i g => ?_⟩
  rw [← hPm i g, inv_mul_cancel_left₀
    (pow_ne_zero _ (_root_.Matrix.GeneralLinearGroup.det_ne_zero g))]

end Field

end Matrix.GeneralLinearGroup

end TauCeti
