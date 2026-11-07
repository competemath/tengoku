/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
module

import all Tengoku.Compply.CompPoly.Univariate.Basic
public import Tengoku.Seed.Algebra.Polynomial.Inductions
public import Tengoku.Seed.Algebra.Ring.TransferInstance
public import Tengoku.Seed.Algebra.Tropical.Basic
public import Tengoku.Seed.RingTheory.Polynomial.Basic
public import Tengoku.Compply.CompPoly.Data.Array.Lemmas
public import Tengoku.Compply.CompPoly.Univariate.Basic
public import Tengoku.Compply.CompPoly.Univariate.Linear

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Computable Univariate To `Polynomial`

Conversions between computable univariate polynomials and mathlib `Polynomial`.
-/

public section

open Polynomial

/-- Convert a mathlib `Polynomial` to a `CPolynomial.Raw` by extracting coefficients
up to the degree.-/
def Polynomial.toImpl {R : Type*} [Semiring R] (p : R[X]) : CompPoly.CPolynomial.Raw R :=
  match p.degree with
  | ⊥ => #[]
  | some d  => .ofFn (fun i : Fin (d + 1) => p.coeff i)

namespace CompPoly

namespace CPolynomial

open Raw

variable {R : Type*}
variable {Q : Type*}

section ToPolyDefs

/-- Convert a `CPolynomial.Raw` to a (mathlib) `Polynomial`.-/
noncomputable def Raw.toPoly [Semiring R] (p : CPolynomial.Raw R) : Polynomial R :=
  p.eval₂ Polynomial.C Polynomial.X

/-- Alternative definition of `toPoly` using `Finsupp`; currently unused.-/
noncomputable def Raw.toPoly' [Semiring R] (p : CPolynomial.Raw R) : Polynomial R :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset (Finset.range p.size) p.coeff (by
    intro n hn
    rw [Finset.mem_range]
    by_contra! h
    have h' : p.coeff n = 0 := by simp [h]
    contradiction
  )))

/-- Convert a canonical polynomial to a (mathlib) `Polynomial`.-/
noncomputable def toPoly [Semiring R] (p : CPolynomial R) : Polynomial R := p.val.toPoly

end ToPolyDefs

section ToPoly

variable [Semiring R] [BEq R]
variable [Semiring Q]

namespace Raw

alias ofPoly := Polynomial.toImpl

/-- Evaluation is preserved by `toPoly`.
@isnad1 id=eq.0h3v.s4.631b53224b28 from=translated src=- shape=82564a95 vocab=33d1e25a
-/
theorem eval_toPoly_eq_eval (x : Q) (p : CPolynomial.Raw Q) : p.toPoly.eval x = p.eval x := by
  unfold Raw.toPoly Raw.eval eval₂
  rw [← Array.foldl_hom (Polynomial.eval x)
    (g₁ := fun acc (t : Q × ℕ) ↦ acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) ↦ acc + a * x ^ i) ]
  · congr; exact Polynomial.eval_zero
  simp

/-- The coefficients of `p.toPoly` match those of `p`.
@isnad1 id=eq.0h3v.s4.bc130f8bfc6c from=translated src=- shape=04a2bb94 vocab=f31a3587
-/
lemma coeff_toPoly {p : CPolynomial.Raw Q} {n : ℕ} : p.toPoly.coeff n = p.coeff n := by
  unfold Raw.toPoly Raw.eval₂

  let f := fun (acc: Q[X]) ((a,i): Q × ℕ) ↦ acc + Polynomial.C a * Polynomial.X ^ i
  change (Array.foldl f 0 p.zipIdx).coeff n = p.coeff n

  let motive (size: ℕ) (acc: Q[X]) := acc.coeff n = if (n < size) then p.coeff n else 0

  have zipIdx_size : p.zipIdx.size = p.size := by simp [Array.zipIdx]

  suffices h : motive p.zipIdx.size (Array.foldl f 0 p.zipIdx) by
    rw [h, ite_eq_left_iff, zipIdx_size]
    intro hn
    replace hn : n ≥ p.size := by linarith
    rw [Raw.coeff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hn, Option.getD_none]

  apply Array.foldl_induction motive
  · simp [motive]

  change ∀ (i : Fin p.zipIdx.size) acc, motive i acc → motive (i + 1) (f acc p.zipIdx[i])
  unfold motive f
  intros i acc h
  have i_lt_p : i < p.size := by linarith [i.is_lt]
  have : p.zipIdx[i] = (p[i], ↑i) := by simp [Array.getElem_zipIdx]
  rw [this, Polynomial.coeff_add, Polynomial.coeff_C_mul, coeff_X_pow, mul_ite, h]
  rcases (Nat.lt_trichotomy i n) with hlt | rfl | hgt
  · have h1 : ¬ (n < i) := by linarith
    have h2 : ¬ (n = i) := by linarith
    have h3 : ¬ (n < i + 1) := by linarith
    simp [h1, h2, h3]
  · simp [i_lt_p]
  · have h1 : ¬ (n = i) := by linarith
    have h2 : n < i + 1 := by linarith
    simp [hgt, h1, h2]

/-- Case analysis for `toImpl`: either the polynomial is zero or has a specific form.
@isnad1 id=or.0h2v.s6.77cd61995a01 from=translated src=- shape=c4182a8f vocab=f341a79a
-/
lemma toImpl_elim (p : Q[X]) :
    (p = 0 ∧ p.toImpl = #[])
  ∨ (p ≠ 0 ∧ p.toImpl = .ofFn (fun i : Fin (p.natDegree + 1) => p.coeff i)) := by
  unfold toImpl
  by_cases hbot : p.degree = ⊥
  · left
    use degree_eq_bot.mp hbot
    rw [hbot]
  right
  use degree_ne_bot.mp hbot
  have hnat : p.degree = p.natDegree := Polynomial.degree_eq_natDegree (degree_ne_bot.mp hbot)
  simp [hnat]

/-- `toImpl` is a right-inverse of `toPoly`: the round-trip from `Polynomial` is the identity.

  This shows `toPoly` is surjective and `toImpl` is injective.
@isnad1 id=eq.0h2v.s4.fe34a00c97d5 from=translated src=- shape=2896fe98 vocab=86764213
-/
theorem toPoly_toImpl {p : Q[X]} : p.toImpl.toPoly = p := by
  ext n
  rw [coeff_toPoly]
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨_, h⟩
  · simp [h]
  rw [h]
  by_cases h : n < p.natDegree + 1
  · simp [h]
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp only [h, reduceDIte, Option.getD_none]
  replace h := Nat.lt_of_succ_le (not_lt.mp h)
  symm
  exact coeff_eq_zero_of_natDegree_lt h

/-- Trimming doesn't change the `toPoly` image.
@isnad1 id=eq.0h2v.s5.e8148eaca9a7 from=translated src=- shape=9942c540 vocab=24efd9e4
-/
@[grind =]
lemma toPoly_trim [LawfulBEq R] {p : CPolynomial.Raw R} : p.trim.toPoly = p.toPoly := by
  ext n
  rw [coeff_toPoly, coeff_toPoly, Trim.coeff_eq_coeff]

/-- `toPoly` preserves addition.
@isnad1 id=eq.0h3v.s5.5af30a8ce9b2 from=translated src=- shape=e5844b44 vocab=3c1a5753
-/
@[grind =]
theorem toPoly_addRaw {p q : CPolynomial.Raw Q} : (addRaw p q).toPoly = p.toPoly + q.toPoly := by
  ext n
  rw [Polynomial.coeff_add, coeff_toPoly, coeff_toPoly, coeff_toPoly, add_coeff?]

/-- `toPoly` of a right-scalar multiplication is multiplication by `Polynomial.C r`
on the right.
@isnad1 id=eq.0h3v.s6.5b7f1cd240d4 from=translated src=- shape=77396326 vocab=0d1e91cf
-/
@[grind =]
theorem toPoly_smulRight {p : CPolynomial.Raw Q} {r : Q} :
    (smulRight r p).toPoly = p.toPoly * Polynomial.C r := by
  ext n
  rw [Polynomial.coeff_mul_C, coeff_toPoly, coeff_toPoly]
  show (Array.map (fun a => a * r) p).getD n 0 = p.getD n 0 * r
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : p[n]? with
  | none => simp
  | some a => simp

/--
@isnad1 id=eq.0h3v.s6.eed3619206be from=translated src=- shape=194c6998 vocab=d26f5547
-/
@[grind =]
lemma toPoly_add [LawfulBEq R] (p q : CPolynomial.Raw R) :
    (p + q).toPoly = p.toPoly + q.toPoly := by
  change (p.add q).toPoly = p.toPoly + q.toPoly; unfold add
  rw [toPoly_trim, toPoly_addRaw]

/-- Non-zero polynomials map to non-empty arrays.
@isnad1 id=lt.1h2v.s5.5574cd42c036 from=translated src=- shape=34746312 vocab=c7b2c8dd
-/
lemma toImpl_nonzero {p : Q[X]} (hp : p ≠ 0) : p.toImpl.size > 0 := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  suffices h : p.toImpl ≠ #[] from Array.size_pos_iff.mpr h
  simp [h]

/-- The last coefficient of `toImpl p` is the leading coefficient of `p`.
@isnad1 id=other.1h2v.s6.638d592feaad from=translated src=- shape=8923ef71 vocab=f58ab834
-/
lemma getLast_toImpl {p : Q[X]} (hp : p ≠ 0) : let h : p.toImpl.size > 0 := toImpl_nonzero hp;
    p.toImpl[p.toImpl.size - 1] = p.leadingCoeff := by
  rcases toImpl_elim p with ⟨rfl, _⟩ | ⟨_, h⟩
  · contradiction
  simp [h]

omit [BEq R] in
/-- `toImpl` lands in the semantic canonical carrier used by `CPolynomial`.
@isnad1 id=iscanoni.0h2v.s4.59748c36d60f from=translated src=- shape=ed10201d vocab=7672020d
-/
@[simp]
theorem isCanonical_toImpl (p : R[X]) : IsCanonical p.toImpl := by
  rcases toImpl_elim p with ⟨rfl, h⟩ | ⟨h_nz, _⟩
  · simpa [h] using (Trim.isCanonical_empty (R := R))
  · intro hp
    have hlast : p.toImpl.getLast hp = p.leadingCoeff := by
      simpa [Array.getLast] using (getLast_toImpl (Q := R) (p := p) h_nz)
    rw [hlast]
    exact Polynomial.leadingCoeff_ne_zero.mpr h_nz

/-- `toImpl` produces canonical polynomials (no trailing zeros).
@isnad1 id=eq.0h2v.s5.97f27881095e from=translated src=- shape=e418adc0 vocab=180721bd
-/
@[simp, grind =]
theorem trim_toImpl [LawfulBEq R] (p : R[X]) : p.toImpl.trim = p.toImpl := by
  exact Trim.trim_eq_of_isCanonical (isCanonical_toImpl p)

end Raw

omit [BEq R] in
/-- Building a canonical polynomial from `toImpl` and converting it back yields the
original mathlib polynomial.
@isnad1 id=eq.0h2v.s5.dac3937b4f60 from=translated src=- shape=91cf4f02 vocab=06a83238
-/
theorem toPoly_mk_toImpl (p : R[X]) :
    CPolynomial.toPoly ⟨p.toImpl, Raw.isCanonical_toImpl p⟩ = p := by
  exact Raw.toPoly_toImpl

/-- `ofArray` preserves the raw polynomial's `toPoly` image.
@isnad1 id=eq.0h2v.s5.3e10bf531db9 from=translated src=- shape=e418adc0 vocab=098b0107
-/
theorem ofArray_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) :
    (CPolynomial.ofArray p).toPoly = p.toPoly := by
  unfold CPolynomial.ofArray
  exact Raw.toPoly_trim

/-- On canonical polynomials, `toImpl` is a left-inverse of `toPoly`.

  This shows `toPoly` is a bijection from `CPolynomial R` to `Polynomial R`.
@isnad1 id=eq.0h2v.s5.4246c9f3bc52 from=translated src=- shape=24d58410 vocab=71b07000
-/
@[grind =]
lemma toImpl_toPoly_of_canonical [LawfulBEq R] (p : CPolynomial R) : p.toPoly.toImpl = p := by
  suffices h_inj : ∀ q : CPolynomial R, p.toPoly = q.toPoly → p = q by
    have : p.toPoly = p.toPoly.toImpl.toPoly := by rw [toPoly_toImpl]
    exact
      h_inj ⟨p.toPoly.toImpl, isCanonical_toImpl p.toPoly⟩ this
        |> congrArg Subtype.val
        |>.symm
  intro q hpq
  apply CPolynomial.ext
  apply Trim.isCanonical_ext p.property q.property
  intro i
  rw [← coeff_toPoly, ← coeff_toPoly]
  exact hpq |> congrArg (fun p => p.coeff i)

/-- The round-trip from `CPolynomial.Raw` to `Polynomial` and back yields the canonical form.
@isnad1 id=eq.0h2v.s5.eea2ac328f3c from=translated src=- shape=71f22ba5 vocab=68571cea
-/
@[simp, grind =]
theorem Raw.toImpl_toPoly [LawfulBEq R] (p : CPolynomial.Raw R) : p.toPoly.toImpl = p.trim := by
  rw [← toPoly_trim]
  exact toImpl_toPoly_of_canonical ⟨ p.trim, Trim.isCanonical_trim p⟩

/-- A nonempty trimmed raw polynomial bounds the degree of its `toPoly` image.
@isnad1 id=lt.1h2v.s5.a6c3062ff741 from=translated src=- shape=eefabea7 vocab=fc67b087
-/
theorem Raw.toPoly_natDegree_lt_trim_size_of_pos [LawfulBEq R]
    (p : CPolynomial.Raw R) (hp : 0 < p.trim.size) :
    p.toPoly.natDegree < p.trim.size := by
  have hround := Raw.toImpl_toPoly (R := R) p
  have hsize : p.toPoly.toImpl.size = p.trim.size := congrArg Array.size hround
  rcases Raw.toImpl_elim p.toPoly with ⟨_hzero, himpl⟩ | ⟨_hnz, himpl⟩
  · have : p.trim.size = 0 := by
      rw [← hsize, himpl]
      simp
    omega
  · have himpl_size : p.toPoly.toImpl.size = p.toPoly.natDegree + 1 := by
      simp [himpl]
    omega

/-- `toPoly` maps a canonical polynomial to `0` iff the polynomial is `0`.
@isnad1 id=iff.0h2v.s6.5bc87cd50b00 from=translated src=- shape=f7674a08 vocab=1119bf79
-/
theorem toPoly_eq_zero_iff [LawfulBEq R] (p : CPolynomial R) :
    p.toPoly = 0 ↔ p = 0 := by
  constructor
  · intro hp
    apply CPolynomial.ext
    calc
      (p : CPolynomial.Raw R) = p.toPoly.toImpl := (toImpl_toPoly_of_canonical p).symm
      _ = (0 : CPolynomial.Raw R) := by
        simp [hp, Polynomial.toImpl]
  · rintro rfl
    ext n
    rw [CPolynomial.toPoly, Raw.coeff_toPoly, Polynomial.coeff_zero]
    simpa [CPolynomial.coeff] using (CPolynomial.coeff_zero (R := R) n)

/-- Evaluation is preserved by `toImpl`.
@isnad1 id=eq.0h3v.s5.8f129eb033d2 from=translated src=- shape=f7205a36 vocab=cd3d7fba
-/
@[simp, grind =]
theorem eval_toImpl_eq_eval [LawfulBEq R] (x : R) (p : R[X]) : p.toImpl.eval x = p.eval x := by
  rw [← toPoly_toImpl (p := p), toImpl_toPoly, ← toPoly_trim, eval_toPoly_eq_eval]

/-- Evaluation is unchanged by trimming.
@isnad1 id=eq.0h3v.s5.ec41d4ec081f from=translated src=- shape=28788a9d vocab=a5825b02
-/
@[simp, grind =]
lemma Raw.eval_trim_eq_eval [LawfulBEq R] (x : R) (p : CPolynomial.Raw R) :
    p.trim.eval x = p.eval x := by
  rw [← toImpl_toPoly, eval_toImpl_eq_eval, eval_toPoly_eq_eval]

end ToPoly

end CPolynomial

end CompPoly
