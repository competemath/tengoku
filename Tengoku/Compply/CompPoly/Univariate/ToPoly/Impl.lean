/-
Copyright (c) 2025 CompPoly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Gregor Mitscha-Baude, Derek Sorensen
-/
module

import all Tengoku.Compply.CompPoly.Univariate.ToPoly.Equiv
public import Tengoku.Compply.CompPoly.Univariate.ToPoly.Equiv
public import Tengoku.Seed.Algebra.Polynomial.Roots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proofs of Correctness for CPolynomial Operations, wrt Mathlib Specs

Proofs that operations defined on CPolynomial and CPolynomial.Raw are correct
wrt the mathlib specs, using the ring equivalence
-/

public section

open Polynomial

namespace CompPoly

namespace CPolynomial

open Raw

section ImplementationCorrectness

variable {R : Type*} [Semiring R]

/-- CPolynomial.monomial is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s6.e11fef916c35 from=translated src=- shape=e618f75f vocab=b353f883
-/
theorem monomial_toPoly [DecidableEq R] [LawfulBEq R] (n : ℕ) (c : R) :
    (monomial n c).toPoly = Polynomial.monomial n c := by
  ext i
  simp only [CPolynomial.toPoly, monomial]
  rw [Polynomial.coeff_monomial, coeff_toPoly, CPolynomial.Raw.coeff_monomial]

/-- CPolynomial.C is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s6.409108e76570 from=translated src=- shape=d9e863da vocab=8850f944
-/
theorem C_toPoly [BEq R] [LawfulBEq R] (r : R) : (C r).toPoly = Polynomial.C r := by
  change ((Raw.C r).trim : Raw R).toPoly = Polynomial.C r
  rw [Raw.toPoly_trim]
  exact Raw.toPoly_C r

/-- CPolynomial.X is correct wrt the Mathlib spec.
@isnad1 id=eq.0h1v.s4.5af231d78b04 from=translated src=- shape=c68a7190 vocab=4e59a5b5
-/
theorem X_toPoly [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).toPoly = Polynomial.X := by
  change (CPolynomial.Raw.X : CPolynomial.Raw R).toPoly = Polynomial.X
  exact CPolynomial.Raw.toPoly_X (R := R)

/-- CPolynomial.eval is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s5.f4290291e228 from=translated src=- shape=51a2bf06 vocab=a19ef9c8
-/
theorem eval_toPoly [BEq R] [LawfulBEq R] (x : R) (p : CPolynomial R) :
    eval x p = p.toPoly.eval x := by
  change Raw.eval x p.val = p.val.toPoly.eval x
  exact (Raw.eval_toPoly_eq_eval x p.val).symm

/-- Evaluation of a constant computable polynomial.
@isnad1 id=eq.0h3v.s5.09eaa214182a from=translated src=- shape=faf8e1e9 vocab=5c1e51d0
-/
theorem eval_C [BEq R] [LawfulBEq R] (a c : R) :
    CPolynomial.eval a (CPolynomial.C c) = c := by
  rw [CPolynomial.eval_toPoly, CPolynomial.C_toPoly, Polynomial.eval_C]

/-- Raw.eval₂ is correct wrt the Mathlib spec.
@isnad1 id=eq.0h5v.s5.dce2b467fbe3 from=translated src=- shape=58d3d4d0 vocab=872201a0
-/
theorem Raw.eval₂_toPoly {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial.Raw R) :
    p.eval₂ f x = p.toPoly.eval₂ f x := by
  unfold CompPoly.CPolynomial.Raw.toPoly CompPoly.CPolynomial.Raw.eval₂
  rw [← Array.foldl_hom (fun q : R[X] => q.eval₂ f x)
    (g₁ := fun acc (t : R × ℕ) => acc + Polynomial.C t.1 * Polynomial.X ^ t.2)
    (g₂ := fun acc (a, i) => acc + f a * x ^ i)]
  · simp
  · intro acc t
    rcases t with ⟨a, i⟩
    simp [Polynomial.eval₂_add, Polynomial.C_mul_X_pow_eq_monomial]

/-- CPolynomial.eval₂ is correct wrt the Mathlib spec.
@isnad1 id=eq.0h5v.s5.d05a31ceb9c7 from=translated src=- shape=58d3d4d0 vocab=d6f3d50c
-/
theorem eval₂_toPoly {S : Type*} [Semiring S]
    (f : R →+* S) (x : S) (p : CPolynomial R) :
    eval₂ f x p = p.toPoly.eval₂ f x := by
  simpa [CompPoly.CPolynomial.eval₂, CompPoly.CPolynomial.toPoly, CompPoly.CPolynomial.Raw.eval₂]
    using
    (Raw.eval₂_toPoly (f := f) (x := x) (p := p.val))

/-- CPolynomial.coeff is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s5.5d1c42f335e5 from=translated src=- shape=70e2cd40 vocab=12fe7ea9
-/
theorem coeff_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) (i : ℕ) :
    p.coeff i = p.toPoly.coeff i := by
  unfold toPoly coeff
  simp [Raw.coeff_toPoly]

/-- Evaluation at zero returns the constant coefficient.
@isnad1 id=eq.0h2v.s5.555053a96c90 from=translated src=- shape=84c3f194 vocab=f0cd1f6d
-/
theorem eval_zero_eq_coeff_zero [BEq R] [LawfulBEq R]
    (p : CPolynomial R) : CPolynomial.eval 0 p = p.coeff 0 := by
  rw [CPolynomial.eval_toPoly]
  rw [← Polynomial.coeff_zero_eq_eval_zero p.toPoly]
  exact (CPolynomial.coeff_toPoly p 0).symm

/-- CPolynomial.divX is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s5.93e5e87431d7 from=translated src=- shape=7623d9ae vocab=9d9b5cb2
-/
theorem divX_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (divX p).toPoly = p.toPoly.divX := by
  ext n
  simp only [CPolynomial.toPoly, CompPoly.CPolynomial.Raw.coeff_toPoly, CPolynomial.coeff,
    CompPoly.CPolynomial.coeff_divX, Polynomial.coeff_divX]

/-- CPolynomial.support is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s5.c1a4d8af5388 from=translated src=- shape=ae04fd19 vocab=28f6251e
-/
theorem support_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.support = p.toPoly.support := by
  ext i
  rw [CPolynomial.mem_support_iff, Polynomial.mem_support_iff, coeff_toPoly]

/-- lemma: toImpl is natDegree's succ-/
private lemma size_toImpl_eq_natDegree_succ {q : R[X]} (hq : q ≠ 0) :
    q.toImpl.size = q.natDegree + 1 := by
  rcases Raw.toImpl_elim q with ⟨hzero, _⟩ | ⟨_, himpl⟩
  · exact (hq hzero).elim
  · simp [himpl]

/-- lemma: size = natDegree's succ-/
private lemma size_eq_toPoly_natDegree_succ [BEq R] [LawfulBEq R]
    (p : CPolynomial R) (hp : p ≠ 0) :
    p.val.size = p.toPoly.natDegree + 1 := by
  have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
  have hsize : p.toPoly.toImpl.size = p.val.size := by
    simpa using congrArg Array.size (toImpl_toPoly_of_canonical p)
  rw [← hsize]
  exact size_toImpl_eq_natDegree_succ htoPoly

/-- CPolynomial.degree is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s5.4922eaeb3620 from=translated src=- shape=ae04fd19 vocab=c5c921be
-/
theorem degree_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.degree = p.toPoly.degree := by
  by_cases hp : p = 0
  · subst hp
    rw [toPoly_zero, CPolynomial.degree]
    rfl
  · have hsize := size_eq_toPoly_natDegree_succ p hp
    have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
    cases hs : p.val.size with
    | zero =>
        simp [hs] at hsize
    | succ n =>
        have hnat : p.toPoly.natDegree = n := by omega
        simp [CPolynomial.degree, hs, hnat,
          Polynomial.degree_eq_natDegree htoPoly]

/-- CPolynomial.natDegree is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s5.6a3314327ef5 from=translated src=- shape=ff4796ba vocab=89ad07ab
-/
theorem natDegree_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.natDegree = p.toPoly.natDegree := by
  by_cases hp : p = 0
  · subst hp
    rw [
      toPoly_zero,
      CPolynomial.natDegree
    ]
    rfl
  · have hsize := size_eq_toPoly_natDegree_succ p hp
    cases hs : p.val.size with
    | zero =>
        simp [hs] at hsize
    | succ n =>
        have hnat : p.toPoly.natDegree = n := by omega
        rw [
          hnat,
          CPolynomial.natDegree,
          hs
        ]

/-- CPolynomial.leadingCoeff is correct wrt the Mathlib spec.
@isnad1 id=eq.0h2v.s5.8a7d3818de62 from=translated src=- shape=2eea39e6 vocab=c3966895
-/
theorem leadingCoeff_toPoly [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.leadingCoeff = p.toPoly.leadingCoeff := by
  by_cases hp : p = 0
  · subst hp
    rw [toPoly_zero, CPolynomial.leadingCoeff]
    rfl
  · have htoPoly : p.toPoly ≠ 0 := (toPoly_eq_zero_iff p).not.mpr hp
    have hpos : p.val.size > 0 := by
      have hsize := size_eq_toPoly_natDegree_succ p hp
      omega
    have hlastImpl :
        p.toPoly.toImpl.getLast (Raw.toImpl_nonzero htoPoly) = p.toPoly.leadingCoeff := by
      simpa [Array.getLast] using Raw.getLast_toImpl htoPoly
    have hround : p.toPoly.toImpl = (p : CPolynomial.Raw R) := by
      simpa using toImpl_toPoly_of_canonical p
    have hlast : p.val.getLast hpos = p.toPoly.leadingCoeff := by
      simpa [hround, Array.getLast] using hlastImpl
    simpa [CPolynomial.leadingCoeff, Array.getLastD, Array.getLast, hpos] using hlast

/-- CPolynomial.monic is correct wrt the Mathlib spec
@isnad1 id=iff.0h2v.s5.5a5b1eff29fd from=translated src=- shape=21d0b664 vocab=4f4d0411
-/
theorem monic_toPoly_iff [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    p.monic ↔ p.toPoly.Monic := by
  rw [monic, Polynomial.Monic.def, beq_iff_eq, leadingCoeff_toPoly]

/-- CPolynomial.erase is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s5.3e182cec1e49 from=translated src=- shape=0c922e57 vocab=a2b07802
-/
theorem erase_toPoly {R : Type*} [Ring R] [BEq R] [LawfulBEq R] [DecidableEq R]
    (n : ℕ) (p : CPolynomial R) :
    (erase n p).toPoly = p.toPoly.erase n := by
  ext i
  rw [← coeff_toPoly, Polynomial.coeff_erase, coeff_erase, ← coeff_toPoly]

/-- CPolynomial.C r mul CPolynomial.X ^ n is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s7.8b37c1174b8e from=translated src=- shape=ab6d6954 vocab=7a46b42a
-/
theorem C_mul_X_pow_toPoly [BEq R] [LawfulBEq R] [DecidableEq R] [Nontrivial R] (r : R) (n : ℕ) :
    (C r * X ^ n).toPoly = Polynomial.monomial n r := by
  rw [C_mul_X_pow_eq_monomial r n]
  exact monomial_toPoly n r

/-- CPolynomial.lcoeff is correct wrt the Mathlib spec.
@isnad1 id=eq.0h3v.s7.b399c762d779 from=translated src=- shape=876ba62e vocab=b5499576
-/
theorem lcoeff_toPoly [BEq R] [LawfulBEq R] (n : ℕ) (p : CPolynomial R) :
    lcoeff (R := R) n p = Polynomial.lcoeff R n (toPoly p) := by
    simp [Polynomial.lcoeff_apply, ← coeff_toPoly]

/-- CPolynomial.degreeLE is correct wrt the Mathlib spec.
@isnad1 id=iff.0h3v.s7.8ed7a6248186 from=translated src=- shape=a2c79041 vocab=557b8609
-/
theorem degreeLE_toPoly {n : WithBot ℕ} [BEq R] [LawfulBEq R] {p : CPolynomial R} :
    p ∈ degreeLE (R := R) n ↔ p.toPoly ∈ Polynomial.degreeLE R n := by
  rw [Polynomial.mem_degreeLE]
  rw [mem_degreeLE]
  rw [degree_toPoly]

/-- CPolynomial.degreeLT is correct wrt the Mathlib spec.
@isnad1 id=iff.0h3v.s7.08a44f3da588 from=translated src=- shape=4612a1df vocab=dcccfcd9
-/
theorem degreeLT_toPoly {n : ℕ} [BEq R] [LawfulBEq R] {p : CPolynomial R} :
    p ∈ degreeLT (R := R) n ↔ p.toPoly ∈ Polynomial.degreeLT R n := by
  rw [Polynomial.mem_degreeLT]
  rw [mem_degreeLT]
  rw [degree_toPoly]

end ImplementationCorrectness

section EvaluationDivision

variable {R : Type*}

/-- Evaluation preserves multiplication.
@isnad1 id=eq.0h4v.s6.ec37d1587236 from=translated src=- shape=a026bf6a vocab=7cf9bc7f
-/
theorem eval_mul [CommSemiring R] [BEq R] [LawfulBEq R]
    (p q : CPolynomial R) (x : R) :
    (p * q).eval x = p.eval x * q.eval x := by
  rw [eval_toPoly, toPoly_mul, Polynomial.eval_mul, ← eval_toPoly, ← eval_toPoly]

/-- **Univariate eval-extensionality (degree-bounded).** Two `CPolynomial`s
over an integral domain that agree on more than $d$ points of a `Finset S` are
equal, when $d$ bounds the natural degree of their difference.

The degree bound is needed over finite fields, where two distinct polynomials
may agree on every field element.
@isnad1 id=eq.2h5v.s7.3662604d4274 from=translated src=- shape=4c847d00 vocab=233ec154
-/
theorem eval_ext
    [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]
    {p q : CPolynomial R} {d : ℕ} {S : Finset R}
    (hdeg : (p - q).natDegree ≤ d)
    (hagree :
      d < (S.filter
              (fun r ↦ p.eval r = q.eval r)).card) :
    p = q := by
  by_contra hne
  let r : CPolynomial R := p - q
  have hrne : r ≠ 0 := sub_ne_zero.mpr hne
  have hrPolyNe : r.toPoly ≠ 0 := by
    intro h
    exact hrne ((toPoly_eq_zero_iff r).mp h)
  have hrPolyDeg : r.toPoly.natDegree ≤ d := by
    rwa [← natDegree_toPoly]
  let T : Finset R :=
    S.filter (fun x ↦ p.eval x = q.eval x)
  have hTcard : d < T.card := hagree
  have heval_zero : ∀ x ∈ T, r.toPoly.eval x = 0 := by
    intro x hx
    have hxeq : p.eval x = q.eval x := (Finset.mem_filter.mp hx).2
    rw [← eval_toPoly]
    show r.eval x = 0
    rw [show r = p - q from rfl, eval_toPoly, toPoly_sub, Polynomial.eval_sub,
      ← eval_toPoly, ← eval_toPoly, hxeq, sub_self]
  exact hrPolyNe <|
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' r.toPoly T
      heval_zero (lt_of_le_of_lt hrPolyDeg hTcard)

/-- Evaluation preserves subtraction.
@isnad1 id=eq.0h4v.s6.6ac12e9f228a from=translated src=- shape=aafe491f vocab=c4d5dbfe
-/
theorem eval_sub [Ring R] [BEq R] [LawfulBEq R]
    (a : R) (p q : CPolynomial R) :
    CPolynomial.eval a (p - q) = CPolynomial.eval a p - CPolynomial.eval a q := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_sub, Polynomial.eval_sub,
    ← CPolynomial.eval_toPoly, ← CPolynomial.eval_toPoly]

/-- Evaluation of the constant one computable polynomial.
@isnad1 id=eq.0h2v.s5.881624181679 from=translated src=- shape=79c67346 vocab=d5bebb71
-/
theorem eval_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) : CPolynomial.eval a (1 : CPolynomial R) = 1 := by
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_one, Polynomial.eval_one]

/-- Dividing by `X` preserves a nonzero root when the constant coefficient vanishes.
@isnad1 id=eq.3h3v.s7.3588f14b7514 from=translated src=- shape=8a3ed33e vocab=846794b2
-/
theorem eval_divX_eq_zero_of_ne_zero_root [Field R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {a : R} (ha : a ≠ 0)
    (hcoeff : p.coeff 0 = 0) (hroot : CPolynomial.eval a p = 0) :
    CPolynomial.eval a (CPolynomial.divX p) = 0 := by
  have hdecomp := CPolynomial.X_mul_divX_add (p := p)
  have hroot' :
      CPolynomial.eval a (CPolynomial.X * CPolynomial.divX p + CPolynomial.C (p.coeff 0)) =
        0 := by
    rw [← hdecomp]
    exact hroot
  rw [CPolynomial.eval_toPoly, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.X_toPoly, CPolynomial.C_toPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_C, ← CPolynomial.eval_toPoly] at hroot'
  rw [hcoeff] at hroot'
  simp at hroot'
  rcases hroot' with hzero | hdivRoot
  · exact (ha hzero).elim
  · exact hdivRoot

/-- If a nonzero polynomial has zero constant coefficient, its quotient by `X` is nonzero.
@isnad1 id=ne.2h2v.s7.ad0cba9d3e60 from=translated src=- shape=d75887ef vocab=6e5f90c7
-/
theorem divX_ne_zero_of_ne_zero_coeff_zero [Field R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} (hp : p ≠ 0) (hcoeff : p.coeff 0 = 0) :
    CPolynomial.divX p ≠ 0 := by
  intro hdiv
  apply hp
  have hC0 : CPolynomial.C (0 : R) = 0 := by
    apply (CPolynomial.eq_iff_coeff).2
    intro i
    simp
  rw [CPolynomial.X_mul_divX_add (p := p), hdiv, hcoeff]
  rw [hC0]
  simp

namespace Raw

/--
@isnad1 id=eq.1h6v.s7.23ebbbba8ae7 from=translated src=- shape=7c2b3c78 vocab=ddd18b86
-/
theorem eval_sub_C_mul_X_pow_trim_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) (scale : R)
    (shift : ℕ) {x : R} (hq : q.eval x = 0) :
    ((p - C scale * (q * X ^ shift)).trim).eval x = p.eval x := by
  rw [eval_trim_eq_eval]
  rw [← eval_toPoly_eq_eval x]
  rw [toPoly_sub, toPoly_mul, toPoly_C, toPoly_mul, toPoly_pow, toPoly_X]
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X]
  simp [eval_toPoly_eq_eval, hq]

/--
@isnad1 id=eq.1h5v.s6.2b671a0abcb8 from=translated src=- shape=e6c54161 vocab=f74e91a9
-/
theorem eval_divModByMonicAux_go_snd_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] :
    ∀ (fuel : ℕ) (p q : CPolynomial.Raw R) {x : R}, q.eval x = 0 →
      (divModByMonicAux.go fuel p q).2.eval x = p.eval x := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q x hq
      rfl
  | succ fuel ih =>
      intro p q x hq
      unfold divModByMonicAux.go
      by_cases hsize : p.size < q.size
      · simp [hsize]
      · simp [hsize]
        trans ((p - C p.leadingCoeff * (q * X ^ (p.size - q.size))).trim).eval x
        · exact ih _ _ hq
        · exact eval_sub_C_mul_X_pow_trim_eq_self_of_eval_eq_zero p q p.leadingCoeff
            (p.size - q.size) hq

/-- Reducing by a polynomial that vanishes at `x` preserves evaluation at `x`.
@isnad1 id=eq.1h4v.s6.0dc962dc2fa1 from=translated src=- shape=f276d8f9 vocab=2e0912a8
-/
theorem eval_modByMonic_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial.Raw R) {x : R}
    (hq : q.eval x = 0) :
    (modByMonic p q).eval x = p.eval x :=
  eval_divModByMonicAux_go_snd_eq_self_of_eval_eq_zero p.size p q hq

end Raw

/-- Reducing by a polynomial that vanishes at `x` preserves evaluation at `x`.
@isnad1 id=eq.1h4v.s6.11ede6ca088f from=translated src=- shape=f276d8f9 vocab=e6f35855
-/
theorem eval_modByMonic_eq_self_of_eval_eq_zero
    [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) {x : R}
    (hq : q.eval x = 0) :
    (CPolynomial.modByMonic p q).eval x = p.eval x := by
  have hq_raw : q.val.eval x = 0 := by
    simpa [CPolynomial.eval, Raw.eval, Raw.eval₂] using hq
  change (Raw.modByMonic p.val q.val).eval x = p.val.eval x
  exact Raw.eval_modByMonic_eq_self_of_eval_eq_zero p.val q.val hq_raw

end EvaluationDivision

end CPolynomial

end CompPoly
