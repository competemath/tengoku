/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.Seed.FieldTheory.IsRealClosed.Basic
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.Seed.FieldTheory.Separable
import Tengoku.Seed.GroupTheory.Divisible
import Tengoku.Seed.Algebra.Polynomial.FieldDivision
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.Henselian
import Tengoku.Seed.RingTheory.LocalRing.Basic
import Tengoku.Seed.RingTheory.LocalRing.ResidueField.Basic
import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.Seed.RingTheory.HahnSeries.Lex
import Tengoku.Seed.RingTheory.HahnSeries.Binomial
import Tengoku.Seed.RingTheory.HahnSeries.Summable
import Tengoku.Seed.RingTheory.HahnSeries.Valuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hahn--Kaplansky real-closedness

This project formalizes the real-closedness theorem for full Hahn fields.
-/

namespace HahnKaplanskyRealClosedness

open Polynomial
open HahnSeries

noncomputable section

/--
@isnad1 id=issumsq.1h4v.s6.cd37d3652026 from=translated src=- shape=65b4ec1d vocab=e3b41e32
-/
theorem isSumSq_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S)
    {x : R} (hx : IsSumSq x) : IsSumSq (f x) := by
  induction hx with
  | zero => simp
  | sq_add a _ ih =>
      simpa [map_add, map_mul] using IsSumSq.sq_add (f a) ih

/--
@isnad1 id=isrealcl.0h3v.s6.84a5255edd7f from=translated src=- shape=96a879ac vocab=ff0e92be
-/
theorem isRealClosed_of_ringEquiv {R S : Type*} [Field R] [Field S]
    (e : R ≃+* S) [IsRealClosed S] : IsRealClosed R where
  one_add_ne_zero := by
    intro s hs hzero
    have hs' : IsSumSq (e s) := isSumSq_map (e : R →+* S) hs
    have hzero' : 1 + e s = 0 := by
      simpa using congrArg e hzero
    exact IsSemireal.one_add_ne_zero hs' hzero'
  isSquare_or_isSquare_neg := by
    intro x
    rcases IsRealClosed.isSquare_or_isSquare_neg (e x) with ⟨y, hy⟩ | ⟨y, hy⟩
    · left
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      simpa using hy
    · right
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      simpa using hy
  exists_isRoot_of_odd_natDegree := by
    intro f hf
    have hfmap : Odd ((f.map (e : R →+* S)).natDegree) := by
      simpa [Polynomial.natDegree_map] using hf
    rcases IsRealClosed.exists_isRoot_of_odd_natDegree (R := S) (f := f.map (e : R →+* S))
      hfmap with ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    rw [Polynomial.IsRoot]
    apply e.injective
    have hy' : (f.map (e : R →+* S)).eval (e (e.symm y)) = 0 := by
      rw [Polynomial.IsRoot] at hy
      simpa only [RingEquiv.apply_symm_apply] using hy
    have hy'' := Polynomial.eval_map_apply (p := f) (e : R →+* S) (e.symm y)
    simpa using hy''.symm.trans hy'

/-- A separable polynomial with a root has a simple root.
@isnad1 id=ex.2h2v.s8.5fad3cb36182 from=translated src=- shape=45e22e16 vocab=9f464611
-/
theorem exists_simple_root_of_separable_of_exists_root {R : Type*} [Field R]
    {p : R[X]} (hsep : p.Separable) (hroot : ∃ a : R, p.IsRoot a) :
    ∃ a : R, p.IsRoot a ∧ p.derivative.eval a ≠ 0 := by
  rcases hroot with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  simpa [Polynomial.IsRoot, Polynomial.aeval_def] using
    hsep.aeval_derivative_ne_zero (x := a)
      (by simpa [Polynomial.IsRoot, Polynomial.aeval_def] using ha)

/-- Over a perfect field, every squarefree polynomial with a root has a simple root.
@isnad1 id=ex.2h2v.s8.6dd7f6f5220a from=translated src=- shape=8b1ce84d vocab=f8c039f1
-/
theorem exists_simple_root_of_squarefree_of_exists_root {R : Type*} [Field R] [PerfectField R]
    {p : R[X]} (hsq : Squarefree p) (hroot : ∃ a : R, p.IsRoot a) :
    ∃ a : R, p.IsRoot a ∧ p.derivative.eval a ≠ 0 :=
  exists_simple_root_of_separable_of_exists_root
    ((PerfectField.separable_iff_squarefree).mpr hsq) hroot

/-- If a polynomial is not squarefree, then some nonunit square divides it.
@isnad1 id=ex.1h2v.s5.6e0cd3b5846b from=translated src=- shape=14c71fc3 vocab=327a7f10
-/
theorem exists_square_factor_of_not_squarefree {R : Type*} [CommMonoid R]
    {p : R} (h : ¬ Squarefree p) :
    ∃ q : R, q * q ∣ p ∧ ¬ IsUnit q := by
  simpa [Squarefree] using h

/-- A nonzero nonsquarefree polynomial over a field has a positive-degree square factor.
@isnad1 id=ex.2h2v.s8.1fcbcef02d2a from=translated src=- shape=b3993b1a vocab=7fefb550
-/
theorem exists_positive_natDegree_square_factor_of_not_squarefree {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) (h : ¬ Squarefree p) :
    ∃ q : K[X], q ≠ 0 ∧ 0 < q.natDegree ∧ q * q ∣ p := by
  rcases exists_square_factor_of_not_squarefree h with ⟨q, hdvd, hnonunit⟩
  have hq0 : q ≠ 0 := by
    intro hq
    apply hp
    rcases hdvd with ⟨r, hr⟩
    rw [hq, zero_mul, zero_mul] at hr
    exact hr
  have hqpos : 0 < q.natDegree := by
    by_contra hnot
    have hqdeg : q.natDegree = 0 := Nat.eq_zero_of_not_pos hnot
    have hunit : IsUnit q := by
      rw [eq_C_of_natDegree_eq_zero hqdeg]
      apply isUnit_C.mpr
      apply isUnit_iff_ne_zero.mpr
      intro hcoeff
      apply hq0
      rw [eq_C_of_natDegree_eq_zero hqdeg, hcoeff, map_zero]
    exact hnonunit hunit
  exact ⟨q, hq0, hqpos, hdvd⟩

/-- A nonzero nonsquarefree polynomial over a field has a lower-degree square factor.
@isnad1 id=ex.2h2v.s8.cbbeba33c736 from=translated src=- shape=280b5174 vocab=7fefb550
-/
theorem exists_lower_natDegree_square_factor_of_not_squarefree {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) (h : ¬ Squarefree p) :
    ∃ q : K[X], q ≠ 0 ∧ 0 < q.natDegree ∧ q.natDegree < p.natDegree ∧ q * q ∣ p := by
  rcases exists_positive_natDegree_square_factor_of_not_squarefree hp h with
    ⟨q, hq0, hqpos, hdvd⟩
  have hdeg_sq : (q * q).natDegree ≤ p.natDegree :=
    Polynomial.natDegree_le_of_dvd hdvd hp
  have hdeg : q.natDegree + q.natDegree ≤ p.natDegree := by
    simpa [Polynomial.natDegree_mul hq0 hq0] using hdeg_sq
  refine ⟨q, hq0, hqpos, ?_, hdvd⟩
  omega

/-- The part of a polynomial supported in degrees strictly below `n`.-/
noncomputable def polynomialLowerPart {R : Type*} [Semiring R] (p : R[X]) (n : ℕ) :
    R[X] :=
  ∑ i ∈ Finset.range n, Polynomial.monomial i (p.coeff i)

/-- If every nonzero odd-degree polynomial has a root, then every nonzero odd-degree polynomial
has a root of odd multiplicity.
@isnad1 id=ex.3h2v.s7.e059d5313b97 from=translated src=- shape=6cac5072 vocab=1c021b50
-/
theorem exists_root_odd_rootMultiplicity_of_exists_odd_roots {R : Type*} [Field R]
    (hroot : ∀ {p : R[X]}, p ≠ 0 → Odd p.natDegree → ∃ a : R, p.IsRoot a)
    {p : R[X]} (hp : p ≠ 0) (hodd : Odd p.natDegree) :
    ∃ a : R, 0 < p.rootMultiplicity a ∧ Odd (p.rootMultiplicity a) := by
  classical
  have H :
      ∀ n : ℕ, ∀ p : R[X], p.natDegree = n → p ≠ 0 → Odd p.natDegree →
        ∃ a : R, 0 < p.rootMultiplicity a ∧ Odd (p.rootMultiplicity a) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p hpdeg hp hodd
      rcases hroot hp hodd with ⟨a, ha⟩
      let m := p.rootMultiplicity a
      have hmpos : 0 < m := by
        dsimp [m]
        exact (Polynomial.rootMultiplicity_pos hp).2 ha
      by_cases hmodd : Odd m
      · exact ⟨a, hmpos, hmodd⟩
      · have hmeven : Even m := Nat.not_odd_iff_even.mp hmodd
        let q : R[X] := p /ₘ (Polynomial.X - Polynomial.C a) ^ m
        have hfac : (Polynomial.X - Polynomial.C a) ^ m * q = p := by
          dsimp [q, m]
          exact Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p a
        have hpow0 : (Polynomial.X - Polynomial.C a : R[X]) ^ m ≠ 0 := by
          exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero a)
        have hq0 : q ≠ 0 := by
          intro hq
          apply hp
          rw [← hfac, hq, mul_zero]
        have hdeg : p.natDegree = m + q.natDegree := by
          rw [← hfac, Polynomial.natDegree_mul hpow0 hq0]
          congr 1
          rw [(Polynomial.monic_X_sub_C a).natDegree_pow, Polynomial.natDegree_X_sub_C,
            mul_one]
        have hqdeg_lt : q.natDegree < p.natDegree := by
          omega
        have hqodd : Odd q.natDegree := by
          rcases hodd with ⟨r, hr⟩
          rcases hmeven with ⟨s, hs⟩
          refine ⟨r - s, ?_⟩
          omega
        have hqdeg_lt_n : q.natDegree < n := by
          simpa [hpdeg] using hqdeg_lt
        rcases ih q.natDegree hqdeg_lt_n q rfl hq0 hqodd with ⟨b, hbpos, hbodd⟩
        have hqrootb : q.IsRoot b := (Polynomial.rootMultiplicity_pos hq0).1 hbpos
        have hqnotroota : ¬ q.IsRoot a := by
          rw [Polynomial.IsRoot]
          exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero a hp
        have hba : b ≠ a := by
          intro h
          exact hqnotroota (h ▸ hqrootb)
        refine ⟨b, ?_, ?_⟩
        · rw [← hfac]
          have hmul0 : (Polynomial.X - Polynomial.C a) ^ m * q ≠ 0 := by
            rw [hfac]
            exact hp
          have hrootmul :
              ((Polynomial.X - Polynomial.C a : R[X]) ^ m * q).IsRoot b := by
            exact Polynomial.root_mul_left_of_isRoot _ hqrootb
          exact (Polynomial.rootMultiplicity_pos hmul0).2 hrootmul
        · have hmul0 : (Polynomial.X - Polynomial.C a) ^ m * q ≠ 0 := by
            rw [hfac]
            exact hp
          have hfactor_zero :
              Polynomial.rootMultiplicity b ((Polynomial.X - Polynomial.C a : R[X]) ^ m) = 0 := by
            apply Polynomial.rootMultiplicity_eq_zero
            intro hroot
            rw [Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_sub,
              Polynomial.eval_X, Polynomial.eval_C] at hroot
            exact pow_ne_zero m (sub_ne_zero.mpr hba) hroot
          rw [← hfac, Polynomial.rootMultiplicity_mul hmul0, hfactor_zero, zero_add]
          exact hbodd
  exact H p.natDegree p rfl hp hodd

/-- Over a real closed field, every nonzero odd-degree polynomial has a root of odd
multiplicity.
@isnad1 id=ex.2h2v.s7.e441d25f6501 from=translated src=- shape=e20ea5b0 vocab=c57f2894
-/
theorem exists_root_odd_rootMultiplicity {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {p : R[X]} (hp : p ≠ 0) (hodd : Odd p.natDegree) :
    ∃ a : R, 0 < p.rootMultiplicity a ∧ Odd (p.rootMultiplicity a) :=
  exists_root_odd_rootMultiplicity_of_exists_odd_roots
    (fun {p} _hp hodd => IsRealClosed.exists_isRoot_of_odd_natDegree (R := R) (f := p) hodd)
    hp hodd

/-- Over a real closed field, an odd power can cancel any nonzero main coefficient.
@isnad1 id=ex.2h4v.s7.815bdde318ea from=translated src=- shape=b29991db vocab=d537da47
-/
theorem exists_cancel_add_mul_pow_of_odd {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {u b : R} {m : ℕ} (hm : Odd m) (hu : u ≠ 0) :
    ∃ c : R, b + u * c ^ m = 0 := by
  rcases IsRealClosed.exists_eq_pow_of_odd (R := R) (-b / u) hm with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [← hc]
  field_simp [hu]
  ring

/-- If the term to cancel is nonzero, the odd-power cancelling coefficient can be chosen nonzero.
@isnad1 id=ex.3h4v.s7.a621c0801423 from=translated src=- shape=7b59ba1f vocab=d537da47
-/
theorem exists_nonzero_cancel_add_mul_pow_of_odd {R : Type*}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {u b : R} {m : ℕ} (hm : Odd m) (hu : u ≠ 0) (hb : b ≠ 0) :
    ∃ c : R, c ≠ 0 ∧ b + u * c ^ m = 0 := by
  rcases exists_cancel_add_mul_pow_of_odd (R := R) hm hu with ⟨c, hcancel⟩
  refine ⟨c, ?_, hcancel⟩
  intro hc
  apply hb
  have hm_ne : m ≠ 0 := Nat.ne_zero_of_lt hm.pos
  have hpow : c ^ m = 0 := by
    rw [hc]
    exact zero_pow hm_ne
  simpa [hpow] using hcancel

end

end HahnKaplanskyRealClosedness
