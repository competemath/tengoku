/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.PowerSeries.Basic
import Tengoku.Seed.RingTheory.PowerSeries.Derivative
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# B4: the (truncated, completed) associated graded ring of a filtered `ℚ`-algebra

For a decreasing multiplicative ideal filtration `F⁰ = ⊤ ⊇ F¹ ⊇ ⋯` of a `ℚ`-algebra `R`
(`RingFilt`), the *Rees ring* `ReesPS F ⊆ R⟦u⟧` consists of the series `∑ rₙ uⁿ` with `rₙ ∈ Fⁿ`.
For `D : ℕ` the ideal `ReesIdeal F D` consists of those series with `rₙ ∈ F^{n+1}` for `n ≤ D`, and

  `GrT F D := ReesPS F / ReesIdeal F D  =  ⨁_{n ≤ D} Fⁿ/F^{n+1}`

is the associated graded ring truncated in degrees `> D`.  It is an honest commutative
`ℚ`-algebra (no `DirectSum` casts).  `gcl n a` is the class of `a uⁿ` (`a ∈ Fⁿ`), the image of `a` in
`Grⁿ`.  Classes of positive degree are nilpotent: `gcl n a = 0` for `n > D`.  A compatible family of
statements in all `GrT F D` is a statement in the completed associated graded ring.
-/

set_option autoImplicit false

noncomputable section

namespace B4

open PowerSeries

/-- A decreasing multiplicative ideal filtration with `F 0 = ⊤`.-/
structure RingFilt (R : Type*) [CommRing R] where
  /-- the ideals `Fⁿ`-/
  F : ℕ → Ideal R
  zero : F 0 = ⊤
  anti : ∀ {m n : ℕ}, m ≤ n → F n ≤ F m
  mul : ∀ m n, F m * F n ≤ F (m + n)

namespace RingFilt

variable {R : Type*} [CommRing R] (Φ : RingFilt R)

theorem mem_zero (a : R) : a ∈ Φ.F 0 := by rw [Φ.zero]; trivial

theorem mul_mem {m n : ℕ} {a b : R} (ha : a ∈ Φ.F m) (hb : b ∈ Φ.F n) : a * b ∈ Φ.F (m + n) :=
  Φ.mul m n (Ideal.mul_mem_mul ha hb)

theorem pow_mem {a : R} (ha : a ∈ Φ.F 1) (k : ℕ) : a ^ k ∈ Φ.F k := by
  induction k with
  | zero => simpa using Φ.mem_zero 1
  | succ k ih => rw [pow_succ]; exact Φ.mul_mem ih ha

end RingFilt

section Rees

variable {R : Type*} [CommRing R] [Algebra ℚ R] (Φ : RingFilt R)

theorem coeff_mul_mem {r s : R⟦X⟧} (hr : ∀ n, coeff n r ∈ Φ.F n) (hs : ∀ n, coeff n s ∈ Φ.F n)
    (n : ℕ) : coeff n (r * s) ∈ Φ.F n := by
  rw [coeff_mul]
  refine Ideal.sum_mem _ fun p hp => ?_
  have h := Finset.mem_antidiagonal.1 hp
  have := Φ.mul_mem (hr p.1) (hs p.2)
  rwa [h] at this

/-- The Rees ring `{∑ rₙ uⁿ : rₙ ∈ Fⁿ}` as a `ℚ`-subalgebra of `R⟦u⟧`.-/
def ReesPS : Subalgebra ℚ R⟦X⟧ where
  carrier := {r | ∀ n, coeff n r ∈ Φ.F n}
  mul_mem' := fun {r s} hr hs => coeff_mul_mem Φ hr hs
  add_mem' := fun {r s} hr hs n => by rw [map_add]; exact Ideal.add_mem _ (hr n) (hs n)
  one_mem' := fun n => by
    rw [coeff_one]
    split_ifs
    · subst_vars; exact Φ.mem_zero 1
    · exact Ideal.zero_mem _
  zero_mem' := fun n => by rw [map_zero]; exact Ideal.zero_mem _
  algebraMap_mem' := fun c n => by
    show coeff n (algebraMap ℚ R⟦X⟧ c) ∈ Φ.F n
    rw [PowerSeries.algebraMap_apply, coeff_C]
    split_ifs
    · subst_vars; exact Φ.mem_zero _
    · exact Ideal.zero_mem _

theorem mem_ReesPS {r : R⟦X⟧} : r ∈ ReesPS Φ ↔ ∀ n, coeff n r ∈ Φ.F n := Iff.rfl

/-- `∑ rₙ uⁿ` with `rₙ ∈ F^{n+1}` for `n ≤ D`-/
def ReesIdeal (D : ℕ) : Ideal (ReesPS Φ) where
  carrier := {r | ∀ n ≤ D, coeff n (r : R⟦X⟧) ∈ Φ.F (n + 1)}
  add_mem' := fun {r s} hr hs n hn => by
    show coeff n ((r : R⟦X⟧) + (s : R⟦X⟧)) ∈ _
    rw [map_add]; exact Ideal.add_mem _ (hr n hn) (hs n hn)
  zero_mem' := fun n _ => by
    show coeff n (0 : R⟦X⟧) ∈ _
    rw [map_zero]; exact Ideal.zero_mem _
  smul_mem' := fun c r hr n hn => by
    show coeff n ((c : R⟦X⟧) * (r : R⟦X⟧)) ∈ _
    rw [coeff_mul]
    refine Ideal.sum_mem _ fun p hp => ?_
    have h := Finset.mem_antidiagonal.1 hp
    have h2 := Φ.mul_mem (c.2 p.1) (hr p.2 (by omega))
    have : p.1 + (p.2 + 1) = n + 1 := by omega
    rwa [this] at h2

/-- the truncated associated graded ring `Gr_{≤D}`-/
def GrT (D : ℕ) : Type _ := ReesPS Φ ⧸ ReesIdeal Φ D

instance (D : ℕ) : CommRing (GrT Φ D) :=
  inferInstanceAs (CommRing (ReesPS Φ ⧸ ReesIdeal Φ D))

instance (D : ℕ) : Algebra ℚ (GrT Φ D) :=
  inferInstanceAs (Algebra ℚ (ReesPS Φ ⧸ ReesIdeal Φ D))

variable {Φ}

/-- the element `a uⁿ` of the Rees ring (`a ∈ Fⁿ`)-/
def gclPS (n : ℕ) (a : Φ.F n) : ReesPS Φ :=
  ⟨C (a : R) * X ^ n, fun m => by
    rw [coeff_C_mul_X_pow]
    split_ifs with h
    · subst h; exact a.2
    · exact Ideal.zero_mem _⟩

/-- the class of `a ∈ Fⁿ` in `Grⁿ ⊆ Gr_{≤D}`-/
def gcl (D n : ℕ) (a : Φ.F n) : GrT Φ D := Ideal.Quotient.mk _ (gclPS n a)

theorem mk_gclPS_add (D n : ℕ) (a b : Φ.F n) :
    (Ideal.Quotient.mk (ReesIdeal Φ D) (gclPS n (a + b)) : ReesPS Φ ⧸ ReesIdeal Φ D) =
      Ideal.Quotient.mk _ (gclPS n a) + Ideal.Quotient.mk _ (gclPS n b) := by
  rw [← map_add]
  congr 1
  apply Subtype.ext
  show C ((a : R) + (b : R)) * X ^ n = C (a : R) * X ^ n + C (b : R) * X ^ n
  rw [map_add, add_mul]

theorem mk_gclPS_zero (D n : ℕ) :
    (Ideal.Quotient.mk (ReesIdeal Φ D) (gclPS n (0 : Φ.F n)) : ReesPS Φ ⧸ ReesIdeal Φ D) = 0 := by
  rw [← map_zero (Ideal.Quotient.mk (ReesIdeal Φ D))]
  congr 1
  apply Subtype.ext
  show C ((0 : Φ.F n) : R) * X ^ n = 0
  simp

theorem mk_gclPS_mul (D : ℕ) {m n : ℕ} (a : Φ.F m) (b : Φ.F n) :
    (Ideal.Quotient.mk (ReesIdeal Φ D) (gclPS m a) : ReesPS Φ ⧸ ReesIdeal Φ D) *
        Ideal.Quotient.mk _ (gclPS n b) =
      Ideal.Quotient.mk _ (gclPS (m + n) ⟨(a : R) * b, Φ.mul_mem a.2 b.2⟩) := by
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  show C (a : R) * X ^ m * (C (b : R) * X ^ n) = C ((a : R) * b) * X ^ (m + n)
  rw [map_mul, pow_add]; ring

theorem gcl_add (D n : ℕ) (a b : Φ.F n) : gcl D n (a + b) = gcl D n a + gcl D n b :=
  mk_gclPS_add D n a b

theorem gcl_zero (D n : ℕ) : gcl D n (0 : Φ.F n) = 0 := mk_gclPS_zero D n

theorem gcl_neg (D n : ℕ) (a : Φ.F n) : gcl D n (-a) = - gcl D n a := by
  have := gcl_add D n a (-a)
  rw [add_neg_cancel, gcl_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem gcl_sub (D n : ℕ) (a b : Φ.F n) : gcl D n (a - b) = gcl D n a - gcl D n b := by
  rw [sub_eq_add_neg, gcl_add, gcl_neg, sub_eq_add_neg]

theorem gcl_mul (D : ℕ) {m n : ℕ} (a : Φ.F m) (b : Φ.F n) :
    gcl D m a * gcl D n b = gcl D (m + n) ⟨(a : R) * b, Φ.mul_mem a.2 b.2⟩ :=
  mk_gclPS_mul D a b

/-- `ℚ`-multiples of elements of `Fⁿ`-/
def qsmul {n : ℕ} (c : ℚ) (a : Φ.F n) : Φ.F n :=
  ⟨algebraMap ℚ R c * a, Ideal.mul_mem_left _ _ a.2⟩

theorem mk_gclPS_qsmul (D n : ℕ) (c : ℚ) (a : Φ.F n) :
    (Ideal.Quotient.mk (ReesIdeal Φ D) (gclPS n (qsmul c a)) : ReesPS Φ ⧸ ReesIdeal Φ D) =
      c • (Ideal.Quotient.mk _ (gclPS n a) : ReesPS Φ ⧸ ReesIdeal Φ D) := by
  have h := map_smul (Ideal.Quotient.mkₐ ℚ (ReesIdeal Φ D)) c (gclPS n a)
  refine Eq.trans ?_ h
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  congr 1
  apply Subtype.ext
  show C (algebraMap ℚ R c * (a : R)) * X ^ n = c • (C (a : R) * X ^ n)
  rw [Algebra.smul_def, PowerSeries.algebraMap_apply, map_mul]; ring

theorem gcl_qsmul (D n : ℕ) (c : ℚ) (a : Φ.F n) : gcl D n (qsmul c a) = c • gcl D n a :=
  mk_gclPS_qsmul D n c a

/-- `gcl n a = 0` in degree `n > D`-/
theorem gcl_eq_zero_of_lt {D n : ℕ} (h : D < n) (a : Φ.F n) : gcl D n a = 0 := by
  change (Ideal.Quotient.mk _ (gclPS n a) : ReesPS Φ ⧸ ReesIdeal Φ D) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  intro m hm
  show coeff m (C (a : R) * X ^ n) ∈ _
  rw [coeff_C_mul_X_pow, ite_eq_right (by omega)]
  exact Ideal.zero_mem _

/-- `gcl n a = 0` iff `a ∈ F^{n+1}` (for `n ≤ D`): `Grⁿ = Fⁿ/F^{n+1}` injects into `Gr_{≤D}`.-/
theorem gcl_eq_zero_iff {D n : ℕ} (hn : n ≤ D) (a : Φ.F n) :
    gcl D n a = 0 ↔ (a : R) ∈ Φ.F (n + 1) := by
  change (Ideal.Quotient.mk _ (gclPS n a) : ReesPS Φ ⧸ ReesIdeal Φ D) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro h
    have := h n hn
    have e : coeff n ((gclPS n a : ReesPS Φ) : R⟦X⟧) = (a : R) := by
      show coeff n (C (a : R) * X ^ n) = _
      simp
    rwa [e] at this
  · intro h m hm
    show coeff m (C (a : R) * X ^ n) ∈ _
    rw [coeff_C_mul_X_pow]
    split_ifs with hmn
    · subst hmn; exact h
    · exact Ideal.zero_mem _

theorem gcl_congr (D n : ℕ) {a b : Φ.F n} (h : (a : R) = b) : gcl D n a = gcl D n b := by
  rw [Subtype.ext h]

theorem mk_gclPS_one (D : ℕ) :
    (Ideal.Quotient.mk (ReesIdeal Φ D) (gclPS 0 (⟨1, Φ.mem_zero 1⟩ : Φ.F 0)) :
      ReesPS Φ ⧸ ReesIdeal Φ D) = 1 := by
  rw [← map_one (Ideal.Quotient.mk (ReesIdeal Φ D))]
  congr 1
  apply Subtype.ext
  show C (1 : R) * X ^ 0 = 1
  simp

theorem gcl_zero_one (D : ℕ) : gcl D 0 (⟨1, Φ.mem_zero 1⟩ : Φ.F 0) = 1 := mk_gclPS_one D

theorem gcl_one_pow (D k : ℕ) (a : Φ.F 1) :
    (gcl D 1 a) ^ k = gcl D k ⟨(a : R) ^ k, Φ.pow_mem a.2 k⟩ := by
  induction k with
  | zero => rw [pow_zero]; exact (gcl_zero_one D).symm.trans (gcl_congr D 0 (by simp))
  | succ k ih =>
    rw [pow_succ, ih, gcl_mul]
    exact gcl_congr D (k + 1) (by simp [pow_succ])

theorem gcl_one_pow_succ (D : ℕ) (a : Φ.F 1) : (gcl D 1 a) ^ (D + 1) = 0 := by
  rw [gcl_one_pow]; exact gcl_eq_zero_of_lt (Nat.lt_succ_self D) _

/-- classes agree when the difference lies one step deeper-/
theorem gcl_eq_of_sub_mem (D n : ℕ) {a b : Φ.F n} (h : (a : R) - b ∈ Φ.F (n + 1)) :
    gcl D n a = gcl D n b := by
  by_cases hn : n ≤ D
  · have : gcl D n (a - b) = 0 := (gcl_eq_zero_iff hn _).2 h
    rw [gcl_sub] at this
    exact sub_eq_zero.1 this
  · rw [gcl_eq_zero_of_lt (by omega), gcl_eq_zero_of_lt (by omega)]

theorem GrT.commute {D : ℕ} (x y : GrT Φ D) : Commute x y := mul_comm x y

end Rees

end B4
