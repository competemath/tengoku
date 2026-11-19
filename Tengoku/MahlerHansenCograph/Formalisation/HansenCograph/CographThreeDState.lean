/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pointed face-count algebra for the cograph `3^d` argument

This file formalizes only the finite algebra following the restricted-product
face-poset theorem.  It deliberately has no definition of a Hansen polytope
and no claim connecting an actual face lattice to `PointedFaceState`.

The six coordinates are the signed-integer versions of `(s, r, t, a, p, q)`
from `research/cograph_join_inequality_increment_math.md`.  Integer-valued
coordinates make the defect `s - 3*r` literal; a later geometric bridge can
map natural face counts into this state.
-/

namespace HansenCograph

/-- The finite pointed and co-pointed face-count state.-/
structure PointedFaceState where
  /-- all nonempty faces, including the top face-/
  s : ℤ
  /-- proper nonempty faces rooted at the selected apex-/
  r : ℤ
  /-- nonempty faces in the selected distinguished facet-/
  t : ℤ
  /-- faces in the selected apex--facet corner interval-/
  a : ℤ
  /-- `r - a + 1`, when the state is realized geometrically-/
  p : ℤ
  /-- `t - a + 1`, when the state is realized geometrically-/
  q : ℤ

/-- The two affine relations satisfied by a geometrically realized state.-/
def PointedFaceState.WellFormed (X : PointedFaceState) : Prop :=
  X.p = X.r - X.a + 1 ∧ X.q = X.t - X.a + 1

/-- The exact scalar state recurrence for a graph join.-/
def PointedFaceState.join (A B : PointedFaceState) : PointedFaceState where
  s := 2 * A.r * B.r + (A.s - 2 * A.r) * (B.s - 2 * B.r)
  r := A.r * B.r
  t := A.a * B.a + A.q * B.q - 1
  a := A.a * B.a
  p := A.r * B.r - A.a * B.a + 1
  q := A.q * B.q

/-- The pointed defect `x = s - 3r` of the audited cograph state.-/
def PointedFaceState.pointedDefect (X : PointedFaceState) : ℤ :=
  X.s - 3 * X.r

/-- Complementary pointed defect `y = s - 3t`.-/
def PointedFaceState.coPointedDefect (X : PointedFaceState) : ℤ :=
  X.s - 3 * X.t

namespace PointedFaceState

/-- Swap the rooted and co-rooted orientations.-/
def dual (X : PointedFaceState) : PointedFaceState where
  s := X.s
  r := X.t
  t := X.r
  a := X.a
  p := X.q
  q := X.p

/--
@isnad1 id=eq.0h1v.s3.cce76ce9eb2a from=translated src=- shape=47dcad53 vocab=060d1520
-/
@[simp] theorem dual_dual (X : PointedFaceState) : X.dual.dual = X := by
  cases X
  rfl

/--
@isnad1 id=wellform.1h1v.s3.61bb99c525a3 from=translated src=- shape=2c86d966 vocab=64f1d848
-/
theorem dual_wellFormed {X : PointedFaceState} (hX : X.WellFormed) :
    X.dual.WellFormed := by
  exact ⟨hX.2, hX.1⟩

/--
@isnad1 id=eq.0h1v.s3.debac091c40c from=translated src=- shape=7718e021 vocab=8bc985e3
-/
@[simp] theorem dual_pointedDefect (X : PointedFaceState) :
    X.dual.pointedDefect = X.coPointedDefect := rfl

/--
@isnad1 id=eq.0h1v.s3.c0fb9b21e57e from=translated src=- shape=7718e021 vocab=8bc985e3
-/
@[simp] theorem dual_coPointedDefect (X : PointedFaceState) :
    X.dual.coPointedDefect = X.pointedDefect := rfl

/-- The exact scalar state recurrence for a disjoint union, obtained by
complementing before and after the join recurrence.-/
def union (A B : PointedFaceState) : PointedFaceState :=
  (A.dual.join B.dual).dual

/-- The two pointed defects differ by the rooted/co-rooted bookkeeping
coordinates.
@isnad1 id=eq.1h1v.s5.3412a2c05d2b from=translated src=- shape=dfc5eecf vocab=85d6a8be
-/
theorem coPointedDefect_eq_pointedDefect_add {X : PointedFaceState}
    (hX : X.WellFormed) :
    X.coPointedDefect = X.pointedDefect + 3 * (X.p - X.q) := by
  rcases hX with ⟨hp, hq⟩
  simp only [coPointedDefect, pointedDefect]
  rw [hp, hq]
  ring

/-- The join recurrence preserves the two affine `p,q` bookkeeping laws.
@isnad1 id=wellform.2h2v.s3.3f8c778506af from=translated src=- shape=03e07a40 vocab=caff9a77
-/
theorem join_wellFormed {A B : PointedFaceState}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (A.join B).WellFormed := by
  rcases hA with ⟨hpA, hqA⟩
  rcases hB with ⟨hpB, hqB⟩
  constructor
  · dsimp [join]
  · dsimp [join]
    rw [hqA, hqB]
    ring

/--
@isnad1 id=wellform.2h2v.s3.e33a69f98285 from=translated src=- shape=03e07a40 vocab=03ccdf7c
-/
theorem union_wellFormed {A B : PointedFaceState}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (A.union B).WellFormed :=
  dual_wellFormed (join_wellFormed (dual_wellFormed hA) (dual_wellFormed hB))

/-- The audited factorization of the `p` recurrence.
@isnad1 id=eq.2h2v.s6.0adea93eb0ce from=translated src=- shape=b4527db2 vocab=0a1e6969
-/
theorem join_p_eq_product_add_corrections {A B : PointedFaceState}
    (hA : A.WellFormed) (hB : B.WellFormed) :
    (A.join B).p =
      A.p * B.p + (A.a - 1) * (B.p - 1) + (B.a - 1) * (A.p - 1) := by
  rcases hA with ⟨hpA, _⟩
  rcases hB with ⟨hpB, _⟩
  dsimp [join]
  rw [hpA, hpB]
  ring

/--
Exact pointed-defect multiplication identity for a join:

`x_(A ∨ B) = r_A x_B + r_B x_A + x_A x_B`.
@isnad1 id=eq.0h2v.s5.58602c410530 from=translated src=- shape=bb164e44 vocab=bba0b22b
-/
theorem join_pointedDefect {A B : PointedFaceState} :
    (A.join B).pointedDefect =
      A.r * B.pointedDefect + B.r * A.pointedDefect +
        A.pointedDefect * B.pointedDefect := by
  simp only [pointedDefect, join]
  ring

/--
The defect is nonnegative after a join under the explicit count and defect
nonnegativity assumptions.  The geometric face-count bridge is intentionally
not part of this theorem.
@isnad1 id=le.4h2v.s5.cde612a57014 from=translated src=- shape=fa73d3eb vocab=1749dd2e
-/
theorem join_pointedDefect_nonneg {A B : PointedFaceState}
    (hrA : 0 ≤ A.r) (hrB : 0 ≤ B.r)
    (hxA : 0 ≤ A.pointedDefect) (hxB : 0 ≤ B.pointedDefect) :
    0 ≤ (A.join B).pointedDefect := by
  rw [join_pointedDefect]
  exact add_nonneg
    (add_nonneg (Int.mul_nonneg hrA hxB) (Int.mul_nonneg hrB hxA))
    (Int.mul_nonneg hxA hxB)

/--
Under positive rooted counts and nonnegative defects, a join has zero pointed
defect exactly when both factor pointed defects are zero.

This is only the equality algebra of the scalar recurrence: it does not
identify which geometric states have positive rooted count.
@isnad1 id=iff.4h2v.s6.ceb8583f00a2 from=translated src=- shape=d5ea573a vocab=b2ca5047
-/
theorem join_pointedDefect_eq_zero_iff_of_pos {A B : PointedFaceState}
    (hrA : 0 < A.r) (hrB : 0 < B.r)
    (hxA : 0 ≤ A.pointedDefect) (hxB : 0 ≤ B.pointedDefect) :
    (A.join B).pointedDefect = 0 ↔
      A.pointedDefect = 0 ∧ B.pointedDefect = 0 := by
  constructor
  · intro hjoin
    rw [join_pointedDefect] at hjoin
    have hAxB : 0 ≤ A.r * B.pointedDefect :=
      Int.mul_nonneg hrA.le hxB
    have hBxA : 0 ≤ B.r * A.pointedDefect :=
      Int.mul_nonneg hrB.le hxA
    have hxx : 0 ≤ A.pointedDefect * B.pointedDefect :=
      Int.mul_nonneg hxA hxB
    have hsum : A.r * B.pointedDefect + B.r * A.pointedDefect = 0 :=
      (add_eq_zero_iff_of_nonneg (add_nonneg hAxB hBxA) hxx).mp hjoin |>.1
    have hprodB : A.r * B.pointedDefect = 0 :=
      (add_eq_zero_iff_of_nonneg hAxB hBxA).mp hsum |>.1
    have hprodA : B.r * A.pointedDefect = 0 :=
      (add_eq_zero_iff_of_nonneg hAxB hBxA).mp hsum |>.2
    constructor
    · rcases mul_eq_zero.mp hprodA with hroot | hdefect
      · exact False.elim ((ne_of_gt hrB) hroot)
      · exact hdefect
    · rcases mul_eq_zero.mp hprodB with hroot | hdefect
      · exact False.elim ((ne_of_gt hrA) hroot)
      · exact hdefect
  · rintro ⟨hA, hB⟩
    rw [join_pointedDefect, hA, hB]
    ring

/-- Cleared-denominator form of the total-face correction in the audit.
@isnad1 id=eq.0h2v.s5.f95066397550 from=translated src=- shape=f23e6182 vocab=4338d245
-/
theorem join_total_correction {A B : PointedFaceState} :
    3 * (A.join B).s - A.s * B.s =
      2 * A.pointedDefect * B.pointedDefect := by
  simp only [pointedDefect, join]
  ring

/-- The positivity package satisfied by geometrically realized nonempty
pointed face states in the cograph argument.-/
def Admissible (X : PointedFaceState) : Prop :=
  X.WellFormed ∧ 1 ≤ X.a ∧ 1 ≤ X.p ∧ 1 ≤ X.q ∧
    0 ≤ X.pointedDefect ∧ 0 ≤ X.coPointedDefect

/--
@isnad1 id=admissib.1h1v.s3.a621e7569488 from=translated src=- shape=2c86d966 vocab=0623ab6f
-/
theorem dual_admissible {X : PointedFaceState} (hX : X.Admissible) :
    X.dual.Admissible := by
  rcases hX with ⟨hwf, ha, hp, hq, hx, hy⟩
  exact ⟨dual_wellFormed hwf, ha, hq, hp, hy, hx⟩

/-- The complementary pointed defect is nonnegative after a join.  This is
the four-order-case argument from the audited cograph `3^d` proof.
@isnad1 id=le.2h2v.s4.4079df5358e3 from=translated src=- shape=147a9ed0 vocab=0e4c7ab7
-/
theorem join_coPointedDefect_nonneg {A B : PointedFaceState}
    (hA : A.Admissible) (hB : B.Admissible) :
    0 ≤ (A.join B).coPointedDefect := by
  rcases hA with ⟨hwfA, haA, hpA, hqA, hxA, hyA⟩
  rcases hB with ⟨hwfB, haB, hpB, hqB, hxB, hyB⟩
  have hrA : 0 ≤ A.r := by nlinarith [hwfA.1]
  have hrB : 0 ≤ B.r := by nlinarith [hwfB.1]
  have hpAr : A.p ≤ A.r := by nlinarith [hwfA.1]
  have hpBr : B.p ≤ B.r := by nlinarith [hwfB.1]
  have hrelA := coPointedDefect_eq_pointedDefect_add hwfA
  have hrelB := coPointedDefect_eq_pointedDefect_add hwfB
  have hformula :
      (A.join B).coPointedDefect =
        A.r * B.pointedDefect + B.r * A.pointedDefect +
          A.pointedDefect * B.pointedDefect +
        3 * (A.p * B.p + (A.a - 1) * (B.p - 1) +
          (B.a - 1) * (A.p - 1) - A.q * B.q) := by
    rw [coPointedDefect_eq_pointedDefect_add (join_wellFormed hwfA hwfB),
      join_pointedDefect, join_p_eq_product_add_corrections hwfA hwfB]
    rfl
  have hrootA : 0 ≤ A.r * B.pointedDefect := Int.mul_nonneg hrA hxB
  have hrootB : 0 ≤ B.r * A.pointedDefect := Int.mul_nonneg hrB hxA
  have hxx : 0 ≤ A.pointedDefect * B.pointedDefect := Int.mul_nonneg hxA hxB
  have hcorrA : 0 ≤ (A.a - 1) * (B.p - 1) :=
    Int.mul_nonneg (by omega) (by omega)
  have hcorrB : 0 ≤ (B.a - 1) * (A.p - 1) :=
    Int.mul_nonneg (by omega) (by omega)
  by_cases hAqp : A.q ≤ A.p
  · by_cases hBqp : B.q ≤ B.p
    · have hprodA : 0 ≤ (A.p - A.q) * B.p :=
        Int.mul_nonneg (sub_nonneg.mpr hAqp) (by omega)
      have hprodB : 0 ≤ A.q * (B.p - B.q) :=
        Int.mul_nonneg (by omega) (sub_nonneg.mpr hBqp)
      rw [hformula]
      nlinarith
    · have hdeltaB : 0 ≤ B.q - B.p := by omega
      have hxBdelta : 3 * (B.q - B.p) ≤ B.pointedDefect := by
        nlinarith
      have hrAq : A.q ≤ A.r := hAqp.trans hpAr
      have hmul :
          A.r * (3 * (B.q - B.p)) ≤ A.r * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hrA
      have hgoodA : 0 ≤ (A.p - A.q) * B.p :=
        Int.mul_nonneg (sub_nonneg.mpr hAqp) (by omega)
      have hgoodB : 0 ≤ (A.r - A.q) * (B.q - B.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hrAq) hdeltaB
      rw [hformula]
      nlinarith
  · by_cases hBqp : B.q ≤ B.p
    · have hdeltaA : 0 ≤ A.q - A.p := by omega
      have hxAdelta : 3 * (A.q - A.p) ≤ A.pointedDefect := by
        nlinarith
      have hrBq : B.q ≤ B.r := hBqp.trans hpBr
      have hmul :
          B.r * (3 * (A.q - A.p)) ≤ B.r * A.pointedDefect :=
        mul_le_mul_of_nonneg_left hxAdelta hrB
      have hgoodA : 0 ≤ A.p * (B.p - B.q) :=
        Int.mul_nonneg (by omega) (sub_nonneg.mpr hBqp)
      have hgoodB : 0 ≤ (A.q - A.p) * (B.r - B.q) :=
        Int.mul_nonneg hdeltaA (sub_nonneg.mpr hrBq)
      rw [hformula]
      nlinarith
    · have hdeltaA : 0 ≤ A.q - A.p := by omega
      have hdeltaB : 0 ≤ B.q - B.p := by omega
      have hxAdelta : 3 * (A.q - A.p) ≤ A.pointedDefect := by
        nlinarith
      have hxBdelta : 3 * (B.q - B.p) ≤ B.pointedDefect := by
        nlinarith
      have hmulA :
          A.r * (3 * (B.q - B.p)) ≤ A.r * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hrA
      have hmulB :
          B.r * (3 * (A.q - A.p)) ≤ B.r * A.pointedDefect :=
        mul_le_mul_of_nonneg_left hxAdelta hrB
      have hmulXX₁ :
          (3 * (A.q - A.p)) * (3 * (B.q - B.p)) ≤
            A.pointedDefect * (3 * (B.q - B.p)) :=
        mul_le_mul_of_nonneg_right hxAdelta (by positivity)
      have hmulXX₂ :
          A.pointedDefect * (3 * (B.q - B.p)) ≤
            A.pointedDefect * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hxA
      have hgapA : 0 ≤ (A.r - A.p) * (B.q - B.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hpAr) hdeltaB
      have hgapB : 0 ≤ (B.r - B.p) * (A.q - A.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hpBr) hdeltaA
      have hdeltaProd : 0 ≤ (A.q - A.p) * (B.q - B.p) :=
        Int.mul_nonneg hdeltaA hdeltaB
      rw [hformula]
      nlinarith

/-- Admissibility is closed under the exact join recurrence.
@isnad1 id=admissib.2h2v.s3.f4097dbc442a from=translated src=- shape=03e07a40 vocab=939c0cdf
-/
theorem join_admissible {A B : PointedFaceState}
    (hA : A.Admissible) (hB : B.Admissible) :
    (A.join B).Admissible := by
  rcases hA with ⟨hwfA, haA, hpA, hqA, hxA, hyA⟩
  rcases hB with ⟨hwfB, haB, hpB, hqB, hxB, hyB⟩
  have hrA : 0 ≤ A.r := by nlinarith [hwfA.1]
  have hrB : 0 ≤ B.r := by nlinarith [hwfB.1]
  refine ⟨join_wellFormed hwfA hwfB, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [join]
    nlinarith [Int.mul_nonneg (by omega : 0 ≤ A.a) (by omega : 0 ≤ B.a)]
  · rw [join_p_eq_product_add_corrections hwfA hwfB]
    have hpA0 : 0 ≤ A.p := by omega
    have hpB0 : 0 ≤ B.p := by omega
    have hpp0 : 0 ≤ A.p * B.p := Int.mul_nonneg hpA0 hpB0
    have hpp : 1 ≤ A.p * B.p := by nlinarith
    have hcA : 0 ≤ (A.a - 1) * (B.p - 1) := Int.mul_nonneg (by omega) (by omega)
    have hcB : 0 ≤ (B.a - 1) * (A.p - 1) := Int.mul_nonneg (by omega) (by omega)
    omega
  · dsimp [join]
    have hqq : 0 ≤ A.q * B.q := Int.mul_nonneg (by omega) (by omega)
    nlinarith
  · exact join_pointedDefect_nonneg hrA hrB hxA hxB
  · exact join_coPointedDefect_nonneg
      ⟨hwfA, haA, hpA, hqA, hxA, hyA⟩
      ⟨hwfB, haB, hpB, hqB, hxB, hyB⟩

/-- Admissibility is closed under disjoint union by complementary duality.
@isnad1 id=admissib.2h2v.s3.85310914c686 from=translated src=- shape=03e07a40 vocab=159c1cb6
-/
theorem union_admissible {A B : PointedFaceState}
    (hA : A.Admissible) (hB : B.Admissible) :
    (A.union B).Admissible := by
  exact dual_admissible (join_admissible (dual_admissible hA) (dual_admissible hB))

/-- The stronger positivity package supplied by nonempty Hansen face lattices.
The three corner counts are at least two, not merely positive.-/
def StronglyAdmissible (X : PointedFaceState) : Prop :=
  X.Admissible ∧ 2 ≤ X.a ∧ 2 ≤ X.p ∧ 2 ≤ X.q

/--
@isnad1 id=admissib.1h1v.s2.e3e62d118b1e from=translated src=- shape=6321fd23 vocab=e3fdeebb
-/
theorem StronglyAdmissible.admissible {X : PointedFaceState}
    (hX : X.StronglyAdmissible) : X.Admissible := hX.1

/--
@isnad1 id=strongly.1h1v.s3.cc1ec8c3d09a from=translated src=- shape=2c86d966 vocab=9cf7db5b
-/
theorem dual_stronglyAdmissible {X : PointedFaceState}
    (hX : X.StronglyAdmissible) : X.dual.StronglyAdmissible := by
  rcases hX with ⟨hAdm, ha, hp, hq⟩
  exact ⟨dual_admissible hAdm, ha, hq, hp⟩

/--
@isnad1 id=strongly.2h2v.s3.148d8ba72ef1 from=translated src=- shape=03e07a40 vocab=7bff9085
-/
theorem join_stronglyAdmissible {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    (A.join B).StronglyAdmissible := by
  rcases hA with ⟨hAdmA, haA, hpA, hqA⟩
  rcases hB with ⟨hAdmB, haB, hpB, hqB⟩
  refine ⟨join_admissible hAdmA hAdmB, ?_, ?_, ?_⟩
  · dsimp [join]
    nlinarith [Int.mul_nonneg (by omega : 0 ≤ A.a) (by omega : 0 ≤ B.a)]
  · rw [join_p_eq_product_add_corrections hAdmA.1 hAdmB.1]
    have hpp : 4 ≤ A.p * B.p := by nlinarith
    have hcA : 0 ≤ (A.a - 1) * (B.p - 1) :=
      Int.mul_nonneg (by omega) (by omega)
    have hcB : 0 ≤ (B.a - 1) * (A.p - 1) :=
      Int.mul_nonneg (by omega) (by omega)
    omega
  · dsimp [join]
    nlinarith [Int.mul_nonneg (by omega : 0 ≤ A.q) (by omega : 0 ≤ B.q)]

/--
@isnad1 id=strongly.2h2v.s3.c5573283e547 from=translated src=- shape=03e07a40 vocab=98538251
-/
theorem union_stronglyAdmissible {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    (A.union B).StronglyAdmissible := by
  exact dual_stronglyAdmissible
    (join_stronglyAdmissible (dual_stronglyAdmissible hA)
      (dual_stronglyAdmissible hB))

/-- The complementary defect of a join of two nonempty realized states is
strictly positive.  This is the strict four-order-case estimate used in the
equality classification.
@isnad1 id=lt.2h2v.s4.50e09bf6c58d from=translated src=- shape=147a9ed0 vocab=a3a58159
-/
theorem join_coPointedDefect_pos {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    0 < (A.join B).coPointedDefect := by
  rcases hA with ⟨⟨hwfA, haA, hpA, hqA, hxA, hyA⟩, haA2, hpA2, hqA2⟩
  rcases hB with ⟨⟨hwfB, haB, hpB, hqB, hxB, hyB⟩, haB2, hpB2, hqB2⟩
  have hrA : 0 ≤ A.r := by nlinarith [hwfA.1]
  have hrB : 0 ≤ B.r := by nlinarith [hwfB.1]
  have hpAr : A.p ≤ A.r := by nlinarith [hwfA.1]
  have hpBr : B.p ≤ B.r := by nlinarith [hwfB.1]
  have hrelA := coPointedDefect_eq_pointedDefect_add hwfA
  have hrelB := coPointedDefect_eq_pointedDefect_add hwfB
  have hformula :
      (A.join B).coPointedDefect =
        A.r * B.pointedDefect + B.r * A.pointedDefect +
          A.pointedDefect * B.pointedDefect +
        3 * (A.p * B.p + (A.a - 1) * (B.p - 1) +
          (B.a - 1) * (A.p - 1) - A.q * B.q) := by
    rw [coPointedDefect_eq_pointedDefect_add (join_wellFormed hwfA hwfB),
      join_pointedDefect, join_p_eq_product_add_corrections hwfA hwfB]
    rfl
  have hrootA : 0 ≤ A.r * B.pointedDefect := Int.mul_nonneg hrA hxB
  have hrootB : 0 ≤ B.r * A.pointedDefect := Int.mul_nonneg hrB hxA
  have hxx : 0 ≤ A.pointedDefect * B.pointedDefect := Int.mul_nonneg hxA hxB
  have hcorrA : 1 ≤ (A.a - 1) * (B.p - 1) := by nlinarith
  have hcorrB : 1 ≤ (B.a - 1) * (A.p - 1) := by nlinarith
  by_cases hAqp : A.q ≤ A.p
  · by_cases hBqp : B.q ≤ B.p
    · have hprodA : 0 ≤ (A.p - A.q) * B.p :=
        Int.mul_nonneg (sub_nonneg.mpr hAqp) (by omega)
      have hprodB : 0 ≤ A.q * (B.p - B.q) :=
        Int.mul_nonneg (by omega) (sub_nonneg.mpr hBqp)
      rw [hformula]
      nlinarith
    · have hdeltaB : 0 ≤ B.q - B.p := by omega
      have hxBdelta : 3 * (B.q - B.p) ≤ B.pointedDefect := by nlinarith
      have hrAq : A.q ≤ A.r := hAqp.trans hpAr
      have hmul : A.r * (3 * (B.q - B.p)) ≤ A.r * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hrA
      have hgoodA : 0 ≤ (A.p - A.q) * B.p :=
        Int.mul_nonneg (sub_nonneg.mpr hAqp) (by omega)
      have hgoodB : 0 ≤ (A.r - A.q) * (B.q - B.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hrAq) hdeltaB
      rw [hformula]
      nlinarith
  · by_cases hBqp : B.q ≤ B.p
    · have hdeltaA : 0 ≤ A.q - A.p := by omega
      have hxAdelta : 3 * (A.q - A.p) ≤ A.pointedDefect := by nlinarith
      have hrBq : B.q ≤ B.r := hBqp.trans hpBr
      have hmul : B.r * (3 * (A.q - A.p)) ≤ B.r * A.pointedDefect :=
        mul_le_mul_of_nonneg_left hxAdelta hrB
      have hgoodA : 0 ≤ A.p * (B.p - B.q) :=
        Int.mul_nonneg (by omega) (sub_nonneg.mpr hBqp)
      have hgoodB : 0 ≤ (A.q - A.p) * (B.r - B.q) :=
        Int.mul_nonneg hdeltaA (sub_nonneg.mpr hrBq)
      rw [hformula]
      nlinarith
    · have hdeltaA : 0 ≤ A.q - A.p := by omega
      have hdeltaB : 0 ≤ B.q - B.p := by omega
      have hxAdelta : 3 * (A.q - A.p) ≤ A.pointedDefect := by nlinarith
      have hxBdelta : 3 * (B.q - B.p) ≤ B.pointedDefect := by nlinarith
      have hmulA : A.r * (3 * (B.q - B.p)) ≤ A.r * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hrA
      have hmulB : B.r * (3 * (A.q - A.p)) ≤ B.r * A.pointedDefect :=
        mul_le_mul_of_nonneg_left hxAdelta hrB
      have hmulXX₁ :
          (3 * (A.q - A.p)) * (3 * (B.q - B.p)) ≤
            A.pointedDefect * (3 * (B.q - B.p)) :=
        mul_le_mul_of_nonneg_right hxAdelta (by positivity)
      have hmulXX₂ :
          A.pointedDefect * (3 * (B.q - B.p)) ≤
            A.pointedDefect * B.pointedDefect :=
        mul_le_mul_of_nonneg_left hxBdelta hxA
      have hgapA : 0 ≤ (A.r - A.p) * (B.q - B.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hpAr) hdeltaB
      have hgapB : 0 ≤ (B.r - B.p) * (A.q - A.p) :=
        Int.mul_nonneg (sub_nonneg.mpr hpBr) hdeltaA
      have hdeltaProd : 0 ≤ (A.q - A.p) * (B.q - B.p) :=
        Int.mul_nonneg hdeltaA hdeltaB
      rw [hformula]
      nlinarith

/-- The pointed defect of a union of two nonempty realized states is strictly
positive, by duality.
@isnad1 id=lt.2h2v.s4.614a3e1e39f3 from=translated src=- shape=147a9ed0 vocab=7aa0fd8b
-/
theorem union_pointedDefect_pos {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    0 < (A.union B).pointedDefect := by
  change 0 < (A.dual.join B.dual).coPointedDefect
  exact join_coPointedDefect_pos
    (dual_stronglyAdmissible hA) (dual_stronglyAdmissible hB)

/--
@isnad1 id=iff.2h2v.s5.bc6bf3202121 from=translated src=- shape=5d2de0a5 vocab=70f26f5f
-/
theorem join_pointedDefect_eq_zero_iff {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    (A.join B).pointedDefect = 0 ↔
      A.pointedDefect = 0 ∧ B.pointedDefect = 0 := by
  have hrA : 0 < A.r := by nlinarith [hA.1.1.1, hA.2.1, hA.2.2.1]
  have hrB : 0 < B.r := by nlinarith [hB.1.1.1, hB.2.1, hB.2.2.1]
  exact join_pointedDefect_eq_zero_iff_of_pos hrA hrB
    hA.1.2.2.2.2.1 hB.1.2.2.2.2.1

/--
@isnad1 id=iff.2h2v.s5.1d0b2ac93c40 from=translated src=- shape=5d2de0a5 vocab=0d729730
-/
theorem union_coPointedDefect_eq_zero_iff {A B : PointedFaceState}
    (hA : A.StronglyAdmissible) (hB : B.StronglyAdmissible) :
    (A.union B).coPointedDefect = 0 ↔
      A.coPointedDefect = 0 ∧ B.coPointedDefect = 0 := by
  change (A.dual.join B.dual).pointedDefect = 0 ↔
    A.coPointedDefect = 0 ∧ B.coPointedDefect = 0
  simpa using join_pointedDefect_eq_zero_iff
    (dual_stronglyAdmissible hA) (dual_stronglyAdmissible hB)

/-!
## Abstract binary expression induction

`StateExpr` is deliberately not a graph cotree.  Its union interpreter is an
explicit parameter, because the geometric complement bridge which supplies the
actual union recurrence is outside this finite algebra module.
-/

/-- A minimal binary expression language for pointed-state recurrences.-/
inductive StateExpr : Type
  | leaf : StateExpr
  | union : StateExpr → StateExpr → StateExpr
  | join : StateExpr → StateExpr → StateExpr

/-- Evaluate an abstract expression with a chosen leaf state and union operation.-/
def StateExpr.eval (leafState : PointedFaceState)
    (unionOp : PointedFaceState → PointedFaceState → PointedFaceState) :
    StateExpr → PointedFaceState
  | .leaf => leafState
  | .union A B => unionOp (A.eval leafState unionOp) (B.eval leafState unionOp)
  | .join A B => (A.eval leafState unionOp).join (B.eval leafState unionOp)

/-- The exact join/union state interpreter preserves the complete admissible
positivity package.
@isnad1 id=admissib.1h2v.s3.c546f2d870ab from=translated src=- shape=52654377 vocab=7e248a99
-/
theorem StateExpr.eval_admissible
    (leafState : PointedFaceState) (hLeaf : leafState.Admissible) :
    ∀ E : StateExpr, (E.eval leafState PointedFaceState.union).Admissible := by
  intro E
  induction E with
  | leaf => exact hLeaf
  | union A B ihA ihB => exact union_admissible ihA ihB
  | join A B ihA ihB => exact join_admissible ihA ihB

/--
A recursive binary decomposition syntax intended for a later graph/cotree
bridge.  It is deliberately only syntax: it carries no graph semantics.-/
inductive RecursiveDecomposition : Type
  | leaf : RecursiveDecomposition
  | union : RecursiveDecomposition → RecursiveDecomposition → RecursiveDecomposition
  | join : RecursiveDecomposition → RecursiveDecomposition → RecursiveDecomposition

/-- Forget a recursive decomposition into the state-expression syntax.-/
def RecursiveDecomposition.toStateExpr : RecursiveDecomposition → StateExpr
  | .leaf => .leaf
  | .union A B => .union A.toStateExpr B.toStateExpr
  | .join A B => .join A.toStateExpr B.toStateExpr

/--
An explicit realization of a recursive decomposition by pointed states.

The three equations are the only required bridge data.  In particular, this
structure does not assert that a graph cotree already has such a realization.-/
structure RecursiveDecomposition.StateRealization where
  leafState : PointedFaceState
  unionOp : PointedFaceState → PointedFaceState → PointedFaceState
  state : RecursiveDecomposition → PointedFaceState
  state_leaf : state .leaf = leafState
  state_union : ∀ A B,
    state (.union A B) = unionOp (state A) (state B)
  state_join : ∀ A B,
    state (.join A B) = (state A).join (state B)

/-- The explicit realization equations identify recursive and expression evaluation.
@isnad1 id=eq.0h2v.s4.118d073f0edb from=translated src=- shape=9d0eecf7 vocab=0d6c2f3e
-/
theorem RecursiveDecomposition.eval_toStateExpr_eq_state
    (R : RecursiveDecomposition.StateRealization) :
    ∀ D : RecursiveDecomposition,
      (D.toStateExpr.eval R.leafState R.unionOp) = R.state D := by
  intro D
  induction D with
  | leaf =>
      simpa [toStateExpr, StateExpr.eval] using R.state_leaf.symm
  | union A B ihA ihB =>
      simp [toStateExpr, StateExpr.eval, ihA, ihB, R.state_union]
  | join A B ihA ihB =>
      simp [toStateExpr, StateExpr.eval, ihA, ihB, R.state_join]

/--
Abstract induction skeleton for pointed-defect nonnegativity.  The union
closure is assumed as data; join closure is the concrete algebra above.
@isnad1 id=and.3h3v.s7.617d93560c87 from=translated src=- shape=9523c603 vocab=5391afda
-/
theorem StateExpr.eval_root_and_pointedDefect_nonneg
    (leafState : PointedFaceState)
    (unionOp : PointedFaceState → PointedFaceState → PointedFaceState)
    (hLeafRoot : 0 ≤ leafState.r)
    (hLeafDefect : 0 ≤ leafState.pointedDefect)
    (hUnion : ∀ A B : PointedFaceState,
      0 ≤ A.r → 0 ≤ B.r →
      0 ≤ A.pointedDefect → 0 ≤ B.pointedDefect →
      0 ≤ (unionOp A B).r ∧ 0 ≤ (unionOp A B).pointedDefect) :
    ∀ E : StateExpr,
      0 ≤ (E.eval leafState unionOp).r ∧
        0 ≤ (E.eval leafState unionOp).pointedDefect := by
  intro E
  induction E with
  | leaf => exact ⟨hLeafRoot, hLeafDefect⟩
  | union A B ihA ihB =>
      exact hUnion _ _ ihA.1 ihB.1 ihA.2 ihB.2
  | join A B ihA ihB =>
      constructor
      · exact Int.mul_nonneg ihA.1 ihB.1
      · exact join_pointedDefect_nonneg ihA.1 ihB.1 ihA.2 ihB.2

/--
Transport the expression induction to any explicit recursive realization.
The union closure remains an explicit hypothesis of the realization consumer.
@isnad1 id=and.3h2v.s7.a1bd4beb2b47 from=translated src=- shape=5d82c094 vocab=7e741ac1
-/
theorem RecursiveDecomposition.StateRealization.root_and_pointedDefect_nonneg
    (R : RecursiveDecomposition.StateRealization)
    (hLeafRoot : 0 ≤ R.leafState.r)
    (hLeafDefect : 0 ≤ R.leafState.pointedDefect)
    (hUnion : ∀ A B : PointedFaceState,
      0 ≤ A.r → 0 ≤ B.r →
      0 ≤ A.pointedDefect → 0 ≤ B.pointedDefect →
      0 ≤ (R.unionOp A B).r ∧ 0 ≤ (R.unionOp A B).pointedDefect)
    (D : RecursiveDecomposition) :
    0 ≤ (R.state D).r ∧ 0 ≤ (R.state D).pointedDefect := by
  rw [← RecursiveDecomposition.eval_toStateExpr_eq_state R D]
  exact StateExpr.eval_root_and_pointedDefect_nonneg
    R.leafState R.unionOp hLeafRoot hLeafDefect hUnion D.toStateExpr

/--
Equality propagation for the join constructor only.  No analogue for the
abstract union operation is asserted here.
@isnad1 id=iff.4h4v.s6.eb0cf6a96fb8 from=translated src=- shape=3a705ac5 vocab=10f2f700
-/
theorem StateExpr.eval_join_pointedDefect_eq_zero_iff_of_pos
    (leafState : PointedFaceState)
    (unionOp : PointedFaceState → PointedFaceState → PointedFaceState)
    (A B : StateExpr)
    (hARoot : 0 < (A.eval leafState unionOp).r)
    (hBRoot : 0 < (B.eval leafState unionOp).r)
    (hADefect : 0 ≤ (A.eval leafState unionOp).pointedDefect)
    (hBDefect : 0 ≤ (B.eval leafState unionOp).pointedDefect) :
    ((StateExpr.join A B).eval leafState unionOp).pointedDefect = 0 ↔
      (A.eval leafState unionOp).pointedDefect = 0 ∧
        (B.eval leafState unionOp).pointedDefect = 0 := by
  change ((A.eval leafState unionOp).join (B.eval leafState unionOp)).pointedDefect = 0 ↔
    (A.eval leafState unionOp).pointedDefect = 0 ∧
      (B.eval leafState unionOp).pointedDefect = 0
  exact join_pointedDefect_eq_zero_iff_of_pos hARoot hBRoot hADefect hBDefect

end PointedFaceState

end HansenCograph
