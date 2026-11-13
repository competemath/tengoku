/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.MomentMethod.MomentParameters
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar assembly of the uniform band envelope

This file formalizes the complete arithmetic in the component table and
Proposition `band-envelope` (TeX lines 1314--1376).  The operator modules must
supply the individual component bounds; this module proves that their stated
right-hand sides combine to the single constant `3 + sqrt 2`.
-/

namespace NLAlib.SparseSketch

noncomputable section

/-- `a_nu = sqrt ((d+nu+1)/m)`.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def aTerm (d nu m : ℝ) : ℝ := Real.sqrt ((d + nu + 1) / m)

/-- `b_nu = (d+nu+1)/m`.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def bTerm (d nu m : ℝ) : ℝ := (d + nu + 1) / m

/-- `c_nu = (nu+1)/s`.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.-/
def cTerm (nu s : ℝ) : ℝ := (nu + 1) / s

/-- The light square-root envelope term is nonnegative for nonnegative parameters.
Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h3v.s4.0bd80381a63d from=translated src=- shape=ac9c39a3 vocab=02a82c68
-/
theorem aTerm_nonneg (d nu m : ℝ) : 0 ≤ aTerm d nu m :=
  Real.sqrt_nonneg _

/-- The linear dimension-and-grade envelope term is nonnegative.
Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h3v.s5.350d59224b8f from=translated src=- shape=49ed6948 vocab=cc87df87
-/
theorem bTerm_nonneg {d nu m : ℝ}
    (hd : 0 ≤ d) (hnu : 0 ≤ nu) (hm : 0 < m) :
    0 ≤ bTerm d nu m := by
  unfold bTerm
  positivity

/-- The heavy occupation envelope term is nonnegative.
Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h2v.s5.74eb21e5ef13 from=translated src=- shape=42f03e2c vocab=635a4bad
-/
theorem cTerm_nonneg {nu s : ℝ} (hnu : 0 ≤ nu) (hs : 0 < s) :
    0 ≤ cTerm nu s := by
  unfold cTerm
  positivity

/-- The square-root manipulation in lines 1324--1331, with no assumption
`nu <= m`.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h3v.s6.f7469fbb9b83 from=translated src=- shape=50a732e2 vocab=b10b206c
-/
theorem lightPlus_scalar_bound {d nu m : ℝ}
    (hd : 0 ≤ d) (hnu : 0 ≤ nu) (hm : 1 ≤ m) :
    Real.sqrt ((d + nu + 1) * (m + nu)) / m ≤
      aTerm d nu m + bTerm d nu m := by
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have hD : 0 ≤ d + nu + 1 := by positivity
  have hnuDiv : 0 ≤ nu / m := div_nonneg hnu hm0.le
  have hDdiv : 0 ≤ (d + nu + 1) / m := div_nonneg hD hm0.le
  have hsqrtNu : Real.sqrt (nu / m) ≤ Real.sqrt ((d + nu + 1) / m) := by
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith) hm0.le)
  have hsqrtOne : Real.sqrt (1 + nu / m) ≤ 1 + Real.sqrt (nu / m) := by
    have hsq : (1 + nu / m) ≤ (1 + Real.sqrt (nu / m)) ^ 2 := by
      nlinarith [Real.sq_sqrt hnuDiv, Real.sqrt_nonneg (nu / m)]
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hsq⟩
  have hfactor :
      Real.sqrt ((d + nu + 1) * (m + nu)) / m =
        Real.sqrt ((d + nu + 1) / m) * Real.sqrt (1 + nu / m) := by
    have hmne : m ≠ 0 := ne_of_gt hm0
    have hrewrite :
        ((d + nu + 1) * (m + nu)) / m ^ 2 =
          ((d + nu + 1) / m) * (1 + nu / m) := by
      field_simp
    calc
      Real.sqrt ((d + nu + 1) * (m + nu)) / m =
          Real.sqrt (((d + nu + 1) * (m + nu)) / m ^ 2) := by
        rw [Real.sqrt_div (by positivity : 0 ≤ (d + nu + 1) * (m + nu))]
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hm0]
      _ = Real.sqrt (((d + nu + 1) / m) * (1 + nu / m)) := by rw [hrewrite]
      _ = Real.sqrt ((d + nu + 1) / m) * Real.sqrt (1 + nu / m) := by
        rw [Real.sqrt_mul hDdiv]
  rw [hfactor]
  have ha := Real.sqrt_nonneg ((d + nu + 1) / m)
  calc
    Real.sqrt ((d + nu + 1) / m) * Real.sqrt (1 + nu / m) ≤
        Real.sqrt ((d + nu + 1) / m) * (1 + Real.sqrt (nu / m)) :=
      mul_le_mul_of_nonneg_left hsqrtOne ha
    _ ≤ Real.sqrt ((d + nu + 1) / m) *
        (1 + Real.sqrt ((d + nu + 1) / m)) := by
      exact mul_le_mul_of_nonneg_left
        (by simpa [add_comm] using add_le_add_left hsqrtNu 1) ha
    _ = aTerm d nu m + bTerm d nu m := by
      unfold aTerm bTerm
      nlinarith [Real.sq_sqrt hDdiv]

/-- The `+2` (and by adjoint, `-2`) row of the component table.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h3v.s7.53ff5d83b2c6 from=translated src=- shape=25c8a6ec vocab=b43e463b
-/
theorem plus_row_envelope {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a + 2 * b + (5 / 2 : ℝ) * c ≤ bandConstant * (a + b + c) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  rw [bandConstant]
  nlinarith

/-- The grade-zero row of the component table.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h3v.s6.d387fd34501b from=translated src=- shape=5b8e4205 vocab=57162cdf
-/
theorem zero_row_envelope {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (_hc : 0 ≤ c) :
    4 * b + (3 + Real.sqrt 2) * c ≤ bandConstant * (a + b + c) := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := Real.one_le_sqrt.mpr (by norm_num)
  rw [bandConstant]
  nlinarith

/-- Exact scalar conclusion of the common three-band envelope.  The Boolean
tag selects the plus-or-minus component row or the grade-zero row.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.4h5v.s7.53e3d02709eb from=translated src=- shape=9952b141 vocab=32d60020
-/
theorem common_row_envelope {a b c total : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (isZero : Bool)
    (htotal : total ≤ if isZero then
      4 * b + (3 + Real.sqrt 2) * c
    else a + 2 * b + (5 / 2 : ℝ) * c) :
    total ≤ bandConstant * (a + b + c) := by
  cases isZero
  · exact htotal.trans (plus_row_envelope ha hb hc)
  · exact htotal.trans (zero_row_envelope ha hb hc)

/-- Monotonicity from a grade `nu ≤ 2q` to the uniform ladder parameter
`bandEnvelope d q m s`.  This is the exact scalar bridge from the concrete
band proposition to ladder iteration.

Source: ported from `SparseFockFormal.BandEnvelope`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h5v.s6.c7155d5665ee from=translated src=- shape=a2c58f66 vocab=62305477
-/
theorem grade_envelope_le_betaEnvelope {d q nu : ℕ} {m s : ℝ}
    (hnu : nu ≤ 2 * q) (hm : 0 < m) (hs : 0 < s) :
    bandConstant * (aTerm d nu m + bTerm d nu m + cTerm nu s) ≤
      bandEnvelope d q m s := by
  have hnumNat : d + nu + 1 ≤ momentDim d q := by
    simp [momentDim]
    omega
  have hnum : (d : ℝ) + (nu : ℝ) + 1 ≤ (momentDim d q : ℕ) := by
    exact_mod_cast hnumNat
  have hdiv : ((d : ℝ) + (nu : ℝ) + 1) / m ≤
      (momentDim d q : ℕ) / m :=
    div_le_div_of_nonneg_right hnum hm.le
  have hroot : Real.sqrt (((d : ℝ) + (nu : ℝ) + 1) / m) ≤
      Real.sqrt ((momentDim d q : ℕ) / m) := Real.sqrt_le_sqrt hdiv
  have hsparseNat : nu + 1 ≤ 2 * q + 1 := by omega
  have hsparseNum : ((nu + 1 : ℕ) : ℝ) ≤ ((2 * q + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsparseNat
  have hsparse : ((nu + 1 : ℕ) : ℝ) / s ≤
      ((2 * q + 1 : ℕ) : ℝ) / s :=
    div_le_div_of_nonneg_right hsparseNum hs.le
  rw [bandEnvelope]
  apply mul_le_mul_of_nonneg_left _ bandConstant_pos.le
  unfold aTerm bTerm cTerm
  simpa using add_le_add (add_le_add hroot hdiv) hsparse

end

end NLAlib.SparseSketch
