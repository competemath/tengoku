/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ArgumentPrinciple.BoundaryIntegrals
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ZeroCounting.SmoothMainTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Zeta rectangle counts and the direct Riemann--von Mangoldt interface

This module makes the direct route precise without asserting the missing
contour theorem.  It proves that the zeros inside a wide rectangle with a
good top edge are exactly the actual Mathlib-nontrivial zeta zeros in the
corresponding half-open height slab.  It then separates the two genuinely
analytic inputs:

* an argument-principle/Riemann--von Mangoldt formula for the actual
  multiplicity-weighted zeta count; and
* a Backlund bound for that formula's argument term.

The adapter to the canonical xi divisor lives in the reduction layer, so this
file has no dependency on Hadamard products, xi factorization, or RH criteria.
-/

namespace OverflowResidueRH

namespace ZetaRectangle

/-- An actual Mathlib-nontrivial zeta zero lies in the open rectangle.-/
def IsNontrivialZetaZeroInside (R : ZetaRectangle) (s : Complex) : Prop :=
  IsMathlibNontrivialZetaZero s ∧ R.ContainsOpen s

/-- An actual Mathlib-nontrivial zeta zero lies in the positive-ordinate,
half-open height slab `(A, B]`. The positivity clause matches the cumulative
count `zetaWeightedZeroCountUpToHeight`, which counts only positive
ordinates.-/
def IsNontrivialZetaZeroInHeightSlab
    (A B : Real) (s : Complex) : Prop :=
  IsMathlibNontrivialZetaZero s ∧ 0 < s.im ∧ A < s.im ∧ s.im <= B

/-- The finite type of distinct positive-ordinate nontrivial zeta zeros in
the half-open slab `(A,B]`.-/
def ZetaNontrivialZeroInHeightSlab (A B : Real) : Type :=
  {s : Complex // IsNontrivialZetaZeroInHeightSlab A B s}

/-- A bounded positive-height slab contains only finitely many distinct
nontrivial zeta zeros.-/
theorem zetaNontrivialZeroInHeightSlab_finite (A B : Real) :
    Finite (ZetaNontrivialZeroInHeightSlab A B) := by
  exact ((zetaNontrivialZerosUpToHeightSet_finite B).subset (by
    intro s hs
    exact ⟨hs.1, hs.2.1, hs.2.2.2⟩)).to_subtype

/-- One slab occurrence for each unit of analytic multiplicity.-/
noncomputable def ZetaZeroOccurrenceInHeightSlab
    (A B : Real) : Type :=
  Sigma fun s : ZetaNontrivialZeroInHeightSlab A B =>
    Fin (analyticOrderNatAt riemannZeta s.1)

/-- The multiplicity-bearing slab occurrence type is finite.-/
theorem zetaZeroOccurrenceInHeightSlab_finite (A B : Real) :
    Finite (ZetaZeroOccurrenceInHeightSlab A B) := by
  letI : Finite (ZetaNontrivialZeroInHeightSlab A B) :=
    zetaNontrivialZeroInHeightSlab_finite A B
  unfold ZetaZeroOccurrenceInHeightSlab
  infer_instance

/-- The finite occurrence type may be enumerated without choosing an order.
This instance is used only to form the explicit finite principal part of the
zeta divisor in a bounded height slab.-/
noncomputable instance zetaZeroOccurrenceInHeightSlab_fintype
    (A B : Real) : Fintype (ZetaZeroOccurrenceInHeightSlab A B) := by
  letI : Finite (ZetaZeroOccurrenceInHeightSlab A B) :=
    zetaZeroOccurrenceInHeightSlab_finite A B
  exact Fintype.ofFinite _

/-- The explicit sum of unit principal parts indexed by every occurrence of
an actual nontrivial zeta zero in the rectangle's half-open height slab.
Analytic multiplicity is represented by repeated occurrence indices.-/
noncomputable def zetaSlabPrincipalPart (R : ZetaRectangle) :
    Complex -> Complex :=
  finitePrincipalPart Finset.univ
    (fun i : ZetaZeroOccurrenceInHeightSlab R.bottom R.top => i.fst.1)
    (fun _ => 1)

/-- Exact partition of the multiplicity-bearing occurrences up to `B` into
those up to `A` and those in `(A,B]`.-/
noncomputable def zetaZeroOccurrenceUpToHeightEquivSumSlab
    {A B : Real} (hAB : A <= B) :
    ZetaZeroOccurrenceUpToHeight B ≃
      ZetaZeroOccurrenceUpToHeight A ⊕
        ZetaZeroOccurrenceInHeightSlab A B where
  toFun i := if h : i.fst.1.im <= A then
      Sum.inl ⟨⟨i.fst.1,
        i.fst.2.1, i.fst.2.2.1, h⟩, i.snd⟩
    else
      Sum.inr ⟨⟨i.fst.1,
        i.fst.2.1, i.fst.2.2.1, lt_of_not_ge h, i.fst.2.2.2⟩,
        i.snd⟩
  invFun x := match x with
    | Sum.inl i => ⟨⟨i.fst.1,
        i.fst.2.1, i.fst.2.2.1, i.fst.2.2.2.trans hAB⟩, i.snd⟩
    | Sum.inr i => ⟨⟨i.fst.1,
        i.fst.2.1, i.fst.2.2.1, i.fst.2.2.2.2⟩, i.snd⟩
  left_inv i := by
    dsimp
    split_ifs <;> apply Sigma.ext <;> simp
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  right_inv x := by
    rcases x with i | i
    · dsimp
      rw [dite_eq_left i.fst.2.2.2]
      apply congrArg Sum.inl
      apply Sigma.ext <;> simp
      first
        | (all_goals grind; done)
        | (all_goals simp_all; done)
        | (all_goals aesop; done)
        | (all_goals omega; done)
        | (all_goals norm_num; done)
        | (all_goals positivity; done)
        | (all_goals linarith; done)
        | (all_goals decide; done)
        | (all_goals tauto; done)
    · dsimp
      rw [dite_eq_right (not_le.mpr i.fst.2.2.2.1)]
      apply congrArg Sum.inr
      apply Sigma.ext <;> simp
      first
        | (all_goals grind; done)
        | (all_goals simp_all; done)
        | (all_goals aesop; done)
        | (all_goals omega; done)
        | (all_goals norm_num; done)
        | (all_goals positivity; done)
        | (all_goals linarith; done)
        | (all_goals decide; done)
        | (all_goals tauto; done)

/-- For a rectangle containing the critical strip horizontally, based at a
nonnegative height, and with a good top height, its interior nontrivial zeros
are exactly the positive-ordinate zeros in its half-open height slab. The
good-height condition removes the only endpoint discrepancy, at the top
edge.-/
theorem isNontrivialZetaZeroInside_iff_heightSlab
    {R : ZetaRectangle} {s : Complex}
    (hleft : R.left < 0)
    (hright : 1 < R.right)
    (hbottom : 0 <= R.bottom)
    (htopGood : ZetaGoodHeight R.top) :
    R.IsNontrivialZetaZeroInside s ↔
      IsNontrivialZetaZeroInHeightSlab R.bottom R.top s := by
  constructor
  · rintro ⟨hs, hrect⟩
    exact ⟨hs, lt_of_le_of_lt hbottom hrect.2.2.1,
      hrect.2.2.1, hrect.2.2.2.le⟩
  · rintro ⟨hs, _himpos, hslabBottom, htop⟩
    have hxi : entireRiemannXi s = 0 :=
      entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr hs
    have hstrip : s.re ∈ Set.Ioo (0 : Real) 1 :=
      entireRiemannXi_zero_re_mem_Ioo hxi
    have himTop : s.im < R.top :=
      lt_of_le_of_ne htop (htopGood s hs)
    exact ⟨hs, lt_trans hleft hstrip.1, lt_trans hstrip.2 hright,
      hslabBottom, himTop⟩

/-- The exact multiplicity-weighted count in `(A, B]`, expressed as the
increment of the already formalized cumulative actual-zeta count.-/
noncomputable def zetaWeightedZeroCountInHeightSlab
    (A B : Real) : Nat :=
  zetaWeightedZeroCountUpToHeight B - zetaWeightedZeroCountUpToHeight A

/-- The cumulative-count difference is exactly the cardinality of the
multiplicity-bearing slab occurrence type.-/
theorem natCard_zetaZeroOccurrenceInHeightSlab
    {A B : Real} (hAB : A <= B) :
    Nat.card (ZetaZeroOccurrenceInHeightSlab A B) =
      zetaWeightedZeroCountInHeightSlab A B := by
  letI : Finite (ZetaZeroOccurrenceUpToHeight A) :=
    zetaZeroOccurrenceUpToHeight_finite A
  letI : Finite (ZetaZeroOccurrenceUpToHeight B) :=
    zetaZeroOccurrenceUpToHeight_finite B
  letI : Finite (ZetaZeroOccurrenceInHeightSlab A B) :=
    zetaZeroOccurrenceInHeightSlab_finite A B
  have hcard := Nat.card_congr
    (zetaZeroOccurrenceUpToHeightEquivSumSlab hAB)
  rw [Nat.card_sum] at hcard
  unfold zetaWeightedZeroCountInHeightSlab
  unfold zetaWeightedZeroCountUpToHeight
  rw [hcard]
  omega

/-- **The divisor side of the zeta rectangle residue formula, proved
unconditionally.**  For a rectangle wider than the critical strip, based at
a nonnegative height and with a zero-free top edge, the boundary integral of
the explicit finite principal-part sum of all zeta-zero occurrences in the
height slab is exactly `2*pi*I` times the multiplicity-weighted slab count.

What remains for the full zeta argument principle is the analytic
decomposition asserting that `zetaLogDeriv - zetaSlabPrincipalPart R`
extends holomorphically through the zeros in the rectangle.-/
theorem rectangleBoundaryIntegral_zetaSlabPrincipalPart_eq
    {R : ZetaRectangle}
    (hleft : R.left < 0)
    (hright : 1 < R.right)
    (_hbottom : 0 <= R.bottom)
    (htopGood : ZetaGoodHeight R.top) :
    rectangleBoundaryIntegral R.zetaSlabPrincipalPart
        R.left R.right R.bottom R.top =
      twoPiI *
        (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Complex) := by
  classical
  have hprincipal := rectangleBoundaryIntegral_finitePrincipalPart_eq
    (Finset.univ : Finset
      (ZetaZeroOccurrenceInHeightSlab R.bottom R.top))
    (fun i : ZetaZeroOccurrenceInHeightSlab R.bottom R.top => i.fst.1)
    (fun _ => (1 : Complex))
    (left := R.left) (right := R.right)
    (bottom := R.bottom) (top := R.top)
    (by
      intro i _hi
      have hxi : entireRiemannXi i.fst.1 = 0 :=
        entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr
          i.fst.2.1
      exact lt_trans hleft (entireRiemannXi_zero_re_mem_Ioo hxi).1)
    (by
      intro i _hi
      have hxi : entireRiemannXi i.fst.1 = 0 :=
        entireRiemannXi_eq_zero_iff_mathlib_nontrivial_zeta_zero.mpr
          i.fst.2.1
      exact lt_trans (entireRiemannXi_zero_re_mem_Ioo hxi).2 hright)
    (by
      intro i _hi
      exact i.fst.2.2.2.1)
    (by
      intro i _hi
      exact lt_of_le_of_ne i.fst.2.2.2.2
        (htopGood i.fst.1 i.fst.2.1))
  rw [zetaSlabPrincipalPart]
  rw [hprincipal]
  congr 1
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [mul_one]
  have hcard :
      Fintype.card (ZetaZeroOccurrenceInHeightSlab R.bottom R.top) =
        zetaWeightedZeroCountInHeightSlab R.bottom R.top := by
    simpa only [Nat.card_eq_fintype_card] using
      natCard_zetaZeroOccurrenceInHeightSlab R.bottom_lt_top.le
  exact_mod_cast hcard

/-- Monotonicity guarantees that the slab increment reconstructs the upper
cumulative count.-/
theorem zetaWeightedZeroCountInHeightSlab_add_lower
    {A B : Real} (hAB : A <= B) :
    zetaWeightedZeroCountInHeightSlab A B +
        zetaWeightedZeroCountUpToHeight A =
      zetaWeightedZeroCountUpToHeight B := by
  unfold zetaWeightedZeroCountInHeightSlab
  exact Nat.sub_add_cancel (zetaWeightedZeroCountUpToHeight_mono hAB)

/-- The exact missing residue identity for a wide, positive, safe zeta
rectangle. Its divisor mass is the independently defined,
multiplicity-weighted positive-ordinate zeta slab increment; the contour side
is Mathlib's fixed rectangle boundary integral.

The geometric fields are part of the proposition so the boundary equality
cannot be reused accidentally for a narrow rectangle, a rectangle crossing
the real axis, or one whose horizontal edges meet a zeta zero.-/
structure ResidueIdentity (R : ZetaRectangle) : Prop where
  left_of_strip : R.left < 0
  right_of_strip : 1 < R.right
  bottom_pos : 0 < R.bottom
  bottom_good : ZetaGoodHeight R.bottom
  top_good : ZetaGoodHeight R.top
  boundary :
    RectangleResidueIdentity zetaLogDeriv
      R.left R.right R.bottom R.top
      (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Int)

/-- A supplied residue identity evaluates the original four parameterized
edges, because the affine/orientation comparison to Mathlib's boundary
expression has already been proved.-/
theorem ResidueIdentity.rectangleLogDerivIntegral_eq
    {R : ZetaRectangle} (H : R.ResidueIdentity) :
    R.rectangleLogDerivIntegral =
      twoPiI *
        (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Complex) := by
  rw [R.rectangleLogDerivIntegral_eq_mathlibBoundary]
  exact H.boundary.boundaryIntegral_eq

/-- The explicit rectangle contribution to a Riemann--von Mangoldt
remainder.  It is fixed by the boundary integral, rather than defined from
the desired upper zero count.-/
noncomputable def rectangleArgumentTerm (R : ZetaRectangle) : Real :=
  (zetaWeightedZeroCountUpToHeight R.bottom : Real) +
    (R.rectangleLogDerivIntegral / twoPiI).re -
    smoothZeroCountingN0 R.top

/-- Once the exact residue identity is supplied, the fixed rectangle
argument term gives the Riemann--von Mangoldt formula at the rectangle's top
height.  Every remaining step is algebra and monotonicity of the independently
defined weighted count.-/
theorem count_eq_smooth_add_rectangleArgumentTerm_of_residueIdentity
    {R : ZetaRectangle} (H : R.ResidueIdentity) :
    (zetaWeightedZeroCountUpToHeight R.top : Real) =
      smoothZeroCountingN0 R.top + R.rectangleArgumentTerm := by
  have hboundary := H.rectangleLogDerivIntegral_eq
  have hquot :
      R.rectangleLogDerivIntegral / twoPiI =
        (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Complex) := by
    rw [hboundary]
    field_simp [twoPiI_ne_zero]
  have hre := congrArg Complex.re hquot
  have hre' :
      (R.rectangleLogDerivIntegral / twoPiI).re =
        (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Real) := by
    simpa using hre
  have hcountNat := zetaWeightedZeroCountInHeightSlab_add_lower
    R.bottom_lt_top.le
  have hcountReal :
      (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Real) +
          (zetaWeightedZeroCountUpToHeight R.bottom : Real) =
        (zetaWeightedZeroCountUpToHeight R.top : Real) := by
    exact_mod_cast hcountNat
  unfold rectangleArgumentTerm
  rw [hre']
  linarith

/-! ## A fixed standard-rectangle formulation at safe heights -/

/-- A family of exact residue identities for the concrete rectangles
`[-1,2] × [A,T]`, at every sufficiently large safe height `T`.  This is the
precise contour theorem still absent from Mathlib.-/
structure ZetaStandardRectangleResidueFormula (A : Real) : Type where
  threshold : Nat
  threshold_ge_two_pi : 2 * Real.pi <= (threshold : Real)
  A_pos : 0 < A
  A_good : ZetaGoodHeight A
  A_lt_threshold : A < (threshold : Real)
  residue :
    ∀ (T : Real) (_hT : (threshold : Real) <= T)
      (hAT : A < T), ZetaGoodHeight T ->
      (standard A T hAT).ResidueIdentity

/-- The concrete standard rectangle selected by a residue-formula package at
height `T`.-/
noncomputable def ZetaStandardRectangleResidueFormula.rectangleAt
    {A : Real} (F : ZetaStandardRectangleResidueFormula A)
    (T : Real) (hT : (F.threshold : Real) <= T) : ZetaRectangle :=
  standard A T (lt_of_lt_of_le F.A_lt_threshold hT)

/-- Every standard rectangle in the family is geometrically admissible at a
safe top height; this part is proved and is not stored as an analytic
hypothesis.-/
theorem ZetaStandardRectangleResidueFormula.rectangleAt_admissible
    {A : Real} (F : ZetaStandardRectangleResidueFormula A)
    {T : Real} (hT : (F.threshold : Real) <= T)
    (hgood : ZetaGoodHeight T) :
    (F.rectangleAt T hT).AdmissibleForZeta := by
  unfold ZetaStandardRectangleResidueFormula.rectangleAt
  exact standard_admissibleForZeta F.A_pos
    (lt_of_lt_of_le F.A_lt_threshold hT) F.A_good hgood

/-- A standard-rectangle residue package proves the exact
Riemann--von Mangoldt decomposition at each safe height, with the argument
term given by the explicit four-edge integral.-/
theorem ZetaStandardRectangleResidueFormula.count_eq_at_good_height
    {A : Real} (F : ZetaStandardRectangleResidueFormula A)
    {T : Real} (hT : (F.threshold : Real) <= T)
    (hgood : ZetaGoodHeight T) :
    (zetaWeightedZeroCountUpToHeight T : Real) =
      smoothZeroCountingN0 T + (F.rectangleAt T hT).rectangleArgumentTerm := by
  let hAT : A < T := lt_of_lt_of_le F.A_lt_threshold hT
  have Hres : (standard A T hAT).ResidueIdentity :=
    F.residue T hT hAT hgood
  simpa [ZetaStandardRectangleResidueFormula.rectangleAt,
    hAT] using
      count_eq_smooth_add_rectangleArgumentTerm_of_residueIdentity Hres

/-- The missing Backlund estimate, now tied to the fixed standard-rectangle
integral rather than to an arbitrary remainder function.-/
structure ZetaStandardRectangleBacklundBound
    {A : Real} (F : ZetaStandardRectangleResidueFormula A) : Type where
  C : Real
  D : Real
  C_nonneg : 0 <= C
  D_nonneg : 0 <= D
  bound :
    ∀ (T : Real) (hT : (F.threshold : Real) <= T),
      ZetaGoodHeight T ->
      |(F.rectangleAt T hT).rectangleArgumentTerm| <=
        C * Real.log T + D

/-- Residue identities plus a Backlund estimate for the same explicit
rectangle term give the expected `O(log T)` counting remainder at safe
heights.  No term is redefined from the desired conclusion.-/
theorem ZetaStandardRectangleBacklundBound.count_sub_smooth_bound_at_good_height
    {A : Real} {F : ZetaStandardRectangleResidueFormula A}
    (B : ZetaStandardRectangleBacklundBound F)
    {T : Real} (hT : (F.threshold : Real) <= T)
    (hgood : ZetaGoodHeight T) :
    |(zetaWeightedZeroCountUpToHeight T : Real) -
        smoothZeroCountingN0 T| <= B.C * Real.log T + B.D := by
  have hformula := F.count_eq_at_good_height hT hgood
  have hbound := B.bound T hT hgood
  rw [hformula]
  simpa using hbound

/-- Rectangle-level argument-principle output for the actual weighted zeta
divisor.  This is intentionally an interface: constructing it requires the
logarithmic-derivative contour integral (or an equivalent winding-number
theorem).  All geometric admissibility and support identification are proved
outside the structure.-/
structure ArgumentPrincipleFormula (R : ZetaRectangle) : Type where
  left_of_strip : R.left < 0
  right_of_strip : 1 < R.right
  bottom_pos : 0 < R.bottom
  bottom_good : ZetaGoodHeight R.bottom
  top_good : ZetaGoodHeight R.top
  argumentIndex : Int
  realizesBoundaryIndex : R.RealizesArgumentIndex argumentIndex
  formula :
    argumentIndex =
      (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Int)

/-- Every rectangle formula carries a proved geometric admissibility
certificate; this is not part of the missing analytic input.-/
theorem ArgumentPrincipleFormula.admissible
    {R : ZetaRectangle} (F : ArgumentPrincipleFormula R) :
    R.AdmissibleForZeta :=
  admissibleForZeta_of_wide_positive_good
    F.left_of_strip F.right_of_strip F.bottom_pos
    F.bottom_good F.top_good

/-- The argument index of a canonical positive-height rectangle formula is
nonnegative because it is exactly a natural multiplicity count.-/
theorem ArgumentPrincipleFormula.argumentIndex_nonneg
    {R : ZetaRectangle} (F : ArgumentPrincipleFormula R) :
  0 <= F.argumentIndex := by
  rw [F.formula]
  exact Int.natCast_nonneg _

/-- The exact residue identity and the already proved geometric hypotheses
construct the older integer-index interface.  The integer is forced to be
the actual slab count; it is not chosen independently.-/
noncomputable def ArgumentPrincipleFormula.ofResidueIdentity
    {R : ZetaRectangle}
    (H : R.ResidueIdentity) :
    ArgumentPrincipleFormula R where
  left_of_strip := H.left_of_strip
  right_of_strip := H.right_of_strip
  bottom_pos := H.bottom_pos
  bottom_good := H.bottom_good
  top_good := H.top_good
  argumentIndex :=
    (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Int)
  realizesBoundaryIndex := H.rectangleLogDerivIntegral_eq
  formula := rfl

/-- Conversely, every legacy argument-principle formula contains a proof of
the exact residue identity.-/
theorem ArgumentPrincipleFormula.toResidueIdentity
    {R : ZetaRectangle} (F : ArgumentPrincipleFormula R) :
    R.ResidueIdentity := by
  refine
    { left_of_strip := F.left_of_strip
      right_of_strip := F.right_of_strip
      bottom_pos := F.bottom_pos
      bottom_good := F.bottom_good
      top_good := F.top_good
      boundary := ?_ }
  unfold RectangleResidueIdentity
  change R.mathlibBoundaryLogDerivIntegral =
    twoPiI *
      (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Complex)
  rw [← R.rectangleLogDerivIntegral_eq_mathlibBoundary]
  calc
    R.rectangleLogDerivIntegral =
        twoPiI * (F.argumentIndex : Complex) := F.realizesBoundaryIndex
    _ = twoPiI *
        (zetaWeightedZeroCountInHeightSlab R.bottom R.top : Complex) := by
      rw [F.formula]
      norm_cast

end ZetaRectangle

/-! ## The global direct-route analytic interface -/

/-- Legacy Riemann--von Mangoldt formula interface for the actual Mathlib zeta
divisor.  This structure alone does *not* tie `argumentTerm` to a contour;
`argumentTerm_eq_count_sub_smooth` below proves that the formula determines it
as the remainder.  Use `ZetaStandardRectangleResidueFormula` when an explicit
four-edge realization is required.-/
structure ZetaRiemannVonMangoldtArgumentFormula : Type where
  argumentTerm : Real -> Real
  threshold : Nat
  threshold_ge_two_pi : 2 * Real.pi <= (threshold : Real)
  formula :
    ∀ T : Real, (threshold : Real) <= T ->
      (zetaWeightedZeroCountUpToHeight T : Real) =
        smoothZeroCountingN0 T + argumentTerm T

/-- A Backlund estimate for the term of a chosen legacy
Riemann--von Mangoldt formula.  The stronger
`ZetaStandardRectangleBacklundBound` is tied to a fixed boundary integral.-/
structure ZetaBacklundArgumentBound
    (F : ZetaRiemannVonMangoldtArgumentFormula) : Type where
  threshold : Nat
  threshold_ge_two_pi : 2 * Real.pi <= (threshold : Real)
  C : Real
  D : Real
  C_nonneg : 0 <= C
  D_nonneg : 0 <= D
  bound :
    ∀ T : Real, (threshold : Real) <= T ->
      |F.argumentTerm T| <= C * Real.log T + D

/-- A Riemann--von Mangoldt formula determines its argument term uniquely:
above its threshold it is exactly the independently defined counting
remainder.  Thus the bare formula structure alone contains no boundary
estimate; an explicit contour realization is genuinely additional work.-/
theorem ZetaRiemannVonMangoldtArgumentFormula.argumentTerm_eq_count_sub_smooth
    (F : ZetaRiemannVonMangoldtArgumentFormula)
    {T : Real} (hT : (F.threshold : Real) <= T) :
    F.argumentTerm T =
      (zetaWeightedZeroCountUpToHeight T : Real) -
        smoothZeroCountingN0 T := by
  rw [F.formula T hT]
  ring

/-- Likewise, a `ZetaBacklundArgumentBound` is precisely an eventual
logarithmic estimate for the actual zero-counting remainder once the formula
is known.-/
theorem ZetaBacklundArgumentBound.count_sub_smooth_bound
    {F : ZetaRiemannVonMangoldtArgumentFormula}
    (B : ZetaBacklundArgumentBound F)
    {T : Real} (hT : (max F.threshold B.threshold : Nat) <= T) :
    |(zetaWeightedZeroCountUpToHeight T : Real) -
        smoothZeroCountingN0 T| <= B.C * Real.log T + B.D := by
  have hF : (F.threshold : Real) <= T :=
    le_trans (by exact_mod_cast Nat.le_max_left F.threshold B.threshold) hT
  have hB : (B.threshold : Real) <= T :=
    le_trans (by exact_mod_cast Nat.le_max_right F.threshold B.threshold) hT
  rw [← F.argumentTerm_eq_count_sub_smooth hF]
  exact B.bound T hB

end OverflowResidueRH
