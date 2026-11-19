import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.KrauseLaceyQuadraticSmoothProjection

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Arithmetic for the seven separated frequency classes

The direct quadratic proof separates integer output scales into seven
residue classes.  In each class, imposing a lower scale cutoff selects an
ordinary suffix of the natural-number index.  This file records that exact
finite identity independently of the analytic estimates.
-/

namespace QuadraticCarleson.KrauseLaceyQuadraticResidueArithmetic

open KrauseLaceyQuadraticSmoothProjection

set_option autoImplicit false

/-- The first index in residue class `r mod 7` whose scale is at least `q`.
The numerator is nonnegative because `r ≤ 6`.-/
def firstResidueIndex (r : Fin 7) (q : ℕ) : ℕ :=
  (q + 6 - (r : ℕ)) / 7

/--
@isnad1 id=iff.0h3v.s4.0295230a67bc from=translated src=- shape=763286b3 vocab=413970a9
-/
theorem firstResidueIndex_le_iff
    (r : Fin 7) (q n : ℕ) :
    firstResidueIndex r q ≤ n ↔
      (q : ℤ) ≤ residueScale r n := by
  unfold firstResidueIndex residueScale
  have hr : (r : ℕ) ≤ 6 := Nat.le_pred_of_lt r.isLt
  omega

/-- A lower scale cutoff inside one residue class is literally a finite
interval of natural indices.
@isnad1 id=eq.0h3v.s5.96aae35189d6 from=translated src=- shape=3785ce82 vocab=5b656979
-/
theorem range_filter_residueScale_ge
    (r : Fin 7) (q N : ℕ) :
    (Finset.range N).filter (fun n ↦ (q : ℤ) ≤ residueScale r n) =
      Finset.Ico (firstResidueIndex r q) N := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
  rw [← firstResidueIndex_le_iff]
  tauto

/-- Hence every truncated sum in a fixed residue class is one of the
ordinary suffixes used by the annular maximal-tail theorem.
@isnad1 id=eq.0h5v.s6.55d433268ed4 from=translated src=- shape=30dc7661 vocab=540fc716
-/
theorem sum_filter_residueScale_ge_eq_Ico
    {E : Type*} [AddCommMonoid E] (u : ℕ → E)
    (r : Fin 7) (q N : ℕ) :
    ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n =
      ∑ n ∈ Finset.Ico (firstResidueIndex r q) N, u n := by
  rw [range_filter_residueScale_ge]

/-- The cutoff sum is therefore represented by a tail whose starting index
always lies in `0, ..., N`, including the empty-tail case.
@isnad1 id=eq.0h5v.s6.cc1af61d3147 from=translated src=- shape=c0f759a5 vocab=a11c96f6
-/
theorem sum_filter_residueScale_ge_eq_finitePieceTail
    (u : ℕ → ℝ → ℂ) (r : Fin 7) (q N : ℕ) (x : ℝ) :
    ∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n x =
      KrauseLaceyQuadraticAnnularTail.finitePieceTail N u
        (min (firstResidueIndex r q) N) x := by
  rw [KrauseLaceyQuadraticAnnularTail.finitePieceTail_eq_sum_Ico
    (min_le_right _ _)]
  rw [sum_filter_residueScale_ge_eq_Ico]
  by_cases h : firstResidueIndex r q ≤ N
  · rw [min_eq_left h]
  · have hN : N ≤ firstResidueIndex r q := Nat.le_of_not_ge h
    rw [min_eq_right hN]
    simp only [Finset.Ico_eq_empty (not_lt_of_ge hN), Finset.sum_empty,
      Finset.Ico_self]

/-- Each residue-class cutoff is pointwise bounded by the corresponding
finite annular tail maximum.
@isnad1 id=le.0h5v.s6.efd5a7cf8818 from=translated src=- shape=e3753798 vocab=80fb3df9
-/
theorem enorm_sum_filter_residueScale_ge_le_tailMax
    (u : ℕ → ℝ → ℂ) (r : Fin 7) (q N : ℕ) (x : ℝ) :
    ‖∑ n ∈ (Finset.range N).filter
        (fun n ↦ (q : ℤ) ≤ residueScale r n), u n x‖ₑ ≤
      KrauseLaceyQuadraticAnnularTail.finitePieceTailMax N u x := by
  rw [sum_filter_residueScale_ge_eq_finitePieceTail]
  unfold KrauseLaceyQuadraticAnnularTail.finitePieceTailMax
  exact Finset.le_sup
    (s := Finset.range (N + 1))
    (f := fun n ↦ ‖KrauseLaceyQuadraticAnnularTail.finitePieceTail N u n x‖ₑ)
    (by
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le (min_le_right _ _))

end QuadraticCarleson.KrauseLaceyQuadraticResidueArithmetic
