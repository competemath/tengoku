import Tengoku.Nlalib.NLAlib.Probability.Free.WordWickUltracontractivity
import Tengoku.Seed.Algebra.FreeAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Scalar noncommutative polynomial ultracontractivity for actual word fields

Multiplication of a Wick word by a field creates its initial letter and
contracts at most its initial letter. Consequently every genuine ordinary
word of length at most `k` belongs to the actual degree-`k` Wick span. This
derives the scalar source estimate for native free-algebra evaluation, with
degree expressed by the support of its canonical free-monoid coefficients.

Source: Lemma 4.5 of arXiv:2406.11453v2. Neither a Wick expansion nor an
operator-norm comparison is assumed.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical

namespace NLAlib

variable {ι : Type*}
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W

/-- Every actual Wick word is in the actual degree span up to its length.
@isnad1 id=mem.1h3v.s14.b08e3469fd30 from=translated src=- shape=7d7587d1 vocab=d236f0f1
-/
theorem wordWickOperator_mem_wordWickDegreeSpan (w : List ι) {k : ℕ}
    (hlen : w.length ≤ k) : wordWickOperator w ∈ wordWickDegreeSpan (ι := ι) k := by
  apply Submodule.subset_span
  exact ⟨⟨⟨w.length, Nat.lt_succ_of_le hlen⟩, ⟨w, rfl⟩⟩, rfl⟩

/-- Genuine degree spans are nested.
@isnad1 id=le.1h3v.s14.de622401ea6a from=translated src=- shape=bcdafc09 vocab=d8eaea14
-/
theorem wordWickDegreeSpan_mono {j k : ℕ} (hjk : j ≤ k) :
    wordWickDegreeSpan (ι := ι) j ≤ wordWickDegreeSpan (ι := ι) k := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨m, w⟩, rfl⟩
  apply wordWickOperator_mem_wordWickDegreeSpan
  have hw : w.toList.length = (m : ℕ) := by simp
  rw [hw]
  exact (Nat.le_of_lt_succ m.isLt).trans hjk

/-- The actual field times a nonempty Wick word has precisely one possible
initial-letter contraction. This is a literal operator identity.
@isnad1 id=eq.0h4v.s14.c54a21beaf72 from=translated src=- shape=0f5c0cb2 vocab=634fd31e
-/
theorem wordField_mul_wordWickOperator_cons (i j : ι) (w : List ι) :
    wordField i * wordWickOperator (j :: w) =
      wordWickOperator (i :: j :: w) + if i = j then wordWickOperator w else 0 := by
  change wordField i * wordWickOperator (j :: w) =
    (wordField i * wordWickOperator (j :: w) -
      if i = j then wordWickOperator w else 0) +
        if i = j then wordWickOperator w else 0
  exact (sub_add_cancel _ _).symm

private theorem wordField_mul_wordWickOperator_mem (i : ι) (w : List ι) :
    wordField i * wordWickOperator w ∈ wordWickDegreeSpan (ι := ι) (w.length + 1) := by
  cases w with
  | nil =>
    simpa only [wordWickOperator, mul_one, List.length_nil, zero_add] using
      (wordWickOperator_mem_wordWickDegreeSpan [i] (by simp : [i].length ≤ 1))
  | cons j w =>
    rw [wordField_mul_wordWickOperator_cons]
    apply Submodule.add_mem
    · exact wordWickOperator_mem_wordWickDegreeSpan _ (by simp)
    · by_cases hij : i = j
      · rw [ite_eq_left hij]
        exact wordWickOperator_mem_wordWickDegreeSpan _ (by simp; omega)
      · rw [ite_eq_right hij]
        exact Submodule.zero_mem _

/-- Multiplication by an actual field raises genuine Wick degree by at
most one. This conclusion is proved from the literal contraction identity.
@isnad1 id=mem.1h4v.s15.fc13e838ac80 from=translated src=- shape=61b07760 vocab=567b1b33
-/
theorem wordField_mul_mem_wordWickDegreeSpan (i : ι) {k : ℕ} {T : B}
    (hT : T ∈ wordWickDegreeSpan (ι := ι) k) :
    wordField i * T ∈ wordWickDegreeSpan (ι := ι) (k + 1) := by
  let L : B →ₗ[ℂ] B :=
    { toFun := fun T => wordField i * T
      map_add' := fun _ _ => mul_add _ _ _
      map_smul' := fun _ _ => mul_smul_comm _ _ _ }
  have hspan : wordWickDegreeSpan (ι := ι) k ≤
      (wordWickDegreeSpan (ι := ι) (k + 1)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨m, w⟩, rfl⟩
    change wordField i * wordWickOperator w.toList ∈ wordWickDegreeSpan (ι := ι) (k + 1)
    apply wordWickDegreeSpan_mono (k := k + 1) _ (wordField_mul_wordWickOperator_mem i w.toList)
    have hw : w.toList.length = (m : ℕ) := by simp
    rw [hw]
    exact Nat.succ_le_succ (Nat.le_of_lt_succ m.isLt)
  exact hspan hT

/-- An actual ordered product of fields has genuine Wick degree at most
its number of factors. No expansion or norm conclusion is a premise.
@isnad1 id=mem.0h2v.s14.7d552925bf08 from=translated src=- shape=9bbcd85e vocab=796f874c
-/
theorem list_prod_wordField_mem_wordWickDegreeSpan (w : List ι) :
    (w.map wordField).prod ∈ wordWickDegreeSpan (ι := ι) w.length := by
  induction w with
  | nil =>
    simpa only [List.map_nil, List.prod_nil, List.length_nil, wordWickOperator] using
      (wordWickOperator_mem_wordWickDegreeSpan ([] : List ι)
        (by simp : ([] : List ι).length ≤ 0))
  | cons i w hw =>
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.succ_eq_add_one] using
      wordField_mul_mem_wordWickDegreeSpan i hw

/-- Actual finite word-polynomial evaluation obeys the source scalar
ultracontractive estimate, with degree read from the genuine finite support.
@isnad1 id=le.1h3v.s15.cc9ad72402ec from=translated src=- shape=9c5e05d3 vocab=e38bb5e8
-/
theorem norm_finsupp_sum_list_prod_wordField_le [Fintype ι] (k : ℕ)
    (a : List ι →₀ ℂ) (hdeg : ∀ w ∈ a.support, w.length ≤ k) :
    ‖a.sum (fun w z => z • (w.map wordField).prod)‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(a.sum (fun w z => z • (w.map wordField).prod)) (wordVacuum ι)‖ := by
  apply norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordWickDegreeSpan_mono (hdeg w hw) (list_prod_wordField_mem_wordWickDegreeSpan w)

/-- Native free-monoid algebra evaluation has the scalar degree-dependent
bound, with its actual canonical finite coefficient support.
@isnad1 id=le.1h3v.s18.3789f47f1ae1 from=translated src=- shape=136d423f vocab=00bcfa92
-/
theorem norm_monoidAlgebra_lift_wordField_le [Fintype ι] (k : ℕ)
    (P : MonoidAlgebra ℂ (FreeMonoid ι))
    (hdeg : ∀ w ∈ P.coeff.support, w.toList.length ≤ k) :
    ‖MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField) P‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField) P) (wordVacuum ι)‖ := by
  simp only [MonoidAlgebra.lift_apply, FreeMonoid.lift_apply]
  apply norm_le_mul_sqrt_vacuum_of_mem_wordWickDegreeSpan
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  exact wordWickDegreeSpan_mono (hdeg w hw) (list_prod_wordField_mem_wordWickDegreeSpan w.toList)

/-- Genuine native free-algebra evaluation satisfies the scalar source
degree-`k` ultracontractive estimate. The degree premise is exactly a bound
on the lengths in the canonical free-monoid coefficient support.
@isnad1 id=le.1h3v.s16.1245aee3d2d5 from=translated src=- shape=79aa671e vocab=125ebc19
-/
theorem norm_freeAlgebra_lift_wordField_le [Fintype ι] (k : ℕ) (P : FreeAlgebra ℂ ι)
    (hdeg : ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι) P).coeff.support,
      w.toList.length ≤ k) :
    ‖FreeAlgebra.lift ℂ (wordField : ι → B) P‖ ≤
      (k + 1 : ℝ) * Real.sqrt (k + 1) *
        ‖(FreeAlgebra.lift ℂ (wordField : ι → B) P) (wordVacuum ι)‖ := by
  have hEval : FreeAlgebra.lift ℂ (wordField : ι → B) =
      (MonoidAlgebra.lift ℂ B (FreeMonoid ι) (FreeMonoid.lift wordField)).comp
        (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℂ) (X := ι)).toAlgHom := by
    ext i
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hEval, AlgHom.comp_apply]
  exact norm_monoidAlgebra_lift_wordField_le k _ hdeg

end NLAlib
