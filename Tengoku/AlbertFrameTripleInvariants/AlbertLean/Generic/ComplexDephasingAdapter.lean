import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexMatrixDephasing
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ComplexPairRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms det_dephase_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms dephase_eq_dephased` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms legal_of_all_overlap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms dephase_inverseTranspose_entry22` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms td_eq_dualRoot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms dephased_pair_matrix_classification` (it only prints; the queue checks the axioms of every declaration). -/

/-! Source-only structural dephasing and legal-chart adapter. No import of
ComplexTransposePair or its rational overlap calculations. -/
noncomputable section
namespace AlbertLean.Generic.ComplexDephasingAdapter
open C1Coordinates ComplexPairPolynomial ComplexDephasedPair
open ComplexPairRoots ComplexMatrixDephasing
variable {K : Type*} [Field K]

/--
@isnad1 id=ne.3h2v.s7.d9b87cfe829c from=translated src=- shape=22309060 vocab=ec986ef2
-/
theorem det_dephase_ne_zero (X : Mat3 K) (hdet : X.det ≠ 0)
    (hrow : ∀ j, X 0 j ≠ 0) (hcol : ∀ i, X i 0 ≠ 0) :
    (dephase X).det ≠ 0 := by
  rw [dephase_eq_diagonal_mul, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_diagonal, Matrix.det_diagonal]
  apply mul_ne_zero
  · apply mul_ne_zero
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact div_ne_zero (hrow 0) (hcol i)
    · exact hdet
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact inv_ne_zero (hrow i)

/--
@isnad1 id=eq.2h2v.s7.585bf6183c4d from=translated src=- shape=c5b73525 vocab=c2817d35
-/
theorem dephase_eq_dephased (X : Mat3 K)
    (hrow : ∀ j, X 0 j ≠ 0) (hcol : ∀ i, X i 0 ≠ 0) :
    dephase X = dephased (dephase X 1 1) (dephase X 1 2)
      (dephase X 2 1) (dephase X 2 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dephased, Matrix.cons_val_two,
      dephase_first_row X (hrow 0) hrow, dephase_first_col X (hrow 0) hcol]

/--
@isnad1 id=eq.1h3v.s6.b9695b527ff0 from=translated src=- shape=5ca4ad89 vocab=7b4b4db9
-/
theorem overlap_row_sum (X : Mat3 K) (hdet : X.det ≠ 0) (i : Fin 3) :
    ∑ j, overlapOf X i j = 1 := by
  have h := congrFun (congrFun
    (Matrix.mul_nonsing_inv X (isUnit_iff_ne_zero.mpr hdet)) i) i
  simpa [overlapOf, Matrix.mul_apply] using h

/--
@isnad1 id=eq.1h3v.s6.5fb927a343d4 from=translated src=- shape=03efd5ef vocab=7b4b4db9
-/
theorem overlap_col_sum (X : Mat3 K) (hdet : X.det ≠ 0) (j : Fin 3) :
    ∑ i, overlapOf X i j = 1 := by
  have h := congrFun (congrFun
    (Matrix.nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hdet)) j) j
  simpa [overlapOf, Matrix.mul_apply, mul_comm] using h

/--
@isnad1 id=eq.1h2v.s7.0e4af8dc6506 from=translated src=- shape=a3c6ad52 vocab=a1495daa
-/
theorem A2_eq_opposite_overlap_product (X : Mat3 K) (hdet : X.det ≠ 0) :
    A2 (overlapOf X 0 0) (overlapOf X 0 1) (overlapOf X 1 0) =
      overlapOf X 0 2 * overlapOf X 2 0 := by
  have hr := overlap_row_sum X hdet 0
  have hc := overlap_col_sum X hdet 0
  simp [Fin.sum_univ_succ] at hr hc
  unfold A2
  rw [show 1-overlapOf X 0 0-overlapOf X 0 1 = overlapOf X 0 2 by
        linear_combination -hr,
      show 1-overlapOf X 0 0-overlapOf X 1 0 = overlapOf X 2 0 by
        linear_combination -hc]

/--
@isnad1 id=ne.1h4v.s7.4689255e1643 from=translated src=- shape=e9494c5d vocab=e5ba1b4d
-/
theorem inverseTranspose_entries (X : Mat3 K)
    (hopen : ∀ i j, overlapOf X i j ≠ 0) :
    ∀ i j, Matrix.transpose X⁻¹ i j ≠ 0 := by
  intro i j
  exact (entries_ne_zero_of_overlap_ne_zero X hopen).2 i j

/--
@isnad1 id=and.2h2v.s8.c19b77958caa from=translated src=- shape=f37fdb87 vocab=4d8edcb3
-/
theorem transpose_dephase_data (X : Mat3 K) (hdet : X.det ≠ 0)
    (hopen : ∀ i j, overlapOf X i j ≠ 0) :
    (dephase (Matrix.transpose X⁻¹)).det ≠ 0 ∧
      (∀ i j, overlapOf (dephase (Matrix.transpose X⁻¹)) i j = overlapOf X i j) ∧
      (∀ i j, overlapOf (dephase (Matrix.transpose X⁻¹)) i j ≠ 0) := by
  have hentry := inverseTranspose_entries X hopen
  have hdetT : (Matrix.transpose X⁻¹).det ≠ 0 := by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact inv_ne_zero hdet
  have hover (i j : Fin 3) :
      overlapOf (dephase (Matrix.transpose X⁻¹)) i j = overlapOf X i j := by
    rw [overlap_dephase _ hentry hdetT, overlap_inverseTranspose X hdet]
  exact ⟨det_dephase_ne_zero _ hdetT (hentry 0) (fun i => hentry i 0),
    hover, fun i j => (hover i j).symm ▸ hopen i j⟩

structure Legal (a b c d : K) : Prop where
  delta_ne_zero : delta a b c d ≠ 0
  d_ne_zero : d ≠ 0
  d_sub_one_ne_zero : d-1 ≠ 0
  nu_ne_zero : nu (overlap a b c d 0 0) (overlap a b c d 0 1)
    (overlap a b c d 1 0) (overlap a b c d 1 1) d ≠ 0
  A2_ne_zero : A2 (overlap a b c d 0 0) (overlap a b c d 0 1)
    (overlap a b c d 1 0) ≠ 0
  c_sub_d_ne_zero : c-d ≠ 0
  b_sub_d_ne_zero : b-d ≠ 0
  c_sub_a_ne_zero : c-a ≠ 0
  b_sub_a_ne_zero : b-a ≠ 0

/--
@isnad1 id=legal.2h5v.s6.eea3e5606a67 from=translated src=- shape=be75338e vocab=9bc5043d
-/
theorem legal_of_all_overlap (a b c d : K) (hΔ : delta a b c d ≠ 0)
    (hopen : ∀ i j, overlap a b c d i j ≠ 0) : Legal a b c d := by
  have ht := overlap_table a b c d hΔ
  have hn (x y : K) (h : x/y ≠ 0) : x ≠ 0 := by
    intro hx
    exact h (by simp only [hx, zero_div])
  have hd : d ≠ 0 := by
    have hz := hopen 2 2
    rw [show overlap a b c d 2 2 = d*(a-1)/delta a b c d by
      simpa [Matrix.cons_val_two] using congrFun (congrFun ht 2) 2] at hz
    exact (mul_ne_zero_iff.mp (hn _ _ hz)).1
  have hd1 : d-1 ≠ 0 := by
    have hz := hopen 1 1
    rw [show overlap a b c d 1 1 = a*(d-1)/delta a b c d by
      simpa using congrFun (congrFun ht 1) 1] at hz
    exact (mul_ne_zero_iff.mp (hn _ _ hz)).2
  have hnu : nu (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d ≠ 0 := by
    have hh := nu_mul_delta a b c d hΔ
    have hz : nu (overlap a b c d 0 0) (overlap a b c d 0 1)
        (overlap a b c d 1 0) (overlap a b c d 1 1) d * delta a b c d ≠ 0 := by
      rw [hh]
      exact mul_ne_zero hd hd1
    exact (mul_ne_zero_iff.mp hz).1
  have hA2 : A2 (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) ≠ 0 := by
    have hh := A2_eq_opposite_overlap_product (dephased a b c d)
      (by simpa only [det_dephased] using hΔ)
    change A2 (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) = overlap a b c d 0 2 * overlap a b c d 2 0 at hh
    rw [hh]
    exact mul_ne_zero (hopen 0 2) (hopen 2 0)
  refine ⟨hΔ, hd, hd1, hnu, hA2, ?_, ?_, ?_, ?_⟩
  · have hz := hopen 1 0
    rw [show overlap a b c d 1 0 = (c-d)/delta a b c d by
      simpa using congrFun (congrFun ht 1) 0] at hz
    exact hn _ _ hz
  · have hz := hopen 0 1
    rw [show overlap a b c d 0 1 = (b-d)/delta a b c d by
      simpa using congrFun (congrFun ht 0) 1] at hz
    exact hn _ _ hz
  · have hz := hopen 0 2
    rw [show overlap a b c d 0 2 = (c-a)/delta a b c d by
      simpa [Matrix.cons_val_two] using congrFun (congrFun ht 0) 2] at hz
    exact hn _ _ hz
  · have hz := hopen 2 0
    rw [show overlap a b c d 2 0 = (b-a)/delta a b c d by
      simpa [Matrix.cons_val_two] using congrFun (congrFun ht 2) 0] at hz
    exact hn _ _ hz

/--
@isnad1 id=eq.3h5v.s7.e07abb2b42c6 from=translated src=- shape=6e756eeb vocab=8a2fa58a
-/
theorem dephase_inverseTranspose_entry22 (a b c d : K)
    (hΔ : delta a b c d ≠ 0) (hba : b-a ≠ 0) (hca : c-a ≠ 0) :
    dephase (Matrix.transpose (dephased a b c d)⁻¹) 2 2 = td a b c d := by
  rw [dephased_inv_eq a b c d hΔ]
  change ((delta a b c d)⁻¹ * (a*d-b*c)) * ((delta a b c d)⁻¹ * (a-1)) /
    (((delta a b c d)⁻¹ * (b-a)) * ((delta a b c d)⁻¹ * (c-a))) = td a b c d
  unfold td
  field_simp [hΔ, hba, hca]

/-- Only this scalar Vieta computation is retained; nine rational overlap
identities are replaced by structural overlap invariance.
@isnad1 id=eq.1h5v.s7.1208433060e7 from=translated src=- shape=3ea1424f vocab=738d73eb
-/
theorem td_eq_dualRoot (a b c d : K) (h : Legal a b c d) :
    td a b c d = dualRoot (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d := by
  have ht := overlap_table a b c d h.delta_ne_zero
  have hp := congrFun (congrFun ht 0) 0
  have hq := congrFun (congrFun ht 0) 1
  have hr := congrFun (congrFun ht 1) 0
  have hs := congrFun (congrFun ht 1) 1
  have h22 := congrFun (congrFun ht 2) 2
  have h02 := congrFun (congrFun ht 0) 2
  have h20 := congrFun (congrFun ht 2) 0
  change overlap a b c d 0 0 = (a*d-b*c) / delta a b c d at hp
  change overlap a b c d 0 1 = (b-d) / delta a b c d at hq
  change overlap a b c d 1 0 = (c-d) / delta a b c d at hr
  change overlap a b c d 1 1 = a*(d-1) / delta a b c d at hs
  change overlap a b c d 2 2 = d*(a-1) / delta a b c d at h22
  change overlap a b c d 0 2 = (c-a) / delta a b c d at h02
  change overlap a b c d 2 0 = (b-a) / delta a b c d at h20
  have htheta : overlap a b c d 0 0 + overlap a b c d 0 1 +
      overlap a b c d 1 0 + overlap a b c d 1 1 - 1 = overlap a b c d 2 2 := by
    rw [hp, hq, hr, hs, h22]
    field_simp [h.delta_ne_zero]
    unfold delta
    ring
  have hlead := A2_eq_opposite_overlap_product (dephased a b c d)
    (by simpa only [det_dephased] using h.delta_ne_zero)
  change A2 (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) = overlap a b c d 0 2 * overlap a b c d 2 0 at hlead
  rw [dualRoot, A0, htheta, hlead, hp, h22, h02, h20]
  unfold td
  field_simp [h.delta_ne_zero, h.d_ne_zero, h.b_sub_a_ne_zero, h.c_sub_a_ne_zero]

/-- Actual matrix classification, with all legality of the transpose branch
derived from structural dephasing. Only the initial invertibilities and a
single all-nine overlap open are assumptions.
@isnad1 id=or.4h9v.s7.da02fcfa5148 from=translated src=- shape=189ca594 vocab=6a284bc4
-/
theorem dephased_pair_matrix_classification
    (a b c d a' b' c' d' : K)
    (hΔ : delta a b c d ≠ 0) (hΔ' : delta a' b' c' d' ≠ 0)
    (hopen : ∀ i j, overlap a b c d i j ≠ 0)
    (hover : ∀ i j, overlap a' b' c' d' i j = overlap a b c d i j) :
    dephased a' b' c' d' = dephased a b c d ∨
      dephased a' b' c' d' = dephase (Matrix.transpose (dephased a b c d)⁻¹) := by
  have hopen' : ∀ i j, overlap a' b' c' d' i j ≠ 0 := by
    intro i j
    rw [hover i j]
    exact hopen i j
  have h := legal_of_all_overlap a b c d hΔ hopen
  have h' := legal_of_all_overlap a' b' c' d' hΔ' hopen'
  have hdet : (dephased a b c d).det ≠ 0 := by
    simpa only [det_dephased] using hΔ
  have hdata := transpose_dephase_data (dephased a b c d) hdet hopen
  have hentry := inverseTranspose_entries (dephased a b c d) hopen
  let T := dephase (Matrix.transpose (dephased a b c d)⁻¹)
  let aT := T 1 1
  let bt := T 1 2
  let ct := T 2 1
  let dt := T 2 2
  have hT : T = dephased aT bt ct dt :=
    dephase_eq_dephased _ (hentry 0) (fun i => hentry i 0)
  have hΔT : delta aT bt ct dt ≠ 0 := by
    rw [← det_dephased, ← hT]
    exact hdata.1
  have hoverT : ∀ i j, overlap aT bt ct dt i j = overlap a b c d i j := by
    intro i j
    change overlapOf (dephased aT bt ct dt) i j = overlapOf (dephased a b c d) i j
    rw [← hT]
    exact hdata.2.1 i j
  have hopenT : ∀ i j, overlap aT bt ct dt i j ≠ 0 := by
    intro i j
    rw [hoverT i j]
    exact hopen i j
  have ht := legal_of_all_overlap aT bt ct dt hΔT hopenT
  have hdt : dt = dualRoot (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d :=
    (dephase_inverseTranspose_entry22 a b c d hΔ
      h.b_sub_a_ne_zero h.c_sub_a_ne_zero).trans (td_eq_dualRoot a b c d h)
  have hQ' : pairQuadratic (overlap a b c d 0 0) (overlap a b c d 0 1)
      (overlap a b c d 1 0) (overlap a b c d 1 1) d' = 0 := by
    simpa only [hover] using pairQuadratic_root a' b' c' d' hΔ'
  rcases roots_eq_or_eq_dual _ _ _ _ d d' h.A2_ne_zero h.d_ne_zero
      (pairQuadratic_root a b c d hΔ) hQ' with hd | hd
  · exact Or.inl (dephased_eq_of_overlap_of_d_eq a b c d a' b' c' d'
      hΔ hΔ' h.nu_ne_zero h'.nu_ne_zero hover hd)
  · right
    apply Eq.trans ?_ hT.symm
    apply dephased_eq_of_overlap_of_d_eq aT bt ct dt a' b' c' d'
      hΔT hΔ' ht.nu_ne_zero h'.nu_ne_zero
    · intro i j
      exact (hover i j).trans (hoverT i j).symm
    · exact hd.trans hdt.symm

end AlbertLean.Generic.ComplexDephasingAdapter
