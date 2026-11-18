import Tengoku.WasowAsymptoticsLean.WasowShearingExceptional
import Tengoku.WasowAsymptoticsLean.WasowSingleEigenBlocks
import Tengoku.WasowAsymptoticsLean.WasowPencilDescent
import Tengoku.WasowAsymptoticsLean.WasowPencilSimilarity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms shearedLeading_single_eigen_mass_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fractional_single_eigen_feedback` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fractional_single_eigen_strict_drop` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_slope_with_pencil_descent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flatten_val` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms prefix_sum_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flatten_block_lt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flatCoefficients_apply` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms jordan_nonzero_flat_adjacent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flat_initial_shape` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms flat_normalized_rows` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shearedLeading_lastRowForm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shearedLeading_lowerBlocks` (it only prints; the queue checks the axioms of every declaration). -/

/-! The actual globally weighted shearing on ordered concatenated blocks.
The flattening is the explicit prefix-sum equivalence, not an arbitrary
enumeration. Wasow (19.12) uses exactly these global positions. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
namespace WasowOrderedShearing
open WasowMultiShiftReduction WasowPencilReduction WasowShearingLeading
open WasowShearingExceptional WasowNilpotentNormalized
variable {s : ℕ}

def flatten (h : Fin s → ℕ) : Index h ≃ Fin (∑ a, (h a+1)) := finSigmaFinEquiv (m := s) (n := fun a => h a+1)

/--
@isnad1 id=eq.0h4v.s8.5a66f3e0fcc4 from=translated src=- shape=55726f6b vocab=f595563b
-/
theorem flatten_val (h : Fin s → ℕ) (a : Fin s) (i : Fin (h a+1)) :
    (flatten h ⟨a,i⟩).val =
      (∑ b : Fin a.val, (h (Fin.castLE a.isLt.le b)+1)) + i.val :=
  finSigmaFinEquiv_apply (n := fun a => h a+1) ⟨a,i⟩

/--
@isnad1 id=le.2h4v.s6.e0bfa7b06d20 from=translated src=- shape=cf6610d3 vocab=b2608c40
-/
theorem prefix_sum_le {k l : ℕ} (hkl : k≤l) (hls : l≤s) (h : Fin s → ℕ) :
    (∑ a : Fin k, h (Fin.castLE (hkl.trans hls) a)) ≤
      ∑ a : Fin l, h (Fin.castLE hls a) := by
  let e : Fin k → Fin l := Fin.castLE hkl
  have hinj : Function.Injective e := Fin.castLE_injective hkl
  have hh : (∑ a : Fin k, h (Fin.castLE (hkl.trans hls) a)) =
      ∑ b ∈ Finset.univ.image e, h (Fin.castLE hls b) := by
    rw [Finset.sum_image (by exact hinj.injOn)]
    rfl
  rw [hh]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/--
@isnad1 id=lt.1h6v.s9.c7bb4aac9c9e from=translated src=- shape=29c646ab vocab=34488c36
-/
theorem flatten_block_lt (h : Fin s → ℕ) (a b : Fin s) (hab : a<b)
    (i : Fin (h a+1)) (j : Fin (h b+1)) : flatten h ⟨a,i⟩ < flatten h ⟨b,j⟩ := by
  have hprefix := prefix_sum_le (show a.val+1≤b.val by omega) b.isLt.le
    (fun c => h c+1)
  rw [Fin.sum_univ_castSucc] at hprefix
  have hlast : Fin.castLE ((show a.val+1≤b.val by omega).trans b.isLt.le)
      (Fin.last a.val) = a := Fin.ext rfl
  rw [hlast] at hprefix
  have hsum : (∑ c : Fin a.val,
      (h (Fin.castLE ((show a.val+1≤b.val by omega).trans b.isLt.le) c.castSucc)+1)) =
      ∑ c : Fin a.val, (h (Fin.castLE a.isLt.le c)+1) := by rfl
  rw [hsum] at hprefix
  change (flatten h ⟨a,i⟩).val < (flatten h ⟨b,j⟩).val
  rw [flatten_val,flatten_val]
  omega

def flatCoefficients (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) :
    ℕ → Matrix (Fin (∑ a, (h a+1))) (Fin (∑ a, (h a+1))) ℂ :=
  fun k => (A k).submatrix (flatten h).symm (flatten h).symm

def shearedLeading (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (σ : ℚ) : Matrix (Index h) (Index h) ℂ :=
  (leadingMatrix (flatCoefficients h A) σ).submatrix (flatten h) (flatten h)

def flatLastRows (h : Fin s → ℕ) : Set (Fin (∑ a, (h a+1))) :=
  {i | ((flatten h).symm i).2.val = h ((flatten h).symm i).1}

/--
@isnad1 id=eq.0h6v.s8.0064a953d512 from=translated src=- shape=0652c11a vocab=afe49a66
-/
theorem flatCoefficients_apply (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (k : ℕ) (i j : Index h) :
    flatCoefficients h A k (flatten h i) (flatten h j)=A k i j := by
  simp [flatCoefficients,Matrix.submatrix]

/--
@isnad1 id=eq.1h4v.s8.fbef629bca0e from=translated src=- shape=e65854d7 vocab=82882a7c
-/
theorem jordan_nonzero_flat_adjacent (h : Fin s → ℕ) (i j : Index h)
    (hne : jordanShift h i j ≠ 0) :
    (flatten h j).val = (flatten h i).val+1 := by
  rcases i with ⟨a,i⟩
  rcases j with ⟨b,j⟩
  by_cases hab : a=b
  · subst b
    have he : j.val=i.val+1 := by
      by_contra hh
      exact hne (by simp [jordanShift,WasowShiftReduction.shift,hh])
    rw [flatten_val,flatten_val,he]
    omega
  · exact False.elim (hne (Matrix.blockDiagonal'_apply_ne _ _ _ hab))

/--
@isnad1 id=eq.2h5v.s7.a432a2269581 from=translated src=- shape=b9b38bcc vocab=dae2ece9
-/
theorem flat_initial_shape (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h) :
    ∀ i j, flatCoefficients h A 0 i j≠0 → j.val=i.val+1 := by
  intro i j hne
  have hh := jordan_nonzero_flat_adjacent h ((flatten h).symm i) ((flatten h).symm j)
    (by simpa only [flatCoefficients,Matrix.submatrix_apply,hA] using hne)
  simpa using hh

/--
@isnad1 id=eq.3h6v.s8.ca747a144a47 from=translated src=- shape=41640f7c vocab=9dea72b7
-/
theorem flat_normalized_rows (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0) :
    ∀ k, 0<k → ∀ i j, i ∉ flatLastRows h → flatCoefficients h A k i j=0 := by
  intro k hk i j hi
  change ((flatten h).symm i).2.val ≠ h ((flatten h).symm i).1 at hi
  have hil : ((flatten h).symm i).2.val < h ((flatten h).symm i).1 := by
    have := ((flatten h).symm i).2.isLt
    omega
  exact hrows k hk ((flatten h).symm i).1 ((flatten h).symm i).2
    ((flatten h).symm j) hil

/-- The zero-weight entries retain exactly the original global shift rows.
@isnad1 id=lastrowf.3h4v.s7.d6b33930507c from=translated src=- shape=9376b7f3 vocab=700cdd35
-/
theorem shearedLeading_lastRowForm (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0)
    {σ : ℚ} (hσ : 0<σ) : LastRowForm h (shearedLeading h A σ) := by
  intro a i j
  have hi : flatten h ⟨a,i.castSucc⟩ ∉ flatLastRows h := by
    change ((flatten h).symm ((flatten h) ⟨a,i.castSucc⟩)).2.val ≠
      h ((flatten h).symm ((flatten h) ⟨a,i.castSucc⟩)).1
    rw [Equiv.symm_apply_apply]
    exact Nat.ne_of_lt i.isLt
  have hh := leadingMatrix_normalized_rows (flatCoefficients h A) (flat_initial_shape h A hA)
    (flatLastRows h) (flat_normalized_rows h A hrows) hσ
    (flatten h ⟨a,i.castSucc⟩) (flatten h j) hi
  change leadingMatrix (flatCoefficients h A) σ
    (flatten h ⟨a,i.castSucc⟩) (flatten h j)=_
  rw [hh,flatCoefficients_apply,hA]
  exact WasowPencilDescent.jordan_lastRowForm h a i j

/-- Later blocks have larger actual shearing weights, so every upper
off-diagonal block vanishes in the new leading matrix.
@isnad1 id=lowerblo.2h4v.s6.6c30b802d37a from=translated src=- shape=8006c3fe vocab=3fbd8a76
-/
theorem shearedLeading_lowerBlocks (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    {σ : ℚ} (hσ : 0<σ) : WasowPencilDescent.LowerBlocks h (shearedLeading h A σ) := by
  intro a b hab i j
  change leadingMatrix (flatCoefficients h A) σ (flatten h ⟨a,i⟩) (flatten h ⟨b,j⟩)=0
  rw [leadingMatrix_above _ (flat_initial_shape h A hA) hσ _ _
    (flatten_block_lt h a b hab i j),flatCoefficients_apply,hA]
  exact Matrix.blockDiagonal'_apply_ne _ _ _ (ne_of_lt hab)

/-- Every single-eigenvalue shearing step has weak mass decrease, including
integer slopes. The matrix shape is proved from the input coefficient sequence.
@isnad1 id=le.4h5v.s9.9aaf30503a15 from=translated src=- shape=a2cac3d3 vocab=f8790632
-/
theorem shearedLeading_single_eigen_mass_le (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0)
    {σ : ℚ} (hσ : 0<σ) (α : ℂ)
    (hN : IsNilpotent (shearedLeading h A σ-α • 1)) :
    WasowPencilDescent.degreeMass (pencil (shearedLeading h A σ)) ≤
      WasowPencilDescent.degreeMass (pencil (jordanShift h)) := by
  apply WasowPencilSimilarity.single_eigen_pencil_mass_le _ α
    (shearedLeading_lastRowForm h A hA hrows hσ) _ hN
  intro u v huv
  exact shearedLeading_lowerBlocks h A hA hσ u.1 v.1 huv u.2 v.2

/-- In the fractional single-eigenvalue branch, actual feedback cannot
stay inside a diagonal block: nilpotence forces every such block to be a shift.
@isnad1 id=and.6h5v.s9.cfa437151158 from=translated src=- shape=80401d7c vocab=53446404
-/
theorem fractional_single_eigen_feedback (h : Fin s → ℕ)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0)
    {σ : ℚ} (hσ : 0<σ) (hfrac : ∀ k : ℕ, σ ≠ k)
    (hfeedback : ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients h A) σ i j ≠ 0)
    (α : ℂ) (hN : IsNilpotent (shearedLeading h A σ-α • 1)) :
    α=0 ∧ WasowPencilDescent.ShiftDiagonal h (shearedLeading h A σ) ∧
      ∃ a b, a ≠ b ∧ ∃ j,
        shearedLeading h A σ ⟨a,Fin.last (h a)⟩ ⟨b,j⟩ ≠ 0 := by
  obtain ⟨i,j,_,hilast,hne⟩ := fractional_feedback_last_row
    (flatCoefficients h A) (flat_initial_shape h A hA) (flatLastRows h)
    (flat_normalized_rows h A hrows) hσ hfrac hfeedback
  let C := shearedLeading h A σ
  have hform : LastRowForm h C := shearedLeading_lastRowForm h A hA hrows hσ
  have hlo : WasowSingleEigenBlocks.LowerBlocks C := by
    intro u v huv
    exact shearedLeading_lowerBlocks h A hA hσ u.1 v.1 huv u.2 v.2
  have htr : C.trace=0 := by
    unfold Matrix.trace
    apply Finset.sum_eq_zero
    intro u _
    exact leadingMatrix_diagonal_zero (flatCoefficients h A) σ hfrac (flatten h u)
  have hncard : (Fintype.card (Index h) : ℂ) ≠ 0 := by
    let : Nonempty (Index h) := ⟨(flatten h).symm i⟩
    exact_mod_cast Fintype.card_ne_zero
  have htrace := (Matrix.isNilpotent_trace_of_isNilpotent hN).eq_zero
  rw [Matrix.trace_sub,Matrix.trace_smul,Matrix.trace_one,htr] at htrace
  have halpha : α=0 := by
    have hm : α*(Fintype.card (Index h) : ℂ)=0 := by
      simpa only [smul_eq_mul,zero_sub,neg_eq_zero] using htrace
    exact (mul_eq_zero.mp hm).resolve_right hncard
  have hnil : IsNilpotent C := by simpa only [halpha,zero_smul,sub_zero] using hN
  have hd : WasowPencilDescent.ShiftDiagonal h C := by
    intro a u v
    have he := nilpotent_normalized_eq_shift (block C a a)
      (WasowSingleEigenBlocks.lastRowForm_diagonal_rows C hform a)
      (WasowSingleEigenBlocks.diagonalBlock_nilpotent C hlo hnil a)
    exact congrFun (congrFun he u) v
  refine ⟨halpha,hd,?_⟩
  let u := (flatten h).symm i
  let v := (flatten h).symm j
  have hlast : u.2=Fin.last (h u.1) := by
    apply Fin.ext
    exact hilast
  have hentry : C ⟨u.1,Fin.last (h u.1)⟩ v ≠ 0 := by
    rw [← hlast]
    change leadingMatrix (flatCoefficients h A) σ (flatten h u) (flatten h v) ≠ 0
    simpa only [u,v,Equiv.apply_symm_apply] using hne
  refine ⟨u.1,v.1,?_,v.2,hentry⟩
  intro he
  have hz : C ⟨u.1,Fin.last (h u.1)⟩ v=0 := by
    rcases v with ⟨b,l⟩
    dsimp only at he
    subst b
    rw [hd]
    have hl : l.val ≠ h u.1+1 := Nat.ne_of_lt l.isLt
    simp [WasowShiftReduction.shift,hl]
  exact hentry hz

/-- Strict decrease of the original full pencil for the actual fractional
single-eigenvalue leading matrix selected by shearing.
@isnad1 id=lt.7h5v.s9.6d42cc6b3f39 from=translated src=- shape=e7000f36 vocab=3fcbfd3f
-/
theorem fractional_single_eigen_strict_drop (h : Fin s → ℕ) (hh : Monotone h)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0)
    {σ : ℚ} (hσ : 0<σ) (hfrac : ∀ k : ℕ, σ ≠ k)
    (hfeedback : ∃ i j, j ≤ i ∧ leadingMatrix (flatCoefficients h A) σ i j ≠ 0)
    (α : ℂ) (hN : IsNilpotent (shearedLeading h A σ-α • 1)) :
    WasowPencilDescent.degreeMass (pencil (shearedLeading h A σ)) <
      WasowPencilDescent.degreeMass (pencil (jordanShift h)) := by
  obtain ⟨_,hd,hfb⟩ := fractional_single_eigen_feedback h A hA hrows hσ hfrac hfeedback α hN
  exact WasowPencilDescent.pencil_degreeMass_strict_drop hh
    (shearedLeading_lastRowForm h A hA hrows hσ)
    (shearedLeading_lowerBlocks h A hA hσ) hd hfb

/-- Slope selection and the actual ordered-block matrix together supply
the strict branch; no invariant-decrease hypothesis is accepted by this theorem.
@isnad1 id=ex.3h4v.s9.5e5366b36da4 from=translated src=- shape=22d90114 vocab=adefb857
-/
theorem exists_slope_with_pencil_descent (h : Fin s → ℕ) (hh : Monotone h)
    (A : ℕ → Matrix (Index h) (Index h) ℂ) (hA : A 0=jordanShift h)
    (hrows : ∀ k, 0<k → ∀ a (i : Fin (h a+1)) j, i.val<h a → A k ⟨a,i⟩ j=0)
    (q : ℕ) :
    ∃ σ : ℚ, 0<σ ∧ σ ≤ (q+1 : ℕ) ∧
      (∀ k i j, flatCoefficients h A k i j ≠ 0 → 0 ≤ weightedDegree σ k i j) ∧
      LastRowForm h (shearedLeading h A σ) ∧
      WasowPencilDescent.LowerBlocks h (shearedLeading h A σ) ∧
      ((∃ m : ℕ, σ=m) ∨ (σ < (q+1 : ℕ) ∧
        ∀ α : ℂ, IsNilpotent (shearedLeading h A σ-α • 1) →
          WasowPencilDescent.degreeMass (pencil (shearedLeading h A σ)) <
            WasowPencilDescent.degreeMass (pencil (jordanShift h)))) := by
  classical
  obtain ⟨σ,hσ,hcap,hbound,hfb⟩ := exists_slope_with_leading_feedback
    (flatCoefficients h A) q (flat_initial_shape h A hA)
  refine ⟨σ,hσ,hcap,hbound,shearedLeading_lastRowForm h A hA hrows hσ,
    shearedLeading_lowerBlocks h A hA hσ,?_⟩
  by_cases hint : ∃ m : ℕ, σ=m
  · exact Or.inl hint
  · have hfrac : ∀ k : ℕ, σ ≠ k := by simpa only [not_exists] using hint
    have hnecap := hfrac (q+1)
    refine Or.inr ⟨lt_of_le_of_ne hcap hnecap,?_⟩
    intro α hN
    exact fractional_single_eigen_strict_drop h hh A hA hrows hσ hfrac
      (hfb.resolve_left hnecap) α hN

end WasowOrderedShearing
