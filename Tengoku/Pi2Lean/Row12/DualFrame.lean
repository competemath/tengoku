import Tengoku.Pi2Lean.Row12.NativeSeries
import Tengoku.Pi2Lean.Row12.Residue
import Tengoku.Seed.Analysis.Calculus.Deriv.Prod
import Tengoku.Seed.LinearAlgebra.Matrix.Notation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms Row12.dual_state_matrix_entry_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.native_solution_metric_entry_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_contact_matrix` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_frame_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.native_solution_metric_identity` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_hasDerivAt_div` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.nativeEuler_three_div` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.native_state_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.native_state_derivative_connection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_hasDerivAt_product` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_derivative_connection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_hasDerivAt` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms Row12.dual_state_deriv` (it only prints; the queue checks the axioms of every declaration). -/

namespace Row12

section DualFrame

variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def nativeEulerConnection (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![0, 1, 0; 0, 0, 1;
    5*q/(72*(1-q)), 23*q/(36*(1-q)), 3*q/(2*(1-q))]

noncomputable def ordinarySymmetricConnection (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  let p := (1-(3/2)*q)/(q*(1-q))
  let c := 5/(144*q*(1-q))
  !![0, 1, 0; 2*c, -p, 2; 0, c, -2*p]

noncomputable def dualStateMatrix (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![(-5/72)*q, 0, 2*q^2*(1-q); (-1/2)*q, q*(q-1), 0; 1-q, 0, 0]

noncomputable def dualStateMatrixDerivative (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![-5/72, 0, 4*q-6*q^2; -1/2, 2*q-1, 0; -1, 0, 0]

noncomputable def nativeSolutionMetric (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![(-5/36)*q, (-1/2)*q, 1-q; (-1/2)*q, q-1, 0; 1-q, 0, 0]

noncomputable def nativeSolutionMetricDerivative : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![-5/36, -1/2, -1; -1/2, 1, 0; -1, 0, 0]

noncomputable def dualStateEntryDerivative (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  fun i j => deriv (fun z : 𝕜 => dualStateMatrix z i j) q

noncomputable def nativeMetricEntryDerivative (q : 𝕜) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  fun i j => deriv (fun z : 𝕜 => nativeSolutionMetric z i j) q

/--
@isnad1 id=hasderiv.0h4v.s6.4a9a1111fe5a from=translated src=- shape=6ace6c94 vocab=ad462b52
-/
theorem dual_state_matrix_entry_hasDerivAt (q : 𝕜) (i j : Fin 3) :
    HasDerivAt (fun z : 𝕜 => dualStateMatrix z i j)
      (dualStateMatrixDerivative q i j) q := by
  have hid := hasDerivAt_id q
  have hone := hasDerivAt_const q (1 : 𝕜)
  have hzero := hasDerivAt_const q (0 : 𝕜)
  have hquad : HasDerivAt (fun z : 𝕜 => 2*z^2*(1-z)) (4*q-6*q^2) q := by
    exact ((((hid.fun_pow 2).const_mul (2 : 𝕜)).fun_mul (hone.fun_sub hid))).congr_deriv
      (by simp only [id_eq]; ring)
  have hprod : HasDerivAt (fun z : 𝕜 => z*(z-1)) (2*q-1) q := by
    exact (hid.fun_mul (hid.fun_sub hone)).congr_deriv (by simp only [id_eq]; ring)
  have hsub : HasDerivAt (fun z : 𝕜 => 1-z) (-1) q := by
    simpa only [id_eq, zero_sub] using hone.fun_sub hid
  fin_cases i <;> fin_cases j
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hid.const_mul (-5/72 : 𝕜)
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hzero
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hquad
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hid.const_mul (-1/2 : 𝕜)
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hprod
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hzero
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hsub
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hzero
  · simpa [dualStateMatrix, dualStateMatrixDerivative] using hzero

/--
@isnad1 id=hasderiv.0h4v.s6.7d8410c94f5b from=translated src=- shape=cc293172 vocab=a83690d2
-/
theorem native_solution_metric_entry_hasDerivAt (q : 𝕜) (i j : Fin 3) :
    HasDerivAt (fun z : 𝕜 => nativeSolutionMetric z i j)
      (nativeSolutionMetricDerivative i j) q := by
  have hid := hasDerivAt_id q
  have hone := hasDerivAt_const q (1 : 𝕜)
  have hzero := hasDerivAt_const q (0 : 𝕜)
  have hsub : HasDerivAt (fun z : 𝕜 => 1-z) (-1) q := by
    simpa only [id_eq, zero_sub] using hone.fun_sub hid
  have hminus : HasDerivAt (fun z : 𝕜 => z-1) 1 q := by
    simpa only [id_eq, sub_zero] using hid.fun_sub hone
  fin_cases i <;> fin_cases j
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using
      hid.const_mul (-5/36 : 𝕜)
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using
      hid.const_mul (-1/2 : 𝕜)
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hsub
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using
      hid.const_mul (-1/2 : 𝕜)
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hminus
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hzero
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hsub
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hzero
  · simpa [nativeSolutionMetric, nativeSolutionMetricDerivative] using hzero

/--
@isnad1 id=eq.0h0v.s5.56876acbdd0a from=translated src=- shape=343131bd vocab=5e2aed5d
-/
theorem dual_state_contact_matrix :
    dualStateMatrix (27/125 : ℝ) = contactStateMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [dualStateMatrix, contactStateMatrix]

/--
@isnad1 id=eq.2h2v.s9.0b7b719176e4 from=translated src=- shape=cf42d7e0 vocab=f6a5735d
-/
theorem dual_frame_identity (q : 𝕜) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dualStateEntryDerivative q +
      q⁻¹ • ((nativeEulerConnection q).transpose * dualStateMatrix q) +
      dualStateMatrix q * ordinarySymmetricConnection q = 0 := by
  have hsub : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hd : dualStateEntryDerivative q = dualStateMatrixDerivative q := by
    ext i j
    exact (dual_state_matrix_entry_hasDerivAt q i j).deriv
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dualStateMatrixDerivative, dualStateMatrix, nativeEulerConnection,
      ordinarySymmetricConnection, Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul,
      Fin.sum_univ_succ] <;>
    field_simp [hq0, hsub] <;> ring

/--
@isnad1 id=eq.2h2v.s9.326cfdba790c from=translated src=- shape=041b94e8 vocab=71b5ac72
-/
theorem native_solution_metric_identity (q : 𝕜) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    nativeMetricEntryDerivative q +
      q⁻¹ • ((nativeEulerConnection q).transpose * nativeSolutionMetric q) +
      q⁻¹ • (nativeSolutionMetric q * nativeEulerConnection q) = 0 := by
  have hsub : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hd : nativeMetricEntryDerivative q = nativeSolutionMetricDerivative := by
    ext i j
    exact (native_solution_metric_entry_hasDerivAt q i j).deriv
  rw [hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeSolutionMetricDerivative, nativeSolutionMetric, nativeEulerConnection,
      Matrix.mul_apply, Matrix.transpose_apply, smul_eq_mul, Fin.sum_univ_succ] <;>
    field_simp [hq0, hsub] <;> ring

/--
@isnad1 id=hasderiv.2h3v.s7.a7ba164b5372 from=translated src=- shape=10ad5cc2 vocab=41a4289f
-/
theorem nativeEuler_hasDerivAt_div (k : ℕ) (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt (nativeEuler k) (nativeEuler (k+1) q / q) q := by
  have he : deriv (nativeEuler k) q = nativeEuler (k+1) q / q := by
    apply (eq_div_iff hq0).2
    rw [mul_comm]
    exact (nativeEuler_succ_eq k q hq).symm
  exact (nativeEuler_hasDerivAt k q hq).differentiableAt.hasDerivAt.congr_deriv he

/--
@isnad1 id=eq.2h2v.s8.9e18e1feab94 from=translated src=- shape=7b2504f7 vocab=075e3d6a
-/
theorem nativeEuler_three_div (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    nativeEuler 3 q / q =
      ((5/72 : 𝕜)*nativeF q + (23/36 : 𝕜)*nativeEuler 1 q +
        (3/2 : 𝕜)*nativeEuler 2 q)/(1-q) := by
  have hq1 : q ≠ 1 := by
    intro h
    simp [h] at hq
  have hsub : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hode := nativeEuler_cubic q hq
  change nativeEuler 3 q / q =
    ((5/72 : 𝕜)*nativeEuler 0 q + (23/36 : 𝕜)*nativeEuler 1 q +
      (3/2 : 𝕜)*nativeEuler 2 q)/(1-q)
  field_simp [hq0, hsub]
  linear_combination (5184 : 𝕜) * hode

noncomputable def nativeState (q : 𝕜) : Fin 3 → 𝕜 :=
  ![nativeF q, nativeEuler 1 q, nativeEuler 2 q]

noncomputable def nativeStateOrdinaryDerivative (q : 𝕜) : Fin 3 → 𝕜 :=
  ![nativeEuler 1 q / q, nativeEuler 2 q / q,
    ((5/72 : 𝕜)*nativeF q + (23/36 : 𝕜)*nativeEuler 1 q +
      (3/2 : 𝕜)*nativeEuler 2 q)/(1-q)]

/--
@isnad1 id=hasderiv.2h2v.s7.6ca57fad8d52 from=translated src=- shape=696c8e43 vocab=a5c423cc
-/
theorem native_state_hasDerivAt (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt nativeState (nativeStateOrdinaryDerivative q) q := by
  have hd0 := nativeEuler_hasDerivAt_div 0 q hq hq0
  have hd1 := nativeEuler_hasDerivAt_div 1 q hq hq0
  have hd2 := (nativeEuler_hasDerivAt_div 2 q hq hq0).congr_deriv
    (nativeEuler_three_div q hq hq0)
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · simpa [nativeState, nativeStateOrdinaryDerivative, nativeF] using hd0
  · simpa [nativeState, nativeStateOrdinaryDerivative] using hd1
  · simpa [nativeState, nativeStateOrdinaryDerivative] using hd2

/--
@isnad1 id=eq.2h2v.s7.786e0d229f9d from=translated src=- shape=2ad623b4 vocab=fd181f7e
-/
theorem native_state_derivative_connection (q : 𝕜) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    nativeStateOrdinaryDerivative q = q⁻¹ • (nativeEulerConnection q).mulVec (nativeState q) := by
  have hsub : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  ext i
  fin_cases i <;>
    simp [nativeStateOrdinaryDerivative, nativeState, nativeEulerConnection, smul_eq_mul] <;>
    field_simp [hq0, hsub]
  ring

noncomputable def dualState (q : 𝕜) : Fin 3 → 𝕜 :=
  (dualStateMatrix q).transpose.mulVec (nativeState q)

noncomputable def dualStateOrdinaryDerivative (q : 𝕜) : Fin 3 → 𝕜 :=
  (dualStateMatrixDerivative q).transpose.mulVec (nativeState q) +
    (dualStateMatrix q).transpose.mulVec (nativeStateOrdinaryDerivative q)

/--
@isnad1 id=eq.0h2v.s9.8fcd3d5b7b11 from=translated src=- shape=901d6ecd vocab=f79d9f80
-/
theorem dual_state_formula (q : 𝕜) :
    dualState q =
      ![((-5/72 : 𝕜)*q)*nativeF q + ((-1/2 : 𝕜)*q)*nativeEuler 1 q +
          (1-q)*nativeEuler 2 q,
        q*(q-1)*nativeEuler 1 q, 2*q^2*(1-q)*nativeF q] := by
  ext i
  fin_cases i <;>
    simp [dualState, dualStateMatrix, nativeState, Matrix.mulVec,
      Matrix.transpose_apply, dotProduct, Fin.sum_univ_succ]
  ring

/--
@isnad1 id=hasderiv.2h2v.s7.9dcd6a9fdcfd from=translated src=- shape=696c8e43 vocab=27beeab6
-/
theorem dual_state_hasDerivAt_product (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt dualState (dualStateOrdinaryDerivative q) q := by
  have hY := native_state_hasDerivAt q hq hq0
  apply hasDerivAt_pi.2
  intro i
  have hs := HasDerivAt.sum (u := Finset.univ) (fun k _ =>
    (dual_state_matrix_entry_hasDerivAt q k i).mul (hasDerivAt_pi.1 hY k))
  have hfun : (fun z : 𝕜 => dualState z i) =
      ∑ k : Fin 3, (fun z : 𝕜 => dualStateMatrix z k i) * (fun z => nativeState z k) := by
    funext z
    simp [dualState, Matrix.mulVec, Matrix.transpose_apply, dotProduct,
      Finset.sum_apply, Pi.mul_apply]
  rw [← hfun] at hs
  simpa [dualStateOrdinaryDerivative, Matrix.mulVec,
    Matrix.transpose_apply, dotProduct, Finset.sum_add_distrib] using hs

/--
@isnad1 id=eq.2h2v.s7.0b82f75ac7a4 from=translated src=- shape=2de39809 vocab=4737bcf1
-/
theorem dual_state_derivative_connection (q : 𝕜) (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    dualStateOrdinaryDerivative q = -((ordinarySymmetricConnection q).transpose.mulVec
      (dualState q)) := by
  have hsub : 1-q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  rw [dualStateOrdinaryDerivative, native_state_derivative_connection q hq0 hq1]
  ext i
  fin_cases i <;>
    simp [dualStateMatrixDerivative, dualStateMatrix, nativeEulerConnection,
      ordinarySymmetricConnection, dualState, nativeState,
      Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, dotProduct,
      smul_eq_mul, Fin.sum_univ_succ] <;>
    field_simp [hq0, hsub] <;> ring

/--
@isnad1 id=hasderiv.2h2v.s8.4989de52952a from=translated src=- shape=fdd294a7 vocab=685e7d21
-/
theorem dual_state_hasDerivAt (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasDerivAt dualState (-((ordinarySymmetricConnection q).transpose.mulVec
      (dualState q))) q := by
  have hq1 : q ≠ 1 := by
    intro h
    simp [h] at hq
  rw [← dual_state_derivative_connection q hq0 hq1]
  exact dual_state_hasDerivAt_product q hq hq0

/--
@isnad1 id=eq.2h2v.s8.112486d2bf11 from=translated src=- shape=d75ca4e9 vocab=e9f56fe5
-/
theorem dual_state_deriv (q : 𝕜) (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    deriv dualState q = -((ordinarySymmetricConnection q).transpose.mulVec (dualState q)) :=
  (dual_state_hasDerivAt q hq hq0).deriv

end DualFrame

end Row12

