import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.I1Partition
import Tengoku.FourierJacobiCoreEvaluation.FourierJacobi.Analysis.CoreParameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/abhisaha-git/fourier-jacobi-core-evaluation@fb2b788d6271, `FourierJacobi/Analysis/I1Assembly.lean`: removed 5 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Complete I1 depth weights, absolute summability, and restored row sums. -/
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
open FourierJacobi.Algebra
set_option maxHeartbeats 4000000

/--
@isnad1 id=eq.2h2v.s6.dcea67ec48ac from=translated src=- shape=afe842b9 vocab=f2926e5e
-/
theorem i1_qinv_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q * t ^ 2 = 1) :
    q⁻¹ = t ^ 2 := by
  have he : q = (t ^ 2)⁻¹ := by
    calc
      q = q * (t ^ 2 * (t ^ 2)⁻¹) := by rw [mul_inv_cancel₀ (pow_ne_zero 2 ht), mul_one]
      _ = (t ^ 2)⁻¹ := by rw [← mul_assoc, hqt, one_mul]
  rw [he, inv_inv]

/--
@isnad1 id=eq.3h2v.s7.1f4ad4b67f7f from=translated src=- shape=fb1fdc01 vocab=2892bb6b
-/
theorem i1_prob0_eq (q t : ℂ) (ht : t ≠ 0) (hqt : q*t^2=1)
    (hz : 1-t^2 ≠ 0) : collisionProbability q 0 = (1-2*t^2)/(1-t^2) := by
  have he : q = (t^2)⁻¹ := by
    rw [← i1_qinv_eq q t ht hqt, inv_inv]
  simp only [collisionProbability, ite_true]
  rw [he]
  field_simp [ht,hz]
  <;> ring

/--
@isnad1 id=summable.1h1v.s5.c1a84a95df00 from=translated src=- shape=1c7edae7 vocab=caaea02c
-/
theorem i1_summable_norm_prob_tail (q : ℂ) (hq : ‖q⁻¹‖ < 1) :
    Summable (fun c : ℕ => ‖collisionProbability q (c+1)‖) := by
  simpa only [collisionProbability_succ, norm_mul] using
    (geometric_norm_summable q⁻¹ hq).mul_left ‖q⁻¹‖

/--
@isnad1 id=hassum.4h6v.s7.99587c02bc49 from=translated src=- shape=9b22d325 vocab=4ef4f931
-/
theorem i1_hasSum_product {ι κ : Type*} (f : ι → ℂ) (g : κ → ℂ)
    (s z : ℂ) (hf : HasSum f s) (hg : HasSum g z)
    (hfn : Summable (fun p => ‖f p‖)) (hgn : Summable (fun p => ‖g p‖)) :
    HasSum (fun p : ι × κ => f p.1 * g p.2) (s*z) := by
  have hs := (hfn.mul_norm hgn).of_norm
  have he := tsum_mul_tsum_of_summable_norm hfn hgn
  rw [hf.tsum_eq,hg.tsum_eq] at he
  exact he.symm ▸ hs.hasSum

/--
@isnad1 id=eq.2h7v.s9.391fe87e6ab0 from=translated src=- shape=69bb7e78 vocab=ca1062f8
-/
theorem i1r1_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R1Row × ℕ) :
    masterTerm q t d U V T 1 (i1r1DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r1DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r1_cartan, i1r1_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.543b41a9d4b2 from=translated src=- shape=efa0e900 vocab=22d1bc5e
-/
theorem hasSum_i1r1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 0 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  have hn := summable_norm_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  apply i1r1DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R1Row => p.val.2.1) (fun p : I1R1Row => p.val.2.2)
    (fun p : I1R1Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r1_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.b4dc6eea6000 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 0 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r1_raw t d U V T 0 h.p h.t2 h.t2
  apply i1r1DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R1Row => p.val.2.1) (fun p : I1R1Row => p.val.2.2)
    (fun p : I1R1Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r1_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.8cce5518d10c from=translated src=- shape=97d34063 vocab=5f6001df
-/
theorem i1r1_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm10
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.bc60abe9953e from=translated src=- shape=f172dbcb vocab=c1d7400f
-/
theorem i1r2_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R2Row × ℕ) :
    masterTerm q t d U V T 1 (i1r2DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r2DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r2_cartan, i1r2_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.22aac18d6a3d from=translated src=- shape=427a6c18 vocab=22d1bc5e
-/
theorem hasSum_i1r2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 1 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r2_raw t d U V T 0 h.p h.t2 h.g
  have hn := summable_norm_i1r2_raw t d U V T 0 h.p h.t2 h.g
  apply i1r2DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R2Row => p.val.2.1) (fun p : I1R2Row => p.val.2.2)
    (fun p : I1R2Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r2_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.b94b7fee8b50 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r2_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 1 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r2_raw t d U V T 0 h.p h.t2 h.g
  apply i1r2DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R2Row => p.val.2.1) (fun p : I1R2Row => p.val.2.2)
    (fun p : I1R2Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r2_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.19c8618e6237 from=translated src=- shape=aa5861a3 vocab=6f7c19b3
-/
theorem i1r2_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm11
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.cf3f4e7316e5 from=translated src=- shape=0aa647cf vocab=9b71ba35
-/
theorem i1r3ae_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3AERow × ℕ) :
    masterTerm q t d U V T 1 (i1r3aeDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r3aeDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r3ae_cartan, i1r3ae_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s9.16770e7a6a63 from=translated src=- shape=d1938d71 vocab=22d1bc5e
-/
theorem hasSum_i1r3ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 2 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  have hn := summable_norm_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aeDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R3AERow => p.val.2.1) (fun p : I1R3AERow => p.val.2.2)
    (fun p : I1R3AERow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r3ae_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.1c79ed4f6c07 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r3ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 2 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3ae_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aeDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R3AERow => p.val.2.1) (fun p : I1R3AERow => p.val.2.2)
    (fun p : I1R3AERow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r3ae_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.abaa56799942 from=translated src=- shape=86a2e8f1 vocab=5caaee2f
-/
theorem i1r3ae_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * d * (T*U) * (T * V)^2 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.e8ba36e2f24d from=translated src=- shape=0aa647cf vocab=df30dd97
-/
theorem i1r3ao_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r3aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r3aoDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r3ao_cartan, i1r3ao_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.cc135561bb99 from=translated src=- shape=0dc634ef vocab=22d1bc5e
-/
theorem hasSum_i1r3ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 3 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  have hn := summable_norm_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aoDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R3AORow => p.val.2.1) (fun p : I1R3AORow => p.val.2.2)
    (fun p : I1R3AORow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r3ao_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.219abb05db2a from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r3ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 3 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3ao_raw t d U V T 0 h.p h.e h.t2
  apply i1r3aoDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R3AORow => p.val.2.1) (fun p : I1R3AORow => p.val.2.2)
    (fun p : I1R3AORow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r3ao_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.d6c8427ffecb from=translated src=- shape=0f991b61 vocab=5caaee2f
-/
theorem i1r3ao_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * d * (T*U) * (T * V)^1 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.b8d109b1d46b from=translated src=- shape=b49349d6 vocab=46b48fc7
-/
theorem i1r3b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3BRow) :
    masterTerm q t d U V T 1 (i1r3bDepthEquiv p).val =
      i1Raw t d U V T p.val 0 * collisionProbability q 0 := by
  rw [i1r3bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have hc : 2*p.val.2.2 = p.val.2.1-1 := p.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, ite_false]

/--
@isnad1 id=hassum.5h6v.s8.1e065b8b30bc from=translated src=- shape=c4d56ded vocab=4228febf
-/
theorem hasSum_i1r3b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 4 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3b_raw t d U V T h.p h.e
  have hn := summable_norm_i1r3b_raw t d U V T h.p h.e
  apply i1r3bDepthEquiv.hasSum_iff.mp
  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
  exact funext fun p => i1r3b_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.cd58f3040022 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r3b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 4 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3b_raw t d U V T h.p h.e
  apply i1r3bDepthEquiv.summable_iff.mp
  convert hn.mul_right ‖collisionProbability q 0‖ using 1
  all_goals try rfl
  exact funext fun p => by
    simpa only [norm_mul, Function.comp_apply] using
      congrArg norm (i1r3b_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.c24aa977fb3a from=translated src=- shape=0cd399bc vocab=9ff78764
-/
theorem i1r3b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) = (regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_prob0_eq q t ht hqt hz]
  unfold regionTerm13
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.2b9babad159a from=translated src=- shape=8237f803 vocab=5a6a0259
-/
theorem i1r3c_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R3CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r3cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by
  rw [i1r3cDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2 + 1) =
      i1Raw t d U V T p.1.val 1 := by
    unfold i1Raw
    rw [i1r3c_cartan, i1r3c_cartan]
    all_goals omega
  rw [he]
  have hc : 2*p.1.val.2.2 = p.1.val.2.1-1 := p.1.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, ite_false]

/--
@isnad1 id=hassum.5h6v.s8.2eb088926b0d from=translated src=- shape=d130e926 vocab=8f23bc2b
-/
theorem hasSum_i1r3c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 5 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  have hn := summable_norm_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  apply i1r3cDepthEquiv.hasSum_iff.mp
  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : I1R3CRow => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => i1r3c_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.6ce0cb4ce434 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r3c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 5 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r3c_raw t d U V T ht 1 (by omega) h.p h.e
  apply i1r3cDepthEquiv.summable_iff.mp
  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => congrArg norm (i1r3c_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.496f3d30e1b9 from=translated src=- shape=0e6d276f vocab=af73e014
-/
theorem i1r3c_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) = (regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_qinv_eq q t ht hqt]
  unfold regionTerm14
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.2c0fefbcf048 from=translated src=- shape=b55ea582 vocab=3ddf83fd
-/
theorem i1r4_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R4Row × ℕ) :
    masterTerm q t d U V T 1 (i1r4DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r4DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r4_cartan, i1r4_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s9.a4ee30a06f91 from=translated src=- shape=1a30f4b7 vocab=22d1bc5e
-/
theorem hasSum_i1r4_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 6 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r4_raw t d U V T 0 h.p h.e h.f
  have hn := summable_norm_i1r4_raw t d U V T 0 h.p h.e h.f
  apply i1r4DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R4Row => p.val.2.1) (fun p : I1R4Row => p.val.2.2)
    (fun p : I1R4Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r4_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.f1d080214369 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r4_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 6 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r4_raw t d U V T 0 h.p h.e h.f
  apply i1r4DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R4Row => p.val.2.1) (fun p : I1R4Row => p.val.2.2)
    (fun p : I1R4Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r4_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.a9c4eccce196 from=translated src=- shape=3c177e6f vocab=b795ec22
-/
theorem i1r4_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) = (regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm15
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.0982c4e165f6 from=translated src=- shape=02b1cce9 vocab=379336f9
-/
theorem i1r5_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R5Row × ℕ) :
    masterTerm q t d U V T 1 (i1r5DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r5DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r5_cartan, i1r5_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s9.e96cf837f3dc from=translated src=- shape=68b00cbe vocab=22d1bc5e
-/
theorem hasSum_i1r5_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 7 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r5_raw t d U V T 0 h.p h.f h.g
  have hn := summable_norm_i1r5_raw t d U V T 0 h.p h.f h.g
  apply i1r5DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R5Row => p.val.2.1) (fun p : I1R5Row => p.val.2.2)
    (fun p : I1R5Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r5_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.ce2505a03f68 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r5_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 7 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r5_raw t d U V T 0 h.p h.f h.g
  apply i1r5DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R5Row => p.val.2.1) (fun p : I1R5Row => p.val.2.2)
    (fun p : I1R5Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r5_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.b53c6c4f5d38 from=translated src=- shape=e8e5bd10 vocab=c6f87d86
-/
theorem i1r5_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm16
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.6163ba7bb966 from=translated src=- shape=29af8389 vocab=36863683
-/
theorem i1r6a_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R6ARow × ℕ) :
    masterTerm q t d U V T 1 (i1r6aDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r6aDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r6a_cartan, i1r6a_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.cd3fd99b0668 from=translated src=- shape=393c5b3d vocab=22d1bc5e
-/
theorem hasSum_i1r6a_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 8 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r6a_raw t d U V T 0 h.t2 h.t2
  have hn := summable_norm_i1r6a_raw t d U V T 0 h.t2 h.t2
  apply i1r6aDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R6ARow => p.val.2.1) (fun p : I1R6ARow => p.val.2.2)
    (fun p : I1R6ARow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r6a_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.5ea74945594b from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r6a_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 8 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r6a_raw t d U V T 0 h.t2 h.t2
  apply i1r6aDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R6ARow => p.val.2.1) (fun p : I1R6ARow => p.val.2.2)
    (fun p : I1R6ARow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r6a_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.b273d4efa575 from=translated src=- shape=e50b1259 vocab=33dc3902
-/
theorem i1r6a_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm17
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.99e00437bf5c from=translated src=- shape=b424d6b2 vocab=2e2f293b
-/
theorem i1r6b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R6BRow × ℕ) :
    masterTerm q t d U V T 1 (i1r6bDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r6bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r6b_cartan, i1r6b_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.f0106e6f61dc from=translated src=- shape=20c58605 vocab=8f23bc2b
-/
theorem hasSum_i1r6b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 9 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  have hn := summable_norm_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  apply i1r6bDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R6BRow => p.val.2.1) (fun p : I1R6BRow => p.val.2.2)
    (fun p : I1R6BRow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r6b_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.41b56b8f601c from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r6b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 9 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r6b_raw t d U V T 0 h.n h.t2 h.t2
  apply i1r6bDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R6BRow => p.val.2.1) (fun p : I1R6BRow => p.val.2.2)
    (fun p : I1R6BRow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r6b_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.3f210cd75ec3 from=translated src=- shape=d2110355 vocab=2be387ab
-/
theorem i1r6b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = (regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm18
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.e939a0ad3ade from=translated src=- shape=fa8681ce vocab=5716e5fe
-/
theorem i1r7_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R7Row × ℕ) :
    masterTerm q t d U V T 1 (i1r7DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r7DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r7_cartan, i1r7_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.657e6d6bd49a from=translated src=- shape=203b8b39 vocab=8f23bc2b
-/
theorem hasSum_i1r7_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 10 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r7_raw t d U V T 0 h.n h.t2 h.g
  have hn := summable_norm_i1r7_raw t d U V T 0 h.n h.t2 h.g
  apply i1r7DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R7Row => p.val.2.1) (fun p : I1R7Row => p.val.2.2)
    (fun p : I1R7Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r7_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.1d0ece407b01 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r7_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 10 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r7_raw t d U V T 0 h.n h.t2 h.g
  apply i1r7DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R7Row => p.val.2.1) (fun p : I1R7Row => p.val.2.2)
    (fun p : I1R7Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r7_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.7a4f2101c495 from=translated src=- shape=356b6e9c vocab=7bbb47e7
-/
theorem i1r7_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm19
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.6ffdc275679c from=translated src=- shape=bd7e6882 vocab=3c6c858c
-/
theorem i1r8ae_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8AERow × ℕ) :
    masterTerm q t d U V T 1 (i1r8aeDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r8aeDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r8ae_cartan, i1r8ae_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.9c2700af1c6e from=translated src=- shape=7c4a6948 vocab=8f23bc2b
-/
theorem hasSum_i1r8ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 11 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  have hn := summable_norm_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aeDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R8AERow => p.val.2.1) (fun p : I1R8AERow => p.val.2.2)
    (fun p : I1R8AERow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r8ae_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.1c92aeaad0f9 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r8ae_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 11 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8ae_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aeDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R8AERow => p.val.2.1) (fun p : I1R8AERow => p.val.2.2)
    (fun p : I1R8AERow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r8ae_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.1823545e807b from=translated src=- shape=cf7e3b71 vocab=725f659c
-/
theorem i1r8ae_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * (T*U) * (T * V)^1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.dff18646d712 from=translated src=- shape=bd7e6882 vocab=1b49584e
-/
theorem i1r8ao_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8AORow × ℕ) :
    masterTerm q t d U V T 1 (i1r8aoDepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r8aoDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r8ao_cartan, i1r8ao_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.958564e6b76d from=translated src=- shape=55bb27e1 vocab=8f23bc2b
-/
theorem hasSum_i1r8ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 12 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  have hn := summable_norm_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aoDepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R8AORow => p.val.2.1) (fun p : I1R8AORow => p.val.2.2)
    (fun p : I1R8AORow => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r8ao_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.3b69ab8a3c0b from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r8ao_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 12 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8ao_raw t d U V T 0 h.n h.e h.t2
  apply i1r8aoDepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R8AORow => p.val.2.1) (fun p : I1R8AORow => p.val.2.2)
    (fun p : I1R8AORow => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r8ao_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.4fe166dc53cb from=translated src=- shape=e2a2e8b2 vocab=725f659c
-/
theorem i1r8ao_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹) = ((1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.ec097a341be9 from=translated src=- shape=88678325 vocab=a92a0ba1
-/
theorem i1r8b_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8BRow) :
    masterTerm q t d U V T 1 (i1r8bDepthEquiv p).val =
      i1Raw t d U V T p.val 0 * collisionProbability q 0 := by
  rw [i1r8bDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have hc : 2*p.val.2.2 = p.val.2.1-1 := p.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, ite_false]

/--
@isnad1 id=hassum.5h6v.s8.d409cd2cdeb1 from=translated src=- shape=a83f8a9c vocab=4247b5ae
-/
theorem hasSum_i1r8b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 13 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8b_raw t d U V T h.n h.e
  have hn := summable_norm_i1r8b_raw t d U V T h.n h.e
  apply i1r8bDepthEquiv.hasSum_iff.mp
  convert hs.mul_right (collisionProbability q 0) using 1
  all_goals try rfl
  exact funext fun p => i1r8b_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.ac46b8dd1336 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r8b_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 13 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8b_raw t d U V T h.n h.e
  apply i1r8bDepthEquiv.summable_iff.mp
  convert hn.mul_right ‖collisionProbability q 0‖ using 1
  all_goals try rfl
  exact funext fun p => by
    simpa only [norm_mul, Function.comp_apply] using
      congrArg norm (i1r8b_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.cb685bf21684 from=translated src=- shape=3bd93453 vocab=69d8d039
-/
theorem i1r8b_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0)) = (regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_prob0_eq q t ht hqt hz]
  unfold regionTerm21
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.379d7289c4ea from=translated src=- shape=ee4a5860 vocab=3d8ff7fd
-/
theorem i1r8c_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R8CRow × ℕ) :
    masterTerm q t d U V T 1 (i1r8cDepthEquiv p).val =
      i1Raw t d U V T p.1.val 1 * collisionProbability q (p.2+1) := by
  rw [i1r8cDepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2 + 1) =
      i1Raw t d U V T p.1.val 1 := by
    unfold i1Raw
    rw [i1r8c_cartan, i1r8c_cartan]
    all_goals omega
  rw [he]
  have hc : 2*p.1.val.2.2 = p.1.val.2.1-1 := p.1.property.2.2.2
  simp only [collisionWeight, one_ne_zero, hc, ne_eq, not_true_eq_false, false_or, ite_false]

/--
@isnad1 id=hassum.5h6v.s8.ecc2b56592a8 from=translated src=- shape=c30b8764 vocab=8f23bc2b
-/
theorem hasSum_i1r8c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 14 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.hasSum_iff.mp
  have hg := hasSum_collisionProbability_tail q 0 hq
  simp only [Nat.add_zero, zero_add, pow_one] at hg
  convert i1_hasSum_product (fun p : I1R8CRow => i1Raw t d U V T p.val 1)
    (fun c : ℕ => collisionProbability q (c+1)) _ _ hs hg hn
    (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => i1r8c_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.ab5996470ef9 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r8c_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 14 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r8c_raw t d U V T ht 1 (by omega) h.n h.e
  apply i1r8cDepthEquiv.summable_iff.mp
  convert hn.mul_norm (i1_summable_norm_prob_tail q hq) using 1
  exact funext fun p => congrArg norm (i1r8c_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.af9bb174127c from=translated src=- shape=038f0b64 vocab=af9ad4b9
-/
theorem i1r8c_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹)) = (regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  rw [i1_qinv_eq q t ht hqt]
  unfold regionTerm22
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s9.097830c6a9f6 from=translated src=- shape=992a63d0 vocab=861e9026
-/
theorem i1r9_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R9Row × ℕ) :
    masterTerm q t d U V T 1 (i1r9DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r9DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r9_cartan, i1r9_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.bb8fc745f6bb from=translated src=- shape=32757957 vocab=8f23bc2b
-/
theorem hasSum_i1r9_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 15 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r9_raw t d U V T 0 h.n h.e h.f
  have hn := summable_norm_i1r9_raw t d U V T 0 h.n h.e h.f
  apply i1r9DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R9Row => p.val.2.1) (fun p : I1R9Row => p.val.2.2)
    (fun p : I1R9Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r9_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.d264353e6436 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r9_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 15 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r9_raw t d U V T 0 h.n h.e h.f
  apply i1r9DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R9Row => p.val.2.1) (fun p : I1R9Row => p.val.2.2)
    (fun p : I1R9Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r9_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.1971e08f47f9 from=translated src=- shape=86f8404e vocab=5fc8116b
-/
theorem i1r9_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹) = (regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm23
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

/--
@isnad1 id=eq.2h7v.s8.0188c8b17504 from=translated src=- shape=03e1444c vocab=71dc5573
-/
theorem i1r10_master_reindexed (q t d U V T : ℂ) (ht : t ≠ 0)
    (hqt : q*t^2=1) (p : I1R10Row × ℕ) :
    masterTerm q t d U V T 1 (i1r10DepthEquiv p).val =
      i1Raw t d U V T p.1.val 0 * collisionWeight q 1 p.1.val.2.1 p.1.val.2.2 p.2 := by
  rw [i1r10DepthEquiv_val]
  unfold masterTerm
  rw [← i1Raw_eq_shell q t d U V T ht hqt]
  have he : i1Raw t d U V T p.1.val (p.2) =
      i1Raw t d U V T p.1.val 0 := by
    unfold i1Raw
    rw [i1r10_cartan, i1r10_cartan]
    
  rw [he]

/--
@isnad1 id=hassum.5h6v.s8.58a7b7db660f from=translated src=- shape=22bec3e6 vocab=8f23bc2b
-/
theorem hasSum_i1r10_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (fun p : I1Cell 16 => masterTerm q t d U V T 1 p.val)
      (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hs := hasSum_i1r10_raw t d U V T 0 h.n h.f h.g
  have hn := summable_norm_i1r10_raw t d U V T 0 h.n h.f h.g
  apply i1r10DepthEquiv.hasSum_iff.mp
  convert hasSum_weighted_collision q 1
    (fun p : I1R10Row => p.val.2.1) (fun p : I1R10Row => p.val.2.2)
    (fun p : I1R10Row => i1Raw t d U V T p.val 0) _ hq0 hq1 hq hs hn using 1
  exact funext fun p => i1r10_master_reindexed q t d U V T ht hqt p

/--
@isnad1 id=summable.3h6v.s7.4b6aa4b4c9e5 from=translated src=- shape=f51a89c9 vocab=c319bc85
-/
theorem summable_norm_i1r10_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : I1Cell 16 => ‖masterTerm q t d U V T 1 p.val‖) := by
  have hq : ‖q⁻¹‖ < 1 := by rw [i1_qinv_eq q t ht hqt]; exact h.t2
  have hn := summable_norm_i1r10_raw t d U V T 0 h.n h.f h.g
  apply i1r10DepthEquiv.summable_iff.mp
  convert summable_norm_weighted_collision q 1
    (fun p : I1R10Row => p.val.2.1) (fun p : I1R10Row => p.val.2.2)
    (fun p : I1R10Row => i1Raw t d U V T p.val 0) hq hn using 1
  exact funext fun p => congrArg norm (i1r10_master_reindexed q t d U V T ht hqt p)

/--
@isnad1 id=eq.4h6v.s9.3f5499bfefbf from=translated src=- shape=5d283c9e vocab=ca511d09
-/
theorem i1r10_value_eq (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹) = (regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)) := by
  have hz := norm_one_sub_ne_zero h.t2
  have hp := norm_one_sub_ne_zero h.p
  have hn := norm_one_sub_ne_zero h.n
  have he := norm_one_sub_ne_zero h.e
  have hf := norm_one_sub_ne_zero h.f
  have hg := norm_one_sub_ne_zero h.g
  
  unfold regionTerm24
  simp only [pow_one, mul_assoc] at *
  field_simp [hz,hp,hn,he,hf,hg,ht,hd]
  <;> ring

def i1CellValue (q t d U V T : ℂ) : Fin 17 → ℂ :=
  ![((1 - t ^ 2) ^ 3 * d * (T * U) * t) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t ^ 3) * (1 - d * T * V * t)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V)^2 * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U) * (T * V) * t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * d * (T * V)^2 / t) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^3) * (1 - d * T * V * t)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * d * (T * U)^2 * (T * V) * t^5) * (1 - d * T * V * t)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * V) * t^2) * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t / d) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * (T * V) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U) * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (collisionProbability q 0),
    ((1 - t ^ 2) ^ 3 * (T * V) / t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (q⁻¹ * (1 - q⁻¹)⁻¹),
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^2) * (1 - T * V * t / d)⁻¹ * (1 - (T * V) ^ 2 * t ^ 2)⁻¹ * (1 - T * U * t ^ 2)⁻¹,
    ((1 - t ^ 2) ^ 3 * (T * U)^2 * t^4) * (1 - T * V * t / d)⁻¹ * (1 - T * U * t ^ 2)⁻¹ * (1 - T * U * t ^ 4)⁻¹]

/--
@isnad1 id=hassum.5h7v.s7.b44d5d4eef93 from=translated src=- shape=c2811b8f vocab=e77d72b3
-/
theorem hasSum_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    HasSum (fun p : I1Cell i => masterTerm q t d U V T 1 p.val)
      (i1CellValue q t d U V T i) := by
  fin_cases i
  · exact hasSum_i1r1_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r2_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r3c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r4_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r5_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6a_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r6b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r7_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ae_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8ao_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8b_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r8c_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r9_master q t d U V T ht hq0 hq1 hqt h
  · exact hasSum_i1r10_master q t d U V T ht hq0 hq1 hqt h

/--
@isnad1 id=summable.3h7v.s6.ae67981ed20e from=translated src=- shape=3ff2a2eb vocab=c319bc85
-/
theorem summable_norm_i1_cell (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) (i : Fin 17) :
    Summable (fun p : I1Cell i => ‖masterTerm q t d U V T 1 p.val‖) := by
  fin_cases i
  · exact summable_norm_i1r1_master q t d U V T ht hqt h
  · exact summable_norm_i1r2_master q t d U V T ht hqt h
  · exact summable_norm_i1r3ae_master q t d U V T ht hqt h
  · exact summable_norm_i1r3ao_master q t d U V T ht hqt h
  · exact summable_norm_i1r3b_master q t d U V T ht hqt h
  · exact summable_norm_i1r3c_master q t d U V T ht hqt h
  · exact summable_norm_i1r4_master q t d U V T ht hqt h
  · exact summable_norm_i1r5_master q t d U V T ht hqt h
  · exact summable_norm_i1r6a_master q t d U V T ht hqt h
  · exact summable_norm_i1r6b_master q t d U V T ht hqt h
  · exact summable_norm_i1r7_master q t d U V T ht hqt h
  · exact summable_norm_i1r8ae_master q t d U V T ht hqt h
  · exact summable_norm_i1r8ao_master q t d U V T ht hqt h
  · exact summable_norm_i1r8b_master q t d U V T ht hqt h
  · exact summable_norm_i1r8c_master q t d U V T ht hqt h
  · exact summable_norm_i1r9_master q t d U V T ht hqt h
  · exact summable_norm_i1r10_master q t d U V T ht hqt h

/-- Absolute summability of the actual complete I1 lattice, before rearrangement.
@isnad1 id=summable.3h6v.s6.cdd0bb8fc522 from=translated src=- shape=372867fe vocab=e29c612a
-/
theorem summable_norm_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    Summable (fun p : LatticeIndex => ‖masterTerm q t d U V T 1 p‖) := by
  apply i1PartitionEquiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun p => norm_nonneg _)).mpr
  exact ⟨summable_norm_i1_cell q t d U V T ht hqt h, (hasSum_fintype _).summable⟩

/--
@isnad1 id=hassum.5h6v.s7.230a66c493b3 from=translated src=- shape=85d6d339 vocab=712b2ebc
-/
theorem hasSum_i1_master_cells (q t d U V T : ℂ)
    (ht : t ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1) (∑ i : Fin 17, i1CellValue q t d U V T i) := by
  have hs := (summable_norm_i1_master q t d U V T ht hqt h).of_norm
  apply i1PartitionEquiv.hasSum_iff.mp
  exact (hasSum_fintype (i1CellValue q t d U V T)).sigma_of_hasSum
    (hasSum_i1_cell q t d U V T ht hq0 hq1 hqt h)
    (i1PartitionEquiv.summable_iff.mpr hs)

def i1CellSimplified (t d U V T : ℂ) : Fin 17 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * d * (T*U) * (T * V)^2 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * d * (T*U) * (T * V)^1 * t^3 * (1 - d * (T * V) * t)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    (1-t^2)^2 * (T*U) * (T * V)^1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    (1-t^2)^2 * (T*U) * 1 * t^2 * (1 - (T * V) * t / d)⁻¹ * (1 - (T * V)^2 * t^2)⁻¹,
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]

def i1StoredRows (t d U V T : ℂ) : Fin 15 → ℂ :=
  ![regionTerm10 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm11 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm12 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm13 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm14 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm15 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm16 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm17 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm18 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm19 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm20 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm21 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm22 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm23 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4),
    regionTerm24 t d (T*U) (T*V) (1 - d * (T * V) * t) (1 - (T * V) * t / d) (1 - (T * V)^2 * t^2) (1 - (T * U) * t^2) (1 - (T * U) * t^4)]

/--
@isnad1 id=eq.0h6v.s6.19eb39ee4088 from=translated src=- shape=19d43604 vocab=e02e521e
-/
theorem i1StoredRows_eq_regionTerms (t d U V T : ℂ) (i : Fin 15) :
    i1StoredRows t d U V T i =
      regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  fin_cases i <;> rfl

/--
@isnad1 id=eq.4h7v.s6.07f90e2168d5 from=translated src=- shape=9fb44a5e vocab=fd98edf1
-/
theorem i1CellValue_eq_simplified (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) (i : Fin 17) :
    i1CellValue q t d U V T i = i1CellSimplified t d U V T i := by
  fin_cases i
  · exact i1r1_value_eq q t d U V T ht hd hqt h
  · exact i1r2_value_eq q t d U V T ht hd hqt h
  · exact i1r3ae_value_eq q t d U V T ht hd hqt h
  · exact i1r3ao_value_eq q t d U V T ht hd hqt h
  · exact i1r3b_value_eq q t d U V T ht hd hqt h
  · exact i1r3c_value_eq q t d U V T ht hd hqt h
  · exact i1r4_value_eq q t d U V T ht hd hqt h
  · exact i1r5_value_eq q t d U V T ht hd hqt h
  · exact i1r6a_value_eq q t d U V T ht hd hqt h
  · exact i1r6b_value_eq q t d U V T ht hd hqt h
  · exact i1r7_value_eq q t d U V T ht hd hqt h
  · exact i1r8ae_value_eq q t d U V T ht hd hqt h
  · exact i1r8ao_value_eq q t d U V T ht hd hqt h
  · exact i1r8b_value_eq q t d U V T ht hd hqt h
  · exact i1r8c_value_eq q t d U V T ht hd hqt h
  · exact i1r9_value_eq q t d U V T ht hd hqt h
  · exact i1r10_value_eq q t d U V T ht hd hqt h

/--
@isnad1 id=eq.0h5v.s6.581f32ee9e3b from=translated src=- shape=084630a7 vocab=97a8cf31
-/
theorem i1CellSimplified_sum (t d U V T : ℂ) :
    (∑ i : Fin 17, i1CellSimplified t d U V T i) =
      ∑ i : Fin 15, i1StoredRows t d U V T i := by
  simp only [i1CellSimplified, i1StoredRows, Fin.sum_univ_succ,
    Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  unfold regionTerm10 regionTerm11 regionTerm12 regionTerm13 regionTerm14 regionTerm15 regionTerm16 regionTerm17 regionTerm18 regionTerm19 regionTerm20 regionTerm21 regionTerm22 regionTerm23 regionTerm24
  simp only [pow_one]
  ring

/--
@isnad1 id=eq.4h6v.s7.ce256c0e526b from=translated src=- shape=d2c639be vocab=feb61837
-/
theorem i1CellValue_sum_eq_regions (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hqt : q*t^2=1)
    (h : GeometricRange t d U V T) :
    (∑ i : Fin 17, i1CellValue q t d U V T i) =
      ∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩ := by
  calc
    _ = ∑ i : Fin 17, i1CellSimplified t d U V T i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1CellValue_eq_simplified q t d U V T ht hd hqt h i
    _ = ∑ i : Fin 15, i1StoredRows t d U V T i := i1CellSimplified_sum t d U V T
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact i1StoredRows_eq_regionTerms t d U V T i

/-- The complete infinite I1 master lattice equals the exact stored fifteen
restored row fractions. Absolute summability was established before this
partition and parity recombination. Damping remains in each unsummed term.
@isnad1 id=hassum.6h6v.s7.6c2533549855 from=translated src=- shape=ee46f648 vocab=147a9b69
-/
theorem hasSum_i1_master (q t d U V T : ℂ)
    (ht : t ≠ 0) (hd : d ≠ 0) (hq0 : q ≠ 0) (hq1 : q-1 ≠ 0)
    (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  rw [← i1CellValue_sum_eq_regions q t d U V T ht hd hqt h]
  exact hasSum_i1_master_cells q t d U V T ht hq0 hq1 hqt h

/--
@isnad1 id=and.2h2v.s6.4e65359dc2f4 from=translated src=- shape=12ff62b2 vocab=23206046
-/
theorem i1_basic_nonzero (q t : ℂ) (hqt : q*t^2=1) (hz : ‖t^2‖<1) :
    t ≠ 0 ∧ q ≠ 0 ∧ q-1 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    simp [ht] at hqt
  · intro hq
    simp [hq] at hqt
  · intro hq
    have he : q = 1 := sub_eq_zero.mp hq
    have he' : t^2=1 := by simpa only [he,one_mul] using hqt
    rw [he',norm_one] at hz
    exact (lt_irrefl (1 : ℝ)) hz

/-- All auxiliary nonzero q/t hypotheses follow from the independent
normalization equation and the convergent parameter range.
@isnad1 id=hassum.3h6v.s7.fd52ebaf4345 from=translated src=- shape=4728c3a6 vocab=25c8d030
-/
theorem hasSum_i1_master_of_geometricRange (q t d U V T : ℂ)
    (hd : d ≠ 0) (hqt : q*t^2=1) (h : GeometricRange t d U V T) :
    HasSum (masterTerm q t d U V T 1)
      (∑ i : Fin 15, regionTerms t d (T*U) (T*V) ⟨10+i.val, by omega⟩) := by
  obtain ⟨ht,hq0,hq1⟩ := i1_basic_nonzero q t hqt h.t2
  exact hasSum_i1_master q t d U V T ht hd hq0 hq1 hqt h

/-- Natural real damping and unitary monomial hypotheses. The strict
inequality T*t < ‖δ‖ covers damped endpoint and undamped interior cases.
@isnad1 id=and.10h6v.s8.8d78d8c076e9 from=translated src=- shape=47145d7d vocab=360f568e
-/
theorem i1_master_of_bounds (q t T : ℝ) (d U V : ℂ)
    (hqt : q*t^2=1) (ht0 : 0<t) (ht1 : t<1) (hT0 : 0≤T) (hT1 : T≤1)
    (hdlo : t≤‖d‖) (hdhi : ‖d‖≤1) (hstrict : T*t<‖d‖)
    (hU : ‖U‖=1) (hV : ‖V‖=1) :
    Summable (fun p : LatticeIndex => ‖masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1 p‖) ∧
    HasSum (masterTerm (q:ℂ) (t:ℂ) d U V (T:ℂ) 1)
      (∑ i : Fin 15, regionTerms (t:ℂ) d ((T:ℂ)*U) ((T:ℂ)*V) ⟨10+i.val, by omega⟩) := by
  have h := geometricRange_of_bounds ht0 ht1 hT0 hT1 hdlo hdhi hstrict hU hV
  have he : (q:ℂ)*(t:ℂ)^2=1 := by exact_mod_cast hqt
  have ht : (t:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
  have hd : d ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le ht0 hdlo)
  exact ⟨summable_norm_i1_master q t d U V T ht he h,
    hasSum_i1_master_of_geometricRange q t d U V T hd he h⟩

end FourierJacobi.Analysis
