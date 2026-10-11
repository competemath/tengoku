import Tengoku.OpenaiMath.OAI.Probability.ProjectionMoments.Seeded

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
variable {d M T : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma uniformSuccess_le_sum_fixed (L : Learner d M T Ω) (ρ : Measure Ω) (ε : ℝ) :
    L.uniformSuccess ρ ε ≤ ∑ t : Fin (T+1), L.uniformFixedSuccess ρ ε t := by
  classical
  let μ := (uniformSphere d).prod (ρ.prod (sampleLaw d T))
  have hs : {z : UnitSphere d × (Ω × Samples d T) |
      angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} =
      ⋃ t : Fin (T+1), {z | (L.terminal z.1 z.2.1 z.2.2).1 = t ∧
        angularError z.1 (L.estimate z.1 z.2.1 z.2.2) ≤ ε} := by
    ext z
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro hz
      obtain ⟨t,ht,he⟩ := L.terminal_forced_witness z.1 z.2.1 z.2.2
      exact ⟨⟨t,by omega⟩,by simpa [he] using hz⟩
    · rintro ⟨t,ht,hz⟩
      exact hz
  change μ _ ≤ ∑ t : Fin (T+1), μ _
  rw [hs]
  exact (measure_iUnion_le _).trans_eq (tsum_fintype _)

end Learner
namespace FiniteKernelLearner

section
universe u

end

section

universe u
variable {d M T : ℕ} {Ξ : Type u} [MeasurableSpace Ξ]

lemma seededSuccess_eq_integral_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε) :
    seededSuccess K ρ ε = ∫⁻ s, seededPointwiseSuccess K ρ ε s ∂uniformSphere d := by
  let f := fun z : UnitSphere d × (Ξ × Samples d T) =>
    (K z.2.1).conditionalSuccess ε z.1 z.2.2
  let e : ((UnitSphere d × Samples d T) × Ξ) ≃ᵐ UnitSphere d × (Ξ × Samples d T) :=
    MeasurableEquiv.prodAssoc.trans (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.prodComm))
  have hp : MeasurePreserving e (((uniformSphere d).prod (sampleLaw d T)).prod ρ)
      ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
    ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := ρ))).comp
      (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) ρ)
  have hf : AEMeasurable f ((uniformSphere d).prod (ρ.prod (sampleLaw d T))) := hm
  have hfD : AEMeasurable (fun z : (UnitSphere d × Samples d T) × Ξ => f (e z))
      (((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
    hf.comp_quasiMeasurePreserving hp.quasiMeasurePreserving
  calc
    _ = ∫⁻ ξ, ∫⁻ z : UnitSphere d × Samples d T, f (z.1,(ξ,z.2))
          ∂((uniformSphere d).prod (sampleLaw d T)) ∂ρ := rfl
    _ = ∫⁻ z : UnitSphere d × Samples d T, ∫⁻ ξ, f (z.1,(ξ,z.2)) ∂ρ
          ∂((uniformSphere d).prod (sampleLaw d T)) := (lintegral_lintegral_swap hfD).symm
    _ = ∫⁻ z, f (e z) ∂(((uniformSphere d).prod (sampleLaw d T)).prod ρ) :=
      (lintegral_prod _ hfD).symm
    _ = ∫⁻ z, f z ∂((uniformSphere d).prod (ρ.prod (sampleLaw d T))) :=
      hp.lintegral_comp_emb e.measurableEmbedding f
    _ = _ := lintegral_prod _ hf

lemma seededSuccess_of_pointwise [NeZero d]
    (K : Ξ → FiniteKernelLearner d M T) (ρ : Measure Ξ) [SFinite ρ] (ε : ℝ)
    (hm : JointSuccessMeasurable K ρ ε)
    (hs : ∀ s, (2/3 : ℝ≥0∞) ≤ seededPointwiseSuccess K ρ ε s) :
    (2/3 : ℝ≥0∞) ≤ seededSuccess K ρ ε := by
  rw [seededSuccess_eq_integral_pointwise K ρ ε hm]
  calc
    _ = ∫⁻ _ : UnitSphere d, (2/3 : ℝ≥0∞) ∂uniformSphere d := by simp
    _ ≤ _ := lintegral_mono hs

end

universe u

lemma cap_memory_factor (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) :
    Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)) ≤ Real.exp ((C+32)*d) := by
  have hk : 0 < (d/16:ℕ) := by omega
  have hkR : (0:ℝ) < (d/16:ℕ) := by exact_mod_cast hk
  have hdk : d ≤ 32*(d/16) := by omega
  have hdkR : (d:ℝ) ≤ 32*(d/16:ℕ) := by exact_mod_cast hdk
  have hfrac : (M:ℝ)/(d/16:ℕ) ≤ 32*d := by
    rw [div_le_iff₀ hkR]
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at h ⊢
    exact h
  rw [Real.rpow_def_of_pos (by norm_num),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hnon : (0:ℝ) ≤ (M:ℝ)/(d/16:ℕ) := by positivity
  have hl := mul_le_mul_of_nonneg_right hlog hnon
  nlinarith

lemma cap_finite_to_asymptotic (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) (ε α : ℝ) (n : ℕ) (hε : 0 ≤ ε) :
    Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n ≤
      Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by
  have hbase := cap_memory_factor C hd hM
  have hfront : Real.exp (C*d) ≤ Real.exp ((C+32)*d) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have ht := mul_le_mul (mul_le_mul_of_nonneg_right hfront (Real.rpow_nonneg (by positivity : 0 ≤ ε/2) α))
    (pow_le_pow_left₀ (by positivity) hbase n) (by positivity) (by positivity)
  apply ht.trans_eq
  rw [← Real.exp_nat_mul]
  calc
    Real.exp ((C+32)*d)*(ε/2)^α*Real.exp ((n:ℝ)*((C+32)*d)) =
        (Real.exp ((C+32)*d)*Real.exp ((n:ℝ)*((C+32)*d)))*(ε/2)^α := by ring
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

lemma cap_ceil_cost {d T : ℕ} (hd : 32 ≤ d) :
    (d:ℝ)*(1+((T+d/16-1)/(d/16):ℕ)) ≤ 2*d+32*T := by
  let k := d/16
  let n := (T+k-1)/k
  have hk : 0 < k := by dsimp [k]; omega
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hdiv : n*k ≤ T+k := (Nat.div_mul_le_self _ _).trans (by omega)
  have hdivR : (n:ℝ)*k ≤ (T:ℝ)+k := by exact_mod_cast hdiv
  have hdR : (d:ℝ) ≤ 32*k := by exact_mod_cast (show d ≤ 32*k by dsimp [k]; omega)
  have hn : (n:ℝ) ≤ (T:ℝ)/k+1 := by
    have he := div_mul_cancel₀ (T:ℝ) hkR.ne'
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg (α := ℝ) d)
  have hdk : (d:ℝ)/(k:ℝ) ≤ 32 := (div_le_iff₀ hkR).mpr hdR
  have hT := mul_le_mul_of_nonneg_right hdk (Nat.cast_nonneg (α := ℝ) T)
  change (d:ℝ)*(1+(n:ℝ)) ≤ _
  calc
    _ ≤ (d:ℝ)*((T:ℝ)/k+2) := by nlinarith
    _ = (d:ℝ)/k*T+2*d := by ring
    _ ≤ _ := by linarith

lemma cap_accuracy_cost {d : ℕ} (hd : 3 ≤ d) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (ε/2)^(((d:ℝ)-1)/2) ≤ Real.exp (-(d:ℝ)*Real.log (1/ε)/3) := by
  have hdR : (3:ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 ≤ ((d:ℝ)-1)/2 := by linarith
  calc
    _ ≤ ε^(((d:ℝ)-1)/2) := Real.rpow_le_rpow (by positivity) (by linarith) ha
    _ ≤ ε^((d:ℝ)/3) := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)
    _ = _ := by
      rw [Real.rpow_def_of_pos hε,one_div,Real.log_inv]
      congr 1
      ring

end FiniteKernelLearner
end NoiselessRegression

end

end OAI
