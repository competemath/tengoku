import Tengoku.OpenaiMath.OAI.Analysis.Littlewood.AlmostSign

namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators
lemma unitCircle_parameter {z : ℂ} (hz : ‖z‖=1) :
    ∃ t∈Set.Icc (0:ℝ) 1, z=realPhase (2*Real.pi*t) := by
  let Z : Circle := ⟨z,by change dist z 0=1; simpa using hz⟩
  let u := (AddCircle.homeomorphCircle (T := (1:ℝ)) one_ne_zero).symm Z
  let t := AddCircle.equivIco (1:ℝ) 0 u
  refine ⟨t.val,⟨t.property.1,by simpa using t.property.2.le⟩,?_⟩
  have hu : (t.val : UnitAddCircle)=u := AddCircle.coe_equivIco
  have hs : Circle.exp (2*Real.pi*t.val)=Z := by
    rw [show 2*Real.pi*t.val=2*Real.pi/(1:ℝ)*t.val by ring]
    rw [← AddCircle.toCircle_apply_mk,hu,← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact (AddCircle.homeomorphCircle one_ne_zero).apply_symm_apply Z
  have hcoe := congrArg (fun w : Circle ↦ (w : ℂ)) hs
  simpa only [Circle.coe_exp,realPhase,mul_comm] using hcoe.symm

lemma littlewood_phase {N : ℕ} (X : Fin N → ℝ) (t : ℝ) :
    littlewoodValue X (realPhase (2*Real.pi*t))=
      ∑ k : Fin N, (X k : ℂ)*realPhase (2*Real.pi*t*k) := by
  unfold littlewoodValue
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  rw [realPhase,← Complex.exp_nat_mul,realPhase]
  congr 1
  push_cast
  ring

end
end AsymptoticallyMinimalLittlewood
namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped Topology
open Filter

lemma entropy_small_defect {δ N u : ℝ} (hδ : 0<δ) (hδ20 : δ<1/20)
    (hN : 0<N) (hu : 0≤u) (hub : u≤4*δ*N) :
    u*Real.log (80*N/u)≤4*δ*N*Real.log (20/δ) := by
  have hlog2 : (1/2:ℝ)≤Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at this ⊢
    exact this
  have hL : 1≤Real.log (20/δ) := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4)
      (show 4≤20/δ by apply (le_div_iff₀ hδ).mpr; linarith)
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow] at hh
    norm_num at hh
    linarith
  by_cases hz : u=0
  · rw [hz]
    simp only [zero_mul]
    positivity
  have hup : 0<u := lt_of_le_of_ne hu (Ne.symm hz)
  have hb : 0<4*δ*N := by positivity
  have hsplit : Real.log (80*N/u)=Real.log (20/δ)+Real.log ((4*δ*N)/u) := by
    rw [← Real.log_mul (by positivity : 20/δ≠0) (by positivity : (4*δ*N)/u≠0)]
    congr 1
    field_simp
    ring
  have hs : u*Real.log ((4*δ*N)/u)≤4*δ*N-u := by
    calc
      _ ≤ u*((4*δ*N)/u-1) := mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos (by positivity)) hu
      _ = _ := by field_simp
  have hm := mul_le_mul_of_nonneg_right hub (sub_nonneg.mpr hL)
  rw [hsplit,mul_add]
  nlinarith

lemma small_delta_budget {η : ℝ} (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/20 ∧
      Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ))<1+η/2 := by
  let f (x : ℝ) := Real.sqrt ((1+x)^3/(1-x))+
    393216*Real.sqrt (x*Real.log 20-x*Real.log x)
  have hf : ContinuousAt f 0 := by
    apply ContinuousAt.add
    · exact Real.continuous_sqrt.continuousAt.comp
        (((continuousAt_const.add continuousAt_id).pow 3).div
          (continuousAt_const.sub continuousAt_id) (by norm_num))
    · exact continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp
        ((continuousAt_id.mul continuousAt_const).sub Real.continuous_mul_log.continuousAt))
  have hf0 : f 0=1 := by norm_num [f]
  obtain ⟨r,hr,hh⟩ := Metric.continuousAt_iff.mp hf (η/2) (by positivity)
  let δ := min (r/2) (1/40)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  have hδ20 : δ<1/20 := (min_le_right _ _).trans_lt (by norm_num)
  have hδr : δ<r := (min_le_left _ _).trans_lt (by linarith)
  have hd : dist δ (0:ℝ)<r := by simpa only [Real.dist_eq,sub_zero,abs_of_pos hδ] using hδr
  have hval := hh hd
  rw [hf0,Real.dist_eq] at hval
  have he : f δ=Real.sqrt ((1+δ)^3/(1-δ))+393216*Real.sqrt (δ*Real.log (20/δ)) := by
    dsimp [f]
    rw [Real.log_div (by norm_num : (20:ℝ)≠0) hδ.ne',mul_sub]
  refine ⟨δ,hδ,hδ20,?_⟩
  rw [he] at hval
  have := (abs_lt.mp hval).2
  linarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

lemma defect_from_energy {N : ℕ} (_hN : 1≤N) {δ : ℝ} (X : Fin N → ℝ)
    (hX : ∀ k, |X k|≤1)
    (hE : (1-8*δ)*(N : ℝ)≤∑ k, (X k)^2) :
    0≤defectMass X ∧ defectMass X≤4*δ*N := by
  have hμ : 0≤defectMass X := div_nonneg
    (Finset.sum_nonneg (fun k _ ↦ sub_nonneg.mpr (hX k))) (by norm_num)
  have hs : (∑ k, (1-|X k|))≤∑ k, (1-(X k)^2) := by
    apply Finset.sum_le_sum
    intro k _
    have hh := mul_nonneg (abs_nonneg (X k)) (sub_nonneg.mpr (hX k))
    nlinarith [sq_abs (X k)]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one] at hs
  refine ⟨hμ,?_⟩
  dsimp [defectMass]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one]
  nlinarith

end
end AsymptoticallyMinimalLittlewood

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open scoped BigOperators Topology
open Filter

end
end AsymptoticallyMinimalLittlewood

end OAI
