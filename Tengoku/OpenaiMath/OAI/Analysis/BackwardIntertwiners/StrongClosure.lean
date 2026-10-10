import Tengoku.OpenaiMath.OAI.Analysis.BackwardIntertwiners.DiagonalSymbols

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

open scoped Classical

lemma fiber_norm_sq (v : Fiber) : ‖v‖^2 = ∑' j, ‖v j‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) v
lemma fiber_tendsto_zero_of_dominated {ι : Type*} {l : Filter ι} (v : ι → Fiber) (b : ℤ → ℝ)
    (hb : Summable (fun j => b j^2))
    (hB : ∀ n j, ‖v n j‖ ≤ b j)
    (hlim : ∀ j, Tendsto (fun n => v n j) l (𝓝 0)) :
    Tendsto v l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun n => ‖v n‖^2) l (𝓝 0) := by
    simp_rw [fiber_norm_sq]
    simpa using tendsto_tsum_of_dominated_convergence (g:=fun _ : ℤ => (0:ℝ)) hb
      (fun j => by simpa using (hlim j).norm.pow 2)
      (Filter.Eventually.of_forall fun n j => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB n j) 2)
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
    using Real.continuous_sqrt.continuousAt.tendsto.comp hi

lemma L2_integrable_bound_sq (f : GlobalHilbert) (C : ℝ) :
    Integrable (fun x => (C*‖f x‖)^2) baseMeasure := by
  have hf : Integrable (fun x => ‖f x‖^2) baseMeasure :=
    (Lp.memLp f).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)
  simpa only [mul_pow] using hf.const_mul (C^2)

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [completeSpace : CompleteSpace H]

def strongOperatorTopology : TopologicalSpace (H →L[ℂ] H) :=
  TopologicalSpace.induced (fun T : H →L[ℂ] H => (fun v : H => T v)) inferInstance

def StronglyClosed (A : StarSubalgebra ℂ (H →L[ℂ] H)) : Prop :=
  @IsClosed (H →L[ℂ] H) strongOperatorTopology A

omit completeSpace in
lemma strong_continuous_apply [CompleteSpace H] (v : H) :
    @Continuous (H →L[ℂ] H) H strongOperatorTopology inferInstance (fun T => T v) := by
  let := strongOperatorTopology (H:=H)
  exact (continuous_apply v).comp continuous_induced_dom

lemma StronglyClosed.mem_of_tendsto {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : StronglyClosed A) {ι : Type*} {l : Filter ι} [l.NeBot]
    {T : ι → H →L[ℂ] H} {S : H →L[ℂ] H}
    (hT : ∀ᶠ i in l, T i ∈ A) (hlim : ∀ v, Tendsto (fun i => T i v) l (𝓝 (S v))) :
    S ∈ A := by
  let := strongOperatorTopology (H:=H)
  refine IsClosed.mem_of_tendsto hA (f:=T) ?_ hT
  change Tendsto T l (@nhds (H →L[ℂ] H) (TopologicalSpace.induced _ _) S)
  rw [nhds_induced,Filter.tendsto_comap_iff]
  exact tendsto_pi_nhds.mpr hlim

def strongGenerated (s : Set (H →L[ℂ] H)) : StarSubalgebra ℂ (H →L[ℂ] H) :=
  sInf {A | StronglyClosed A ∧ s ⊆ A}
lemma mem_strongGenerated {s : Set (H →L[ℂ] H)} {T : H →L[ℂ] H} :
    T ∈ strongGenerated s ↔ ∀ A : StarSubalgebra ℂ (H →L[ℂ] H),
      StronglyClosed A → s ⊆ A → T ∈ A := by
  simp [strongGenerated,StarSubalgebra.mem_sInf]
lemma subset_strongGenerated (s : Set (H →L[ℂ] H)) : s ⊆ strongGenerated s := by
  intro T hT
  exact mem_strongGenerated.mpr fun _ _ hs => hs hT
lemma strongGenerated_le {s : Set (H →L[ℂ] H)} {A : StarSubalgebra ℂ (H →L[ℂ] H)}
    (hA : StronglyClosed A) (hs : s ⊆ A) : strongGenerated s ≤ A :=
  fun _ hT => mem_strongGenerated.mp hT A hA hs
lemma strongGenerated_closed (s : Set (H →L[ℂ] H)) : StronglyClosed (strongGenerated s) := by
  let := strongOperatorTopology (H:=H)
  have he : (strongGenerated s : Set (H →L[ℂ] H)) =
      ⋂ A : StarSubalgebra ℂ (H →L[ℂ] H), ⋂ (_ : StronglyClosed A ∧ s ⊆ A), (A : Set _) := by
    ext T
    simp [mem_strongGenerated]
  rw [StronglyClosed,he]
  exact isClosed_iInter fun A => isClosed_iInter fun h => h.1
lemma strongGenerated_mono {s t : Set (H →L[ℂ] H)} (hst : s ⊆ t) :
    strongGenerated s ≤ strongGenerated t :=
  strongGenerated_le (strongGenerated_closed t) (hst.trans (subset_strongGenerated t))

lemma strong_centralizer_closed (s : Set (H →L[ℂ] H)) :
    StronglyClosed (StarSubalgebra.centralizer ℂ s) := by
  let := strongOperatorTopology (H:=H)
  have he : (StarSubalgebra.centralizer ℂ s : Set (H →L[ℂ] H)) =
      ⋂ A ∈ s ∪ star s, ⋂ v : H, {T | A (T v) = T (A v)} := by
    ext T
    change (∀ A ∈ s ∪ star s, A*T=T*A) ↔ _
    simp only [mem_iInter,mem_ofPred_eq]
    exact forall₂_congr fun A hA => ⟨fun h v => DFunLike.congr_fun h v,
      fun h => ContinuousLinearMap.ext h⟩
  rw [StronglyClosed,he]
  exact isClosed_iInter fun A => isClosed_iInter fun _ => isClosed_iInter fun v =>
    isClosed_eq (A.continuous.comp (strong_continuous_apply v)) (strong_continuous_apply (A v))

lemma strongGenerated_commutative {s : Set (H →L[ℂ] H)}
    (hs : ∀ A ∈ s, IsSelfAdjoint A) (hc : ∀ A ∈ s, ∀ B ∈ s, A*B=B*A) :
    ∀ A ∈ strongGenerated s, ∀ B ∈ strongGenerated s, A*B=B*A := by
  have hle : strongGenerated s ≤ StarSubalgebra.centralizer ℂ s := by
    apply strongGenerated_le (strong_centralizer_closed s)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    exact ⟨hc A hA B hB, by rw [(hs A hA).star_eq]; exact hc A hA B hB⟩
  have hle' : strongGenerated s ≤ StarSubalgebra.centralizer ℂ (strongGenerated s : Set _) := by
    apply strongGenerated_le (strong_centralizer_closed _)
    intro B hB
    apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
    intro A hA
    refine ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle hA) B hB).1.symm, ?_⟩
    exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle ((strongGenerated s).star_mem' hA)) B hB).1.symm
  intro A hA B hB
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (hle' hB) A hA).1

end
end BackwardIntertwiners

end OAI
