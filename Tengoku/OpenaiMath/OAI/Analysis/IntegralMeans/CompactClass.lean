import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Distortion

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

instance : LocallyCompactSpace disk := (show IsOpen disk from Metric.isOpen_ball).locallyCompactSpace

lemma compact_closure_of_disk_bounds (S : Set C(disk,ℂ))
    (hLip : ∀ R : ℝ, R < 1 → ∃ C : ℝ, ∀ g ∈ S, ∀ z w : disk,
      ‖(z : ℂ)‖ ≤ R → ‖(w : ℂ)‖ ≤ R → ‖g z-g w‖ ≤ C*‖(z : ℂ)-(w : ℂ)‖)
    (hBd : ∀ z : disk, ∃ C : ℝ, ∀ g ∈ S, ‖g z‖ ≤ C) :
    IsCompact (closure S) := by
  let : T2Space (UniformOnFun disk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have heq : Equicontinuous (fun g : S => fun z : disk => g.1 z) := by
    intro z
    obtain ⟨R,hzR,hR⟩ := exists_between (show ‖(z : ℂ)‖ < 1 by simpa [disk] using z.2)
    obtain ⟨C,hC⟩ := hLip R hR
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : disk => C*dist (z : ℂ) (w : ℂ))
    · simpa using (tendsto_const_nhds (x := C)).mul
        ((tendsto_const_nhds (x := (z : ℂ))).dist (continuous_subtype_val.tendsto z))
    · have hn : ∀ᶠ w : disk in 𝓝 z, ‖(w : ℂ)‖ < R :=
        (continuous_norm.comp continuous_subtype_val).continuousAt (Iio_mem_nhds hzR)
      filter_upwards [hn] with w hw g
      simpa [dist_eq_norm] using hC g.1 g.2 z w hzR.le hw.le
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun g : C(disk,ℂ) => fun z : disk => g z)
    (𝔖 := {K | IsCompact K}) (fun _ h => h)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K _
    exact heq.equicontinuousOn K
  · intro K _ z _
    obtain ⟨C,hC⟩ := hBd z
    exact ⟨Metric.closedBall 0 C,isCompact_closedBall _ _,by simpa using hC⟩

def diskExtend (g : C(disk,ℂ)) (z : ℂ) : ℂ :=
  by classical exact if hz : z ∈ disk then g ⟨z,hz⟩ else 0

@[simp] lemma diskExtend_apply (g : C(disk,ℂ)) (z : disk) : diskExtend g z = g z := by
  simp [diskExtend,z.2]

lemma diskExtend_convergence.{u_1} {ι : Type u_1} {l : Filter ι}
    {g : ι → C(disk,ℂ)} {f : C(disk,ℂ)} (h : Tendsto g l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => diskExtend (g i)) (diskExtend f) l disk := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,diskExtend_apply] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

def diskSchlichtSet : Set C(disk,ℂ) := {g | Schlicht (diskExtend g)}

def DiskClass := diskSchlichtSet

instance : TopologicalSpace DiskClass := inferInstanceAs (TopologicalSpace diskSchlichtSet)

lemma differentiableOn_iteratedDeriv_disk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) disk := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv (show IsOpen disk from Metric.isOpen_ball)

lemma tendstoLocallyUniformlyOn_iteratedDeriv_disk.{u_1} {ι : Type u_1} {l : Filter ι}
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn f g l disk)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) disk) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l disk := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => differentiableOn_iteratedDeriv_disk h n))
      (show IsOpen disk from Metric.isOpen_ball)

def diskClassJet (n : ℕ) (g : DiskClass) : C(disk,ℂ) :=
  ⟨fun z => iteratedDeriv n (diskExtend g.1) z,
    continuousOn_iff_continuous_domRestrict.mp
      (differentiableOn_iteratedDeriv_disk g.2.1.1 n).continuousOn⟩

lemma continuous_diskClassJet (n : ℕ) : Continuous (diskClassJet n) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have h := tendstoLocallyUniformlyOn_iteratedDeriv_disk
    (diskExtend_convergence (continuous_subtype_val.tendsto g))
    (Eventually.of_forall (fun f : DiskClass => f.2.1.1)) n
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp h

lemma continuous_diskClassJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × disk => iteratedDeriv n (diskExtend p.1.1) p.2) :=
  continuous_eval.comp ((continuous_diskClassJet n).prodMap continuous_id)

end Brennan

end

end OAI
