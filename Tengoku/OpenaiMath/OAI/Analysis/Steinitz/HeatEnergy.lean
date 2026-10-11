import Tengoku.OpenaiMath.OAI.Analysis.Steinitz.PathLaws

namespace OAI

/-! Survival-energy estimates and simultaneous diagonal separation. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators Pointwise
namespace GaussianKernel
variable {ι : Type*} [Fintype ι]

lemma pdf_scale {s : ℝ≥0} (hs : 0<s) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 (s^2*v) ((s:ℝ)*x) = (s:ℝ)⁻¹*gaussianPDFReal 0 v x := by
  have hs' : 0<(s:ℝ) := hs
  have he : 2*Real.pi*((s:ℝ)^2*(v:ℝ))=(s:ℝ)^2*(2*Real.pi*(v:ℝ)) := by ring
  unfold gaussianPDFReal
  simp only [sub_zero,NNReal.coe_mul,NNReal.coe_pow,he,Real.sqrt_mul (sq_nonneg (s:ℝ)),
    Real.sqrt_sq hs'.le,mul_inv_rev]
  have hx : -(((s:ℝ)*x)^2)/(2*((s:ℝ)^2*(v:ℝ))) = -(x^2)/(2*(v:ℝ)) := by
    rw [mul_pow]
    field_simp
  rw [hx]
  ring

lemma density_scale {s : ℝ≥0} (hs : 0<s) (v : ι → ℝ≥0) (x : EuclideanSpace ℝ ι) :
    density (fun i => s^2*v i) ((s:ℝ) • x) = ((s:ℝ)^(Fintype.card ι))⁻¹*density v x := by
  simp only [density,PiLp.smul_apply,smul_eq_mul,pdf_scale hs,Finset.prod_mul_distrib,
    Finset.prod_const,Finset.card_univ,inv_pow]

omit [Fintype ι] in
lemma pi_smul {T : Type*} (s : ℝ) (hs : s≠0) (D : Set (EuclideanSpace ℝ ι)) :
    (univ.pi (fun _ : T => s • D))=s • (univ.pi (fun _ : T => D)) := by
  ext p
  rw [mem_smul_set_iff_inv_smul_mem₀ hs]
  simp only [mem_pi,mem_univ,forall_const,Pi.smul_apply]
  exact forall_congr' fun t => mem_smul_set_iff_inv_smul_mem₀ hs D (p t)

end GaussianKernel

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal ComplexInnerProductSpace
namespace HeatL2
section Rate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma energy_smul (w : E → ℝ) (c : ℂ) (f : Lp ℂ 2 (volume : Measure E)) :
    energy w (c • f) = ‖c‖^2 * energy w f := by
  unfold energy
  rw [fourier_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c (𝓕 f)] with x hx
  simp only [hx, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

lemma supported_smul (D : Set E) {f : Lp ℂ 2 (volume : Measure E)}
    (hf : f ∈ supported D) (c : ℂ) : c • f ∈ supported D := by
  filter_upwards [hf, Lp.coeFn_smul c f] with x hx he hn
  simp only [he, Pi.smul_apply, hx hn, smul_zero]

end Rate
end HeatL2

end

section

open Set Finset

namespace EuclideanSteinitz

end EuclideanSteinitz

end

section

open MeasureTheory FourierTransform Set Filter ComplexConjugate
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

end

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped ENNReal NNReal ComplexInnerProductSpace
namespace HeatL2
namespace Diagonal
variable {ι : Type*} [Fintype ι]

noncomputable def coordSymbol (i : ι) (ξ : EuclideanSpace ℝ ι) : ℝ := (2*Real.pi*ξ i)^2
omit [Fintype ι] in
lemma coordSymbol_nonneg (i : ι) (ξ : EuclideanSpace ℝ ι) : 0 ≤ coordSymbol i ξ := sq_nonneg _
omit [Fintype ι] in
lemma coordSymbol_continuous (i : ι) : Continuous (coordSymbol i) := by
  unfold coordSymbol
  fun_prop

def Bound (D : Set (EuclideanSpace ℝ ι)) (hD : MeasurableSet D) (c : ℝ) : Prop :=
  ∀ v : ι → ℝ≥0, Real.exp (-(c/2) * ∑ i, (v i:ℝ)) ≤
    ‖compressedHeat D hD (GaussianKernel.symbol v)
      (GaussianKernel.symbol_continuous v).aestronglyMeasurable (GaussianKernel.symbol_nonneg v)‖

end Diagonal
end HeatL2

end

section

open MeasureTheory Set Filter
open scoped NNReal Topology
namespace HeatL2.Diagonal
variable {ι : Type*} [Fintype ι]

end HeatL2.Diagonal

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace NNReal ENNReal Pointwise
namespace GaussianAR
open GaussianKernel HeatL2 GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

end GaussianAR

end

end OAI
