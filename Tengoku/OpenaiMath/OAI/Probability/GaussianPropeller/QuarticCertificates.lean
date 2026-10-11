import Tengoku.OpenaiMath.OAI.Probability.GaussianPropeller.FourReduction

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

noncomputable def quartic (r:ℝ) := (3/5:ℝ)*r^4+(237/500:ℝ)*r^2+(3679/40000:ℝ)
noncomputable def small (r:ℝ) := (217/500:ℝ)*r+(3/20:ℝ)*r^2
noncomputable def large (r:ℝ) := (13/20:ℝ)*r^2+(9/100:ℝ)

lemma quartic_mono : MonotoneOn quartic (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  have h4:=pow_le_pow_left₀ ha hab 4
  unfold quartic; linarith only [h2,h4]
lemma small_mono : MonotoneOn small (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold small; linarith only [h2,hab]
lemma large_mono : MonotoneOn large (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold large; linarith only [h2]

end GaussianPropeller.FourCertificates

end OAI
