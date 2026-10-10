import Tengoku.OpenaiMath.OAI.Analysis.Daugavet.WholeBallConcentration

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uIota

namespace ExactModuli.KW

abbrev infiniteCube := ℕ → unitInterval
abbrev infiniteCubeMeasure : Measure infiniteCube :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

lemma infinite_coordinate_mp (i : ℕ) :
    MeasurePreserving (fun ω : infiniteCube => ω i) infiniteCubeMeasure volume :=
  ⟨measurable_pi_apply i, Measure.infinitePi_map_eval _ i⟩

lemma finite_coordinates_mp {ι : Type uIota} [Fintype ι] (c : ι → ℕ) (hc : Function.Injective c) :
    MeasurePreserving (fun ω : infiniteCube => fun i => ω (c i)) infiniteCubeMeasure (cubeMeasure ι) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj hc, Measure.infinitePi_eq_pi]

end ExactModuli.KW

end

end OAI
