import Tengoku.OpenaiMath.OAI.Analysis.LiebThirring.SpectralTrials

namespace OAI

universe u180

noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 ConstantProof MeasureTheory Set Filter
open scoped Topology

lemma action_constant_eq_sharp {σ : ℝ} (hσ : 0 < σ) :
    actionYoungConstant σ / betaAction σ = sharpConstant (σ+1/2) := by
  rw [actionYoungConstant,young_over_beta hσ,sharpConstant,semiclassicalConstant]
  have h1 : σ+1/2-1/2 = σ := by ring
  have h2 : σ+1/2+1/2 = σ+1 := by ring
  have h3 : σ+1/2+1 = σ+3/2 := by ring
  have h4 : σ+1/2+3/2 = σ+2 := by ring
  rw [h1,h2,h3,h4]
  ring

end SharpLiebThirring.SpectralProof

end

noncomputable section
namespace SharpLiebThirring.SpectralProof
open SobolevProof SobolevProof.C1L2 MeasureTheory Set Module

end SharpLiebThirring.SpectralProof

end

end OAI
