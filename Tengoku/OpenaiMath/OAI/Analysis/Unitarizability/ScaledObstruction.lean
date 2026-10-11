import Tengoku
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.SumObstruction

namespace OAI

noncomputable section
namespace Dixmier
namespace KernelObstruction
variable {G K : Type*} [Group G] [Fintype K]

lemma coefficients_real_smul (t : ℝ) (B : Fibre K →L[ℂ] Fibre K) :
    coefficients (t • B) = t • coefficients B := by
  ext ab
  rfl

end KernelObstruction
namespace DirectSumObstruction
open Filter
variable {G : Type*} [Group G]

end DirectSumObstruction

end Dixmier
end

end OAI
