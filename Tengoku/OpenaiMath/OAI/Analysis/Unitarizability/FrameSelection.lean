import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.SignMatrix
import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.FrameParameters

namespace OAI

/-! The finite union bound chooses one sign matrix that passes every real
net test for every injective subfamily of the prescribed size. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset

theorem embedding_card_le (n p : ℕ) : Fintype.card (Fin p ↪ Fin n) ≤ n^p := by
  have h := Fintype.card_le_of_injective (fun e : Fin p ↪ Fin n => (e : Fin p → Fin n))
    (by intro e f h; apply Function.Embedding.ext; intro i; exact congrFun h i)
  simpa using h

end SignMatrix
end Dixmier

end

end OAI
