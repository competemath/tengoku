import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.AlbertRawFrameIdeal
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceFrameLaws

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sourceFrameFamily_iff_f0Raw` (it only prints; the queue checks the axioms of every declaration). -/

/-! Field-valued semantic bridge from the independent F0 equations to the
actual recovered source product. -/

noncomputable section
namespace AlbertLean.Generic.AlbertRawSourceDictionary

open scoped BigOperators
open AlbertLean.Triality CoordinateTensor StructuredCubic StructuredProduct
open AlbertLean.Triality.GenericCoordinates
open AlbertLean.Comparison.GenericF0
open AlbertLean.Comparison.GenericProductTransport
open AlbertRawFrameIdeal SourceFrameLaws

variable {K : Type*} [Field K] [CharZero K]

def toF0Family (E : Fin 3 → Fin 3 → JCoord K) :
    Fin 3 → Fin 3 → F0Coord K :=
  fun r i => structuredEquivK K (E r i)

theorem sourceFrameFamily_iff_f0Raw
    (E : Fin 3 → Fin 3 → JCoord K) :
    (∀ r, Laws (E r)) ↔ IsRawFrameFamily (toF0Family E) := by
  constructor
  · intro hE
    refine ⟨?_, ?_, ?_⟩
    · intro r i
      dsimp only [toF0Family]
      rw [← GenericStructuredProductAgreesWithF0]
      exact congrArg (structuredEquivK K) ((hE r).idempotent i)
    · intro r i
      dsimp only [toF0Family]
      rw [← sourceTrace_agrees_with_f0K]
      exact (hE r).trace_one i
    · intro r
      change ∑ i : Fin 3, structuredEquivK K (E r i) = f0OneK
      rw [← structuredEquivK_sourceOne]
      simpa [Fin.sum_univ_succ, map_add, add_assoc] using
        congrArg (structuredEquivK K) ((hE r).sum_one)
  · intro hE r
    refine ⟨?_, ?_, ?_⟩
    · intro i
      apply (structuredEquivK K).injective
      rw [GenericStructuredProductAgreesWithF0]
      exact hE.idempotent r i
    · intro i
      rw [sourceTrace_agrees_with_f0K]
      exact hE.trace_one r i
    · apply (structuredEquivK K).injective
      rw [map_add, map_add, structuredEquivK_sourceOne]
      simpa [toF0Family, Fin.sum_univ_succ, add_assoc] using hE.sum_one r

end AlbertLean.Generic.AlbertRawSourceDictionary
