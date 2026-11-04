import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCoefficientMap
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceFrameLaws
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourcePeirceAttachment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms mapSource_reflection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_frameLaws` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SourceCoefficientMap

open AlbertLean.Triality CoordinateTensor StructuredCubic StructuredProduct
open SourceFrameLaws SourcePeirceAttachment

universe u v
variable {K : Type u} {L : Type v}
variable [Field K] [CharZero K] [Field L] [CharZero L]

/--
@isnad1 id=eq.0h5v.s6.f69884724dbf from=translated src=- shape=47357877 vocab=f74b892f
-/
theorem mapSource_reflection (f : K →+* L) (p x : JCoord K) :
    mapSource f (sourcePeirceReflection p x) =
      sourcePeirceReflection (mapSource f p) (mapSource f x) := by
  simp only [sourcePeirceReflection_formula, mapSource_sub, mapSource_add,
    mapSource_smul, mapSource_product, map_ofNat]

/--
@isnad1 id=laws.1h4v.s6.b35cefcbd785 from=translated src=- shape=6850c838 vocab=6752b327
-/
theorem mapSource_frameLaws (f : K →+* L) (P : Fin 3 → JCoord K)
    (hP : Laws P) : Laws (fun i => mapSource f (P i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [← mapSource_product, hP.idempotent]
  · intro i
    rw [mapSource_trace, hP.trace_one, map_one]
  · rw [← mapSource_add, ← mapSource_add, hP.sum_one, mapSource_one]

end AlbertLean.Generic.SourceCoefficientMap
