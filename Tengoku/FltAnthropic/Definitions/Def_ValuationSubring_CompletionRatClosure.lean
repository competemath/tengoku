import Tengoku.Seed.Topology.Algebra.Field
import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic
import Tengoku.FltAnthropic.Definitions.Def_ValuationSubring_CompletionDecompositionAction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace ValuationSubring

variable (A : ValuationSubring (AlgebraicClosure ℚ))

def ratClosure : Subfield A.valuation.Completion :=
  (⊥ : Subfield A.valuation.Completion).topologicalClosure

/--
@isnad1 id=isclosed.0h1v.s9.234e17e663c8 from=translated src=- shape=bedde5e3 vocab=0d62ea6e
-/
theorem isClosed_ratClosure : IsClosed (ratClosure A : Set A.valuation.Completion) :=
  Subfield.isClosed_topologicalClosure _

/--
@isnad1 id=le.0h1v.s11.23f4f437f710 from=translated src=- shape=e583b966 vocab=c60ea502
-/
theorem bot_le_ratClosure : (⊥ : Subfield A.valuation.Completion) ≤ ratClosure A :=
  Subfield.le_topologicalClosure _

/--
@isnad1 id=eq.0h1v.s12.bd90c18c3a44 from=translated src=- shape=21a8812b vocab=d6ebd608
-/
theorem coe_ratClosure :
    (ratClosure A : Set A.valuation.Completion) = closure ((⊥ : Subfield A.valuation.Completion) : Set _) := rfl

/--
@isnad1 id=mem.0h2v.s10.3d55a22536d1 from=translated src=- shape=f77f766c vocab=151d3189
-/
@[simp] theorem ratCast_mem_ratClosure (q : ℚ) : (q : A.valuation.Completion) ∈ ratClosure A :=
  bot_le_ratClosure A (SubfieldClass.ratCast_mem _ q)

/--
@isnad1 id=mem.0h2v.s10.c50feadad944 from=translated src=- shape=32becd63 vocab=0034dd44
-/
@[simp] theorem natCast_mem_ratClosure (n : ℕ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  natCast_mem (ratClosure A) n

/--
@isnad1 id=mem.0h2v.s10.4f13da4e82bb from=translated src=- shape=32becd63 vocab=142d3db9
-/
@[simp] theorem intCast_mem_ratClosure (n : ℤ) : (n : A.valuation.Completion) ∈ ratClosure A :=
  intCast_mem (ratClosure A) n

/--
@isnad1 id=mem.0h2v.s11.0a61643e3b5f from=translated src=- shape=4284f4e4 vocab=ee7c5025
-/
theorem coe_ratCast_mem_ratClosure (q : ℚ) :
    ((q : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((q : AlgebraicClosure ℚ) : A.valuation.Completion) = (q : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (q : AlgebraicClosure ℚ)) = _
    rw [map_ratCast, map_ratCast]
  rw [this]; exact ratCast_mem_ratClosure A q

/--
@isnad1 id=mem.0h2v.s11.3a1440a7441e from=translated src=- shape=b209268d vocab=b680d4f6
-/
theorem coe_natCast_mem_ratClosure (n : ℕ) :
    ((n : AlgebraicClosure ℚ) : A.valuation.Completion) ∈ ratClosure A := by
  have : ((n : AlgebraicClosure ℚ) : A.valuation.Completion) = (n : A.valuation.Completion) := by
    show (UniformSpace.Completion.coeRingHom : WithVal A.valuation →+* A.valuation.Completion)
        ((WithVal.equiv A.valuation).symm (n : AlgebraicClosure ℚ)) = _
    rw [map_natCast, map_natCast]
  rw [this]; exact natCast_mem_ratClosure A n

end ValuationSubring

end
