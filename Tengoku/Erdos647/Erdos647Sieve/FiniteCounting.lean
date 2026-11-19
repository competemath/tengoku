/-
Unconditional finite counting, using the accepted budget transfer and the new
finite moment implementation. New source, not compiled in the assistant environment.
No claim of an asymptotic endpoint or a resolution of Erdős #647 is made.
-/
import Tengoku.Erdos647.Erdos647Sieve.FiniteMoment
import Tengoku.Erdos647.Erdos647Sieve.BudgetConsequences

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace Erdos647Sieve

/--
@isnad1 id=finiteco.0h0v.s0.3716a43f0754 from=translated src=- shape=45709ebd vocab=3716a43f
-/
theorem finiteCounting : FiniteCountingClaim :=
  finiteCounting_of_finiteMoment finiteMoment

end Erdos647Sieve
