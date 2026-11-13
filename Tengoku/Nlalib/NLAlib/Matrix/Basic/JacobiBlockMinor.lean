import Tengoku.Nlalib.NLAlib.Matrix.Basic.ComplementaryRank
import Tengoku.Nlalib.NLAlib.Matrix.Basic.Gram
import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Jacobi's complementary-minor identity for block coordinates

Singular selected blocks have singular complementary inverse blocks by the
right-nullity law. The nonsingular case is the Schur inverse formula.
This includes all singular subminors and empty blocks without limits.
Horn–Johnson 2013, §§0.7.5–0.7.6 and 0.8.4.
-/

noncomputable section
open scoped Matrix
namespace NLAlib
private def complementEquiv (p q : Type*) : {s : p ⊕ q // ¬s.isLeft} ≃ q :=
  (Equiv.subtypeEquivRight (fun s : p ⊕ q => by cases s <;> simp)).trans Equiv.sumIsRight

end NLAlib
