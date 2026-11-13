import Tengoku.Seed.Data.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Entrywise subtraction of block matrices
-/

namespace Matrix
variable {R m n p q : Type*}

/-- Subtraction acts independently on the four blocks.
@isnad1 id=eq.0h13v.s7.f1753c03b49e from=translated src=- shape=f573c320 vocab=49fc1eec
-/
theorem fromBlocks_sub [Sub R] (A A' : Matrix m p R) (B B' : Matrix m q R)
    (C C' : Matrix n p R) (D D' : Matrix n q R) :
    fromBlocks A B C D - fromBlocks A' B' C' D' =
      fromBlocks (A - A') (B - B') (C - C') (D - D') := by
  ext i j
  cases i <;> cases j <;> rfl

end Matrix
