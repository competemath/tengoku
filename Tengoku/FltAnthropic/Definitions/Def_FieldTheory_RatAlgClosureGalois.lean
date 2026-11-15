import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.FieldTheory.Galois.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/--
@isnad1 id=isgalois.0h0v.s4.b04052bb8761 from=translated src=- shape=3905abf2 vocab=49029860
-/
instance AlgebraicClosure.Rat.isGalois :
    @IsGalois ℚ _ (AlgebraicClosure ℚ) _ DivisionRing.toRatAlgebra :=
  @IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ) _ _ (AlgebraicClosure.instAlgebra ℚ) _ _
