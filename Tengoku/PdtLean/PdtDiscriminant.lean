import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/stalex444/pdt-lean@00dddf1b15b2, `PdtDiscriminant.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

namespace PDT

open Polynomial AdjoinRoot Algebra Matrix

noncomputable section

/-- The cubic `X^3 - X - 1`.-/
def fc : ℚ[X] := X ^ 3 - X - 1

/--
@isnad1 id=monic.0h0v.s2.f3647d5403ea from=translated src=- shape=25b03439 vocab=69d2ae61
-/
lemma fc_monic : (fc).Monic := by
  unfold fc; monicity!

/-- K = ℚ[x]/(x³-x-1) as a ℚ-algebra, free of rank 3.-/
abbrev Kc := AdjoinRoot fc

/-- power basis-/
def pbc : PowerBasis ℚ Kc := powerBasis' fc_monic

/-! ## Quartic x⁴ − x − 1, discriminant −283 -/

/-- The quartic `X^4 - X - 1`.-/
def fq : ℚ[X] := X ^ 4 - X - 1

abbrev Kq := AdjoinRoot fq

end

end PDT
