/-
Copyright (c) 2026 Jukka Suomela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jukka Suomela
-/
module

public import Tengoku.LeanPool.LeanPool.TwoColoringOneRound.LowerBound.N1000000StructureConstants
public import Tengoku

/-!
# LeanPool.TwoColoringOneRound.LowerBound.N1000000MaskAtFacts
-/

@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000MaskAtFacts

open Distributed2Coloring.LowerBound.N1000000StructureConstants

/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev Mask := Distributed2Coloring.LowerBound.Mask
/-- Imported auxiliary declaration for the 2-coloring one-round formalization. -/
abbrev DirIdx := N1000000StructureConstants.DirIdx

/--
@isnad1 id=eq.0h3v.s6.4756f4fef7e3 from=translated src=- shape=85eb199a vocab=7824aa74
-/
theorem maskAt_testBit_eq_decide_colMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (colMatch (maskAt d) j = some i) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

/--
@isnad1 id=eq.0h3v.s6.4a5b04f4487f from=translated src=- shape=6c0ba89b vocab=8e5675a0
-/
theorem maskAt_testBit_eq_decide_rowMatch (d : DirIdx) (i j : Fin 3) :
    (maskAt d).testBit (i.1 * 3 + j.1) = decide (rowMatch (maskAt d) i = some j) := by
  fin_cases d <;> fin_cases i <;> fin_cases j <;> decide

end N1000000MaskAtFacts

end Distributed2Coloring.LowerBound
