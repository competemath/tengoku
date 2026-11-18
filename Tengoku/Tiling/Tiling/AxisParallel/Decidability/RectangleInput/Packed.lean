import Tengoku.Tiling.Tiling.AxisParallel.Decidability.RectangleInput.Coarse
import Tengoku.Tiling.Tiling.AxisParallel.Terminal.ExecutableInput

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Packed runtime region input

The frontend returns finite lists of point labels and cell selectors. Each
selector chooses the first intrinsic vertex on a cell's supporting coordinate
line. The dependent production `RegionCode` is recovered from these lists once
the vertex list is nonempty; malformed selectors have a fixed modular default.
-/

set_option autoImplicit false

open Tiling.AxisParallel.SetFormulation

namespace Tiling.AxisParallel.Decidability.RectangleInput

abbrev PackedRegion := List PointLabel × List Cell

def firstVertex (input : TableInput) (vertical : Bool) (i : ℕ) : ℕ :=
  (vertexLabels input).findIdx fun p => (bif vertical then p.2 else p.1) == i

def encodedCell (input : TableInput) (c : Cell) : Cell :=
  ((firstVertex input false c.1.1, firstVertex input false c.1.2),
    (firstVertex input true c.2.1, firstVertex input true c.2.2))

def packedRegion (input : TableInput) : PackedRegion :=
  (vertexLabels input, (coarseCells input).map (encodedCell input))

/--
@isnad1 id=and.1h3v.s6.a610957ebf04 from=translated src=- shape=c6367a95 vocab=f2a24969
-/
theorem firstVertex_spec {input : TableInput} {vertical : Bool} {i : ℕ}
    (hi : usedLevel input vertical i = true) :
    firstVertex input vertical i < (vertexLabels input).length ∧
      (bif vertical then
        ((vertexLabels input).getD (firstVertex input vertical i) (0, 0)).2
      else ((vertexLabels input).getD (firstVertex input vertical i) (0, 0)).1) = i := by
  have hex : ∃ p ∈ vertexLabels input, (bif vertical then p.2 else p.1) == i := by
    simpa only [beq_iff_eq] using usedLevel_eq_true.mp hi
  have hlt : firstVertex input vertical i < (vertexLabels input).length :=
    List.findIdx_lt_length_of_exists hex
  refine ⟨hlt, ?_⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact of_decide_eq_true (List.findIdx_getElem (w := hlt))

/-- Interpret packed selectors in the production finite input type. The modular
fallback affects malformed data only.-/
def regionCode (P : PackedRegion) (hP : 0 < P.1.length) :
    Tiling.AxisParallel.Terminal.Executable.RegionCode where
  vertexCount := P.1.length
  cellCount := P.2.length
  originVertex := ⟨0, hP⟩
  leftVertex e := ⟨(P.2.getD e (0, 0)).1.1 % P.1.length, Nat.mod_lt _ hP⟩
  rightVertex e := ⟨(P.2.getD e (0, 0)).1.2 % P.1.length, Nat.mod_lt _ hP⟩
  bottomVertex e := ⟨(P.2.getD e (0, 0)).2.1 % P.1.length, Nat.mod_lt _ hP⟩
  topVertex e := ⟨(P.2.getD e (0, 0)).2.2 % P.1.length, Nat.mod_lt _ hP⟩

end Tiling.AxisParallel.Decidability.RectangleInput
