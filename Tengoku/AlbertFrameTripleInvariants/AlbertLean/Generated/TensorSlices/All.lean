import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord00
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord01
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord02
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord03
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord04
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord05
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord06
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord07
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord08
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord09
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord10
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord11
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord12
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord13
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord14
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord15
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord16
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord17
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord18
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord19
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord20
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord21
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord22
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord23
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord24
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord25
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generated.TensorSlices.Coord26

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AlbertLean.Generated

set_option maxHeartbeats 30000000
set_option maxRecDepth 100000

theorem tensorProduct_eq_productForm (x y : Coord) :
    tensorProduct x y = productForm x y := by
  funext k
  fin_cases k
  exact tensorProduct_coord_00_slice x y
  exact tensorProduct_coord_01_slice x y
  exact tensorProduct_coord_02_slice x y
  exact tensorProduct_coord_03_slice x y
  exact tensorProduct_coord_04_slice x y
  exact tensorProduct_coord_05_slice x y
  exact tensorProduct_coord_06_slice x y
  exact tensorProduct_coord_07_slice x y
  exact tensorProduct_coord_08_slice x y
  exact tensorProduct_coord_09_slice x y
  exact tensorProduct_coord_10_slice x y
  exact tensorProduct_coord_11_slice x y
  exact tensorProduct_coord_12_slice x y
  exact tensorProduct_coord_13_slice x y
  exact tensorProduct_coord_14_slice x y
  exact tensorProduct_coord_15_slice x y
  exact tensorProduct_coord_16_slice x y
  exact tensorProduct_coord_17_slice x y
  exact tensorProduct_coord_18_slice x y
  exact tensorProduct_coord_19_slice x y
  exact tensorProduct_coord_20_slice x y
  exact tensorProduct_coord_21_slice x y
  exact tensorProduct_coord_22_slice x y
  exact tensorProduct_coord_23_slice x y
  exact tensorProduct_coord_24_slice x y
  exact tensorProduct_coord_25_slice x y
  exact tensorProduct_coord_26_slice x y

end AlbertLean.Generated
