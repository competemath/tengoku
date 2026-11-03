import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCoefficientMap
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceVectorPairDephase

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms mapV_nV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapV_BV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapV_evenV` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms mapSource_v` (it only prints; the queue checks the axioms of every declaration). -/

/-! Literal coefficient naturality needed to move a chosen V reflection word
through a common finite-root extension. No arbitrary-Aut extension assumed. -/
noncomputable section
namespace AlbertLean.Generic.SourceVectorCoefficientMap
open AlbertLean.Triality ExteriorSix CoordinateTensor StructuredCubic
open SourceEvenReflections SourceVectorPairDephase
open SourceCoefficientMap
universe u v w
variable {K : Type u} {L : Type v} {M : Type w}
variable [Field K] [CharZero K] [Field L] [CharZero L] [Field M] [CharZero M]

def mapV (f : K →+* L) (x : VCoord K) : VCoord L :=
  { r := f x.r, z := f x.z, omega := fun i => f (x.omega i) }

@[simp] theorem mapV_comp (g : L →+* M) (f : K →+* L) (x : VCoord K) :
    mapV g (mapV f x) = mapV (g.comp f) x := rfl

@[simp] theorem mapV_sub (f : K →+* L) (x y : VCoord K) :
    mapV f (x-y) = mapV f x - mapV f y := by
  ext <;> simp [mapV]

@[simp] theorem mapV_smul (f : K →+* L) (a : K) (x : VCoord K) :
    mapV f (a • x) = f a • mapV f x := by
  ext <;> simp [mapV]

@[simp] theorem mapV_nV (f : K →+* L) (x : VCoord K) :
    nV (mapV f x) = f (nV x) := by
  simp [nV, pf_coordinate, mapV]

@[simp] theorem mapV_BV (f : K →+* L) (x y : VCoord K) :
    BV (mapV f x) (mapV f y) = f (BV x y) := by
  simp [BV, BW, mapV]

@[simp] theorem mapV_reflect (f : K →+* L) (a x : VCoord K) :
    mapV f (reflectV a x) = reflectV (mapV f a) (mapV f x) := by
  simp only [reflectV, mapV_sub, mapV_smul, map_div₀, mapV_BV, mapV_nV]

@[simp] theorem mapV_evenV (f : K →+* L) (a b x : VCoord K) :
    mapV f (evenV a b x) = evenV (mapV f a) (mapV f b) (mapV f x) := by
  simp only [evenV, mapV_reflect]

@[simp] theorem mapV_targetFirst (f : K →+* L) (a : K) :
    mapV f (targetFirst a) = targetFirst (f a) := by
  ext <;> simp [mapV, targetFirst, planeVector]

@[simp] theorem mapV_targetSecond (f : K →+* L) (a h s : K) :
    mapV f (targetSecond a h s) = targetSecond (f a) (f h) (f s) := by
  ext <;> simp [mapV, targetSecond, targetB, targetC, planeVector, map_ofNat]

/-- The actual accepted source coefficient map, not an alternative carrier map.-/
@[simp] theorem mapSource_v (f : K →+* L) (x : JCoord K) :
    (mapSource f x).v = mapV f x.v := by
  apply VCoord.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl

end AlbertLean.Generic.SourceVectorCoefficientMap
