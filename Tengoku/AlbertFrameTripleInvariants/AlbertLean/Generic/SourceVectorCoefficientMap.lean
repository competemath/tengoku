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

/--
@isnad1 id=eq.0h6v.s7.1799fc63524e from=translated src=- shape=0817b10e vocab=d4ae1f04
-/
@[simp] theorem mapV_comp (g : L →+* M) (f : K →+* L) (x : VCoord K) :
    mapV g (mapV f x) = mapV (g.comp f) x := rfl

/--
@isnad1 id=eq.0h5v.s7.d03392763108 from=translated src=- shape=c1c9629d vocab=eede3448
-/
@[simp] theorem mapV_sub (f : K →+* L) (x y : VCoord K) :
    mapV f (x-y) = mapV f x - mapV f y := by
  ext <;> simp [mapV]

/--
@isnad1 id=eq.0h5v.s8.e417a6c3df38 from=translated src=- shape=d5598f76 vocab=45217609
-/
@[simp] theorem mapV_smul (f : K →+* L) (a : K) (x : VCoord K) :
    mapV f (a • x) = f a • mapV f x := by
  ext <;> simp [mapV]

/--
@isnad1 id=eq.0h4v.s6.1cf0f1bb1d4a from=translated src=- shape=8b42bc84 vocab=98fe51e3
-/
@[simp] theorem mapV_nV (f : K →+* L) (x : VCoord K) :
    nV (mapV f x) = f (nV x) := by
  simp [nV, pf_coordinate, mapV]

/--
@isnad1 id=eq.0h5v.s7.7b131c41aa46 from=translated src=- shape=57185446 vocab=dfc5fe21
-/
@[simp] theorem mapV_BV (f : K →+* L) (x y : VCoord K) :
    BV (mapV f x) (mapV f y) = f (BV x y) := by
  simp [BV, BW, mapV]

/--
@isnad1 id=eq.0h5v.s6.610dd1c4cfa1 from=translated src=- shape=47357877 vocab=999f78a7
-/
@[simp] theorem mapV_reflect (f : K →+* L) (a x : VCoord K) :
    mapV f (reflectV a x) = reflectV (mapV f a) (mapV f x) := by
  simp only [reflectV, mapV_sub, mapV_smul, map_div₀, mapV_BV, mapV_nV]

/--
@isnad1 id=eq.0h6v.s6.f33ef905e497 from=translated src=- shape=823d5c5e vocab=cc11ca03
-/
@[simp] theorem mapV_evenV (f : K →+* L) (a b x : VCoord K) :
    mapV f (evenV a b x) = evenV (mapV f a) (mapV f b) (mapV f x) := by
  simp only [evenV, mapV_reflect]

/--
@isnad1 id=eq.0h4v.s6.845436763e6b from=translated src=- shape=2f80ab89 vocab=58d075e9
-/
@[simp] theorem mapV_targetFirst (f : K →+* L) (a : K) :
    mapV f (targetFirst a) = targetFirst (f a) := by
  ext <;> simp [mapV, targetFirst, planeVector]

/--
@isnad1 id=eq.0h6v.s7.264874a105ff from=translated src=- shape=7d1ac29a vocab=0a2c0824
-/
@[simp] theorem mapV_targetSecond (f : K →+* L) (a h s : K) :
    mapV f (targetSecond a h s) = targetSecond (f a) (f h) (f s) := by
  ext <;> simp [mapV, targetSecond, targetB, targetC, planeVector, map_ofNat]

/-- The actual accepted source coefficient map, not an alternative carrier map.
@isnad1 id=eq.0h4v.s6.e9dd1a4193e6 from=translated src=- shape=252d3252 vocab=1cea2bd5
-/
@[simp] theorem mapSource_v (f : K →+* L) (x : JCoord K) :
    (mapSource f x).v = mapV f x.v := by
  apply VCoord.ext
  · rfl
  · rfl
  · funext i
    fin_cases i <;> rfl

end AlbertLean.Generic.SourceVectorCoefficientMap
