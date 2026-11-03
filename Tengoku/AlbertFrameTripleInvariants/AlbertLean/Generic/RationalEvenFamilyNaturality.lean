import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceCoefficientMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms map_center` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms center_cleared` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_open_denominator` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_evenJEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms familyAut_natural` (it only prints; the queue checks the axioms of every declaration). -/

/-! Coefficient naturality of the actual eight-parameter even source family.
This is a direct coordinate identity; it neither factors through an
intermediate ambient field nor asserts a density theorem. -/

noncomputable section
namespace AlbertLean.Triality.RationalEvenFamilyNaturality

open ExteriorSix CoordinateTensor StructuredCubic StructuredAdjoint
open SourceEvenReflections SourceEvenAutomorphism RationalEvenFamily
open AlbertLean.Generic.SourceCoefficientMap

universe u v
variable {K : Type u} {L : Type v}
variable [Field K] [CharZero K] [Field L] [CharZero L]

local instance sourceTwo : Invertible (2 : K) :=
  invertibleOfNonzero (by norm_num)
local instance targetTwo : Invertible (2 : L) :=
  invertibleOfNonzero (by norm_num)

def mapW (f : K →+* L) (w : W K) : W L := f ∘ w

def mapV (f : K →+* L) (x : VCoord K) : VCoord L :=
  { r := f x.r, z := f x.z, omega := mapW f x.omega }

def mapS (f : K →+* L) (x : SCoord K) : SCoord L :=
  { p := f ∘ x.p, phi := f ∘ x.phi }

def mapC (f : K →+* L) (x : CCoord K) : CCoord L :=
  { q := f ∘ x.q, psi := f ∘ x.psi }

def mapJ (f : K →+* L) (x : JCoord K) : JCoord L :=
  { d1 := f x.d1, d2 := f x.d2, d3 := f x.d3
    v := mapV f x.v, s := mapS f x.s, c := mapC f x.c }

theorem mapJ_eq_mapSource (f : K →+* L) (x : JCoord K) :
    mapJ f x = mapSource f x := by
  apply (AlbertLean.Triality.GenericCoordinates.structuredEquivK L).injective
  simp only [mapSource, LinearEquiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

theorem mapPf (f : K →+* L) (w : W K) :
    Pf (mapW f w) = f (Pf w) := by
  rw [pf_coordinate, pf_coordinate]
  simp [mapW]

theorem map_nV (f : K →+* L) (x : VCoord K) :
    nV (mapV f x) = f (nV x) := by
  simp only [nV, mapV, map_mul]
  rw [mapPf]
  simp only [map_add, map_mul]

theorem map_BV (f : K →+* L) (x y : VCoord K) :
    BV (mapV f x) (mapV f y) = f (BV x y) := by
  simp [BV, mapV, BW, mapW]

theorem map_center (f : K →+* L) (alpha r : K) (omega : W K) (rho : K) :
    mapV f (center alpha r omega rho) =
      center (f alpha) (f r) (mapW f omega) (f rho) := by
  apply VCoord.ext
  · rfl
  · simp [center, mapV, mapPf, map_div₀]
  · rfl

/-- Division-free numerator identity for the sole rational coordinate of the
eight-parameter center chart.-/
theorem center_cleared (alpha r : K) (omega : W K) (rho : K)
    (ha : alpha ≠ 0) (hr : r ≠ 0) :
    alpha * r * (center alpha r omega rho).z =
      rho ^ 2 - alpha * Pf omega := by
  simp only [center]
  field_simp [ha, hr]

theorem map_open_denominator (f : K →+* L) (r rho : K) :
    f (r * rho) = f r * f rho := map_mul f r rho

theorem map_reflectV (f : K →+* L) (a x : VCoord K) :
    mapV f (reflectV a x) = reflectV (mapV f a) (mapV f x) := by
  have hquot : f (BV a x / nV a) =
      BV (mapV f a) (mapV f x) / nV (mapV f a) := by
    rw [map_div₀, map_BV, map_nV]
  apply VCoord.ext
  · simp [reflectV, mapV, hquot]
  · simp [reflectV, mapV, hquot]
  · funext i
    simp [reflectV, mapV, mapW, hquot]

theorem map_evenV (f : K →+* L) (a b x : VCoord K) :
    mapV f (evenV a b x) = evenV (mapV f a) (mapV f b) (mapV f x) := by
  simp only [evenV, map_reflectV]

theorem map_sourceMuS (f : K →+* L) (c : CCoord K) (x : VCoord K) :
    mapS f (sourceMuS c x) = sourceMuS (mapC f c) (mapV f x) := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuS, mapS, mapC, mapV, mapW] <;> ring

theorem map_sourceMuC (f : K →+* L) (x : VCoord K) (s : SCoord K) :
    mapC f (sourceMuC x s) = sourceMuC (mapV f x) (mapS f s) := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [sourceMuC, mapS, mapC, mapV, mapW] <;> ring

theorem map_evenS (f : K →+* L) (a b : VCoord K) (rho : K) (s : SCoord K) :
    mapS f (evenS a b rho s) =
      evenS (mapV f a) (mapV f b) (f rho) (mapS f s) := by
  rw [evenS, evenS, ← map_sourceMuC, ← map_sourceMuS]
  apply SCoord.ext <;> funext i <;>
    simp [mapS, map_inv₀]

theorem map_evenC (f : K →+* L) (a b : VCoord K) (rho : K) (c : CCoord K) :
    mapC f (evenC a b rho c) =
      evenC (mapV f a) (mapV f b) (f rho) (mapC f c) := by
  rw [evenC, evenC, ← map_sourceMuS, ← map_sourceMuC]
  apply CCoord.ext <;> funext i <;>
    simp [mapC, map_inv₀]

/-- Naturality of the actual source-even coordinate formula.  The proof
objects establishing anisotropy and the root equation do not enter the map.-/
theorem map_evenJEquiv
    (f : K →+* L) (a b : VCoord K) (rho : K)
    (ha : nV a ≠ 0) (hb : nV b ≠ 0)
    (hrho : rho ^ 2 = nV a * nV b) (hrho0 : rho ≠ 0)
    (x : JCoord K) :
    mapJ f (evenJEquiv a b rho ha hb hrho hrho0 x) =
      evenJEquiv (mapV f a) (mapV f b) (f rho)
        (by simpa [map_nV] using f.injective.ne ha)
        (by simpa [map_nV] using f.injective.ne hb)
        (by simpa [map_nV] using congrArg f hrho)
        (by simpa only [map_zero] using f.injective.ne hrho0) (mapJ f x) := by
  rw [evenJEquiv_apply, evenJEquiv_apply]
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · exact map_evenV f a b x.v
  · exact map_evenS f a b rho x.s
  · exact map_evenC f a b rho x.c

/-- Full-family field-hom naturality.  This is the coefficient identity used
before clearing numerators in a grid argument.-/
theorem familyAut_natural
    (f : K →+* L) (A : VCoord K) (hA : nV A ≠ 0)
    (r : K) (omega : W K) (rho : K) (hr : r ≠ 0) (hp : rho ≠ 0)
    (x : JCoord K) :
    mapSource f ((familyAut A hA r omega rho hr hp).linear x) =
      (familyAut (mapV f A) (by simpa [map_nV] using f.injective.ne hA)
        (f r) (mapW f omega) (f rho)
        (by simpa only [map_zero] using f.injective.ne hr)
        (by simpa only [map_zero] using f.injective.ne hp)).linear
        (mapSource f x) := by
  rw [← mapJ_eq_mapSource, ← mapJ_eq_mapSource]
  change mapJ f
      (evenJEquiv A (center (nV A) r omega rho) rho _ _ _ _ x) =
    evenJEquiv (mapV f A)
      (center (nV (mapV f A)) (f r) (mapW f omega) (f rho))
      (f rho) _ _ _ _ (mapJ f x)
  simpa only [map_center, map_nV] using
    (map_evenJEquiv f A (center (nV A) r omega rho) rho hA
      (norm_center_ne_zero (nV A) r omega rho hA hr hp)
      (center_root (nV A) r omega rho hA hr) hp x)

end AlbertLean.Triality.RationalEvenFamilyNaturality
