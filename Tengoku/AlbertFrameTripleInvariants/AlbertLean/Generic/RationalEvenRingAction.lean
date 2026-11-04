import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.RationalEvenFamily
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceRingReflectionFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ringNV_centerB` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms centerB_inverseNorm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ofF0_toF0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms toF0_ofF0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_familyF0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms map_twoFamilyF0` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms familyF0_eq_sourceEvenAut` (it only prints; the queue checks the axioms of every declaration). -/

/-! The full 27-coordinate rational formula for the eight-parameter even
source family.  Inverses are supplied as ring elements, so the formula lives
in a principal localization and can be composed before any field evaluation. -/

noncomputable section
namespace AlbertLean.Generic.RationalEvenRingAction

open AlbertLean.Triality.ExteriorSix
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredAdjoint
open AlbertLean.Triality.SourceEvenReflections
open AlbertLean.Triality.SourceEvenAutomorphism
open AlbertLean.Triality.RationalEvenFamily
open AlbertLean.Triality.GenericCoordinates

universe u
variable {R : Type u} [CommRing R] [Algebra ℚ R] [Invertible (2 : R)]

def ringNV (v : VCoord R) : R := v.r * v.z + Pf v.omega

def ringBV (v w : VCoord R) : R :=
  v.r * w.z + v.z * w.r + BW v.omega w.omega

def ringReflectV (a : VCoord R) (nInv : R) (v : VCoord R) : VCoord R :=
  v - (ringBV a v * nInv) • a

def ringMuS (c : CCoord R) (v : VCoord R) : SCoord R :=
  { p := ![
      c.psi 1 * v.omega .i12 + c.psi 2 * v.omega .i13 + c.psi 3 * v.omega .i14 + c.q 0 * v.r,
      -c.psi 0 * v.omega .i12 + c.psi 2 * v.omega .i23 + c.psi 3 * v.omega .i24 + c.q 1 * v.r,
      -c.psi 0 * v.omega .i13 - c.psi 1 * v.omega .i23 + c.psi 3 * v.omega .i34 + c.q 2 * v.r,
      -c.psi 0 * v.omega .i14 - c.psi 1 * v.omega .i24 - c.psi 2 * v.omega .i34 + c.q 3 * v.r]
    phi := ![
      c.psi 0 * v.z + c.q 1 * v.omega .i34 - c.q 2 * v.omega .i24 + c.q 3 * v.omega .i23,
      c.psi 1 * v.z - c.q 0 * v.omega .i34 + c.q 2 * v.omega .i14 - c.q 3 * v.omega .i13,
      c.psi 2 * v.z + c.q 0 * v.omega .i24 - c.q 1 * v.omega .i14 + c.q 3 * v.omega .i12,
      c.psi 3 * v.z - c.q 0 * v.omega .i23 + c.q 1 * v.omega .i13 - c.q 2 * v.omega .i12] }

def ringMuC (v : VCoord R) (s : SCoord R) : CCoord R :=
  { q := ![
      s.p 0 * v.z - s.phi 1 * v.omega .i12 - s.phi 2 * v.omega .i13 - s.phi 3 * v.omega .i14,
      s.p 1 * v.z + s.phi 0 * v.omega .i12 - s.phi 2 * v.omega .i23 - s.phi 3 * v.omega .i24,
      s.p 2 * v.z + s.phi 0 * v.omega .i13 + s.phi 1 * v.omega .i23 - s.phi 3 * v.omega .i34,
      s.p 3 * v.z + s.phi 0 * v.omega .i14 + s.phi 1 * v.omega .i24 + s.phi 2 * v.omega .i34]
    psi := ![
      -s.p 1 * v.omega .i34 + s.p 2 * v.omega .i24 - s.p 3 * v.omega .i23 + s.phi 0 * v.r,
      s.p 0 * v.omega .i34 - s.p 2 * v.omega .i14 + s.p 3 * v.omega .i13 + s.phi 1 * v.r,
      -s.p 0 * v.omega .i24 + s.p 1 * v.omega .i14 - s.p 3 * v.omega .i12 + s.phi 2 * v.r,
      s.p 0 * v.omega .i23 - s.p 1 * v.omega .i13 + s.p 2 * v.omega .i12 + s.phi 3 * v.r] }

/-- The solved center.  `alphaInv`, `rInv`, and `rhoInv` are the images of
the three inverses in the chosen localization.-/
def centerB (alphaInv r : R) (omega : W R) (rho rInv : R) : VCoord R :=
  { r := r
    z := (rho ^ 2 * alphaInv - Pf omega) * rInv
    omega := omega }

/--
@isnad1 id=eq.2h7v.s7.54625ff872e0 from=translated src=- shape=dbb946bb vocab=98468f17
-/
theorem ringNV_centerB (alpha alphaInv r : R) (omega : W R)
    (rho rInv : R) (ha : alpha * alphaInv = 1) (hr : r * rInv = 1) :
    ringNV (centerB alphaInv r omega rho rInv) = rho ^ 2 * alphaInv := by
  simp only [ringNV, centerB]
  calc
    r * ((rho ^ 2 * alphaInv - Pf omega) * rInv) + Pf omega =
        (rho ^ 2 * alphaInv - Pf omega) * (r * rInv) + Pf omega := by ring
    _ = rho ^ 2 * alphaInv := by rw [hr]; ring

/--
@isnad1 id=eq.3h8v.s7.9a1b8a2a5349 from=translated src=- shape=ef476459 vocab=98468f17
-/
theorem centerB_inverseNorm (alpha alphaInv r : R) (omega : W R)
    (rho rInv rhoInv : R) (ha : alpha * alphaInv = 1)
    (hr : r * rInv = 1) (hp : rho * rhoInv = 1) :
    ringNV (centerB alphaInv r omega rho rInv) * (alpha * rhoInv ^ 2) = 1 := by
  rw [ringNV_centerB alpha alphaInv r omega rho rInv ha hr]
  calc
    rho ^ 2 * alphaInv * (alpha * rhoInv ^ 2) =
        (alpha * alphaInv) * (rho * rhoInv) ^ 2 := by ring
    _ = 1 := by rw [ha, hp]; norm_num

/-- Full V/S/C action.  All operations are polynomial in the displayed ring
data; there is no division or field structure in this definition.-/
def familyJ (A : VCoord R) (alpha alphaInv r : R) (omega : W R)
    (rho rInv rhoInv : R) (x : JCoord R) : JCoord R :=
  let B := centerB alphaInv r omega rho rInv
  { d1 := x.d1, d2 := x.d2, d3 := x.d3
    v := ringReflectV A alphaInv (ringReflectV B (alpha * rhoInv ^ 2) x.v)
    s := rhoInv • ringMuS (ringMuC B x.s) A
    c := rhoInv • ringMuC A (ringMuS x.c B) }

abbrev F0Ring (S : Type*) := Fin 27 → S

def toF0 (x : JCoord R) : F0Ring R := fun i =>
  match i.val with
  | 0 => x.d1 | 1 => x.d2 | 2 => x.d3 | 3 => x.v.r | 4 => x.v.z
  | 5 => x.v.omega .i12 | 6 => x.v.omega .i13 | 7 => x.v.omega .i14
  | 8 => x.v.omega .i23 | 9 => x.v.omega .i24 | 10 => x.v.omega .i34
  | 11 => x.s.p 0 | 12 => x.s.p 1 | 13 => x.s.p 2 | 14 => x.s.p 3
  | 15 => x.s.phi 0 | 16 => x.s.phi 1 | 17 => x.s.phi 2 | 18 => x.s.phi 3
  | 19 => x.c.q 0 | 20 => x.c.q 1 | 21 => x.c.q 2 | 22 => x.c.q 3
  | 23 => x.c.psi 0 | 24 => x.c.psi 1 | 25 => x.c.psi 2 | 26 => x.c.psi 3
  | _ => 0

def ofF0 (x : F0Ring R) : JCoord R :=
  { d1 := x 0, d2 := x 1, d3 := x 2
    v := { r := x 3, z := x 4, omega := fun
      | .i12 => x 5 | .i13 => x 6 | .i14 => x 7
      | .i23 => x 8 | .i24 => x 9 | .i34 => x 10 }
    s := { p := ![x 11, x 12, x 13, x 14], phi := ![x 15, x 16, x 17, x 18] }
    c := { q := ![x 19, x 20, x 21, x 22], psi := ![x 23, x 24, x 25, x 26] } }

/--
@isnad1 id=eq.0h2v.s6.a663fea8d709 from=translated src=- shape=41d12750 vocab=4a568b65
-/
@[simp] theorem ofF0_toF0 (x : JCoord R) : ofF0 (toF0 x) = x := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · apply SCoord.ext <;> funext i <;> fin_cases i <;> rfl
  · apply CCoord.ext <;> funext i <;> fin_cases i <;> rfl

/--
@isnad1 id=eq.0h2v.s6.a72966289602 from=translated src=- shape=41d12750 vocab=cca16782
-/
@[simp] theorem toF0_ofF0 (x : F0Ring R) : toF0 (ofF0 x) = x := by
  funext i
  fin_cases i <;> rfl

def familyF0 (A : VCoord R) (alpha alphaInv r : R) (omega : W R)
    (rho rInv rhoInv : R) (x : F0Ring R) : F0Ring R :=
  toF0 (familyJ A alpha alphaInv r omega rho rInv rhoInv (ofF0 x))

def mapW {S : Type*} [CommRing S] (f : R →+* S) (w : W R) : W S := f ∘ w

def mapV {S : Type*} [CommRing S] (f : R →+* S) (v : VCoord R) : VCoord S :=
  { r := f v.r, z := f v.z, omega := mapW f v.omega }

def mapS {S : Type*} [CommRing S] (f : R →+* S) (s : SCoord R) : SCoord S :=
  { p := f ∘ s.p, phi := f ∘ s.phi }

def mapC {S : Type*} [CommRing S] (f : R →+* S) (c : CCoord R) : CCoord S :=
  { q := f ∘ c.q, psi := f ∘ c.psi }

def mapJ {S : Type*} [CommRing S] (f : R →+* S) (x : JCoord R) : JCoord S :=
  { d1 := f x.d1, d2 := f x.d2, d3 := f x.d3
    v := mapV f x.v, s := mapS f x.s, c := mapC f x.c }

def mapF0 {S : Type*} [CommRing S] (f : R →+* S) (x : F0Ring R) : F0Ring S := f ∘ x

private theorem map_centerB {S : Type*} [CommRing S] [Algebra ℚ S]
    [Invertible (2 : S)]
    (f : R →+* S) (alphaInv r : R) (omega : W R) (rho rInv : R) :
    mapV f (centerB alphaInv r omega rho rInv) =
      centerB (f alphaInv) (f r) (mapW f omega) (f rho) (f rInv) := by
  apply VCoord.ext
  · rfl
  · change f ((rho ^ 2 * alphaInv - Pf omega) * rInv) =
      (f rho ^ 2 * f alphaInv - Pf (mapW f omega)) * f rInv
    have hPf : f (Pf omega) = Pf (mapW f omega) := by
      rw [pf_coordinate, pf_coordinate]
      simp only [mapW, Function.comp_apply, map_add, map_sub, map_mul]
    rw [map_mul, map_sub, map_mul, map_pow]
    rw [hPf]
  · rfl

private theorem map_ringBV {S : Type*} [CommRing S]
    (f : R →+* S) (a x : VCoord R) :
    f (ringBV a x) = ringBV (mapV f a) (mapV f x) := by
  simp [ringBV, mapV, mapW, BW]

private theorem mapV_sub {S : Type*} [CommRing S]
    (f : R →+* S) (x y : VCoord R) :
    mapV f (x - y) = mapV f x - mapV f y := by
  apply VCoord.ext
  · exact f.map_sub x.r y.r
  · exact f.map_sub x.z y.z
  · funext i
    exact f.map_sub (x.omega i) (y.omega i)

private theorem mapV_smul {S : Type*} [CommRing S]
    (f : R →+* S) (a : R) (x : VCoord R) :
    mapV f (a • x) = f a • mapV f x := by
  apply VCoord.ext
  · simp [mapV]
  · simp [mapV]
  · funext i
    simp [mapV, mapW]

private theorem map_ringReflectV {S : Type*} [CommRing S]
    (f : R →+* S) (a : VCoord R) (nInv : R) (x : VCoord R) :
    mapV f (ringReflectV a nInv x) =
      ringReflectV (mapV f a) (f nInv) (mapV f x) := by
  rw [ringReflectV, ringReflectV, mapV_sub, mapV_smul, map_mul,
    map_ringBV]

private theorem map_ringMuS {S : Type*} [CommRing S]
    (f : R →+* S) (c : CCoord R) (v : VCoord R) :
    mapS f (ringMuS c v) = ringMuS (mapC f c) (mapV f v) := by
  apply SCoord.ext <;> funext i <;> fin_cases i <;>
    simp [ringMuS, mapS, mapC, mapV, mapW]

private theorem map_ringMuC {S : Type*} [CommRing S]
    (f : R →+* S) (v : VCoord R) (s : SCoord R) :
    mapC f (ringMuC v s) = ringMuC (mapV f v) (mapS f s) := by
  apply CCoord.ext <;> funext i <;> fin_cases i <;>
    simp [ringMuC, mapS, mapC, mapV, mapW]

private theorem mapS_smul {S : Type*} [CommRing S]
    (f : R →+* S) (a : R) (s : SCoord R) :
    mapS f (a • s) = f a • mapS f s := by
  apply SCoord.ext <;> funext i <;> simp [mapS]

private theorem mapC_smul {S : Type*} [CommRing S]
    (f : R →+* S) (a : R) (c : CCoord R) :
    mapC f (a • c) = f a • mapC f c := by
  apply CCoord.ext <;> funext i <;> simp [mapC]

private theorem map_familyJ {S : Type*} [CommRing S] [Algebra ℚ S]
    [Invertible (2 : S)]
    (f : R →+* S) (A : VCoord R) (alpha alphaInv r : R) (omega : W R)
    (rho rInv rhoInv : R) (x : JCoord R) :
    mapJ f (familyJ A alpha alphaInv r omega rho rInv rhoInv x) =
      familyJ (mapV f A) (f alpha) (f alphaInv) (f r) (mapW f omega)
        (f rho) (f rInv) (f rhoInv) (mapJ f x) := by
  rw [familyJ, familyJ]
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · simp only [mapJ]
    rw [map_ringReflectV, map_ringReflectV, map_centerB, map_mul, map_pow]
  · simp only [mapJ]
    rw [mapS_smul, map_ringMuS, map_ringMuC, map_centerB]
  · simp only [mapJ]
    rw [mapC_smul, map_ringMuC, map_ringMuS, map_centerB]

private theorem map_toF0 {S : Type*} [CommRing S]
    (f : R →+* S) (x : JCoord R) :
    mapF0 f (toF0 x) = toF0 (mapJ f x) := by
  funext i
  fin_cases i <;> rfl

private theorem map_ofF0 {S : Type*} [CommRing S]
    (f : R →+* S) (x : F0Ring R) :
    mapJ f (ofF0 x) = ofF0 (mapF0 f x) := by
  apply JCoord.ext
  · rfl
  · rfl
  · rfl
  · apply VCoord.ext <;> first | rfl | (funext i; fin_cases i <;> rfl)
  · apply SCoord.ext <;> funext i <;> fin_cases i <;> rfl
  · apply CCoord.ext <;> funext i <;> fin_cases i <;> rfl

/-- The entire rational coordinate map specializes coefficientwise.  This is
the composition-safe interface: several `familyF0` maps may be composed in
the localization before applying this theorem once.
@isnad1 id=eq.0h12v.s8.6f404fe15fe8 from=translated src=- shape=857c2668 vocab=9824de57
-/
theorem map_familyF0 {S : Type*} [CommRing S] [Algebra ℚ S] [Invertible (2 : S)]
    (f : R →+* S) (A : VCoord R) (alpha alphaInv r : R) (omega : W R)
    (rho rInv rhoInv : R) (x : F0Ring R) :
    mapF0 f (familyF0 A alpha alphaInv r omega rho rInv rhoInv x) =
      familyF0 (mapV f A) (f alpha) (f alphaInv) (f r) (mapW f omega)
        (f rho) (f rInv) (f rhoInv) (mapF0 f x) := by
  rw [familyF0, familyF0, map_toF0, map_familyJ, map_ofF0]

/-- Two stages are specialized only after their coordinate maps have been
composed.  No map from an intermediate normalized ambient function field is
introduced.
@isnad1 id=eq.0h20v.s9.cae68181e6df from=translated src=- shape=b849594c vocab=9824de57
-/
theorem map_twoFamilyF0 {S : Type*} [CommRing S] [Algebra ℚ S]
    [Invertible (2 : S)] (f : R →+* S)
    (A₁ A₂ : VCoord R)
    (alpha₁ alphaInv₁ r₁ : R) (omega₁ : W R) (rho₁ rInv₁ rhoInv₁ : R)
    (alpha₂ alphaInv₂ r₂ : R) (omega₂ : W R) (rho₂ rInv₂ rhoInv₂ : R)
    (x : F0Ring R) :
    mapF0 f
        (familyF0 A₂ alpha₂ alphaInv₂ r₂ omega₂ rho₂ rInv₂ rhoInv₂
          (familyF0 A₁ alpha₁ alphaInv₁ r₁ omega₁ rho₁ rInv₁ rhoInv₁ x)) =
      familyF0 (mapV f A₂) (f alpha₂) (f alphaInv₂) (f r₂) (mapW f omega₂)
        (f rho₂) (f rInv₂) (f rhoInv₂)
        (familyF0 (mapV f A₁) (f alpha₁) (f alphaInv₁) (f r₁) (mapW f omega₁)
          (f rho₁) (f rInv₁) (f rhoInv₁) (mapF0 f x)) := by
  rw [map_familyF0, map_familyF0]

section FieldAgreement

variable {K : Type*} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/--
@isnad1 id=eq.0h2v.s5.d1fe0922219e from=translated src=- shape=061290fe vocab=ea9269b3
-/
theorem ringNV_eq_nV (v : VCoord K) : ringNV v = nV v := rfl
/--
@isnad1 id=eq.0h3v.s5.36ba5fee1dec from=translated src=- shape=fc4301df vocab=e8b0c0a1
-/
theorem ringBV_eq_BV (v w : VCoord K) : ringBV v w = BV v w := rfl
/--
@isnad1 id=eq.0h3v.s5.9fd4babac82b from=translated src=- shape=b8bbb0a1 vocab=f9110fa5
-/
theorem ringMuS_eq (c : CCoord K) (v : VCoord K) : ringMuS c v = sourceMuS c v := rfl
/--
@isnad1 id=eq.0h3v.s5.93fa3dd78573 from=translated src=- shape=b8bbb0a1 vocab=268b2f30
-/
theorem ringMuC_eq (v : VCoord K) (s : SCoord K) : ringMuC v s = sourceMuC v s := rfl

/--
@isnad1 id=eq.0h3v.s5.1b07f09f37c3 from=translated src=- shape=fdd9f8f9 vocab=bc9a184f
-/
theorem ringReflectV_eq (a v : VCoord K) :
    ringReflectV a (nV a)⁻¹ v = reflectV a v := by
  simp [ringReflectV, reflectV, ringBV_eq_BV, div_eq_mul_inv]

/--
@isnad1 id=eq.0h5v.s6.c8beb4d18913 from=translated src=- shape=8f9df193 vocab=249e4496
-/
theorem centerB_eq_center (alpha r : K) (omega : W K) (rho : K) :
    centerB alpha⁻¹ r omega rho r⁻¹ = center alpha r omega rho := by
  apply VCoord.ext
  · rfl
  · simp [centerB, center, div_eq_mul_inv]
  · rfl

/-- Evaluation correctness for all 27 coordinates at once.
@isnad1 id=eq.3h6v.s10.44ef2deb74f9 from=translated src=- shape=b6c9d956 vocab=a702aa8a
-/
theorem familyF0_eq_sourceEvenAut
    (A : VCoord K) (hA : nV A ≠ 0)
    (r : K) (omega : W K) (rho : K) (hr : r ≠ 0) (hp : rho ≠ 0)
    (x : JCoord K) :
    familyF0 A (nV A) (nV A)⁻¹ r omega rho r⁻¹ rho⁻¹
        (structuredEquivK K x) =
      structuredEquivK K ((familyAut A hA r omega rho hr hp).linear x) := by
  rw [familyF0]
  have hdecode : ofF0 (structuredEquivK K x) = x := by
    change ofF0 (toF0 x) = x
    exact ofF0_toF0 x
  rw [hdecode]
  have hB : nV (center (nV A) r omega rho) ≠ 0 :=
    norm_center_ne_zero (nV A) r omega rho hA hr hp
  have hinv : nV A * rho⁻¹ ^ 2 =
      (nV (center (nV A) r omega rho))⁻¹ := by
    apply (mul_left_cancel₀ hB)
    rw [mul_inv_cancel₀ hB]
    have hprod := centerB_inverseNorm (nV A) (nV A)⁻¹ r omega rho r⁻¹ rho⁻¹
      (mul_inv_cancel₀ hA) (mul_inv_cancel₀ hr) (mul_inv_cancel₀ hp)
    simpa only [ringNV_eq_nV, centerB_eq_center] using hprod
  have hJ : familyJ A (nV A) (nV A)⁻¹ r omega rho r⁻¹ rho⁻¹ x =
      evenJEquiv A (center (nV A) r omega rho) rho hA hB
        (center_root (nV A) r omega rho hA hr) hp x := by
    rw [evenJEquiv_apply]
    apply JCoord.ext
    · rfl
    · rfl
    · rfl
    · change ringReflectV A (nV A)⁻¹
          (ringReflectV (centerB (nV A)⁻¹ r omega rho r⁻¹)
            (nV A * rho⁻¹ ^ 2) x.v) = _
      rw [centerB_eq_center, hinv, ringReflectV_eq, ringReflectV_eq] <;> rfl
    · change rho⁻¹ • ringMuS
          (ringMuC (centerB (nV A)⁻¹ r omega rho r⁻¹) x.s) A = _
      rw [centerB_eq_center, ringMuS_eq, ringMuC_eq] <;> rfl
    · change rho⁻¹ • ringMuC A
          (ringMuS x.c (centerB (nV A)⁻¹ r omega rho r⁻¹)) = _
      rw [centerB_eq_center, ringMuS_eq, ringMuC_eq] <;> rfl
  rw [hJ] <;> rfl

end FieldAgreement
end AlbertLean.Generic.RationalEvenRingAction
