import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericFieldChart
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms j_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms PA_mul_inversePA` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms PB_mul_inversePB` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms root_mul_inverseRoot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms detN_mul_inverseDetN` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms evaluation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ambient_ne_zero_of_evaluation_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
A small localization for specializing the actual generic detector and its
reciprocal-root mate. Its denominator is C(PA * PB * det N) * X.
Neither a, kappa, nor the branch polynomial is inverted.

The ambient map lands in the already used nested FunctionField. Evaluation
is defined only on this localization, under four explicit nonvanishing
hypotheses, and never on the entire fraction field.
-/

noncomputable section
namespace AlbertLean.Generic.GenericDetectorLocalization

open Polynomial
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.NestedReciprocalField

universe u
variable (k : Type u) [Field k] [CharZero k]

abbrev CoefficientRing := R k
abbrev CoordinateRing := Polynomial (CoefficientRing k)

def denominator : CoordinateRing k :=
  Polynomial.C (PA k * PB k * Matrix.det (N k)) * Polynomial.X

abbrev LocalRing := Localization (Submonoid.powers (denominator k))

def loc : CoordinateRing k →+* LocalRing k :=
  algebraMap (CoordinateRing k) (LocalRing k)

/-- The original nineteen polynomial coordinates inside the localization.-/
def coefficient : CoefficientRing k →+* LocalRing k :=
  (loc k).comp Polynomial.C

/-- The independent twentieth coordinate.-/
def root : LocalRing k := loc k Polynomial.X

/-- Inclusion of P[T] into the existing Frac(Frac(P)[T]).-/
def ambientMap : CoordinateRing k →+* FunctionField k :=
  (algebraMap (Polynomial (Base k)) (FunctionField k)).comp
    (Polynomial.mapRingHom (ι k))

/--
@isnad1 id=injectiv.0h1v.s10.3a2e18f51e9c from=translated src=- shape=e937283c vocab=387b43f0
-/
theorem ambientMap_injective : Function.Injective (ambientMap k) :=
  (polynomialMap_injective (Base k)).comp
    (Polynomial.map_injective _ (iota_injective k))

/--
@isnad1 id=eq.0h2v.s11.24bad1308aa5 from=translated src=- shape=f6368197 vocab=317e8811
-/
@[simp] theorem ambientMap_C (p : CoefficientRing k) :
    ambientMap k (Polynomial.C p) = includeBase k (ι k p) := by
  change algebraMap (Polynomial (Base k)) (FunctionField k)
    (Polynomial.map (ι k) (Polynomial.C p)) = _
  rw [Polynomial.map_C]
  exact polynomialMap_C (Base k) (ι k p)

/--
@isnad1 id=eq.0h1v.s10.1ec0090249e9 from=translated src=- shape=489a6b32 vocab=ef6ff1e8
-/
@[simp] theorem ambientMap_X : ambientMap k Polynomial.X = T (Base k) := by
  change algebraMap (Polynomial (Base k)) (FunctionField k)
    (Polynomial.map (ι k) Polynomial.X) = _
  rw [Polynomial.map_X]
  rfl

/--
@isnad1 id=ne.0h1v.s10.879d7263d00d from=translated src=- shape=fcfb5405 vocab=b8cbe06b
-/
theorem ambientMap_denominator_ne_zero : ambientMap k (denominator k) ≠ 0 := by
  have hc : ι k (PA k * PB k * Matrix.det (N k)) ≠ 0 := by
    rw [map_mul, map_mul]
    exact mul_ne_zero (mul_ne_zero (PA_ne_zero k) (PB_ne_zero k))
      (mapped_detN_ne_zero k)
  rw [denominator, map_mul, ambientMap_C, ambientMap_X]
  exact mul_ne_zero ((map_ne_zero (includeBase k)).mpr hc) (T_ne_zero (Base k))

private theorem ambientMap_denominator_unit : IsUnit (ambientMap k (denominator k)) :=
  isUnit_iff_ne_zero.mpr (ambientMap_denominator_ne_zero k)

/-- The injective localization map into the existing generic field.-/
def j : LocalRing k →+* FunctionField k :=
  IsLocalization.Away.lift (denominator k) (ambientMap_denominator_unit k)

/--
@isnad1 id=eq.0h2v.s11.b37525ddd3d6 from=translated src=- shape=390e7d5b vocab=4f1ab3d4
-/
@[simp] theorem j_loc (p : CoordinateRing k) : j k (loc k p) = ambientMap k p :=
  IsLocalization.Away.lift_eq (denominator k) (ambientMap_denominator_unit k) p

/--
@isnad1 id=eq.0h2v.s11.3e15c3835f6e from=translated src=- shape=3c3b2067 vocab=8bb7a495
-/
@[simp] theorem j_coefficient (p : CoefficientRing k) :
    j k (coefficient k p) = includeBase k (ι k p) := by
  change j k (loc k (Polynomial.C p)) = _
  rw [j_loc, ambientMap_C]

/--
@isnad1 id=eq.0h1v.s10.44543d5686ad from=translated src=- shape=38894fea vocab=439bba67
-/
@[simp] theorem j_root : j k (root k) = T (Base k) := by
  rw [root, j_loc, ambientMap_X]

/--
@isnad1 id=injectiv.0h1v.s10.99aa5845a277 from=translated src=- shape=e937283c vocab=976ecfaa
-/
theorem j_injective : Function.Injective (j k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (denominator k)) (j k)).2
  intro p q
  constructor
  · exact congrArg (j k)
  · intro h
    change j k (loc k p) = j k (loc k q) at h
    have hpq : p = q := ambientMap_injective k (by simpa only [j_loc] using h)
    exact congrArg (loc k) hpq

/--
@isnad1 id=injectiv.0h1v.s8.93f9139b9a93 from=translated src=- shape=e937283c vocab=1cab19c5
-/
theorem loc_injective : Function.Injective (loc k) := by
  intro p q h
  apply ambientMap_injective k
  simpa only [j_loc] using congrArg (j k) h

/-! Explicit factor inverses, obtained from the one inverted denominator. -/

def inverseDenominator : LocalRing k := IsLocalization.Away.invSelf (denominator k)

def inversePA : LocalRing k :=
  loc k (Polynomial.C (PB k * Matrix.det (N k)) * Polynomial.X) * inverseDenominator k

def inversePB : LocalRing k :=
  loc k (Polynomial.C (PA k * Matrix.det (N k)) * Polynomial.X) * inverseDenominator k

def inverseRoot : LocalRing k :=
  loc k (Polynomial.C (PA k * PB k * Matrix.det (N k))) * inverseDenominator k

def inverseDetN : LocalRing k :=
  loc k (Polynomial.C (PA k * PB k) * Polynomial.X) * inverseDenominator k

private theorem factor_mul_inverse (p q : CoordinateRing k) (h : p * q = denominator k) :
    loc k p * (loc k q * inverseDenominator k) = 1 := by
  rw [← mul_assoc, ← map_mul, h]
  exact IsLocalization.Away.mul_invSelf (denominator k)

/--
@isnad1 id=eq.0h1v.s9.a11be0d5a2e3 from=translated src=- shape=89547afd vocab=2760e510
-/
@[simp] theorem PA_mul_inversePA : coefficient k (PA k) * inversePA k = 1 := by
  apply factor_mul_inverse
  change Polynomial.C (PA k) * (Polynomial.C (PB k * Matrix.det (N k)) * Polynomial.X) = denominator k
  simp only [denominator, map_mul]
  ring

/--
@isnad1 id=eq.0h1v.s9.a1c6db140ea3 from=translated src=- shape=89547afd vocab=f4bdea40
-/
@[simp] theorem PB_mul_inversePB : coefficient k (PB k) * inversePB k = 1 := by
  apply factor_mul_inverse
  change Polynomial.C (PB k) * (Polynomial.C (PA k * Matrix.det (N k)) * Polynomial.X) = denominator k
  simp only [denominator, map_mul]
  ring

/--
@isnad1 id=eq.0h1v.s8.6d4e7e20933a from=translated src=- shape=38fe24a9 vocab=49ce664a
-/
@[simp] theorem root_mul_inverseRoot : root k * inverseRoot k = 1 := by
  apply factor_mul_inverse
  simp only [denominator, map_mul]
  ring

/--
@isnad1 id=eq.0h1v.s9.1195717b5130 from=translated src=- shape=e0d10f26 vocab=ce22d341
-/
@[simp] theorem detN_mul_inverseDetN :
    coefficient k (Matrix.det (N k)) * inverseDetN k = 1 := by
  apply factor_mul_inverse
  change Polynomial.C (Matrix.det (N k)) * (Polynomial.C (PA k * PB k) * Polynomial.X) = denominator k
  simp only [denominator, map_mul]
  ring

/--
@isnad1 id=eq.0h1v.s9.9e1798e579c5 from=translated src=- shape=1197b7f8 vocab=2760e510
-/
@[simp] theorem inversePA_mul_PA : inversePA k * coefficient k (PA k) = 1 := by
  rw [mul_comm, PA_mul_inversePA]

/--
@isnad1 id=eq.0h1v.s9.7ecc2b3ca622 from=translated src=- shape=1197b7f8 vocab=f4bdea40
-/
@[simp] theorem inversePB_mul_PB : inversePB k * coefficient k (PB k) = 1 := by
  rw [mul_comm, PB_mul_inversePB]

/--
@isnad1 id=eq.0h1v.s8.b50784247fab from=translated src=- shape=38fe24a9 vocab=49ce664a
-/
@[simp] theorem inverseRoot_mul_root : inverseRoot k * root k = 1 := by
  rw [mul_comm, root_mul_inverseRoot]

/--
@isnad1 id=eq.0h1v.s9.a8d7faf8a84f from=translated src=- shape=1b0dcfb9 vocab=ce22d341
-/
@[simp] theorem inverseDetN_mul_detN :
    inverseDetN k * coefficient k (Matrix.det (N k)) = 1 := by
  rw [mul_comm, detN_mul_inverseDetN]

/-- A ring inverse maps to the field inverse. The source need not be a field.-/
private theorem map_inverse {D E : Type*} [CommRing D] [Field E]
    (f : D →+* E) {x y : D} (hxy : x * y = 1) : f y = (f x)⁻¹ := by
  have h : f x * f y = 1 := by rw [← map_mul, hxy, map_one]
  have hx : f x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at h
    exact zero_ne_one h
  apply mul_left_cancel₀ hx
  rw [h, mul_inv_cancel₀ hx]

/--
@isnad1 id=eq.0h1v.s11.375d8d2693c6 from=translated src=- shape=bc404280 vocab=6875f735
-/
@[simp] theorem j_inversePA :
    j k (inversePA k) = (includeBase k (ι k (PA k)))⁻¹ := by
  simpa only [j_coefficient] using map_inverse (j k) (PA_mul_inversePA k)

/--
@isnad1 id=eq.0h1v.s11.5b7832cad41b from=translated src=- shape=bc404280 vocab=6249f8ad
-/
@[simp] theorem j_inversePB :
    j k (inversePB k) = (includeBase k (ι k (PB k)))⁻¹ := by
  simpa only [j_coefficient] using map_inverse (j k) (PB_mul_inversePB k)

/--
@isnad1 id=eq.0h1v.s10.c98966e2252f from=translated src=- shape=9ebc5bde vocab=c313cea2
-/
@[simp] theorem j_inverseRoot : j k (inverseRoot k) = (T (Base k))⁻¹ := by
  simpa only [j_root] using map_inverse (j k) (root_mul_inverseRoot k)

/--
@isnad1 id=eq.0h1v.s11.f83e24b83d75 from=translated src=- shape=e0ccbcac vocab=dd0fad01
-/
@[simp] theorem j_inverseDetN :
    j k (inverseDetN k) = (includeBase k (ι k (Matrix.det (N k))))⁻¹ := by
  simpa only [j_coefficient] using map_inverse (j k) (detN_mul_inverseDetN k)

/-! Partial specialization: only four displayed nonzero values are required. -/

variable (e : CoefficientRing k →+* k) (t : k)

def evalPolynomial : CoordinateRing k →+* k := Polynomial.eval₂RingHom e t

/--
@isnad1 id=eq.0h4v.s8.01bf2d591c83 from=translated src=- shape=8d70efa9 vocab=d752ab3f
-/
@[simp] theorem evalPolynomial_C (p : CoefficientRing k) :
    evalPolynomial k e t (Polynomial.C p) = e p := by
  simp [evalPolynomial]

/--
@isnad1 id=eq.0h3v.s7.60a58d4116b5 from=translated src=- shape=cf025821 vocab=b46b54a5
-/
@[simp] theorem evalPolynomial_X : evalPolynomial k e t Polynomial.X = t := by
  simp [evalPolynomial]

/--
@isnad1 id=eq.0h3v.s8.5088693580c6 from=translated src=- shape=8951d894 vocab=68e6781d
-/
@[simp] theorem evalPolynomial_denominator :
    evalPolynomial k e t (denominator k) =
      (e (PA k) * e (PB k) * e (Matrix.det (N k))) * t := by
  simp only [denominator, map_mul, evalPolynomial_C, evalPolynomial_X]

variable (hPA : e (PA k) ≠ 0) (hPB : e (PB k) ≠ 0)
  (hDetN : e (Matrix.det (N k)) ≠ 0) (ht : t ≠ 0)

include hPA hPB hDetN ht in
private theorem evalPolynomial_denominator_unit : IsUnit (evalPolynomial k e t (denominator k)) := by
  rw [evalPolynomial_denominator]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero (mul_ne_zero hPA hPB) hDetN) ht)

/-- An actual evaluation map from the small localization, not from FunctionField.-/
def evaluation : LocalRing k →+* k :=
  IsLocalization.Away.lift (denominator k)
    (evalPolynomial_denominator_unit k e t hPA hPB hDetN ht)

/--
@isnad1 id=eq.4h4v.s10.aa508b133db7 from=translated src=- shape=04fa8f49 vocab=7e6c7c6c
-/
@[simp] theorem evaluation_loc (p : CoordinateRing k) :
    evaluation k e t hPA hPB hDetN ht (loc k p) = evalPolynomial k e t p :=
  IsLocalization.Away.lift_eq (denominator k)
    (evalPolynomial_denominator_unit k e t hPA hPB hDetN ht) p

/--
@isnad1 id=eq.4h4v.s10.f5deaa8ec918 from=translated src=- shape=13bd260c vocab=053f4d12
-/
@[simp] theorem evaluation_coefficient (p : CoefficientRing k) :
    evaluation k e t hPA hPB hDetN ht (coefficient k p) = e p := by
  change evaluation k e t hPA hPB hDetN ht (loc k (Polynomial.C p)) = _
  rw [evaluation_loc, evalPolynomial_C]

/--
@isnad1 id=eq.4h3v.s9.a8c85dca63c0 from=translated src=- shape=eb2ac873 vocab=b778b135
-/
@[simp] theorem evaluation_root :
    evaluation k e t hPA hPB hDetN ht (root k) = t := by
  rw [root, evaluation_loc, evalPolynomial_X]

/--
@isnad1 id=eq.4h3v.s9.5b988043343d from=translated src=- shape=455a56d9 vocab=0440f4fd
-/
@[simp] theorem evaluation_inversePA :
    evaluation k e t hPA hPB hDetN ht (inversePA k) = (e (PA k))⁻¹ := by
  simpa only [evaluation_coefficient] using
    map_inverse (evaluation k e t hPA hPB hDetN ht) (PA_mul_inversePA k)

/--
@isnad1 id=eq.4h3v.s9.b960f75d9a7e from=translated src=- shape=a57a4d4b vocab=7bf1123f
-/
@[simp] theorem evaluation_inversePB :
    evaluation k e t hPA hPB hDetN ht (inversePB k) = (e (PB k))⁻¹ := by
  simpa only [evaluation_coefficient] using
    map_inverse (evaluation k e t hPA hPB hDetN ht) (PB_mul_inversePB k)

/--
@isnad1 id=eq.4h3v.s9.92dd99148060 from=translated src=- shape=a8d6bae9 vocab=9efe50c7
-/
@[simp] theorem evaluation_inverseRoot :
    evaluation k e t hPA hPB hDetN ht (inverseRoot k) = t⁻¹ := by
  simpa only [evaluation_root] using
    map_inverse (evaluation k e t hPA hPB hDetN ht) (root_mul_inverseRoot k)

/--
@isnad1 id=eq.4h3v.s9.ddabd29d73ae from=translated src=- shape=3a7958ab vocab=be5b969c
-/
@[simp] theorem evaluation_inverseDetN :
    evaluation k e t hPA hPB hDetN ht (inverseDetN k) = (e (Matrix.det (N k)))⁻¹ := by
  simpa only [evaluation_coefficient] using
    map_inverse (evaluation k e t hPA hPB hDetN ht) (detN_mul_inverseDetN k)

/-- One nonzero allowed specialization proves ambient generic nonvanishing.
@isnad1 id=ne.5h4v.s11.81c89b1bba59 from=translated src=- shape=a56ae280 vocab=1544f6cc
-/
theorem ambient_ne_zero_of_evaluation_ne_zero {z : LocalRing k}
    (hz : evaluation k e t hPA hPB hDetN ht z ≠ 0) : j k z ≠ 0 := by
  intro hjz
  have hz0 : z = 0 := j_injective k (by simpa only [map_zero] using hjz)
  apply hz
  rw [hz0, map_zero]

end AlbertLean.Generic.GenericDetectorLocalization
