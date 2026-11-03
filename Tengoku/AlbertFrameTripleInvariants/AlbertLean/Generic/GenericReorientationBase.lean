import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericDeterminantOpen
import Tengoku.Seed.RingTheory.Localization.Away.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms localHom_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms numerator_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_involutive` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_constant` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_off` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms reorient_orientation` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The actual weighted-transpose involution of the existing nineteen-variable
base field. The only intermediate localization inverts the gauge variable a.
No new fraction field, algebraic-independence hypothesis, or AsSubring import.
-/

noncomputable section

namespace AlbertLean.Generic.GenericReorientationBase

open Matrix
open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.GenericDeterminantOpen

universe u
variable (k : Type u) [Field k] [CharZero k]

abbrev LocalRing := Localization (Submonoid.powers (a k))

def loc : R k →+* LocalRing k := algebraMap (R k) (LocalRing k)
def invA : LocalRing k := IsLocalization.Away.invSelf (a k)

@[simp] theorem a_mul_invA : loc k (a k) * invA k = 1 :=
  IsLocalization.Away.mul_invSelf (a k)

@[simp] theorem invA_mul_a : invA k * loc k (a k) = 1 := by
  rw [mul_comm, a_mul_invA]

def swapOff (ij : OffDiagonal) : OffDiagonal :=
  ⟨(ij.1.2, ij.1.1), Ne.symm ij.2⟩

@[simp] theorem swapOff_swapOff (ij : OffDiagonal) : swapOff (swapOff ij) = ij := by
  apply Subtype.ext
  rfl

def localWeight (i : Fin 4) : LocalRing k := if i < 2 then 1 else loc k (a k)
def localInvWeight (i : Fin 4) : LocalRing k := if i < 2 then 1 else invA k

@[simp] theorem localWeight_cancel (i : Fin 4) :
    localInvWeight k i * localWeight k i = 1 := by
  unfold localInvWeight localWeight
  split_ifs <;> simp

/-- Concrete polynomial-generator images in P[a^-1].-/
def localImage : BaseVar → LocalRing k
  | Sum.inl i => loc k (diagX k i)
  | Sum.inr (Sum.inl i) =>
      ![loc k (a k), invA k * loc k (c k), loc k (a k) * loc k (b k)] i
  | Sum.inr (Sum.inr ij) =>
      localInvWeight k ij.1.1 * localWeight k ij.1.2 * loc k (offX k (swapOff ij))

def polynomialMap : R k →+* LocalRing k :=
  MvPolynomial.eval₂Hom ((loc k).comp MvPolynomial.C) (localImage k)

@[simp] theorem polynomialMap_C (z : k) :
    polynomialMap k (MvPolynomial.C z) = loc k (MvPolynomial.C z) := by
  simp [polynomialMap]

@[simp] theorem polynomialMap_diag (i : Fin 4) :
    polynomialMap k (diagX k i) = loc k (diagX k i) := by
  simp [polynomialMap, diagX, x, localImage]

@[simp] theorem polynomialMap_a : polynomialMap k (a k) = loc k (a k) := by
  simp [polynomialMap, a, gaugeX, x, localImage]

@[simp] theorem polynomialMap_b :
    polynomialMap k (b k) = invA k * loc k (c k) := by
  simp [polynomialMap, b, gaugeX, x, localImage]

@[simp] theorem polynomialMap_c :
    polynomialMap k (c k) = loc k (a k) * loc k (b k) := by
  simp [polynomialMap, c, gaugeX, x, localImage]

@[simp] theorem polynomialMap_off (ij : OffDiagonal) :
    polynomialMap k (offX k ij) =
      localInvWeight k ij.1.1 * localWeight k ij.1.2 * loc k (offX k (swapOff ij)) := by
  simp [polynomialMap, offX, x, localImage]

private theorem polynomialMap_a_unit : IsUnit (polynomialMap k (a k)) := by
  rw [polynomialMap_a]
  exact IsLocalization.Away.algebraMap_isUnit (a k)

/-- Localization's universal property constructs this before injectivity.-/
def localHom : LocalRing k →+* LocalRing k :=
  IsLocalization.Away.lift (a k) (polynomialMap_a_unit k)

@[simp] theorem localHom_loc (p : R k) :
    localHom k (loc k p) = polynomialMap k p :=
  IsLocalization.Away.lift_eq (a k) (polynomialMap_a_unit k) p

@[simp] theorem localHom_C (z : k) :
    localHom k (loc k (MvPolynomial.C z)) = loc k (MvPolynomial.C z) := by
  rw [localHom_loc, polynomialMap_C]

@[simp] theorem localHom_diag (i : Fin 4) :
    localHom k (loc k (diagX k i)) = loc k (diagX k i) := by
  rw [localHom_loc, polynomialMap_diag]

@[simp] theorem localHom_a : localHom k (loc k (a k)) = loc k (a k) := by
  rw [localHom_loc, polynomialMap_a]

@[simp] theorem localHom_b :
    localHom k (loc k (b k)) = invA k * loc k (c k) := by
  rw [localHom_loc, polynomialMap_b]

@[simp] theorem localHom_c :
    localHom k (loc k (c k)) = loc k (a k) * loc k (b k) := by
  rw [localHom_loc, polynomialMap_c]

@[simp] theorem localHom_invA : localHom k (invA k) = invA k := by
  have h := congrArg (localHom k) (a_mul_invA k)
  rw [map_mul, localHom_a, map_one] at h
  have hh := congrArg (fun z => invA k * z) h
  simpa only [← mul_assoc, invA_mul_a, one_mul, mul_one] using hh

@[simp] theorem localHom_weight (i : Fin 4) :
    localHom k (localWeight k i) = localWeight k i := by
  unfold localWeight
  split_ifs <;> simp only [map_one, localHom_a]

@[simp] theorem localHom_invWeight (i : Fin 4) :
    localHom k (localInvWeight k i) = localInvWeight k i := by
  unfold localInvWeight
  split_ifs <;> simp only [map_one, localHom_invA]

@[simp] theorem localHom_off (ij : OffDiagonal) :
    localHom k (loc k (offX k ij)) =
      localInvWeight k ij.1.1 * localWeight k ij.1.2 * loc k (offX k (swapOff ij)) := by
  rw [localHom_loc, polynomialMap_off]

private theorem localHom_twice_b :
    localHom k (localHom k (loc k (b k))) = loc k (b k) := by
  rw [localHom_b, map_mul, localHom_invA, localHom_c, ← mul_assoc, invA_mul_a, one_mul]

private theorem localHom_twice_c :
    localHom k (localHom k (loc k (c k))) = loc k (c k) := by
  rw [localHom_c, map_mul, localHom_a, localHom_b, ← mul_assoc, a_mul_invA, one_mul]

private theorem localHom_twice_off (ij : OffDiagonal) :
    localHom k (localHom k (loc k (offX k ij))) = loc k (offX k ij) := by
  rw [localHom_off, map_mul, map_mul, localHom_invWeight, localHom_weight,
    localHom_off, swapOff_swapOff]
  change (localInvWeight k ij.1.1 * localWeight k ij.1.2) *
    (localInvWeight k ij.1.2 * localWeight k ij.1.1 * loc k (offX k ij)) = _
  calc
    _ = (localInvWeight k ij.1.1 * localWeight k ij.1.1) *
        (localInvWeight k ij.1.2 * localWeight k ij.1.2) * loc k (offX k ij) := by ring
    _ = loc k (offX k ij) := by rw [localWeight_cancel, localWeight_cancel]; simp

theorem localHom_involutive :
    (localHom k).comp (localHom k) = RingHom.id (LocalRing k) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (a k))
  ext z
  · change localHom k (localHom k (loc k (MvPolynomial.C z))) = loc k (MvPolynomial.C z)
    rw [localHom_C, localHom_C]
  · change localHom k (localHom k (loc k (MvPolynomial.X z))) = loc k (MvPolynomial.X z)
    rcases z with i | (i | ij)
    · change localHom k (localHom k (loc k (diagX k i))) = _
      rw [localHom_diag, localHom_diag]
      rfl
    · fin_cases i
      · change localHom k (localHom k (loc k (a k))) = _
        rw [localHom_a, localHom_a]
        rfl
      · exact localHom_twice_b k
      · exact localHom_twice_c k
    · exact localHom_twice_off k ij

@[simp] theorem localHom_twice (z : LocalRing k) : localHom k (localHom k z) = z :=
  RingHom.congr_fun (localHom_involutive k) z

def localEquiv : LocalRing k ≃+* LocalRing k where
  toFun := localHom k
  invFun := localHom k
  left_inv := localHom_twice k
  right_inv := localHom_twice k
  map_add' := (localHom k).map_add
  map_mul' := (localHom k).map_mul

/-- The sole open needed for this base-field construction.-/
theorem base_a_ne_zero : ι k (a k) ≠ 0 := by
  intro h
  have hp : a k = 0 := iota_injective k (by simpa only [map_zero] using h)
  exact (MvPolynomial.X_ne_zero (R := k) (Sum.inr (Sum.inl (0 : Fin 3)) : BaseVar)) hp

private theorem base_a_unit : IsUnit (ι k (a k)) :=
  isUnit_iff_ne_zero.mpr (base_a_ne_zero k)

/-- Embed the away-localization into the existing coefficient field B.-/
def embed : LocalRing k →+* B k :=
  IsLocalization.Away.lift (a k) (base_a_unit k)

@[simp] theorem embed_loc (p : R k) : embed k (loc k p) = ι k p :=
  IsLocalization.Away.lift_eq (a k) (base_a_unit k) p

@[simp] theorem embed_invA : embed k (invA k) = (ι k (a k))⁻¹ := by
  apply mul_left_cancel₀ (base_a_ne_zero k)
  have h := congrArg (embed k) (a_mul_invA k)
  rw [map_mul, embed_loc, map_one] at h
  rw [h, mul_inv_cancel₀ (base_a_ne_zero k)]

theorem embed_injective : Function.Injective (embed k) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (a k)) (embed k)).2
  intro p q
  constructor
  · exact congrArg (embed k)
  · intro h
    change embed k (loc k p) = embed k (loc k q) at h
    have hpq : p = q := iota_injective k (by simpa only [embed_loc] using h)
    exact congrArg (loc k) hpq

theorem loc_injective : Function.Injective (loc k) := by
  intro p q h
  apply iota_injective k
  simpa only [embed_loc] using congrArg (embed k) h

def numerator : R k →+* B k :=
  (embed k).comp ((localHom k).comp (loc k))

theorem numerator_injective : Function.Injective (numerator k) :=
  (embed_injective k).comp ((localEquiv k).injective.comp (loc_injective k))

/-- Actual endomorphism of the original Frac(k[BaseVar]).-/
def baseHom : B k →+* B k := IsFractionRing.lift (numerator_injective k)

@[simp] theorem baseHom_polynomial (p : R k) :
    baseHom k (ι k p) = numerator k p :=
  IsFractionRing.lift_algebraMap _ p

private theorem baseHom_embed_hom :
    (baseHom k).comp (embed k) = (embed k).comp (localHom k) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (a k))
  apply RingHom.ext
  intro p
  change baseHom k (embed k (loc k p)) = embed k (localHom k (loc k p))
  rw [embed_loc, baseHom_polynomial]
  rfl

@[simp] theorem baseHom_embed (z : LocalRing k) :
    baseHom k (embed k z) = embed k (localHom k z) :=
  RingHom.congr_fun (baseHom_embed_hom k) z

theorem baseHom_involutive : (baseHom k).comp (baseHom k) = RingHom.id (B k) := by
  apply IsFractionRing.ringHom_ext (A := R k)
  intro p
  change baseHom k (baseHom k (ι k p)) = ι k p
  rw [baseHom_polynomial]
  change baseHom k (embed k (localHom k (loc k p))) = _
  rw [baseHom_embed, localHom_twice, embed_loc]

@[simp] theorem baseHom_twice (z : B k) : baseHom k (baseHom k z) = z :=
  RingHom.congr_fun (baseHom_involutive k) z

/-- Reorientation on the literal existing nineteen-variable generic base.-/
def reorient : B k ≃+* B k where
  toFun := baseHom k
  invFun := baseHom k
  left_inv := baseHom_twice k
  right_inv := baseHom_twice k
  map_add' := (baseHom k).map_add
  map_mul' := (baseHom k).map_mul

@[simp] theorem reorient_twice (z : B k) : reorient k (reorient k z) = z :=
  baseHom_twice k z

theorem reorient_involutive : (reorient k).trans (reorient k) = RingEquiv.refl _ := by
  ext z
  exact reorient_twice k z

private theorem reorient_polynomial (p : R k) :
    reorient k (ι k p) = embed k (localHom k (loc k p)) :=
  baseHom_polynomial k p

@[simp] theorem reorient_C (z : k) :
    reorient k (ι k (MvPolynomial.C z)) = ι k (MvPolynomial.C z) := by
  rw [reorient_polynomial, localHom_C, embed_loc]

@[simp] theorem reorient_constant (z : k) :
    reorient k (algebraMap k (B k) z) = algebraMap k (B k) z := by
  have h : algebraMap k (B k) z = ι k (MvPolynomial.C z) :=
    IsScalarTower.algebraMap_apply k (R k) (B k) z
  rw [h, reorient_C]

@[simp] theorem reorient_diag (i : Fin 4) :
    reorient k (ι k (diagX k i)) = ι k (diagX k i) := by
  rw [reorient_polynomial, localHom_diag, embed_loc]

@[simp] theorem reorient_a : reorient k (ι k (a k)) = ι k (a k) := by
  rw [reorient_polynomial, localHom_a, embed_loc]

@[simp] theorem reorient_b : reorient k (ι k (b k)) = ι k (c k) / ι k (a k) := by
  rw [reorient_polynomial, localHom_b, map_mul, embed_invA, embed_loc]
  rw [div_eq_mul_inv, mul_comm]

@[simp] theorem reorient_c : reorient k (ι k (c k)) = ι k (a k) * ι k (b k) := by
  rw [reorient_polynomial, localHom_c, map_mul, embed_loc, embed_loc]

def weight (i : Fin 4) : B k := if i < 2 then 1 else ι k (a k)

theorem weight_ne_zero (i : Fin 4) : weight k i ≠ 0 := by
  unfold weight
  split_ifs
  · exact one_ne_zero
  · exact base_a_ne_zero k

private theorem embed_weight (i : Fin 4) :
    embed k (localWeight k i) = weight k i := by
  unfold localWeight weight
  split_ifs <;> simp only [map_one, embed_loc]

private theorem embed_invWeight (i : Fin 4) :
    embed k (localInvWeight k i) = (weight k i)⁻¹ := by
  unfold localInvWeight weight
  split_ifs <;> simp only [map_one, inv_one, embed_invA]

@[simp] theorem reorient_off (ij : OffDiagonal) :
    reorient k (ι k (offX k ij)) =
      (weight k ij.1.1)⁻¹ * weight k ij.1.2 * ι k (offX k (swapOff ij)) := by
  rw [reorient_polynomial, localHom_off, map_mul, map_mul,
    embed_invWeight, embed_weight, embed_loc]

@[simp] theorem reorient_orientation :
    reorient k (ι k (c k) - ι k (a k) * ι k (b k)) =
      -(ι k (c k) - ι k (a k) * ι k (b k)) := by
  rw [map_sub, map_mul, reorient_c, reorient_a, reorient_b]
  field_simp [base_a_ne_zero k]
  ring

end AlbertLean.Generic.GenericReorientationBase
