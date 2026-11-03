import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionActualWeightedSecondProjector

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms weightedCoordinateEquiv_symm_eq_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms coordinateConjugate_eq_formula` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms pivotBlock_entry_eq_formula` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Explicit inverse coordinates for the exact weighted equivalence.

The field theorem is extracted from `weighted_pairing_extract_reverse`; the
displayed formula itself is defined over a commutative ring and uses supplied
inverse parameters only.  This is the finite formula needed before adjoining
the quadratic splitter root.
-/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.WeightedInverseCoordinates

open scoped BigOperators
open GroupedBridge SelfAdjointCarrier SymplecticMatrixBridge
open WeightedProjectorGauge

universe u

/-- The polynomial expression underlying the fixed symplectic pairing.-/
def finiteOmega {R : Type u} [CommRing R] (x y : Ix6 → R) : R :=
  ∑ i : Fin 3,
    (x (Sum.inl i) * y (Sum.inr i) -
      x (Sum.inr i) * y (Sum.inl i))

/-- The literal six-column weighted coordinate map, written without any
field or linear-equivalence structure.-/
def weightedForwardFormula {R : Type u} [CommRing R]
    (Eu Ev : Fin 3 → Ix6 → R) (z : Ix6 → R) : Ix6 → R :=
  fun q =>
    (∑ i : Fin 3, z (Sum.inl i) * Eu i q) +
      ∑ i : Fin 3, z (Sum.inr i) * Ev i q

/-- Finite inverse-coordinate formula.  `pinv i` is an explicit parameter;
the definition neither chooses nor assumes an inverse.-/
def weightedInverseFormula {R : Type u} [CommRing R]
    (Eu Ev : Fin 3 → Ix6 → R) (pinv : Fin 3 → R)
    (w : Ix6 → R) : Ix6 → R
  | Sum.inl i => -(finiteOmega (Ev i) w) * pinv i
  | Sum.inr i => finiteOmega (Eu i) w * pinv i

/-- The finite conjugation formula obtained by substituting the displayed
forward and inverse coordinates.-/
def coordinateConjugateFormula {R : Type u} [CommRing R]
    (Eu Ev : Fin 3 → Ix6 → R) (pinv : Fin 3 → R)
    (T : (Ix6 → R) → (Ix6 → R)) (z : Ix6 → R) : Ix6 → R :=
  weightedInverseFormula Eu Ev pinv (T (weightedForwardFormula Eu Ev z))

variable {K : Type u} [Field K] [CharZero K]

private theorem finiteOmega_eq_omega (x y : Vec6 K) :
    finiteOmega x y = (omega (K := K)) x y := rfl

/-- Pairing extraction computes the inverse of the exact, already selected
`weightedCoordinateEquiv`; no replacement equivalence is introduced.
@isnad1 id=other.4h7v.s12.a02634e5e5ef from=translated src=- shape=520992fa vocab=dd95bec2
-/
theorem weightedCoordinateEquiv_symm_apply
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (w : Vec6 K) (i : Fin 3) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    (L.symm w) (Sum.inl i) =
        -((omega (K := K)) (matrixAction (E i : Mat6 K) v) w) * (p i)⁻¹ ∧
      (L.symm w) (Sum.inr i) =
        (omega (K := K)) (matrixAction (E i : Mat6 K) u) w * (p i)⁻¹ := by
  dsimp only
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  have h := weighted_pairing_extract_reverse E hEidem hEsum u v p hp
    (L.symm w) i
  change
    (omega (K := K)) (matrixAction (E i : Mat6 K) u) (L (L.symm w)) =
        (L.symm w) (Sum.inr i) * p i ∧
      (omega (K := K)) (matrixAction (E i : Mat6 K) v) (L (L.symm w)) =
        -((L.symm w) (Sum.inl i) * p i) at h
  rw [L.apply_symm_apply] at h
  have hleft :
      -((omega (K := K)) (matrixAction (E i : Mat6 K) v) w) =
        (L.symm w) (Sum.inl i) * p i := by
    calc
      -((omega (K := K)) (matrixAction (E i : Mat6 K) v) w) =
          -(-((L.symm w) (Sum.inl i) * p i)) := congrArg Neg.neg h.2
      _ = (L.symm w) (Sum.inl i) * p i := neg_neg _
  constructor
  · calc
      (L.symm w) (Sum.inl i) = (L.symm w) (Sum.inl i) * 1 :=
        (mul_one _).symm
      _ = (L.symm w) (Sum.inl i) * (p i * (p i)⁻¹) := by
        rw [mul_inv_cancel₀ (hpne i)]
      _ = ((L.symm w) (Sum.inl i) * p i) * (p i)⁻¹ := by
        rw [mul_assoc]
      _ = -((omega (K := K)) (matrixAction (E i : Mat6 K) v) w) *
          (p i)⁻¹ := by rw [← hleft]
  · calc
      (L.symm w) (Sum.inr i) = (L.symm w) (Sum.inr i) * 1 :=
        (mul_one _).symm
      _ = (L.symm w) (Sum.inr i) * (p i * (p i)⁻¹) := by
        rw [mul_inv_cancel₀ (hpne i)]
      _ = ((L.symm w) (Sum.inr i) * p i) * (p i)⁻¹ := by
        rw [mul_assoc]
      _ = (omega (K := K)) (matrixAction (E i : Mat6 K) u) w *
          (p i)⁻¹ := by rw [← h.1]

/-- Function-valued form of the preceding coordinate equations.
@isnad1 id=other.4h6v.s12.b3491660a8b3 from=translated src=- shape=9900a790 vocab=cd32ffc2
-/
theorem weightedCoordinateEquiv_symm_eq_formula
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (w : Vec6 K) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    L.symm w = weightedInverseFormula
      (fun i => matrixAction (E i : Mat6 K) u)
      (fun i => matrixAction (E i : Mat6 K) v)
      (fun i => (p i)⁻¹) w := by
  dsimp only
  funext q
  rcases q with i | i
  · rw [(weightedCoordinateEquiv_symm_apply E hEidem hEsum u v p hp hpne w i).1]
    simp only [weightedInverseFormula, finiteOmega_eq_omega]
  · rw [(weightedCoordinateEquiv_symm_apply E hEidem hEsum u v p hp hpne w i).2]
    simp only [weightedInverseFormula, finiteOmega_eq_omega]

private theorem weightedCoordinateEquiv_apply_eq_formula
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (z : Vec6 K) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    L z = weightedForwardFormula
      (fun i => matrixAction (E i : Mat6 K) u)
      (fun i => matrixAction (E i : Mat6 K) v) z := by
  dsimp only
  change weightedCoordinateLinear E u v z = weightedForwardFormula
    (fun i => matrixAction (E i : Mat6 K) u)
    (fun i => matrixAction (E i : Mat6 K) v) z
  funext q
  change
    ((∑ i, z (Sum.inl i) • matrixAction (E i : Mat6 K) u) +
      ∑ i, z (Sum.inr i) • matrixAction (E i : Mat6 K) v) q =
      (∑ i, z (Sum.inl i) * matrixAction (E i : Mat6 K) u q) +
        ∑ i, z (Sum.inr i) * matrixAction (E i : Mat6 K) v q
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

/-- `coordinateConjugate` for the exact weighted equivalence is the finite
pairing formula with only the three explicit inverses `p i⁻¹`.
@isnad1 id=other.4h7v.s12.440bf0e0a665 from=translated src=- shape=05cfa9bd vocab=88ba1508
-/
theorem coordinateConjugate_eq_formula
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (T : Vec6 K →ₗ[K] Vec6 K) (z : Vec6 K) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    coordinateConjugate L T z = coordinateConjugateFormula
      (fun i => matrixAction (E i : Mat6 K) u)
      (fun i => matrixAction (E i : Mat6 K) v)
      (fun i => (p i)⁻¹) T z := by
  dsimp only
  let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
  rw [show coordinateConjugate L T z = L.symm (T (L z)) by
    rfl]
  rw [weightedCoordinateEquiv_symm_eq_formula E hEidem hEsum u v p hp hpne]
  rw [weightedCoordinateEquiv_apply_eq_formula E hEidem hEsum u v p hp hpne]
  rfl

/-- In particular, every entry of the pivot block used by the deterministic
splitter is given by the same finite formula.
@isnad1 id=other.4h8v.s12.c1491c03f513 from=translated src=- shape=69ef12f9 vocab=b519c8ea
-/
theorem pivotBlock_entry_eq_formula
    (E : Fin 3 → Carrier K)
    (hEidem : ∀ i, (E i : Mat6 K) * E i = E i)
    (hEsum : (E 0 : Mat6 K) + E 1 + E 2 = 1)
    (u v : Vec6 K) (p : Fin 3 → K)
    (hp : ∀ i, p i = (omega (K := K))
      (matrixAction (E i : Mat6 K) u)
      (matrixAction (E i : Mat6 K) v))
    (hpne : ∀ i, p i ≠ 0) (F1 : Carrier K) (r s : Fin 2) :
    let L := weightedCoordinateEquiv E hEidem hEsum u v p hp hpne
    weightedBlock (coordinateConjugate L (matrixAction (F1 : Mat6 K))) 0 1 r s =
      coordinateConjugateFormula
        (fun i => matrixAction (E i : Mat6 K) u)
        (fun i => matrixAction (E i : Mat6 K) v)
        (fun i => (p i)⁻¹) (matrixAction (F1 : Mat6 K))
        (basisVector (weightedPairIndex 1 s)) (weightedPairIndex 0 r) := by
  dsimp only
  exact congrFun
    (coordinateConjugate_eq_formula E hEidem hEsum u v p hp hpne
      (matrixAction (F1 : Mat6 K)) (basisVector (weightedPairIndex 1 s)))
    (weightedPairIndex 0 r)

end AlbertLean.Generic.QuaternionRow.WeightedInverseCoordinates
