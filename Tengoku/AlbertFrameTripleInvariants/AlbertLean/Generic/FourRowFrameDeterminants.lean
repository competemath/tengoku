import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FourRowUniqueness

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameDeterminants.normalized_endpoint_determinants` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameDeterminants.normalized_endpoint_determinants_nonsing_inv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AlbertLean.Generic.FourRowFrameDeterminants.adjugate_normalized_endpoint_determinants` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Endpoint determinants for normalized frame matrices

The argument is ordinary matrix algebra. It does not introduce an Albert
algebra model or identify the component equations with frame laws.

If `Aℓ` denotes the adjugate of the first Tits `aℓ` component and `A0i` is a
two-sided inverse of `A0`, normalization gives

`U = (A0 + A1 - A2) * A0i`,  `V = A1 * A0i`.

The endpoint matrices are therefore `V = A1 * A0i` and
`1 - U + V = A2 * A0i`.  Their determinants are the required squares.  The
lemma below isolates exactly the matrix facts needed by
`FourRowUniqueness.three_goodSolutions_pairwise_eq`.
-/

noncomputable section

namespace AlbertLean.Generic.FourRowFrameDeterminants

universe u

variable {K : Type u} [Field K]

abbrev Mat3 (K : Type u) := Matrix (Fin 3) (Fin 3) K

/-- The normalized endpoint determinant identities.  No matrices are assumed
to commute. The determinant inverse identity is derived from the supplied
right-inverse certificate.

For the intended adjugate specialization, `hdetA1` and `hdetA2` follow from
`det(adjugate a) = det(a)^2` together with
`det a1 = c * det a0` and `det a2 = d * det a0`.
@isnad1 id=and.5h9v.s9.5ae6a515f909 from=translated src=- shape=d7995f0a vocab=f6af96c8
-/
theorem normalized_endpoint_determinants
    (A0 A1 A2 A0i U V : Mat3 K) (c d : K)
    (hA0i : A0 * A0i = 1)
    (hU : U = (A0 + A1 - A2) * A0i)
    (hV : V = A1 * A0i)
    (hdetA1 : A1.det = c ^ 2 * A0.det)
    (hdetA2 : A2.det = d ^ 2 * A0.det) :
    V.det = c ^ 2 ∧ (1 - U + V).det = d ^ 2 := by
  have hdetA0i : A0.det * A0i.det = 1 := by
    simpa only [Matrix.det_mul, Matrix.det_one] using congrArg Matrix.det hA0i
  have hnegOneMatrix : 1 - U + V = A2 * A0i := by
    rw [hU, hV, ← hA0i]
    simp only [add_mul, sub_mul]
    abel
  constructor
  · rw [hV, Matrix.det_mul, hdetA1]
    calc
      c ^ 2 * A0.det * A0i.det = c ^ 2 * (A0.det * A0i.det) := by ring
      _ = c ^ 2 := by rw [hdetA0i, mul_one]
  · rw [hnegOneMatrix, Matrix.det_mul, hdetA2]
    calc
      d ^ 2 * A0.det * A0i.det = d ^ 2 * (A0.det * A0i.det) := by ring
      _ = d ^ 2 := by rw [hdetA0i, mul_one]

/-- Preferred bridge interface when `A0i` is the standard nonsingular inverse.
The caller supplies only nonsingularity of `A0`, the definitions of `U,V`, and
the two adjugate determinant scaling identities.
@isnad1 id=and.5h8v.s9.46f4a20758ae from=translated src=- shape=44a034d1 vocab=311b6d90
-/
theorem normalized_endpoint_determinants_nonsing_inv
    (A0 A1 A2 U V : Mat3 K) (c d : K)
    (hA0 : IsUnit A0.det)
    (hU : U = (A0 + A1 - A2) * A0⁻¹)
    (hV : V = A1 * A0⁻¹)
    (hdetA1 : A1.det = c ^ 2 * A0.det)
    (hdetA2 : A2.det = d ^ 2 * A0.det) :
    V.det = c ^ 2 ∧ (1 - U + V).det = d ^ 2 := by
  apply normalized_endpoint_determinants A0 A1 A2 A0⁻¹ U V c d
  · exact Matrix.mul_nonsing_inv A0 hA0
  · exact hU
  · exact hV
  · exact hdetA1
  · exact hdetA2

/-- Fully specialized endpoint identities for the normalized first-Tits
components.  No frame-sum or commutation hypothesis is needed at this stage.
@isnad1 id=other.1h4v.s10.07cd263699c5 from=translated src=- shape=28c58bc0 vocab=ff3f6fe8
-/
theorem adjugate_normalized_endpoint_determinants
    (a0 a1 a2 : Mat3 K) (ha0 : a0.det ≠ 0) :
    let A0 := Matrix.adjugate a0
    let A1 := Matrix.adjugate a1
    let A2 := Matrix.adjugate a2
    let c := a1.det / a0.det
    let d := a2.det / a0.det
    let U := (A0 + A1 - A2) * A0⁻¹
    let V := A1 * A0⁻¹
    V.det = c ^ 2 ∧ (1 - U + V).det = d ^ 2 := by
  dsimp only
  have hadj (a : Mat3 K) : (Matrix.adjugate a).det = a.det ^ 2 := by
    simpa using Matrix.det_adjugate a
  have hA0det : (Matrix.adjugate a0).det ≠ 0 := by
    rw [hadj]
    exact pow_ne_zero 2 ha0
  apply normalized_endpoint_determinants_nonsing_inv
      (Matrix.adjugate a0) (Matrix.adjugate a1) (Matrix.adjugate a2)
      ((Matrix.adjugate a0 + Matrix.adjugate a1 - Matrix.adjugate a2) *
        (Matrix.adjugate a0)⁻¹)
      (Matrix.adjugate a1 * (Matrix.adjugate a0)⁻¹)
      (a1.det / a0.det) (a2.det / a0.det)
  · exact isUnit_iff_ne_zero.mpr hA0det
  · rfl
  · rfl
  · rw [hadj, hadj]
    field_simp [ha0]
  · rw [hadj, hadj]
    field_simp [ha0]

end AlbertLean.Generic.FourRowFrameDeterminants
