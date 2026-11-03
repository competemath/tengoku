import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionWordMatrixConnection
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticLiteralFixedTwelve

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms symplecticPart_form` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms symplecticPart_standard_hyperbolicTriple` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_fixed_twelve_scalar_presentation_for_gsp_extension_agreement` (it only prints; the queue checks the axioms of every declaration). -/

/-! A root-free, literal twelve-transvection presentation of every explicitly
invertible symplectic similitude.  The final scalar factor is
`diag(mu I, I)` in the grouped basis. -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.SimilitudeWordCoverage

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SymplecticMatrixBridge
open AlbertLean.Generic.QuaternionRow.ActualFrameCoverage
open AlbertLean.Generic.QuaternionRow.WordMatrixConnection
open AlbertLean.Generic.SymplecticTransvection

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Remove the multiplier from the right, without choosing a square root.-/
def symplecticPart (M : Mat6 K) (mu : K) : Mat6 K :=
  M * scalarSimilitudeInv mu

/-- The right-normalized part of a similitude is symplectic.-/
theorem symplecticPart_form
    (M : Mat6 K) (mu : K) (hmu : mu ≠ 0)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    (symplecticPart M mu).transpose * symplecticJ * symplecticPart M mu =
      symplecticJ := by
  have hD :
      (scalarSimilitudeInv mu).transpose * symplecticJ * scalarSimilitudeInv mu =
        mu⁻¹ • symplecticJ := by
    change (scalarSimilitude mu⁻¹).transpose * symplecticJ *
      scalarSimilitude mu⁻¹ = mu⁻¹ • symplecticJ
    exact scalarSimilitude_form mu⁻¹
  calc
    (symplecticPart M mu).transpose * symplecticJ * symplecticPart M mu =
        (scalarSimilitudeInv mu).transpose *
          (M.transpose * symplecticJ * M) * scalarSimilitudeInv mu := by
            simp only [symplecticPart, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (scalarSimilitudeInv mu).transpose *
          (mu • symplecticJ) * scalarSimilitudeInv mu := by rw [hform]
    _ = mu • ((scalarSimilitudeInv mu).transpose * symplecticJ *
          scalarSimilitudeInv mu) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul]
    _ = mu • (mu⁻¹ • symplecticJ) := by rw [hD]
    _ = symplecticJ := by simp [smul_smul, hmu]

private theorem symplecticPart_preserves_basis_pair
    (M : Mat6 K) (mu : K) (hmu : mu ≠ 0)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ)
    (i j : Ix6) :
    (omega (K := K))
        (matrixAction (symplecticPart M mu) (basisVector i))
        (matrixAction (symplecticPart M mu) (basisVector j)) =
      (omega (K := K)) (basisVector i) (basisVector j) := by
  rw [matrixAction_basisVector, matrixAction_basisVector,
    ← symplectic_product_entry, symplecticPart_form M mu hmu hform,
    omega_basisVector]

/-- The images of the literal grouped basis by the normalized part form the
hyperbolic triple needed by the fixed-word coverage theorem.-/
theorem symplecticPart_standard_hyperbolicTriple
    (M : Mat6 K) (mu : K) (hmu : mu ≠ 0)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    HyperbolicTriple (omega (K := K))
      (fun i => matrixAction (symplecticPart M mu) (standardE i))
      (fun i => matrixAction (symplecticPart M mu) (standardF i)) := by
  let hstd := standard_hyperbolicTriple (K := K)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    change (omega (K := K))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inl i)))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inr i))) = 1
    rw [symplecticPart_preserves_basis_pair M mu hmu hform]
    simpa only [standardE, standardF] using hstd.pair i
  · intro i j hij
    change (omega (K := K))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inl i)))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inl j))) = 0
    rw [symplecticPart_preserves_basis_pair M mu hmu hform]
    simpa only [standardE] using hstd.uu i j hij
  · intro i j hij
    change (omega (K := K))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inl i)))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inr j))) = 0
    rw [symplecticPart_preserves_basis_pair M mu hmu hform]
    simpa only [standardE, standardF] using hstd.uv i j hij
  · intro i j hij
    change (omega (K := K))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inr i)))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inl j))) = 0
    rw [symplecticPart_preserves_basis_pair M mu hmu hform]
    simpa only [standardE, standardF] using hstd.vu i j hij
  · intro i j hij
    change (omega (K := K))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inr i)))
      (matrixAction (symplecticPart M mu) (basisVector (Sum.inr j))) = 0
    rw [symplecticPart_preserves_basis_pair M mu hmu hform]
    simpa only [standardF] using hstd.vv i j hij

/-- The explicit 85-parameter presentation used by the future extension
identity argument: twelve transvections (72 direction coordinates and 12 coefficients) followed by
one scalar similitude parameter.  The inverse matrix is retained as an
explicit hypothesis, matching the GSp input interface, although the displayed
factorization itself only needs the multiplier equation.-/
theorem exists_fixed_twelve_scalar_presentation_for_gsp_extension_agreement
    (M N : Mat6 K) (mu : K)
    (hMN : M * N = 1) (hNM : N * M = 1) (hmu : mu ≠ 0)
    (hform : M.transpose * symplecticJ * M = mu • symplecticJ) :
    ∃ schedule : FixedTwelveSchedule (K := K) (V := Vec6 K),
      M = matrixOfLinear (fixedTwelveMap (omega (K := K)) schedule) *
        scalarSimilitude mu := by
  let U := symplecticPart M mu
  have htarget : HyperbolicTriple (omega (K := K))
      (fun i => matrixAction U (standardE i))
      (fun i => matrixAction U (standardF i)) := by
    exact symplecticPart_standard_hyperbolicTriple M mu hmu hform
  obtain ⟨schedule, hsE, hsF⟩ :=
    exists_literal_fixed_twelve_triple_alignment
      (omega (K := K)) omega_alternating omega_left_nondegenerate
      omega_right_nondegenerate
      (standardE (K := K)) (standardF (K := K))
      (fun i => matrixAction U (standardE i))
      (fun i => matrixAction U (standardF i))
      (standard_hyperbolicTriple (K := K)) htarget
  have hmap : fixedTwelveMap (omega (K := K)) schedule = matrixAction U := by
    apply LinearMap.ext
    intro x
    obtain ⟨a, b, hx⟩ := standard_spans (K := K) x
    rw [hx]
    simp only [map_add, map_sum, map_smul, hsE, hsF]
  have hword : matrixOfLinear (fixedTwelveMap (omega (K := K)) schedule) = U := by
    apply matrixAction_injective
    rw [matrixAction_matrixOfLinear]
    exact hmap
  refine ⟨schedule, ?_⟩
  rw [hword]
  change M = (M * scalarSimilitudeInv mu) * scalarSimilitude mu
  rw [Matrix.mul_assoc, scalarSimilitude_inv_mul mu hmu, Matrix.mul_one]

end AlbertLean.Generic.QuaternionRow.SimilitudeWordCoverage
