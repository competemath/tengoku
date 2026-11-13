import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_NormTheta_Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Coefficient Formula (Theorem 5)

B_N = Σ BWeight(k,r) over all (k,r) with E(k,r) = N.
Formalized as BCoeff = ACoeff + DCoeff, with completeness lemmas showing
the bounding boxes capture all solutions.

## Strategy
- Nat-parametrize each cone: A-cone ≅ ℕ², D-cone via (m,s) ↦ (-(m+1),-(s+1))
- Crude bounds via Q = 2N (division-free): k ≤ N, r ≤ 2N+1
- Completeness: if in cone and E = N, then in box
- Sanity check: decide specific coefficients
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Completeness: A-cone bounds

If k ≥ 0, r ≥ 0, and E(k,r) = N, then k ≤ N and r ≤ 2N+1.
Proved via Q = 2N (no triZ division).
-/

/--
@isnad1 id=le.3h3v.s5.4ac3c2b62664 from=translated src=- shape=510a2288 vocab=08177ece
-/
theorem A_bound_k (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) (hE : E k r = ↑N) :
    k ≤ ↑N := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  nlinarith [sq_nonneg r, mul_nonneg hk hr]

/--
@isnad1 id=le.3h3v.s5.3ecaf5a89280 from=translated src=- shape=b37f1717 vocab=1a032775
-/
theorem A_bound_r (k r : Int) (hk : 0 ≤ k) (hr : 0 ≤ r) (hE : E k r = ↑N) :
    r ≤ 2 * ↑N + 1 := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  nlinarith [sq_nonneg k, mul_nonneg hk hr]

/-! ## Completeness: D-cone bounds

If k < 0, r < 0, and E(k,r) = N, then -(N+1) ≤ k and -(2N+2) ≤ r.
Equivalently, writing k = -(m+1), r = -(s+1): m ≤ N and s ≤ 2N+1.
-/

/--
@isnad1 id=le.3h3v.s5.3a4b2d0f56d0 from=translated src=- shape=b52d4655 vocab=39e1443b
-/
theorem D_bound_k (k r : Int) (hk : k < 0) (hr : r < 0) (hE : E k r = ↑N) :
    -(↑N + 1) ≤ k := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  have hkr : 0 ≤ (-k - 1) * (-r - 1) := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg r, sq_nonneg (k + r)]

/--
@isnad1 id=le.3h3v.s6.258a5815cba8 from=translated src=- shape=d5efab79 vocab=7addb476
-/
theorem D_bound_r (k r : Int) (hk : k < 0) (hr : r < 0) (hE : E k r = ↑N) :
    -(2 * ↑N + 2) ≤ r := by
  have hQ : Q k r = 2 * ↑N := by
    have := Q_eq_two_mul_E k r; omega
  simp only [Q] at hQ
  have hkr : 0 ≤ (-k - 1) * (-r - 1) := mul_nonneg (by omega) (by omega)
  nlinarith [sq_nonneg k, sq_nonneg (k + r)]

/-! ## Sanity check: kernel-verified small coefficients -/

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s4.e5d450878d3b from=translated src=- shape=b5968027 vocab=fe947022
-/
theorem B_coeff_0 : BCoeff 0 = -1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.4a7668f0742e from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_1 : BCoeff 1 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.2fbb5467a0ea from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_2 : BCoeff 2 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s4.9bfb7e250951 from=translated src=- shape=b5968027 vocab=fe947022
-/
theorem B_coeff_3 : BCoeff 3 = -2 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s4.068b84ca51dc from=translated src=- shape=b5968027 vocab=fe947022
-/
theorem B_coeff_4 : BCoeff 4 = -1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.42650fab204a from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_5 : BCoeff 5 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.c56acc80e988 from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_6 : BCoeff 6 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.ee09170b64ab from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_7 : BCoeff 7 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.61948e78e48a from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_8 : BCoeff 8 = 1 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s3.44221ade7b3f from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_9 : BCoeff 9 = 0 := by decide
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 2000 in
/--
@isnad1 id=eq.0h0v.s4.89fe6fee3f2f from=translated src=- shape=b5968027 vocab=fe947022
-/
theorem B_coeff_10 : BCoeff 10 = -2 := by decide

/-! ## Large coefficient: kernel-checked evaluation -/

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 4000 in
/--
@isnad1 id=eq.0h0v.s3.108851b5c321 from=translated src=- shape=1ac31801 vocab=a928f163
-/
theorem B_coeff_34 : BCoeff 34 = 3 := by decide

/-- The coefficient sequence fails multiplicativity on the norm variables
`11`, `31`, and `341 = 11 * 31`.
@isnad1 id=ne.0h0v.s4.5d20d92de534 from=translated src=- shape=8262217e vocab=1fdf08bb
-/
theorem BCoeff_not_multiplicative_witness :
    BCoeff 34 ≠ BCoeff 1 * BCoeff 3 := by
  rw [B_coeff_34, B_coeff_1, B_coeff_3]
  norm_num

/-! ## Norm support (Theorem C)

If ACoeff N ≠ 0, there exists β ∈ L with N(β) = -(10N+1).
Proof: sum ≠ 0 ⟹ filtered finset nonempty ⟹ ∃ (k,r) with E=N ⟹ beta(k,r) witnesses.
-/

/-! ## Combined norm support (Theorem C)

B_N ≠ 0 ⟹ 10N+1 is a norm from Z[φ].
-/

end Ch10
end QseriesFormalization
