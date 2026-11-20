import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenAlgebra
import Tengoku.Seed.Data.Int.Interval
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The parity-triangle coordinates for two path tokens

This file develops the arithmetic model before it is connected to the token graph itself.
Coordinates `x,y` are one-based.
-/

namespace BurningPath

/-- A legal ordered pair of one-based token positions on `P_n`.-/
def TwoPathPoint (n : ℕ) :=
  {p : ℤ × ℤ // 1 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 ≤ n}

/-- The unshifted parity lattice from the square-model remark.-/
def parityLattice (n : ℕ) : Set (ℤ × ℤ) :=
  {p | p.1 ≡ p.2 [ZMOD 2] ∧ 1 ≤ p.2 ∧ 2 ≤ p.1 - p.2 ∧ p.1 + p.2 ≤ 2 * n}

/-- The shifted parity triangle `𝒯_N^(σ)`.-/
def parityTriangle (N : ℕ) (σ : ℤ) : Set (ℤ × ℤ) :=
  {p |
    0 ≤ p.2 ∧ p.2 ≤ N ∧ |p.1| ≤ (N : ℤ) - p.2 ∧ p.1 - p.2 ≡ σ [ZMOD 2]}

/-- The unshifted sum/difference coordinates `(u,v)=(x+y,y-x)`.-/
def twoTokenSquareCoordinates {n : ℕ} (p : TwoPathPoint n) : ℤ × ℤ :=
  (p.1.1 + p.1.2, p.1.2 - p.1.1)

/-- Shifted sum-and-gap coordinates for the parity-triangle model.-/
def twoTokenPhi {n : ℕ} (p : TwoPathPoint n) : ℤ × ℤ :=
  (p.1.1 + p.1.2 - (n + 1), p.1.2 - p.1.1 - 1)

/-- Inverse affine formulas for the parity-triangle coordinates, before proving legality.-/
def twoTokenPhiInverseCoordinates (n : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.1 - p.2 + n) / 2, (p.1 + p.2 + n + 2) / 2)

/-- Translate unshifted square-model coordinates to parity-triangle coordinates.-/
def squareToTriangleCoordinates (n : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 - (n + 1), p.2 - 1)

/-- Translate parity-triangle coordinates back to the unshifted square model.-/
def triangleToSquareCoordinates (n : ℕ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + (n + 1), p.2 + 1)

@[simp]
theorem squareToTriangleCoordinates_twoTokenSquareCoordinates {n : ℕ}
    (p : TwoPathPoint n) :
    squareToTriangleCoordinates n (twoTokenSquareCoordinates p) = twoTokenPhi p :=
  rfl

@[simp]
theorem triangleToSquareCoordinates_squareToTriangleCoordinates (n : ℕ) (p : ℤ × ℤ) :
    triangleToSquareCoordinates n (squareToTriangleCoordinates n p) = p := by
  ext <;> simp [triangleToSquareCoordinates, squareToTriangleCoordinates]

@[simp]
theorem squareToTriangleCoordinates_triangleToSquareCoordinates (n : ℕ) (p : ℤ × ℤ) :
    squareToTriangleCoordinates n (triangleToSquareCoordinates n p) = p := by
  ext <;> simp [triangleToSquareCoordinates, squareToTriangleCoordinates]

/-- The unshifted parity lattice is exactly the translated parity triangle.-/
theorem squareToTriangleCoordinates_mem_iff {n : ℕ} (hn : 2 ≤ n) (p : ℤ × ℤ) :
    squareToTriangleCoordinates n p ∈ parityTriangle (n - 2) n ↔
      p ∈ parityLattice n := by
  have hncast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  simp only [squareToTriangleCoordinates, parityTriangle, parityLattice, Set.mem_ofPred_eq,
    hncast]
  constructor
  · rintro ⟨hY0, hYN, habs, hpar⟩
    rw [abs_le] at habs
    constructor
    · rw [Int.modEq_iff_dvd] at hpar ⊢
      obtain ⟨a, ha⟩ := hpar
      refine ⟨a - n, ?_⟩
      omega
    constructor
    · omega
    constructor <;> omega
  · rintro ⟨hpar, hv, huv, hsum⟩
    constructor
    · omega
    constructor
    · omega
    constructor
    · rw [abs_le]
      constructor <;> omega
    · rw [Int.modEq_iff_dvd] at hpar ⊢
      obtain ⟨a, ha⟩ := hpar
      refine ⟨a + n, ?_⟩
      omega

/-- Legal ordered pairs map into the unshifted parity lattice.-/
theorem twoTokenSquareCoordinates_mem {n : ℕ} (p : TwoPathPoint n) :
    twoTokenSquareCoordinates p ∈ parityLattice n := by
  rcases p.2 with ⟨hx, hxy, hy⟩
  simp only [twoTokenSquareCoordinates, parityLattice, Set.mem_ofPred_eq]
  constructor
  · exact add_modEq_sub_two p.1.1 p.1.2
  constructor
  · omega
  constructor <;> omega

/--
If `σ` is the parity of `n`, the shifted coordinates of a legal pair lie in
`𝒯_(n-2)^(σ)`.-/
theorem twoTokenPhi_mem_parityTriangle {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : TwoPathPoint n) :
    twoTokenPhi p ∈ parityTriangle (n - 2) σ := by
  rcases p.2 with ⟨hx, hxy, hy⟩
  have hncast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  simp only [twoTokenPhi, parityTriangle, Set.mem_ofPred_eq, hncast]
  constructor
  · omega
  constructor
  · omega
  constructor
  · rw [abs_le]
    constructor <;> omega
  · rw [Int.modEq_iff_dvd] at hσ ⊢
    obtain ⟨a, ha⟩ := hσ
    refine ⟨a + ((n : ℤ) - p.1.1), ?_⟩
    omega

/-- The first inverse numerator is even under the triangle parity condition.-/
theorem even_twoTokenPhiInverse_first {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    Even (p.1 - p.2 + n) := by
  have hpar : p.1 - p.2 ≡ σ [ZMOD 2] := hp.2.2.2
  rw [Int.modEq_iff_dvd] at hσ hpar
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ := hpar
  refine ⟨σ - a - b, ?_⟩
  omega

/-- The second inverse numerator is even under the triangle parity condition.-/
theorem even_twoTokenPhiInverse_second {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    Even (p.1 + p.2 + n + 2) := by
  obtain ⟨a, ha⟩ := even_twoTokenPhiInverse_first σ hσ hp
  refine ⟨a + p.2 + 1, ?_⟩
  omega

theorem twoTokenPhiInverse_first_mul_two {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    (twoTokenPhiInverseCoordinates n p).1 * 2 = p.1 - p.2 + n := by
  simpa [twoTokenPhiInverseCoordinates, mul_comm] using
    Int.ediv_two_mul_two_of_even (even_twoTokenPhiInverse_first σ hσ hp)

theorem twoTokenPhiInverse_second_mul_two {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    (twoTokenPhiInverseCoordinates n p).2 * 2 = p.1 + p.2 + n + 2 := by
  simpa [twoTokenPhiInverseCoordinates, mul_comm] using
    Int.ediv_two_mul_two_of_even (even_twoTokenPhiInverse_second σ hσ hp)

/-- The inverse formulas produce a legal ordered token pair.-/
def parityTriangleToTwoPathPoint {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : {z // z ∈ parityTriangle (n - 2) σ}) :
    TwoPathPoint n := by
  refine ⟨twoTokenPhiInverseCoordinates n p.1, ?_⟩
  have hncast : ((n - 2 : ℕ) : ℤ) = (n : ℤ) - 2 := by omega
  have hY0 : 0 ≤ p.1.2 := p.2.1
  have habs := p.2.2.2.1
  rw [hncast, abs_le] at habs
  have hx := twoTokenPhiInverse_first_mul_two σ hσ p.2
  have hy := twoTokenPhiInverse_second_mul_two σ hσ p.2
  constructor
  · omega
  constructor
  · omega
  · omega

@[simp]
theorem parityTriangleToTwoPathPoint_val {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : {z // z ∈ parityTriangle (n - 2) σ}) :
    (parityTriangleToTwoPathPoint hn σ hσ p).1 = twoTokenPhiInverseCoordinates n p.1 :=
  rfl

/-- Applying the inverse formulas after `Φ_n` recovers the original legal pair.-/
theorem parityTriangleToTwoPathPoint_twoTokenPhi {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : TwoPathPoint n) :
    parityTriangleToTwoPathPoint hn σ hσ
        ⟨twoTokenPhi p, twoTokenPhi_mem_parityTriangle hn σ hσ p⟩ = p := by
  apply Subtype.ext
  simp only [parityTriangleToTwoPathPoint_val]
  apply Prod.ext
  · simp only [twoTokenPhiInverseCoordinates, twoTokenPhi]
    rw [show
      p.1.1 + p.1.2 - ((n : ℤ) + 1) - (p.1.2 - p.1.1 - 1) + n =
        2 * p.1.1 by omega]
    exact Int.mul_ediv_cancel_left _ (by norm_num)
  · simp only [twoTokenPhiInverseCoordinates, twoTokenPhi]
    rw [show
      p.1.1 + p.1.2 - ((n : ℤ) + 1) + (p.1.2 - p.1.1 - 1) + n + 2 =
        2 * p.1.2 by omega]
    exact Int.mul_ediv_cancel_left _ (by norm_num)

/-- Applying `Φ_n` after the inverse formulas recovers the parity-triangle point.-/
theorem twoTokenPhi_parityTriangleToTwoPathPoint {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : {z // z ∈ parityTriangle (n - 2) σ}) :
    twoTokenPhi (parityTriangleToTwoPathPoint hn σ hσ p) = p.1 := by
  have hx := twoTokenPhiInverse_first_mul_two σ hσ p.2
  have hy := twoTokenPhiInverse_second_mul_two σ hσ p.2
  rw [show
    twoTokenPhi (parityTriangleToTwoPathPoint hn σ hσ p) =
      ((twoTokenPhiInverseCoordinates n p.1).1 +
          (twoTokenPhiInverseCoordinates n p.1).2 - (n + 1),
        (twoTokenPhiInverseCoordinates n p.1).2 -
          (twoTokenPhiInverseCoordinates n p.1).1 - 1) by rfl]
  apply Prod.ext <;> simp only
  · omega
  · omega

/-- Exact bijection between legal two-token positions and the parity triangle.-/
def twoTokenPhiEquiv {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) :
    TwoPathPoint n ≃ {z // z ∈ parityTriangle (n - 2) σ} where
  toFun p := ⟨twoTokenPhi p, twoTokenPhi_mem_parityTriangle hn σ hσ p⟩
  invFun := parityTriangleToTwoPathPoint hn σ hσ
  left_inv := parityTriangleToTwoPathPoint_twoTokenPhi hn σ hσ
  right_inv p := Subtype.ext (twoTokenPhi_parityTriangleToTwoPathPoint hn σ hσ p)

/-- The unshifted coordinate change is an exact `ℓ₁`-to-`ℓ∞` isometry.-/
theorem twoTokenSquareCoordinates_isometry {n : ℕ} (p q : TwoPathPoint n) :
    max
        ((twoTokenSquareCoordinates p).1 - (twoTokenSquareCoordinates q).1).natAbs
        ((twoTokenSquareCoordinates p).2 - (twoTokenSquareCoordinates q).2).natAbs =
      (p.1.1 - q.1.1).natAbs + (p.1.2 - q.1.2).natAbs := by
  exact max_natAbs_sumDiff_sub_sumDiff p.1.1 p.1.2 q.1.1 q.1.2

/-- The shifted parity-triangle coordinates preserve the exact distance.-/
theorem twoTokenPhi_isometry {n : ℕ} (p q : TwoPathPoint n) :
    max ((twoTokenPhi p).1 - (twoTokenPhi q).1).natAbs
        ((twoTokenPhi p).2 - (twoTokenPhi q).2).natAbs =
      (p.1.1 - q.1.1).natAbs + (p.1.2 - q.1.2).natAbs := by
  simp only [twoTokenPhi]
  rw [show
    p.1.1 + p.1.2 - (n + 1) - (q.1.1 + q.1.2 - (n + 1)) =
      (p.1.1 + p.1.2) - (q.1.1 + q.1.2) by omega]
  rw [show
    p.1.2 - p.1.1 - 1 - (q.1.2 - q.1.1 - 1) =
      (p.1.2 - p.1.1) - (q.1.2 - q.1.1) by omega]
  exact max_natAbs_sumDiff_sub_sumDiff p.1.1 p.1.2 q.1.1 q.1.2

end BurningPath
