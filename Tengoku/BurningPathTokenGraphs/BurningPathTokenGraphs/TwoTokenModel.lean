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

/--
@isnad1 id=eq.0h2v.s4.26e65938925f from=translated src=- shape=2a935572 vocab=cba25f94
-/
@[simp]
theorem squareToTriangleCoordinates_twoTokenSquareCoordinates {n : ℕ}
    (p : TwoPathPoint n) :
    squareToTriangleCoordinates n (twoTokenSquareCoordinates p) = twoTokenPhi p :=
  rfl

/--
@isnad1 id=eq.0h2v.s4.0774750bc63b from=translated src=- shape=d0414de6 vocab=9ba5e1b3
-/
@[simp]
theorem triangleToSquareCoordinates_squareToTriangleCoordinates (n : ℕ) (p : ℤ × ℤ) :
    triangleToSquareCoordinates n (squareToTriangleCoordinates n p) = p := by
  ext <;> simp [triangleToSquareCoordinates, squareToTriangleCoordinates]

/--
@isnad1 id=eq.0h2v.s4.b734c619c009 from=translated src=- shape=d0414de6 vocab=9ba5e1b3
-/
@[simp]
theorem squareToTriangleCoordinates_triangleToSquareCoordinates (n : ℕ) (p : ℤ × ℤ) :
    squareToTriangleCoordinates n (triangleToSquareCoordinates n p) = p := by
  ext <;> simp [triangleToSquareCoordinates, squareToTriangleCoordinates]

/-- The unshifted parity lattice is exactly the translated parity triangle.
@isnad1 id=iff.1h2v.s6.0f8ee9a9d4c8 from=translated src=- shape=2e3248dc vocab=ac7e33bb
-/
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

/-- Legal ordered pairs map into the unshifted parity lattice.
@isnad1 id=mem.0h2v.s4.8c8ae5f676de from=translated src=- shape=6cce048f vocab=24355d3c
-/
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
`𝒯_(n-2)^(σ)`.
@isnad1 id=mem.2h3v.s5.582c8ea3880a from=translated src=- shape=01ea1c19 vocab=969be0dd
-/
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

/-- The first inverse numerator is even under the triangle parity condition.
@isnad1 id=even.2h3v.s6.968bac1801e2 from=translated src=- shape=8679676e vocab=0f80cb53
-/
theorem even_twoTokenPhiInverse_first {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    Even (p.1 - p.2 + n) := by
  have hpar : p.1 - p.2 ≡ σ [ZMOD 2] := hp.2.2.2
  rw [Int.modEq_iff_dvd] at hσ hpar
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨b, hb⟩ := hpar
  refine ⟨σ - a - b, ?_⟩
  omega

/-- The second inverse numerator is even under the triangle parity condition.
@isnad1 id=even.2h3v.s6.c19ac21620b4 from=translated src=- shape=fdee4fc4 vocab=0f80cb53
-/
theorem even_twoTokenPhiInverse_second {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    Even (p.1 + p.2 + n + 2) := by
  obtain ⟨a, ha⟩ := even_twoTokenPhiInverse_first σ hσ hp
  refine ⟨a + p.2 + 1, ?_⟩
  omega

/--
@isnad1 id=eq.2h3v.s6.d71c4667c051 from=translated src=- shape=2d4bddb5 vocab=46159bbb
-/
theorem twoTokenPhiInverse_first_mul_two {n : ℕ} (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) {p : ℤ × ℤ} (hp : p ∈ parityTriangle (n - 2) σ) :
    (twoTokenPhiInverseCoordinates n p).1 * 2 = p.1 - p.2 + n := by
  simpa [twoTokenPhiInverseCoordinates, mul_comm] using
    Int.ediv_two_mul_two_of_even (even_twoTokenPhiInverse_first σ hσ hp)

/--
@isnad1 id=eq.2h3v.s6.d72cb89c02ca from=translated src=- shape=c275b3fd vocab=46159bbb
-/
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

/--
@isnad1 id=eq.2h3v.s7.c922f101c093 from=translated src=- shape=7b7983f2 vocab=3d38f3cd
-/
@[simp]
theorem parityTriangleToTwoPathPoint_val {n : ℕ} (hn : 2 ≤ n) (σ : ℤ)
    (hσ : (n : ℤ) ≡ σ [ZMOD 2]) (p : {z // z ∈ parityTriangle (n - 2) σ}) :
    (parityTriangleToTwoPathPoint hn σ hσ p).1 = twoTokenPhiInverseCoordinates n p.1 :=
  rfl

/-- Applying the inverse formulas after `Φ_n` recovers the original legal pair.
@isnad1 id=eq.2h3v.s6.48b668385a23 from=translated src=- shape=5384e4e9 vocab=21466c81
-/
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

/-- Applying `Φ_n` after the inverse formulas recovers the parity-triangle point.
@isnad1 id=eq.2h3v.s6.c0f2d8290004 from=translated src=- shape=73a96877 vocab=04db7104
-/
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

/-- The unshifted coordinate change is an exact `ℓ₁`-to-`ℓ∞` isometry.
@isnad1 id=eq.0h3v.s8.1b9f2ed5b50e from=translated src=- shape=9a40eb68 vocab=fda4912a
-/
theorem twoTokenSquareCoordinates_isometry {n : ℕ} (p q : TwoPathPoint n) :
    max
        ((twoTokenSquareCoordinates p).1 - (twoTokenSquareCoordinates q).1).natAbs
        ((twoTokenSquareCoordinates p).2 - (twoTokenSquareCoordinates q).2).natAbs =
      (p.1.1 - q.1.1).natAbs + (p.1.2 - q.1.2).natAbs := by
  exact max_natAbs_sumDiff_sub_sumDiff p.1.1 p.1.2 q.1.1 q.1.2

/-- The shifted parity-triangle coordinates preserve the exact distance.
@isnad1 id=eq.0h3v.s8.989cc0e416d2 from=translated src=- shape=9a40eb68 vocab=a28c49db
-/
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
