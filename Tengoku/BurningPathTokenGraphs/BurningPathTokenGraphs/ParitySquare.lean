import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.LatticeBall
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenAlgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact counting of parity squares

The two-dimensional integer `ℓ₁` ball becomes an axis-parallel square in the sum/difference
coordinates. Its image consists exactly of the offsets whose two coordinates have the same parity.
-/

namespace BurningPath

/--
The radius-`r` square of integer offsets in one parity class. The congruence condition is precisely
the condition that the inverse sum/difference transformation has integer coordinates.-/
def parityOffsetSquare (r : ℕ) : Set (ℤ × ℤ) :=
  {p | max p.1.natAbs p.2.natAbs ≤ r ∧ p.1 ≡ p.2 [ZMOD 2]}

/--
@isnad1 id=iff.0h2v.s5.7aa9cd18fe3b from=translated src=- shape=36b956e5 vocab=df8ca925
-/
@[simp]
theorem mem_parityOffsetSquare {r : ℕ} {p : ℤ × ℤ} :
    p ∈ parityOffsetSquare r ↔
      max p.1.natAbs p.2.natAbs ≤ r ∧ p.1 ≡ p.2 [ZMOD 2] :=
  Iff.rfl

/-- The sum/difference transformation sends the two-dimensional `ℓ₁` ball into the parity square.-/
def latticeBallTwoToParityOffsetSquare {r : ℕ} (z : latticeBall 2 r) :
    parityOffsetSquare r := by
  refine ⟨(z.1 0 + z.1 1, z.1 1 - z.1 0), ?_⟩
  constructor
  · rw [max_natAbs_add_sub]
    have hz := z.2
    change ∑ i : Fin 2, Int.natAbs (z.1 i) ≤ r at hz
    simpa only [Fin.sum_univ_two] using hz
  · exact add_modEq_sub_two (z.1 0) (z.1 1)

/-- The inverse affine coordinates `(u-v)/2, (u+v)/2`.-/
def parityOffsetSquareInverseCoordinates (p : ℤ × ℤ) : ℤ × ℤ :=
  ((p.1 - p.2) / 2, (p.1 + p.2) / 2)

private theorem even_sub_of_modEq_two {u v : ℤ} (h : u ≡ v [ZMOD 2]) :
    Even (u - v) := by
  rw [even_iff_two_dvd]
  simpa only [neg_sub] using (dvd_neg.mpr h.dvd)

private theorem even_add_of_modEq_two {u v : ℤ} (h : u ≡ v [ZMOD 2]) :
    Even (u + v) := by
  obtain ⟨a, ha⟩ := even_sub_of_modEq_two h
  exact ⟨a + v, by omega⟩

/--
@isnad1 id=eq.0h2v.s6.da4ea509b303 from=translated src=- shape=8a18fef9 vocab=28514bb3
-/
@[simp]
theorem parityOffsetSquareInverseCoordinates_add {r : ℕ} (p : parityOffsetSquare r) :
    (parityOffsetSquareInverseCoordinates p.1).1 +
        (parityOffsetSquareInverseCoordinates p.1).2 =
      p.1.1 := by
  have hx :=
    Int.ediv_two_mul_two_of_even (even_sub_of_modEq_two p.2.2)
  have hy :=
    Int.ediv_two_mul_two_of_even (even_add_of_modEq_two p.2.2)
  simp only [parityOffsetSquareInverseCoordinates] at hx hy ⊢
  omega

/--
@isnad1 id=eq.0h2v.s6.4eccacf85550 from=translated src=- shape=8a18fef9 vocab=adc6a977
-/
@[simp]
theorem parityOffsetSquareInverseCoordinates_sub {r : ℕ} (p : parityOffsetSquare r) :
    (parityOffsetSquareInverseCoordinates p.1).2 -
        (parityOffsetSquareInverseCoordinates p.1).1 =
      p.1.2 := by
  have hx :=
    Int.ediv_two_mul_two_of_even (even_sub_of_modEq_two p.2.2)
  have hy :=
    Int.ediv_two_mul_two_of_even (even_add_of_modEq_two p.2.2)
  simp only [parityOffsetSquareInverseCoordinates] at hx hy ⊢
  omega

/-- A parity-square offset has a unique preimage in the two-dimensional integer `ℓ₁` ball.-/
def parityOffsetSquareToLatticeBall {r : ℕ} (p : parityOffsetSquare r) :
    latticeBall 2 r := by
  let x := (parityOffsetSquareInverseCoordinates p.1).1
  let y := (parityOffsetSquareInverseCoordinates p.1).2
  refine ⟨Fin.cases x (fun _ ↦ y), ?_⟩
  change ∑ i : Fin 2, Int.natAbs (Fin.cases x (fun _ ↦ y) i) ≤ r
  simp only [Fin.sum_univ_two, Fin.cases_zero]
  rw [← max_natAbs_add_sub]
  change
    max
        ((parityOffsetSquareInverseCoordinates p.1).1 +
          (parityOffsetSquareInverseCoordinates p.1).2).natAbs
        ((parityOffsetSquareInverseCoordinates p.1).2 -
          (parityOffsetSquareInverseCoordinates p.1).1).natAbs ≤ r
  rw [parityOffsetSquareInverseCoordinates_add, parityOffsetSquareInverseCoordinates_sub]
  exact p.2.1

/-- The exact sum/difference equivalence between the radius-`r` ball and its parity square.-/
def latticeBallTwoEquivParityOffsetSquare (r : ℕ) :
    latticeBall 2 r ≃ parityOffsetSquare r where
  toFun := latticeBallTwoToParityOffsetSquare
  invFun := parityOffsetSquareToLatticeBall
  left_inv z := by
    apply Subtype.ext
    funext i
    fin_cases i
    · change ((z.1 0 + z.1 1 - (z.1 1 - z.1 0)) / 2) = z.1 0
      rw [show z.1 0 + z.1 1 - (z.1 1 - z.1 0) = 2 * z.1 0 by omega]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
    · change ((z.1 0 + z.1 1 + (z.1 1 - z.1 0)) / 2) = z.1 1
      rw [show z.1 0 + z.1 1 + (z.1 1 - z.1 0) = 2 * z.1 1 by omega]
      exact Int.mul_ediv_cancel_left _ (by norm_num)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact parityOffsetSquareInverseCoordinates_add p
    · exact parityOffsetSquareInverseCoordinates_sub p

/-- In dimension two, the lattice-ball polynomial is the square-model quadratic.
@isnad1 id=eq.0h1v.s6.1fd17f46049b from=translated src=- shape=ab83e3a2 vocab=d5cde26f
-/
theorem latticeBallPolynomial_two (r : ℕ) :
    latticeBallPolynomial 2 r = 2 * r ^ 2 + 2 * r + 1 := by
  simp only [latticeBallPolynomial, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose_zero_right, Nat.choose_one_right, Nat.choose_self, pow_zero, pow_one, one_mul]
  rw [Nat.choose_two_right]
  cases r with
  | zero => norm_num
  | succ r =>
      simp only [Nat.succ_sub_one]
      have heven : Even ((r + 1) * r) := by
        simpa [Nat.succ_eq_add_one, mul_comm] using Nat.even_mul_pred_self (r + 1)
      have hdiv := Nat.div_mul_cancel heven.two_dvd
      nlinarith

/-- A full radius-`r` parity square contains exactly `2r² + 2r + 1` lattice points.
@isnad1 id=eq.0h1v.s6.53c09aae0ff2 from=translated src=- shape=1035ac18 vocab=2ce24a4c
-/
theorem parityOffsetSquare_ncard (r : ℕ) :
    (parityOffsetSquare r).ncard = 2 * r ^ 2 + 2 * r + 1 := by
  letI : Fintype (latticeBall 2 r) := (latticeBall_finite 2 r).fintype
  letI : Fintype (parityOffsetSquare r) :=
    Fintype.ofEquiv (latticeBall 2 r) (latticeBallTwoEquivParityOffsetSquare r)
  calc
    (parityOffsetSquare r).ncard = Fintype.card (parityOffsetSquare r) := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    _ = Fintype.card (latticeBall 2 r) :=
      Fintype.card_congr (latticeBallTwoEquivParityOffsetSquare r).symm
    _ = (latticeBall 2 r).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    _ = latticeBallPolynomial 2 r := latticeBall_ncard 2 r
    _ = 2 * r ^ 2 + 2 * r + 1 := latticeBallPolynomial_two r

end BurningPath
