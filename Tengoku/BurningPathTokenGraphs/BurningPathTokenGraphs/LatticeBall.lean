import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.VolumePolynomial
import Tengoku.Seed.Data.Fin.Tuple.Finset
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Set.Card
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Integer lattice balls

This file counts the integer `ℓ₁` ball used in the general volume lower bound.
-/

open scoped BigOperators

namespace BurningPath

/-- The radius-`r` integer `ℓ₁` ball in dimension `k`.-/
def latticeBall (k r : ℕ) : Set (Fin k → ℤ) :=
  {z | ∑ i, Int.natAbs (z i) ≤ r}

@[simp]
theorem mem_latticeBall {k r : ℕ} {z : Fin k → ℤ} :
    z ∈ latticeBall k r ↔ ∑ i, Int.natAbs (z i) ≤ r := by
  rfl

private abbrev IntCoordinate (r : ℕ) := {x : ℤ // x.natAbs ≤ r}

/-- Integers of absolute value at most `r` consist of zero and two copies of `Fin r`.-/
private def intCoordinateEquiv (r : ℕ) : IntCoordinate r ≃ Option (Fin r ⊕ Fin r) where
  toFun x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | ofNat n =>
        cases n with
        | zero => exact none
        | succ n =>
            exact some (Sum.inl ⟨n, by
              change n + 1 ≤ r at hx
              omega⟩)
    | negSucc n =>
        exact some (Sum.inr ⟨n, by
          change n + 1 ≤ r at hx
          omega⟩)
  invFun x := by
    rcases x with _ | i
    · exact ⟨0, by simp⟩
    · rcases i with i | i
      · exact ⟨(i.val + 1 : ℕ), by
          change i.val + 1 ≤ r
          omega⟩
      · exact ⟨Int.negSucc i.val, by
          change i.val + 1 ≤ r
          omega⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    cases x with
    | ofNat n => cases n <;> rfl
    | negSucc n => rfl
  right_inv x := by
    rcases x with _ | i
    · rfl
    · rcases i with i | i <;> rfl

private noncomputable instance intCoordinateFintype (r : ℕ) : Fintype (IntCoordinate r) :=
  Fintype.ofEquiv (Option (Fin r ⊕ Fin r)) (intCoordinateEquiv r).symm

/-- The integer `ℓ₁` ball is finite.-/
theorem latticeBall_finite (k r : ℕ) : (latticeBall k r).Finite := by
  have hcoordinate : ({x : ℤ | x.natAbs ≤ r} : Set ℤ).Finite := by
    exact Set.finite_def.mpr ⟨intCoordinateFintype r⟩
  refine (Set.Finite.pi' fun _ ↦ hcoordinate).subset ?_
  intro z hz i
  change Int.natAbs (z i) ≤ r
  exact
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)).trans hz

private noncomputable instance latticeBallFintype (k r : ℕ) :
    Fintype (latticeBall k r) :=
  (latticeBall_finite k r).fintype

/-- Split a nonempty-dimensional lattice ball into its first coordinate and its tail.-/
private def latticeBallSuccEquiv (k r : ℕ) :
    latticeBall (k + 1) r ≃
      Σ x : IntCoordinate r, latticeBall k (r - x.1.natAbs) where
  toFun z := by
    refine ⟨⟨z.1 0, ?_⟩, ⟨fun i ↦ z.1 i.succ, ?_⟩⟩
    · have hz := z.2
      change ∑ i, Int.natAbs (z.1 i) ≤ r at hz
      rw [Fin.sum_univ_succ] at hz
      omega
    · have hz := z.2
      change ∑ i, Int.natAbs (z.1 i) ≤ r at hz
      rw [Fin.sum_univ_succ] at hz
      change ∑ i : Fin k, Int.natAbs (z.1 i.succ) ≤ r - Int.natAbs (z.1 0)
      exact Nat.le_sub_of_add_le (by simpa [add_comm] using hz)
  invFun z := by
    refine ⟨Fin.cons z.1.1 z.2.1, ?_⟩
    change ∑ i : Fin (k + 1),
      Int.natAbs ((Fin.cons z.1.1 z.2.1 : Fin (k + 1) → ℤ) i) ≤ r
    rw [Fin.sum_univ_succ]
    simpa [add_comm] using Nat.add_le_of_le_sub z.1.2 z.2.2
  left_inv z := by
    apply Subtype.ext
    exact Fin.cons_self_tail z.1
  right_inv z := by
    rcases z with ⟨x, z⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      change
        (fun i : Fin k ↦ (Fin.cons x.1 z.1 : Fin (k + 1) → ℤ) i.succ) = z.1
      funext i
      simp

private theorem sum_intCoordinate (r : ℕ) (f : ℕ → ℕ) :
    ∑ x : IntCoordinate r, f x.1.natAbs =
      f 0 + 2 * ∑ n ∈ Finset.range r, f (n + 1) := by
  let g : Option (Fin r ⊕ Fin r) → ℕ
    | none => f 0
    | some (Sum.inl n) => f (n.val + 1)
    | some (Sum.inr n) => f (n.val + 1)
  calc
    ∑ x : IntCoordinate r, f x.1.natAbs = ∑ y, g y := by
      apply Fintype.sum_equiv (intCoordinateEquiv r)
      intro x
      rcases x with ⟨x, hx⟩
      cases x with
      | ofNat n => cases n <;> rfl
      | negSucc n => rfl
    _ = f 0 + (∑ n : Fin r, f (n.val + 1)) + ∑ n : Fin r, f (n.val + 1) := by
      rw [Fintype.sum_option, Fintype.sum_sum_type]
      simp [g, add_assoc]
    _ = f 0 + 2 * ∑ n ∈ Finset.range r, f (n + 1) := by
      have hsum :
          (∑ n : Fin r, f (n.val + 1)) = ∑ n ∈ Finset.range r, f (n + 1) :=
        Fin.sum_univ_eq_sum_range (fun n ↦ f (n + 1)) r
      rw [hsum]
      omega

private theorem latticeBall_card_succ (k r : ℕ) :
    Fintype.card (latticeBall (k + 1) r) =
      Fintype.card (latticeBall k r) +
        2 * ∑ q ∈ Finset.range r, Fintype.card (latticeBall k q) := by
  calc
    Fintype.card (latticeBall (k + 1) r) =
        Fintype.card (Σ x : IntCoordinate r, latticeBall k (r - x.1.natAbs)) :=
      Fintype.card_congr (latticeBallSuccEquiv k r)
    _ = ∑ x : IntCoordinate r, Fintype.card (latticeBall k (r - x.1.natAbs)) :=
      Fintype.card_sigma
    _ = Fintype.card (latticeBall k r) +
        2 * ∑ q ∈ Finset.range r, Fintype.card (latticeBall k (r - (q + 1))) := by
      simpa using sum_intCoordinate r (fun a ↦ Fintype.card (latticeBall k (r - a)))
    _ = Fintype.card (latticeBall k r) +
        2 * ∑ q ∈ Finset.range r, Fintype.card (latticeBall k q) := by
      rw [show (∑ q ∈ Finset.range r, Fintype.card (latticeBall k (r - (q + 1)))) =
          ∑ q ∈ Finset.range r, Fintype.card (latticeBall k q) by
        simpa [Nat.sub_sub, add_comm] using
          (Finset.sum_range_reflect (fun q ↦ Fintype.card (latticeBall k q)) r)]

private theorem latticeBallPolynomial_succ_dim (k r : ℕ) :
    latticeBallPolynomial (k + 1) r =
      latticeBallPolynomial k r + 2 * rankedVolumePolynomial k r := by
  let A : ℕ → ℕ := fun i ↦ 2 ^ (i + 1) * k.choose (i + 1) * r.choose (i + 1)
  let B : ℕ → ℕ := fun i ↦ 2 ^ (i + 1) * k.choose i * r.choose (i + 1)
  have hP :
      (∑ i ∈ Finset.range (k + 1), A i) + 1 = latticeBallPolynomial k r := by
    calc
      (∑ i ∈ Finset.range (k + 1), A i) + 1 =
          (∑ i ∈ Finset.range k, A i) + 1 := by
        rw [Finset.sum_range_succ]
        simp [A, Nat.choose_succ_self]
      _ = latticeBallPolynomial k r := by
        rw [latticeBallPolynomial, Finset.sum_range_succ']
        simp [A]
  have hB :
      (∑ i ∈ Finset.range (k + 1), B i) = 2 * rankedVolumePolynomial k r := by
    simp only [B, rankedVolumePolynomial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [pow_succ', mul_assoc, mul_left_comm]
  calc
    latticeBallPolynomial (k + 1) r =
        (∑ i ∈ Finset.range (k + 1), (A i + B i)) + 1 := by
      rw [latticeBallPolynomial, Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, pow_zero, one_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [A, B, Nat.choose_succ_succ]
      ring
    _ = (∑ i ∈ Finset.range (k + 1), A i) + 1 +
        ∑ i ∈ Finset.range (k + 1), B i := by
      rw [Finset.sum_add_distrib]
      omega
    _ = latticeBallPolynomial k r + 2 * rankedVolumePolynomial k r := by
      rw [hP, hB]

private theorem latticeBall_card_eq_polynomial (k r : ℕ) :
    Fintype.card (latticeBall k r) = latticeBallPolynomial k r := by
  induction k generalizing r with
  | zero =>
      simp [latticeBall, latticeBallPolynomial]
  | succ k ih =>
      calc
        Fintype.card (latticeBall (k + 1) r) =
            Fintype.card (latticeBall k r) +
              2 * ∑ q ∈ Finset.range r, Fintype.card (latticeBall k q) :=
          latticeBall_card_succ k r
        _ = latticeBallPolynomial k r +
            2 * ∑ q ∈ Finset.range r, latticeBallPolynomial k q := by
          simp_rw [ih]
        _ = latticeBallPolynomial k r + 2 * rankedVolumePolynomial k r := by
          rw [← cumulativeLatticeBallPolynomial_eq]
          rfl
        _ = latticeBallPolynomial (k + 1) r :=
          (latticeBallPolynomial_succ_dim k r).symm

/-- The exact cardinality of the ambient integer `ℓ₁` ball.-/
theorem latticeBall_ncard (k r : ℕ) :
    (latticeBall k r).ncard = latticeBallPolynomial k r := by
  calc
    (latticeBall k r).ncard = Fintype.card (latticeBall k r) := by
      rw [Set.ncard_eq_toFinset_card']
      simp
    _ = latticeBallPolynomial k r := latticeBall_card_eq_polynomial k r

/-- Expanded Delannoy formula for the cardinality of the ambient integer `ℓ₁` ball.-/
theorem latticeBall_ncard_formula (k r : ℕ) :
    (latticeBall k r).ncard =
      ∑ j ∈ Finset.range (k + 1), 2 ^ j * k.choose j * r.choose j := by
  simpa [latticeBallPolynomial] using latticeBall_ncard k r

end BurningPath
