import Tengoku.Seed.NumberTheory.ArithmeticFunction.Misc
import Tengoku.Seed.Algebra.Order.Floor.Semifield
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact Dirichlet hyperbola summation

The integer identity is inclusion-exclusion for the two strips covering the
finite hyperbolic region. The real version floors only summation cutoffs;
each quotient inside an arithmetic summatory function remains real.
-/

noncomputable section

open Finset ArithmeticFunction

namespace TwinPrime.Analytic

/-- Exact Dirichlet hyperbola decomposition at arbitrary integer cutoffs.
The two inequalities say that their rectangle lies inside the hyperbola and
that their two strips cover it. Zero cutoffs are allowed.
@isnad1 id=eq.2h6v.s9.b274c0debee9 from=translated src=- shape=6951bfa9 vocab=2bafc4d2
-/
theorem sum_Ioc_convolution_hyperbola {R : Type*} [CommRing R]
    (f g : ArithmeticFunction R) (X Y Z : ℕ)
    (hlower : Y * Z ≤ X) (hupper : X < (Y + 1) * (Z + 1)) :
    (∑ n ∈ Ioc 0 X, (f * g) n) =
      (∑ k ∈ Ioc 0 Y, f k * ∑ d ∈ Ioc 0 (X / k), g d) +
      (∑ d ∈ Ioc 0 Z, g d * ∑ k ∈ Ioc 0 (X / d), f k) -
      (∑ k ∈ Ioc 0 Y, f k) * (∑ d ∈ Ioc 0 Z, g d) := by
  classical
  let P := (Ioc 0 X ×ˢ Ioc 0 X).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ X)
  let A := P.filter (fun p => p.1 ≤ Y)
  let B := P.filter (fun p => p.2 ≤ Z)
  have hcoord (k d : ℕ) (hk : 0 < k) (hd : 0 < d) (hprod : k * d ≤ X) :
      k ≤ X ∧ d ≤ X := by
    constructor
    · exact (Nat.le_mul_of_pos_right k hd).trans hprod
    · exact (Nat.le_mul_of_pos_left d hk).trans hprod
  have hcover : A ∪ B = P := by
    ext p
    simp only [A, B, mem_union, mem_filter]
    constructor
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
    · intro hp
      by_cases hk : p.1 ≤ Y
      · exact Or.inl ⟨hp, hk⟩
      · apply Or.inr
        refine ⟨hp, ?_⟩
        by_contra hd
        have hprod := (mem_filter.mp hp).2
        have hle : (Y + 1) * (Z + 1) ≤ p.1 * p.2 :=
          Nat.mul_le_mul (by omega) (by omega)
        omega
  have hoverlap : A ∩ B = Ioc 0 Y ×ˢ Ioc 0 Z := by
    ext p
    constructor
    · intro hp
      obtain ⟨⟨hpP, hpY⟩, ⟨_, hpZ⟩⟩ := by
        simpa only [A, B, mem_inter, mem_filter] using hp
      obtain ⟨⟨hp1, hp2⟩, _⟩ := by
        simpa only [P, mem_filter, mem_product] using hpP
      exact mem_product.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hp1).1, hpY⟩,
        mem_Ioc.mpr ⟨(mem_Ioc.mp hp2).1, hpZ⟩⟩
    · intro hp
      obtain ⟨⟨hk0, hkY⟩, ⟨hd0, hdZ⟩⟩ := by
        simpa only [mem_product, mem_Ioc] using hp
      have hprod := (Nat.mul_le_mul hkY hdZ).trans hlower
      have hpX := hcoord p.1 p.2 hk0 hd0 hprod
      have hpP : p ∈ P := by
        exact mem_filter.mpr ⟨mem_product.mpr
          ⟨mem_Ioc.mpr ⟨hk0, hpX.1⟩, mem_Ioc.mpr ⟨hd0, hpX.2⟩⟩, hprod⟩
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨hpP, hkY⟩, mem_filter.mpr ⟨hpP, hdZ⟩⟩
  have hA : (∑ p ∈ A, f p.1 * g p.2) =
      ∑ k ∈ Ioc 0 Y, f k * ∑ d ∈ Ioc 0 (X / k), g d := by
    rw [sum_finset_product A (Ioc 0 Y) (fun k => Ioc 0 (X / k)) (fun p => ?_)]
    · apply sum_congr rfl
      intro k _
      simpa only using (mul_sum (Ioc 0 (X / k)) (fun d => g d) (f k)).symm
    · constructor
      · intro hp
        obtain ⟨⟨⟨hk, hd⟩, hprod⟩, hkY⟩ := by
          simpa only [A, P, mem_filter, mem_product, mem_Ioc] using hp
        exact ⟨mem_Ioc.mpr ⟨hk.1, hkY⟩, mem_Ioc.mpr
          ⟨hd.1, (Nat.le_div_iff_mul_le hk.1).mpr (by simpa only [mul_comm] using hprod)⟩⟩
      · intro hp
        obtain ⟨⟨hk0, hkY⟩, ⟨hd0, hdQ⟩⟩ := by
          simpa only [mem_Ioc] using hp
        have hprod : p.1 * p.2 ≤ X := by
          simpa only [mul_comm] using (Nat.le_div_iff_mul_le hk0).mp hdQ
        have hpX := hcoord p.1 p.2 hk0 hd0 hprod
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
          ⟨mem_Ioc.mpr ⟨hk0, hpX.1⟩, mem_Ioc.mpr ⟨hd0, hpX.2⟩⟩, hprod⟩, hkY⟩
  have hB : (∑ p ∈ B, f p.1 * g p.2) =
      ∑ d ∈ Ioc 0 Z, g d * ∑ k ∈ Ioc 0 (X / d), f k := by
    rw [sum_finset_product_right B (Ioc 0 Z) (fun d => Ioc 0 (X / d)) (fun p => ?_)]
    · apply sum_congr rfl
      intro d _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      exact mul_comm _ _
    · constructor
      · intro hp
        obtain ⟨⟨⟨hk, hd⟩, hprod⟩, hdZ⟩ := by
          simpa only [B, P, mem_filter, mem_product, mem_Ioc] using hp
        exact ⟨mem_Ioc.mpr ⟨hd.1, hdZ⟩, mem_Ioc.mpr
          ⟨hk.1, (Nat.le_div_iff_mul_le hd.1).mpr hprod⟩⟩
      · intro hp
        obtain ⟨⟨hd0, hdZ⟩, ⟨hk0, hkQ⟩⟩ := by
          simpa only [mem_Ioc] using hp
        have hprod := (Nat.le_div_iff_mul_le hd0).mp hkQ
        have hpX := hcoord p.1 p.2 hk0 hd0 hprod
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr
          ⟨mem_Ioc.mpr ⟨hk0, hpX.1⟩, mem_Ioc.mpr ⟨hd0, hpX.2⟩⟩, hprod⟩, hdZ⟩
  have hrect : (∑ p ∈ Ioc 0 Y ×ˢ Ioc 0 Z, f p.1 * g p.2) =
      (∑ k ∈ Ioc 0 Y, f k) * (∑ d ∈ Ioc 0 Z, g d) := by
    rw [sum_product, sum_mul]
    apply sum_congr rfl
    intro k _
    simpa only using (mul_sum (Ioc 0 Z) (fun d => g d) (f k)).symm
  have hinc : (∑ p ∈ A ∪ B, f p.1 * g p.2) +
      (∑ p ∈ A ∩ B, f p.1 * g p.2) =
      (∑ p ∈ A, f p.1 * g p.2) + (∑ p ∈ B, f p.1 * g p.2) := sum_union_inter
  rw [hcover, hoverlap, hA, hB, hrect] at hinc
  rw [sum_Ioc_mul_eq_sum_prod_filter]
  change (∑ p ∈ P, f p.1 * g p.2) = _
  exact eq_sub_of_add_eq hinc

/-- Ordinary arithmetic summation at a real endpoint.-/
def arithmeticSummatory (f : ArithmeticFunction ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Ioc 0 ⌊x⌋₊, f n

/--
@isnad1 id=eq.0h2v.s5.e6602319e813 from=translated src=- shape=a17e8e2e vocab=3856fa11
-/
@[simp] theorem arithmeticSummatory_nat (f : ArithmeticFunction ℝ) (N : ℕ) :
    arithmeticSummatory f (N : ℝ) = ∑ n ∈ Ioc 0 N, f n := by
  simp [arithmeticSummatory]

/-- The real Dirichlet hyperbola identity, keeping each quotient real inside
the summatory function.
@isnad1 id=eq.4h5v.s7.fe158e020591 from=translated src=- shape=ab150183 vocab=24674316
-/
theorem arithmeticSummatory_convolution_hyperbola (f g : ArithmeticFunction ℝ)
    (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) (hyz : y * z = x) :
    arithmeticSummatory (f * g) x =
      (∑ k ∈ Ioc 0 ⌊y⌋₊, f k * arithmeticSummatory g (x / k)) +
      (∑ d ∈ Ioc 0 ⌊z⌋₊, g d * arithmeticSummatory f (x / d)) -
      arithmeticSummatory f y * arithmeticSummatory g z := by
  have hx0 : 0 ≤ x := by linarith
  have hy0 : 0 < y := by linarith
  have hz0 : 0 < z := by linarith
  have hlower : ⌊y⌋₊ * ⌊z⌋₊ ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      (⌊y⌋₊ : ℝ) * (⌊z⌋₊ : ℝ) ≤ y * z :=
        mul_le_mul (Nat.floor_le hy0.le) (Nat.floor_le hz0.le) (by positivity) hy0.le
      _ = x := hyz
  have hupper : ⌊x⌋₊ < (⌊y⌋₊ + 1) * (⌊z⌋₊ + 1) := by
    have hylt := Nat.lt_floor_add_one y
    have hzlt := Nat.lt_floor_add_one z
    have hreal : (⌊x⌋₊ : ℝ) < ((⌊y⌋₊ : ℝ) + 1) * ((⌊z⌋₊ : ℝ) + 1) := by
      calc
        _ ≤ x := Nat.floor_le hx0
        _ = y * z := hyz.symm
        _ < ((⌊y⌋₊ : ℝ) + 1) * z := mul_lt_mul_of_pos_right hylt hz0
        _ < _ := mul_lt_mul_of_pos_left hzlt (by positivity)
    exact_mod_cast hreal
  simpa only [arithmeticSummatory, Nat.floor_div_natCast] using
    sum_Ioc_convolution_hyperbola f g ⌊x⌋₊ ⌊y⌋₊ ⌊z⌋₊ hlower hupper

end TwinPrime.Analytic
