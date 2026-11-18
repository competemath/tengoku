import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals
import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Mellin.LogProfiles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]

/--
@isnad1 id=eq.1h4v.s8.07440adb650f from=translated src=- shape=9656b8bf vocab=ea278f65
-/
theorem gauss_transform (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ x : F, χ x * ψ (h * x)) =
      if h = 0 then 0 else (χ h)⁻¹ * gaussSum χ ψ := by
  classical
  by_cases hh : h = 0
  · subst h
    simp only [zero_mul, map_zero_eq_one, mul_one, ite_true]
    exact MulChar.sum_eq_zero_of_ne_one hχ
  · have hu : IsUnit h := isUnit_iff_ne_zero.mpr hh
    have hshift := gaussSum_mulShift_eq χ ψ hu.unit
    simp only [gaussSum, AddChar.mulShift_apply] at hshift
    simpa only [hu.unit_spec, ite_eq_right hh, inv_apply_eq_inv' χ h, gaussSum] using hshift

/--
@isnad1 id=eq.1h5v.s9.46ecfca164f2 from=translated src=- shape=4c946cd8 vocab=992e874b
-/
theorem product_gauss_transform
    {ι : Type*} [Fintype ι]
    (E : ι → Type*) [∀ i, Field (E i)] [∀ i, Fintype (E i)]
    (χ : ∀ i, MulChar (E i) ℂ) (ψ : ∀ i, AddChar (E i) ℂ)
    (hχ : ∀ i, χ i ≠ 1) (h : ∀ i, E i) :
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
      ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
  classical
  calc
    (∑ x : ∀ i, E i, ∏ i, χ i (x i) * ψ i (h i * x i)) =
        ∏ i, ∑ x : E i, χ i x * ψ i (h i * x) := by
      simpa using (Fintype.prod_sum
        (fun i (x : E i) => χ i x * ψ i (h i * x))).symm
    _ = ∏ i, if h i = 0 then 0 else (χ i (h i))⁻¹ * gaussSum (χ i) (ψ i) := by
      apply Finset.prod_congr rfl
      intro i _
      exact gauss_transform (χ i) (ψ i) (hχ i) (h i)

end ShortDraftFiniteGaussFourier

namespace PoissonChildCRT
open scoped Classical

variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)

/--
@isnad1 id=eq.1h3v.s8.3ebec50951e6 from=translated src=- shape=a871c213 vocab=bd2b5d46
-/
theorem inverse_as_row_and_label (hχ : χ ^ 6 = 1) (e : ℕ) :
    (χ (e : ZMod n))⁻¹ = χ (e : ZMod n) * (χ (e : ZMod n)) ^ 4 := by
  by_cases he : IsUnit (e : ZMod n)
  · have h6 : (χ (e : ZMod n)) ^ 6 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, he]
    apply inv_eq_of_mul_eq_one_right
    calc
      χ (e : ZMod n) * (χ (e : ZMod n) * χ (e : ZMod n) ^ 4)
          = (χ (e : ZMod n)) ^ 6 := by ring
      _ = 1 := h6
  · have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ he
    simp [hz]

/--
@isnad1 id=eq.1h8v.s9.c36bf3753092 from=translated src=- shape=7a77d56c vocab=bd2b5d46
-/
theorem child_row_label_identity (hχ : χ ^ 6 = 1)
    (d e k J C v : ℕ) :
    (χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4
      = χ ((d * e * k : ℕ) : ZMod n) *
        (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4 := by
  rw [inverse_as_row_and_label n χ hχ e]
  simp only [Nat.cast_mul, map_mul]
  ring

def mask (n m : ℕ) : ℂ := if n.Coprime m then 1 else 0

/--
@isnad1 id=eq.0h3v.s5.0317b1ee2446 from=translated src=- shape=50a03441 vocab=89221f45
-/
theorem mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [ite_eq_right hab, ite_eq_right hna]
      simp
    · rw [ite_eq_right hab, ite_eq_right hnb]
      simp

/--
@isnad1 id=eq.0h3v.s7.a7e6491226aa from=translated src=- shape=62cb2f5f vocab=489bddff
-/
theorem mask_absorb_char (e : ℕ) :
    mask n e * χ (e : ZMod n) = χ (e : ZMod n) := by
  by_cases he : n.Coprime e
  · simp [mask, he]
  · have hnu : ¬ IsUnit (e : ZMod n) := by
      intro hu
      exact he ((ZMod.isUnit_iff_coprime e n).mp hu).symm
    have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [mask, he, hz]

/--
@isnad1 id=eq.0h3v.s7.6b5cbf7ad93c from=translated src=- shape=780788cf vocab=bb97e6b2
-/
theorem mask_absorb_inv_char (e : ℕ) :
    mask n e * (χ (e : ZMod n))⁻¹ = (χ (e : ZMod n))⁻¹ := by
  by_cases he : n.Coprime e
  · simp [mask, he]
  · have hnu : ¬ IsUnit (e : ZMod n) := by
      intro hu
      exact he ((ZMod.isUnit_iff_coprime e n).mp hu).symm
    have hz : χ (e : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [mask, he, hz]

/--
@isnad1 id=eq.2h12v.s9.3da0175cbaa8 from=translated src=- shape=8efe1aaa vocab=f0513aea
-/
theorem child_row_label_with_mask (hχ : χ ^ 6 = 1)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    mask n (b0 * t) * mask n g *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
      = mask n (b0 * t * r) *
        (χ ((d * e * k : ℕ) : ZMod n) *
          (χ ((J * C * e * v : ℕ) : ZMod n)) ^ 4) := by
  rw [hg, mask_mul n e r]
  have hmask : mask n (b0 * t) * (mask n e * mask n r) =
      mask n (b0 * t * r) * mask n e := by
    rw [mask_mul n (b0 * t) r]
    ring
  rw [hmask]
  have hprior : mask n e *
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) =
      ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
        (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by
    calc
      mask n e * ((χ (e : ZMod n))⁻¹ * χ (d : ZMod n) * χ (k : ZMod n) *
          (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4)
          = (mask n e * (χ (e : ZMod n))⁻¹) *
              (χ (d : ZMod n) * χ (k : ZMod n) *
                (χ ((J * C : ℕ) : ZMod n)) ^ 4 * (χ (v : ZMod n)) ^ 4) := by ring
      _ = _ := by rw [mask_absorb_inv_char n χ e]; ring
  rw [mul_assoc, hprior, child_row_label_identity n χ hχ d e k J C v]

/--
@isnad1 id=eq.2h13v.s9.df081359dff4 from=translated src=- shape=8f14217d vocab=16d8e344
-/
theorem sum_child_row_label_with_mask
    (S : Finset ℕ) (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b0 t g e r d k J C v : ℕ) (hg : g = e * r) :
    (∑ n ∈ S, a n *
      (mask n (b0 * t) * mask n g *
        ((χ n (e : ZMod n))⁻¹ * χ n (d : ZMod n) * χ n (k : ZMod n) *
          (χ n ((J * C : ℕ) : ZMod n)) ^ 4 *
          (χ n (v : ZMod n)) ^ 4))) =
    (∑ n ∈ S, a n *
      (mask n (b0 * t * r) *
        (χ n ((d * e * k : ℕ) : ZMod n) *
          (χ n ((J * C * e * v : ℕ) : ZMod n)) ^ 4))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [child_row_label_with_mask n (χ n) (hχ n) b0 t g e r d k J C v hg]

end PoissonChildCRT

namespace PoissonFirstLocal
open scoped Classical

def bit (b : Bool) : ℕ := if b then 1 else 0
def localE (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)
def cExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) + localE parityBit ε₁ ε₂).val
def cExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) - localE parityBit ε₁ ε₂).val
def EExp (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0
def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)
def totalExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₁ + cExp₁ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂
def totalExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₂ + cExp₂ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂

/--
@isnad1 id=and.0h3v.s6.06df3ce90cb8 from=translated src=- shape=5271f71e vocab=0c11bdec
-/
theorem exponent_table (parityBit ε₁ ε₂ : Bool) :
    totalExp₁ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) ∧
    totalExp₂ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) := by
  cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide

def mask (n p : ℕ) : ℂ := if n.Coprime p then 1 else 0

private theorem mask_mul (n a b : ℕ) :
    mask n (a * b) = mask n a * mask n b := by
  classical
  simp only [mask]
  by_cases hab : n.Coprime (a * b)
  · have ha : n.Coprime a := (Nat.coprime_mul_iff_right.mp hab).1
    have hb : n.Coprime b := (Nat.coprime_mul_iff_right.mp hab).2
    rw [ite_eq_left hab, ite_eq_left ha, ite_eq_left hb]
    norm_num
  · have hna_or_hnb : ¬ n.Coprime a ∨ ¬ n.Coprime b := by
      by_contra h
      exact hab (Nat.coprime_mul_iff_right.mpr ⟨not_not.mp (not_or.mp h).1,
        not_not.mp (not_or.mp h).2⟩)
    rcases hna_or_hnb with hna | hnb
    · rw [ite_eq_right hab, ite_eq_right hna]
      simp
    · rw [ite_eq_right hab, ite_eq_right hnb]
      simp

def oldFactor (side : Bool) (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  let q := χ (p : ZMod n)
  mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂

def newFactor (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ (p : ZMod n)) ^ 4 else mask n p

/--
@isnad1 id=eq.1h7v.s8.7e32851b5fb7 from=translated src=- shape=7b6b8761 vocab=ebf32dfb
-/
theorem first_local_identity (side parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    oldFactor side parityBit ε₁ ε₂ n p χ = newFactor parityBit ε₁ ε₂ n p χ := by
  let q := χ (p : ZMod n)
  by_cases hcop : n.Coprime p
  · have hunit : IsUnit (p : ZMod n) :=
      (ZMod.isUnit_iff_coprime p n).mpr hcop.symm
    have h6 : q ^ 6 = 1 := by
      dsimp [q]
      rw [← MulChar.pow_apply' χ (by decide : 6 ≠ 0), hχ]
      simp [MulChar.one_apply, hunit]
    have hmask : mask n p = 1 := by simp [mask, hcop]
    change mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
      q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
      q ^ EExp parityBit ε₁ ε₂ =
      (if retained parityBit ε₁ ε₂ then q ^ 4 else mask n p)
    rw [hmask, one_mul, ← pow_add, ← pow_add]
    cases side
    · change q ^ (totalExp₁ parityBit ε₁ ε₂) =
          (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).1]
      split_ifs <;> simp
    · change q ^ (totalExp₂ parityBit ε₁ ε₂) =
          (if retained parityBit ε₁ ε₂ then q ^ 4 else 1)
      rw [pow_eq_pow_mod _ h6, (exponent_table parityBit ε₁ ε₂).2]
      split_ifs <;> simp
  · have hnu : ¬ IsUnit (p : ZMod n) := by
      intro hu
      exact hcop ((ZMod.isUnit_iff_coprime p n).mp hu).symm
    have hzero : q = 0 := MulChar.map_nonunit χ hnu
    simp [oldFactor, newFactor, mask, hcop, q, hzero]

private theorem char_prod_four (n : ℕ) (χ : MulChar (ZMod n) ℂ)
    (S : Finset ℕ) :
    (∏ p ∈ S, (χ (p : ZMod n)) ^ 4) =
      (χ ((∏ p ∈ S, p : ℕ) : ZMod n)) ^ 4 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
      simp [hp, ih, Nat.cast_mul, map_mul, mul_pow]

private theorem mask_prod (n : ℕ) (S : Finset ℕ) :
    (∏ p ∈ S, mask n p) = mask n (∏ p ∈ S, p) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [mask]
  | @insert p S hp ih =>
      simp [hp, ih]
      exact (mask_mul n p (∏ p ∈ S, p)).symm

/--
@isnad1 id=eq.1h7v.s8.45da3761f6a1 from=translated src=- shape=b51c7a6e vocab=a3a9ae67
-/
theorem first_prime_product_identity
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) := by
  classical
  calc
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
        ∏ p ∈ P, newFactor (parityBit p) (ε₁ p) (ε₂ p) n p χ := by
          apply Finset.prod_congr rfl
          intro p hp
          exact first_local_identity side (parityBit p) (ε₁ p) (ε₂ p) n p χ hχ
    _ = (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p),
            (χ (p : ZMod n)) ^ 4) *
          (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), mask n p) := by
          simp only [newFactor]
          exact Finset.prod_ite _ _
    _ = _ := by
          rw [char_prod_four, mask_prod]

/--
@isnad1 id=eq.2h6v.s7.c72379d839a6 from=translated src=- shape=8c3cd10e vocab=0d6b720c
-/
theorem mask_redundant_overlap
    (n J B₀ b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ)
    (hB : B₀ ∣ b₀) (hb : b₀ ∣ (B₀ * J) ^ m) :
    (χ (J : ZMod n)) ^ 4 * mask n B₀ =
      (χ (J : ZMod n)) ^ 4 * mask n b₀ := by
  by_cases hJ : n.Coprime J
  · have hiff : n.Coprime B₀ ↔ n.Coprime b₀ := by
      constructor
      · intro hB₀
        have hprod : n.Coprime (B₀ * J) := hB₀.mul_right hJ
        exact Nat.Coprime.of_dvd_right hb (hprod.pow_right m)
      · intro hb₀
        exact Nat.Coprime.of_dvd_right hB hb₀
    simp only [mask]
    split_ifs with h₁ h₂ <;> simp_all
  · have hnu : ¬ IsUnit (J : ZMod n) := by
      intro hu
      exact hJ ((ZMod.isUnit_iff_coprime J n).mp hu).symm
    have hz : χ (J : ZMod n) = 0 := MulChar.map_nonunit χ hnu
    simp [hz]

/--
@isnad1 id=eq.3h9v.s9.9436306a95bf from=translated src=- shape=ccdaafe9 vocab=b0493ece
-/
theorem first_prime_product_with_b0
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n b₀ := by
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n χ hχ]
  exact mask_redundant_overlap n _ _ b₀ m χ hB hb

/--
@isnad1 id=eq.1h8v.s9.cc98ec7d43d1 from=translated src=- shape=c51440ee vocab=611895a7
-/
theorem sum_first_prime_product_identity
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n (χ n) (hχ n)]

/--
@isnad1 id=eq.3h10v.s9.2bfd79dd73ab from=translated src=- shape=2fed2cf1 vocab=240cb3e5
-/
theorem sum_first_prime_product_with_b0
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ)
    (b₀ m : ℕ)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n b₀)) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [first_prime_product_with_b0 side P parityBit ε₁ ε₂ n b₀ m (χ n) (hχ n) hB hb]

end PoissonFirstLocal

open Finset Complex

namespace ActualCubicChar

variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]

omit [IsDomain R] in
private theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj

private noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]

variable [Fintype F]

private theorem euler_jacobi_sum_zero (m : ℕ)
    (hm : 2 * m < Fintype.card F - 1) :
    (∑ x : F, x ^ m * (1 - x) ^ m) = 0 := by
  classical
  simp_rw [sub_eq_add_neg, add_pow]
  simp only [one_pow, one_mul, mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have he : m + (m - j) < Fintype.card F - 1 := by
    have hle : m - j ≤ m := Nat.sub_le m j
    omega
  calc
    (∑ x : F, x ^ m * ((-x) ^ (m - j) * ↑(m.choose j))) =
        ((-1 : F) ^ (m - j) * ↑(m.choose j)) *
          ∑ x : F, x ^ (m + (m - j)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [neg_pow, pow_add]
      ring
    _ = 0 := by rw [FiniteField.sum_pow_lt_card_sub_one F _ he]; ring

private def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]

private noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)

/--
@isnad1 id=eq.3h6v.s8.391ebbe1d368 from=translated src=- shape=ad498085 vocab=3fddc67a
-/
theorem cubicResidueChar_reduce_unit (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) (u : Fˣ) :
    ρ (cubicResidueChar ρ ζ hζ hζF m hq (u : F)) = (u : F) ^ m := by
  let e := cubic_roots_equiv ρ ζ hζ hζF
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m
  have he := e.apply_symm_apply (euler_to_roots m hq u)
  have he' := congrArg (fun v : rootsOfUnity 3 F => ((v : Fˣ) : F)) he
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (((euler_to_roots m hq u : rootsOfUnity 3 F) : Fˣ) : F) at he'
  change ρ (((e.symm (euler_to_roots m hq u) : rootsOfUnity 3 R) : Rˣ) : R) =
    (u : F) ^ m at he'
  exact he'

/--
@isnad1 id=eq.3h5v.s8.67caff5a524c from=translated src=- shape=121d3b43 vocab=0cba38b5
-/
theorem cubicResidueChar_pow_three (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    cubicResidueChar ρ ζ hζ hζF m hq ^ 3 = 1 := by
  apply MulChar.ext
  intro u
  rw [(cubicResidueChar ρ ζ hζ hζF m hq).pow_apply_coe,
    MulChar.one_apply_coe]
  simp only [cubicResidueChar, MulChar.ofUnitHom_coe, MonoidHom.comp_apply]
  let v : rootsOfUnity 3 R :=
    (cubic_roots_equiv ρ ζ hζ hζF).symm (euler_to_roots m hq u)
  change (((v : Rˣ) : R) ^ 3) = 1
  exact (mem_rootsOfUnity' 3 (v : Rˣ)).mp v.property

end ActualCubicChar

namespace ActualEisensteinCubic

section

open NumberField

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

def lambda : O := omega - 1

noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _

noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P

/--
@isnad1 id=isprimit.0h0v.s4.f91c50fddda0 from=translated src=- shape=aeae7466 vocab=36a4ba58
-/
theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot

def traceLambda : O := 1 + 2 * omega

/--
@isnad1 id=eq.0h0v.s5.d620a60611d7 from=translated src=- shape=f091aeb4 vocab=8cc01c00
-/
theorem traceLambda_eq_unit_mul_lambda : traceLambda = -omega * lambda := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  dsimp [traceLambda, lambda]
  linear_combination hrel

/--
@isnad1 id=isunit.0h0v.s5.1c622f5712ea from=translated src=- shape=be2594e7 vocab=c3cbac50
-/
theorem neg_omega_isUnit : IsUnit (-omega) :=
  (omega_primitive.isUnit (by decide)).neg

/--
@isnad1 id=iff.0h1v.s7.13ce69275281 from=translated src=- shape=709598af vocab=ef68d8c6
-/
theorem traceLambda_mem_iff (P : Ideal O) : traceLambda ∈ P ↔ lambda ∈ P := by
  rw [traceLambda_eq_unit_mul_lambda, mul_comm]
  exact P.mul_unit_mem_iff_mem neg_omega_isUnit

/--
@isnad1 id=iff.0h1v.s6.eb285e3e1c6d from=translated src=- shape=3eb1ad42 vocab=f7962e57
-/
theorem traceLambda_sq_dvd_iff (x : O) :
    traceLambda ^ 2 ∣ x ↔ lambda ^ 2 ∣ x := by
  rw [traceLambda_eq_unit_mul_lambda, mul_pow]
  exact (neg_omega_isUnit.pow 2).mul_left_dvd

/--
@isnad1 id=isprimit.1h1v.s9.51d1d0f504ca from=translated src=- shape=a9a690d3 vocab=30e23e5d
-/
theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow

/--
@isnad1 id=dvd.1h1v.s7.7191d85c7d06 from=translated src=- shape=acea02b8 vocab=06ba2a67
-/
theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h

noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq

/--
@isnad1 id=eq.1h2v.s10.1ea11b4a1a66 from=translated src=- shape=0144bd7d vocab=a60eed30
-/
theorem cubicChar_reduce (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    (Ideal.Quotient.mk P) (cubicChar P hgood x) =
      x ^ ((Nat.card (O ⧸ P) - 1) / 3) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  rw [Nat.card_eq_fintype_card]
  change (Ideal.Quotient.mk P)
      (ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
        omega_primitive (omega_reduced_primitive P hgood) m hq x) = x ^ m
  by_cases hx : x = 0
  · subst x
    rw [(ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
      omega_primitive (omega_reduced_primitive P hgood) m hq).map_zero,
      map_zero, zero_pow hm.ne']
  · let u : (O ⧸ P)ˣ := (isUnit_iff_ne_zero.mpr hx).unit
    have hu : (u : O ⧸ P) = x := (isUnit_iff_ne_zero.mpr hx).unit_spec
    rw [← hu]
    exact ActualCubicChar.cubicResidueChar_reduce_unit
      (Ideal.Quotient.mk P) omega omega_primitive
      (omega_reduced_primitive P hgood) m hq u

/--
@isnad1 id=eq.1h1v.s10.2a4d0f8480b2 from=translated src=- shape=71edff3b vocab=e897eab2
-/
theorem cubicChar_pow_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ^ 3 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  change ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq ^ 3 = 1
  exact ActualCubicChar.cubicResidueChar_pow_three
    (Ideal.Quotient.mk P) omega omega_primitive
    (omega_reduced_primitive P hgood) m hq

/--
@isnad1 id=ne.1h1v.s8.a2a4c085885e from=translated src=- shape=5264c0b1 vocab=1a429f10
-/
theorem cubicChar_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : cubicChar P hgood ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 0 < m := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  intro hχ
  have hall : ∀ u : (O ⧸ P)ˣ, u ^ m = 1 := by
    intro u
    apply Units.ext
    have hr := cubicChar_reduce P hgood (u : O ⧸ P)
    rw [hχ, MulChar.one_apply_coe, map_one] at hr
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      Nat.card_eq_fintype_card] using hr.symm
  have hdvd := (FiniteField.forall_pow_eq_one_iff (O ⧸ P) m).mp hall
  rw [hq] at hdvd
  have hle := Nat.le_of_dvd hm hdvd
  omega

/--
@isnad1 id=eq.1h1v.s9.aa88adc8c8ad from=translated src=- shape=515a6597 vocab=535189d7
-/
theorem cubicChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : orderOf (cubicChar P hgood) = 3 := by
  have hdvd : orderOf (cubicChar P hgood) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one (cubicChar_pow_three P hgood)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact False.elim ((cubicChar_ne_one P hgood) (orderOf_eq_one_iff.mp h1))
  · exact h3

/--
@isnad1 id=ex.1h1v.s8.919be675810b from=translated src=- shape=3c75ad3d vocab=ac439e5b
-/
theorem cubicJacobi_primary (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ z ∈ Algebra.adjoin ℤ {omega},
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) =
        -1 + z * lambda ^ 2 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  simpa only [lambda] using
    (exists_jacobiSum_eq_neg_one_add (n := 3) (by decide)
      (cubicChar_pow_three P hgood) (cubicChar_pow_three P hgood)
      (by simpa only [Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood)
      omega_primitive)

/--
@isnad1 id=mem.1h1v.s8.c38feed6bd5e from=translated src=- shape=ff586c73 vocab=92c91b59
-/
theorem cubicJacobi_mem_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  have hm : 2 * m < Fintype.card (O ⧸ P) - 1 := by
    have hcard : 1 < Fintype.card (O ⧸ P) := Fintype.one_lt_card
    omega
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_reduce P hgood]
  simp only [Nat.card_eq_fintype_card]
  exact ActualCubicChar.euler_jacobi_sum_zero m hm

/--
@isnad1 id=eq.1h1v.s9.15a3e3ffe593 from=translated src=- shape=90b9654e vocab=d88f364f
-/
theorem cubicJacobi_product (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ =
        (Nat.card (O ⧸ P) : O) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let ι : O →+* K := algebraMap O K
  let ψ := (cubicChar P hgood).ringHomComp ι
  have hchar : ringChar K ≠ ringChar (O ⧸ P) := by
    rw [ringChar.eq_zero]
    exact (CharP.char_is_prime (O ⧸ P) (ringChar (O ⧸ P))).ne_zero.symm
  have hψ : ψ ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr
      (cubicChar_ne_one P hgood)
  have hχ2 : cubicChar P hgood * cubicChar P hgood ≠ 1 := by
    intro h
    have hd : orderOf (cubicChar P hgood) ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hψ2 : ψ * ψ ≠ 1 := by
    rw [show ψ * ψ =
      (cubicChar P hgood * cubicChar P hgood).ringHomComp ι by
        exact (MulChar.ringHomComp_mul _ _ _).symm]
    exact (MulChar.ringHomComp_ne_one_iff RingOfIntegers.coe_injective).mpr hχ2
  have hprod := jacobiSum_mul_jacobiSum_inv hchar hψ hψ hψ2
  apply RingOfIntegers.coe_injective
  change ι (jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹) =
    ι (Nat.card (O ⧸ P) : O)
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp,
    ← MulChar.ringHomComp_inv]
  simpa only [ψ, Nat.card_eq_fintype_card, map_natCast] using hprod

private noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv

/--
@isnad1 id=eq.0h0v.s8.1a087273d8be from=translated src=- shape=1bccbf1c vocab=efc48f8a
-/
theorem conjO_omega : conjO omega = omega ^ 2 := by
  apply RingOfIntegers.coe_injective
  change conjK (IsCyclotomicExtension.zeta 3 ℚ K) =
    (IsCyclotomicExtension.zeta 3 ℚ K) ^ 2
  exact IsCyclotomicExtension.fromZetaAut_spec
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))

private theorem conjO_cubic_root (x : O) (hx : x ^ 3 = 1) :
    conjO x = x ^ 2 := by
  obtain ⟨j, _, hj⟩ := omega_primitive.eq_pow_of_pow_eq_one hx
  rw [← hj, map_pow, conjO_omega]
  simp only [← pow_mul]
  rw [Nat.mul_comm]

/--
@isnad1 id=eq.1h2v.s10.6da40c4a0b4d from=translated src=- shape=22ef5aec vocab=41b6b18a
-/
theorem cubicChar_conj_eq_inv (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (x : O ⧸ P) :
    conjO (cubicChar P hgood x) = (cubicChar P hgood)⁻¹ x := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let χ := cubicChar P hgood
  have hinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using cubicChar_pow_three P hgood
  rw [hinv, χ.pow_apply' (by decide)]
  by_cases hx : x = 0
  · subst x
    rw [χ.map_zero, map_zero, zero_pow (by decide)]
  · have hχ3 : χ x ^ 3 = 1 := by
      rw [← χ.pow_apply' (by decide), cubicChar_pow_three P hgood]
      exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)
    exact conjO_cubic_root (χ x) hχ3

/--
@isnad1 id=eq.1h1v.s9.4064c17f4de3 from=translated src=- shape=483ff4d2 vocab=014925d4
-/
theorem cubicJacobi_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
      jacobiSum (cubicChar P hgood)⁻¹ (cubicChar P hgood)⁻¹ := by
  classical
  rw [jacobiSum, map_sum]
  simp_rw [map_mul, cubicChar_conj_eq_inv P hgood]
  rfl

/--
@isnad1 id=eq.1h1v.s9.96025088a9e9 from=translated src=- shape=ae02b866 vocab=bf775c9f
-/
theorem cubicJacobi_mul_conj (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) *
      conjO (jacobiSum (cubicChar P hgood) (cubicChar P hgood)) =
        (Nat.card (O ⧸ P) : O) := by
  rw [cubicJacobi_conj P hgood]
  exact cubicJacobi_product P hgood

end

private noncomputable def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)

/--
@isnad1 id=eq.0h1v.s10.834af3c35875 from=translated src=- shape=05c5527e vocab=e7018822
-/
theorem quadraticCharO_sq (P : Ideal O) [P.IsMaximal] :
    quadraticCharO P ^ 2 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change ((quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)) ^ 2 = 1
  exact ((quadraticChar_isQuadratic (O ⧸ P)).comp (Int.castRingHom O)).sq_eq_one

noncomputable def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P

/--
@isnad1 id=and.1h1v.s11.f6d40d7e6a2b from=translated src=- shape=b8d9b578 vocab=86f6cc42
-/
theorem sexticChar_powers (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    sexticChar P hgood ^ 2 = cubicChar P hgood ∧
    sexticChar P hgood ^ 3 = quadraticCharO P ∧
    sexticChar P hgood ^ 6 = 1 := by
  have hc := cubicChar_pow_three P hgood
  have hq := quadraticCharO_sq P
  let c := cubicChar P hgood
  let q := quadraticCharO P
  have htwo : (c ^ 2 * q) ^ 2 = c := by
    calc
      (c ^ 2 * q) ^ 2 = c ^ 4 * q ^ 2 := by rw [mul_pow, ← pow_mul]
      _ = c := by rw [hq]; calc
        c ^ 4 * 1 = c ^ 3 * c := by group
        _ = c := by rw [hc, one_mul]
  have hthree : (c ^ 2 * q) ^ 3 = q := by
    calc
      (c ^ 2 * q) ^ 3 = (c ^ 3) ^ 2 * (q ^ 2) * q := by simp [mul_pow]; group
      _ = q := by rw [hc, hq]; group
  refine ⟨htwo, hthree, ?_⟩
  calc
    (c ^ 2 * q) ^ 6 = ((c ^ 2 * q) ^ 3) ^ 2 := by group
    _ = 1 := by rw [hthree, hq]

/--
@isnad1 id=not.0h0v.s5.4604e1c051a5 from=translated src=- shape=b77b284c vocab=026b0e34
-/
theorem lambda_not_dvd_two : ¬ lambda ∣ (2 : O) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hprime : Prime lambda :=
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'
  let I : Ideal O := Ideal.span {lambda}
  have hI : I.IsMaximal := by
    have hp : I.IsPrime := Ideal.isPrime_span_singleton_of_prime hprime
    have hne : I ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hprime.ne_zero
    exact hp.isMaximal hne
  let : I.IsMaximal := hI
  let : Field (O ⧸ I) := Ideal.Quotient.field I
  let : Fintype (O ⧸ I) := Fintype.ofFinite _
  have hcard : Nat.card (O ⧸ I) = 3 := by
    change Nat.card (O ⧸ Ideal.span {omega - 1}) = 3
    rw [omega,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
        (by decide)]
    norm_num
  intro hdiv
  have hmem : (2 : O) ∈ I := (Ideal.mem_span_singleton).mpr hdiv
  have hzero : (2 : O ⧸ I) = 0 := (Ideal.Quotient.eq_zero_iff_mem).mpr hmem
  have hchar : ringChar (O ⧸ I) = 2 := by
    have hdvd : ringChar (O ⧸ I) ∣ 2 := (ringChar.spec (O ⧸ I) 2).mp hzero
    exact (Nat.prime_dvd_prime_iff_eq
      (CharP.char_is_prime (O ⧸ I) (ringChar (O ⧸ I))) Nat.prime_two).mp hdvd
  have heven := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, hcard] at heven
  norm_num at heven

private theorem conjK_ne_refl : conjK ≠ AlgEquiv.refl := by
  intro he
  have hw : omega ^ 2 = omega := by
    have hc : conjO omega = omega := by
      apply NumberField.RingOfIntegers.coe_injective
      change conjK (omega : K) = (omega : K)
      rw [he]
      rfl
    exact conjO_omega.symm.trans hc
  have hw1 : omega = 1 := by
    have hunit : IsUnit omega := omega_primitive.isUnit (by decide)
    apply (mul_left_cancel₀ hunit.ne_zero)
    calc
      omega * omega = omega ^ 2 := by ring
      _ = omega := hw
      _ = omega * 1 := by ring
  exact (omega_primitive.ne_one (by decide)) hw1

private theorem galois_card_two : Fintype.card (K ≃ₐ[ℚ] K) = 2 := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ K,
    IsCyclotomicExtension.finrank (n := 3) K
      (Polynomial.cyclotomic.irreducible_rat (by decide))]
  decide

private theorem galois_univ_pair [DecidableEq (K ≃ₐ[ℚ] K)] :
    (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {(AlgEquiv.refl : K ≃ₐ[ℚ] K), conjK} := by
  symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  rw [Finset.card_univ, galois_card_two, Finset.card_pair]
  exact conjK_ne_refl.symm

private theorem norm_eq_mul_conjK (p : O) :
    ((Algebra.norm ℚ (p : K) : ℚ) : K) = (p : K) * conjK (p : K) := by
  classical
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K
  have h := Algebra.norm_eq_prod_automorphisms ℚ (p : K)
  rw [galois_univ_pair, Finset.prod_pair conjK_ne_refl.symm] at h
  simpa using h

/--
@isnad1 id=eq.0h1v.s8.db5b8c5aaa0c from=translated src=- shape=075aa398 vocab=412d73a6
-/
theorem norm_int_eq_mul_conjO (p : O) :
    ((Algebra.norm ℤ p : ℤ) : O) = p * conjO p := by
  apply NumberField.RingOfIntegers.coe_injective
  change ((Algebra.norm ℤ p : ℤ) : K) = (p : K) * conjK (p : K)
  have h := norm_eq_mul_conjK p
  rw [← Algebra.coe_norm_int p] at h
  exact h

private theorem generator_mul_conj_eq_sign_card (P : Ideal O) [P.IsMaximal]
    (p : O) (hP : P = Ideal.span {p}) :
    p * conjO p = (Nat.card (O ⧸ P) : O) ∨
      p * conjO p = -(Nat.card (O ⧸ P) : O) := by
  have habs : (Algebra.norm ℤ p).natAbs = Nat.card (O ⧸ P) := by
    calc
      (Algebra.norm ℤ p).natAbs = Ideal.absNorm (Ideal.span {p}) :=
        (Ideal.absNorm_span_singleton p).symm
      _ = Ideal.absNorm P := by rw [← hP]
      _ = Nat.card (O ⧸ P) := by
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hsq : (Algebra.norm ℤ p) * (Algebra.norm ℤ p) =
      (Nat.card (O ⧸ P) : ℤ) * (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.natAbs_eq_iff_mul_self_eq).mp
    simpa using habs
  have hzero : (Algebra.norm ℤ p - (Nat.card (O ⧸ P) : ℤ)) *
      (Algebra.norm ℤ p + (Nat.card (O ⧸ P) : ℤ)) = 0 := by
    nlinarith [hsq]
  rcases mul_eq_zero.mp hzero with hpos | hneg
  · left
    have heq : Algebra.norm ℤ p = (Nat.card (O ⧸ P) : ℤ) := sub_eq_zero.mp hpos
    simp [← norm_int_eq_mul_conjO p, heq]
  · right
    have heq : Algebra.norm ℤ p = -(Nat.card (O ⧸ P) : ℤ) := add_eq_zero_iff_eq_neg.mp hneg
    simp [← norm_int_eq_mul_conjO p, heq]

/--
@isnad1 id=ex.2h2v.s8.425ded2b8750 from=translated src=- shape=a83dedff vocab=3d9c3b50
-/
theorem cubicJacobi_unit_multiple_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p}) :
    ∃ u : Oˣ, jacobiSum (cubicChar P hgood) (cubicChar P hgood) = p * u := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hdiv : p ∣ J := (Ideal.mem_span_singleton).mp (hP ▸ cubicJacobi_mem_prime P hgood)
  obtain ⟨v, hv⟩ := hdiv
  have hqne : (Nat.card (O ⧸ P) : O) ≠ 0 := by
    exact_mod_cast Nat.card_pos.ne'
  have hnorm := generator_mul_conj_eq_sign_card P p hP
  have hpne : p * conjO p ≠ 0 := by
    rcases hnorm with h | h
    · rw [h]; exact hqne
    · rw [h]; exact neg_ne_zero.mpr hqne
  have hprod : (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := by
    calc
      (p * conjO p) * (v * conjO v) = (p * v) * conjO (p * v) := by
        rw [map_mul]; ring
      _ = J * conjO J := by rw [hv]
      _ = (Nat.card (O ⧸ P) : O) := cubicJacobi_mul_conj P hgood
  have hvnorm : v * conjO v = 1 ∨ v * conjO v = -1 := by
    rcases hnorm with hpos | hneg
    · left
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * 1 := by rw [hpos]; ring
    · right
      apply mul_left_cancel₀ hpne
      calc
        (p * conjO p) * (v * conjO v) = (Nat.card (O ⧸ P) : O) := hprod
        _ = (p * conjO p) * -1 := by rw [hneg]; ring
  have hvunit : IsUnit v := by
    rcases hvnorm with h | h
    · exact IsUnit.of_mul_eq_one (conjO v) h
    · apply IsUnit.of_mul_eq_one (-conjO v)
      rw [mul_neg, h]
      ring
  refine ⟨hvunit.unit, ?_⟩
  simpa only [hvunit.unit_spec] using hv

/--
@isnad1 id=eq.3h2v.s8.63e14e18287e from=translated src=- shape=ca5f3e84 vocab=de8d6975
-/
theorem cubicJacobi_eq_neg_primary_generator_of_principal (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  obtain ⟨u, hJu⟩ := cubicJacobi_unit_multiple_of_principal P hgood p hP
  change J = p * (u : O) at hJu
  obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
  have hJmod : lambda ^ 2 ∣ J + 1 := by
    refine ⟨z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring
  have hucong : lambda ^ 2 ∣ (u : O) + 1 := by
    have heq : (u : O) + 1 = (J + 1) - (p - 1) * (u : O) := by
      rw [hJu]
      ring
    rw [heq]
    exact dvd_sub hJmod (dvd_mul_of_dvd_left hprimary _)
  have hunit : u = 1 ∨ u = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) u
    refine ⟨(-1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_neg, Int.cast_one, sub_neg_eq_add] using hucong
  rcases hunit with h1 | hneg
  · have htwo : lambda ^ 2 ∣ (2 : O) := by
      simpa [h1, one_add_one_eq_two] using hucong
    exact False.elim (lambda_not_dvd_two ((dvd_pow_self lambda (by decide)).trans htwo))
  · rw [hneg] at hJu
    simpa only [Units.val_neg, Units.val_one, mul_neg, mul_one] using hJu

/--
@isnad1 id=eq.1h1v.s7.a3e234f643f4 from=translated src=- shape=3789c607 vocab=b74ae676
-/
theorem cubicJacobi_generates_prime (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    P = Ideal.span {jacobiSum (cubicChar P hgood) (cubicChar P hgood)} := by
  classical
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  have hnormJ : Algebra.norm ℤ J = (Nat.card (O ⧸ P) : ℤ) := by
    apply (Int.cast_injective : Function.Injective (Int.cast : ℤ → O))
    change ((Algebra.norm ℤ J : ℤ) : O) = (Nat.card (O ⧸ P) : O)
    rw [norm_int_eq_mul_conjO]
    exact cubicJacobi_mul_conj P hgood
  have habsJ : Ideal.absNorm (Ideal.span {J}) = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_span_singleton, hnormJ]
    simp
  have habsP : Ideal.absNorm P = Nat.card (O ⧸ P) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hle : Ideal.span {J} ≤ P :=
    (Ideal.span_singleton_le_iff_mem P).mpr (cubicJacobi_mem_prime P hgood)
  obtain ⟨Q, hQ⟩ := (Ideal.dvd_iff_le).mpr hle
  have hq : Nat.card (O ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hQnorm : Ideal.absNorm Q = 1 := by
    have heq : Nat.card (O ⧸ P) = Nat.card (O ⧸ P) * Ideal.absNorm Q := by
      calc
        Nat.card (O ⧸ P) = Ideal.absNorm (Ideal.span {J}) := habsJ.symm
        _ = Ideal.absNorm (P * Q) := by rw [hQ]
        _ = Ideal.absNorm P * Ideal.absNorm Q := map_mul Ideal.absNorm P Q
        _ = Nat.card (O ⧸ P) * Ideal.absNorm Q := by rw [habsP]
    exact (mul_left_cancel₀ hq (heq.symm.trans (by ring)))
  have hQtop : Q = ⊤ := Ideal.absNorm_eq_one_iff.mp hQnorm
  change P = Ideal.span {J}
  rw [hQ, hQtop, ← Ideal.one_eq_top, mul_one]

/--
@isnad1 id=ex.1h1v.s8.832bb2059046 from=translated src=- shape=c7898bc6 vocab=de8d6975
-/
theorem cubicJacobi_exists_primary_generator (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    ∃ p : O, P = Ideal.span {p} ∧ lambda ^ 2 ∣ p - 1 ∧
      jacobiSum (cubicChar P hgood) (cubicChar P hgood) = -p := by
  let J := jacobiSum (cubicChar P hgood) (cubicChar P hgood)
  refine ⟨-J, ?_, ?_, by simp [J]⟩
  · have h := cubicJacobi_generates_prime P hgood
    simpa only [J, Ideal.span_singleton_neg] using h
  · obtain ⟨z, _, hJ⟩ := cubicJacobi_primary P hgood
    refine ⟨-z, ?_⟩
    dsimp [J]
    rw [hJ]
    ring

/--
@isnad1 id=eq.5h5v.s9.1463687ca8e8 from=translated src=- shape=e1cb0706 vocab=9d6c1f88
-/
theorem cubicGauss_cube {E : Type*} [Field E] (ι : O →+* E)
    (hι : Function.Injective ι) (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1)
    (ψ : AddChar (O ⧸ P) E) (hψ : ψ.IsPrimitive) :
    gaussSum ((cubicChar P hgood).ringHomComp ι) ψ ^ 3 =
      -(ι p) * (Nat.card (O ⧸ P) : E) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ := cubicChar P hgood
  let ξ := χ.ringHomComp ι
  have hχ3 : χ ^ 3 = 1 := cubicChar_pow_three P hgood
  have hχne : χ ≠ 1 := cubicChar_ne_one P hgood
  have hχ2 : χ * χ ≠ 1 := by
    intro h
    have hd : orderOf χ ∣ 2 := by
      rw [← pow_two] at h
      exact orderOf_dvd_of_pow_eq_one h
    rw [cubicChar_order P hgood] at hd
    norm_num at hd
  have hξne : ξ ≠ 1 := (MulChar.ringHomComp_ne_one_iff hι).mpr hχne
  have hξ2 : ξ * ξ ≠ 1 := by
    rw [show ξ * ξ = (χ * χ).ringHomComp ι by
      exact (MulChar.ringHomComp_mul χ χ ι).symm]
    exact (MulChar.ringHomComp_ne_one_iff hι).mpr hχ2
  have hχinv : χ⁻¹ = χ ^ 2 := by
    apply inv_eq_iff_mul_eq_one.mpr
    simpa only [pow_succ, mul_comm] using hχ3
  have hξinv : ξ⁻¹ = ξ ^ 2 := by
    change (χ.ringHomComp ι)⁻¹ = (χ.ringHomComp ι) ^ 2
    rw [MulChar.ringHomComp_inv, MulChar.ringHomComp_pow, hχinv]
  have hξmul : ξ * ξ = ξ⁻¹ := by rw [hξinv, pow_two]
  have hχneg : χ (-1) = 1 :=
    MulChar.val_neg_one_eq_one_of_odd_order (by decide : Odd 3) hχ3
  have hξneg : ξ (-1) = 1 := by
    change ι (χ (-1)) = 1
    rw [hχneg, map_one]
  have hξinvneg : ξ⁻¹ (-1) = 1 := by
    rw [MulChar.inv_apply_eq_inv', hξneg, inv_one]
  have hgs : gaussSum ξ ψ * gaussSum ξ⁻¹ ψ = (Nat.card (O ⧸ P) : E) := by
    have h := gaussSum_mul_gaussSum_eq_card hξne hψ
    have hshift := mul_gaussSum_inv_eq_gaussSum ξ⁻¹ ψ
    rw [hξinvneg, one_mul] at hshift
    rw [hshift] at h
    simpa only [Nat.card_eq_fintype_card] using h
  have hJ : jacobiSum ξ ξ = -(ι p) := by
    change jacobiSum (χ.ringHomComp ι) (χ.ringHomComp ι) = -(ι p)
    rw [jacobiSum_ringHomComp]
    rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
      map_neg]
  have hgj : gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ = gaussSum ξ ψ * gaussSum ξ ψ := by
    simpa only [hξmul] using jacobiSum_mul_nontrivial hξ2 ψ
  calc
    gaussSum ξ ψ ^ 3 = (gaussSum ξ ψ * gaussSum ξ ψ) * gaussSum ξ ψ := by ring
    _ = (gaussSum ξ⁻¹ ψ * jacobiSum ξ ξ) * gaussSum ξ ψ := by rw [hgj]
    _ = (gaussSum ξ ψ * gaussSum ξ⁻¹ ψ) * jacobiSum ξ ξ := by ring
    _ = -(ι p) * (Nat.card (O ⧸ P) : E) := by rw [hgs, hJ]; ring

private noncomputable def complexEmbedding : K →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift

noncomputable def ringComplex : O →+* ℂ :=
  complexEmbedding.toRingHom.comp (algebraMap O K)

/--
@isnad1 id=injectiv.0h0v.s5.eb29cc9a574e from=translated src=- shape=f51e303a vocab=92272b5f
-/
theorem ringComplex_injective : Function.Injective ringComplex :=
  complexEmbedding.injective.comp NumberField.RingOfIntegers.coe_injective

/--
@isnad1 id=eq.3h2v.s9.77e37871e7b5 from=translated src=- shape=0df029f2 vocab=8ec25ab5
-/
theorem primary_generator_mul_conj_eq_card (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (p : O) (hP : P = Ideal.span {p})
    (hprimary : lambda ^ 2 ∣ p - 1) :
    p * conjO p = (Nat.card (O ⧸ P) : O) := by
  have h := cubicJacobi_mul_conj P hgood
  rw [cubicJacobi_eq_neg_primary_generator_of_principal P hgood p hP hprimary,
    map_neg] at h
  simpa only [neg_mul_neg] using h

/--
@isnad1 id=ne.1h1v.s8.e30d3b0e62f2 from=translated src=- shape=4725e8a4 vocab=263cce5a
-/
theorem quadraticCharO_ne_one (P : Ideal O) [P.IsMaximal]
    (hchar : ringChar (O ⧸ P) ≠ 2) : quadraticCharO P ≠ 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  change (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O) ≠ 1
  exact (MulChar.ringHomComp_ne_one_iff
    (Int.cast_injective (α := O))).2 (quadraticChar_ne_one hchar)

/--
@isnad1 id=eq.2h1v.s9.eb8cdf8dd2cd from=translated src=- shape=0b6ce455 vocab=ed238c5a
-/
theorem sexticChar_order (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (sexticChar P hgood) = 6 := by
  have h2 := (sexticChar_powers P hgood).1
  have h3 := (sexticChar_powers P hgood).2.1
  have h6 := (sexticChar_powers P hgood).2.2
  have hdiv : orderOf (sexticChar P hgood) ∣ 6 :=
    orderOf_dvd_of_pow_eq_one h6
  have hne2 : orderOf (sexticChar P hgood) ≠ 2 := by
    intro he
    have hχ2 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h2] at hχ2
    exact cubicChar_ne_one P hgood hχ2
  have hne3 : orderOf (sexticChar P hgood) ≠ 3 := by
    intro he
    have hχ3 := pow_orderOf_eq_one (sexticChar P hgood)
    rw [he, h3] at hχ3
    exact quadraticCharO_ne_one P hchar hχ3
  have hne1 : orderOf (sexticChar P hgood) ≠ 1 := by
    intro he
    have hχ1 := orderOf_eq_one_iff.mp he
    rw [hχ1] at h2
    exact cubicChar_ne_one P hgood (by simpa using h2.symm)
  have hne0 : orderOf (sexticChar P hgood) ≠ 0 := by
    intro he
    norm_num [he] at hdiv
  have hpos : 0 < orderOf (sexticChar P hgood) := Nat.pos_of_ne_zero hne0
  have hle : orderOf (sexticChar P hgood) ≤ 6 := Nat.le_of_dvd (by norm_num) hdiv
  have hne4 : orderOf (sexticChar P hgood) ≠ 4 := by
    intro he
    norm_num [he] at hdiv
  have hne5 : orderOf (sexticChar P hgood) ≠ 5 := by
    intro he
    norm_num [he] at hdiv
  omega

/--
@isnad1 id=eq.2h2v.s10.750b62b5c309 from=translated src=- shape=ee37758f vocab=7b76ddfd
-/
theorem sexticChar_reduce_unit (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (u : (O ⧸ P)ˣ) :
    (Ideal.Quotient.mk P) (sexticChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((Nat.card (O ⧸ P) - 1) / 6) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let N := Fintype.card (O ⧸ P)
  let m := (N - 1) / 6
  have hthree : 3 ∣ N - 1 := by
    simpa only [N, Nat.card_eq_fintype_card] using card_sub_one_div_three P hgood
  have hodd : N % 2 = 1 := FiniteField.odd_card_of_char_ne_two hchar
  have hN : 1 < N := Fintype.one_lt_card
  have hsix : 6 ∣ N - 1 := by omega
  have hsize : N - 1 = 6 * m := by
    dsimp [m]
    exact (Nat.mul_div_cancel_left' hsix).symm
  have hthird : (N - 1) / 3 = 2 * m := by omega
  have hhalf : N / 2 = 3 * m := by omega
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hquad : ρ (quadraticCharO P (u : O ⧸ P)) =
      (u : O ⧸ P) ^ (N / 2) := by
    change (quadraticChar (O ⧸ P) (u : O ⧸ P) : O ⧸ P) = _
    exact quadraticChar_eq_pow_of_char_ne_two' hchar (u : O ⧸ P)
  have hcub : ρ (cubicChar P hgood (u : O ⧸ P)) =
      (u : O ⧸ P) ^ ((N - 1) / 3) := by
    simpa only [N, Nat.card_eq_fintype_card] using cubicChar_reduce P hgood (u : O ⧸ P)
  have hfermat : (u : O ⧸ P) ^ (N - 1) = 1 :=
    FiniteField.pow_card_sub_one_eq_one _ (Units.ne_zero u)
  change ρ ((cubicChar P hgood ^ 2 * quadraticCharO P) (u : O ⧸ P)) = _
  rw [MulChar.mul_apply, MulChar.pow_apply', map_mul, map_pow, hcub, hquad]
  rw [hthird, hhalf]
  simpa only [Nat.card_eq_fintype_card, N, m] using
    (show ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
      (u : O ⧸ P) ^ m by
      calc
        ((u : O ⧸ P) ^ (2 * m)) ^ 2 * (u : O ⧸ P) ^ (3 * m) =
            (u : O ⧸ P) ^ (7 * m) := by
              rw [← pow_mul, ← pow_add]
              congr 1
              omega
        _ = (u : O ⧸ P) ^ m * (u : O ⧸ P) ^ (N - 1) := by
          rw [hsize, ← pow_add]; congr 1; omega
        _ = (u : O ⧸ P) ^ m := by rw [hfermat, mul_one])
  all_goals norm_num

/--
@isnad1 id=ne.1h1v.s7.3dc513bbaf54 from=translated src=- shape=8c28efee vocab=ecf1e2b7
-/
theorem quotient_char_ne_two_of_two_not_mem (P : Ideal O) [P.IsMaximal]
    (h2 : (2 : O) ∉ P) : ringChar (O ⧸ P) ≠ 2 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  intro heq
  have hz : ((ringChar (O ⧸ P) : ℕ) : O ⧸ P) = 0 := ringChar.Nat.cast_ringChar
  rw [heq] at hz
  apply h2
  exact (Ideal.Quotient.eq_zero_iff_mem).mp (by simpa only [map_ofNat, Nat.cast_ofNat] using hz)

end ActualEisensteinCubic

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
