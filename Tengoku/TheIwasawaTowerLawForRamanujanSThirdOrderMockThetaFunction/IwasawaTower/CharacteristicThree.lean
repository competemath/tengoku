import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.BaseCases
import Tengoku.TheIwasawaTowerLawForRamanujanSThirdOrderMockThetaFunction.IwasawaTower.BlockExpansions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The characteristic-three tower induction

Author: Joesph D. Burke III.

This file keeps the weak bound on `W` logically independent of the stronger
auxiliary theorem.  Only that weak bound enters the induction for `F`.
-/

noncomputable section

open scoped BigOperators

namespace IwasawaTower.Series

open Finset PowerSeries

namespace InitialPolynomial

abbrev P := FinitePolynomial.P

local instance : CharP P 3 := charP_of_injective_algebraMap' 𝔽₃ 3

private theorem cast_mod_three (k : ℕ) :
    ((k : ℕ) : P) = Polynomial.C ((k % 3 : ℕ) : 𝔽₃) := by
  rw [CharP.cast_eq_mod (R := P) 3]
  rfl

private theorem C_two_eq_neg_one : Polynomial.C (2 : 𝔽₃) = (-1 : P) := by
  simpa using congrArg (Polynomial.C : 𝔽₃ →+* P) (show (2 : 𝔽₃) = -1 by decide)

def f (N : ℕ) : P :=
  ∑ r ∈ Finset.range N,
    FinitePolynomial.x ^ (r + 1) * FinitePolynomial.a r ^ 2

def qFThree : P :=
  -(FinitePolynomial.y ^ 2 + FinitePolynomial.y ^ 3 +
    FinitePolynomial.y ^ 5 + FinitePolynomial.y ^ 6 + FinitePolynomial.y ^ 7)

def qAThree : P :=
  FinitePolynomial.y ^ 9 + FinitePolynomial.y ^ 8 + FinitePolynomial.y ^ 7 +
    FinitePolynomial.y ^ 5 - FinitePolynomial.y ^ 4 + FinitePolynomial.y ^ 3 -
    FinitePolynomial.y ^ 2 + FinitePolynomial.y

@[simp] theorem coe_f (N : ℕ) : ((f N : P) : PS) = F N := by
  simp [f, F]

private theorem f_three_exact :
    f 3 = -FinitePolynomial.y + FinitePolynomial.y ^ 2 * qFThree := by
  norm_num [f, FinitePolynomial.a, FinitePolynomial.x, FinitePolynomial.y,
    qFThree, Finset.sum_range_succ, Finset.prod_range_succ]
  ring_nf
  simp only [← Nat.cast_ofNat (R := P), cast_mod_three]
  norm_num
  rw [C_two_eq_neg_one]
  ring

private theorem a_three_sq_exact :
    FinitePolynomial.a 3 ^ 2 - 1 =
      -FinitePolynomial.y ^ 2 + FinitePolynomial.y ^ 3 * qAThree := by
  norm_num [FinitePolynomial.a, FinitePolynomial.x, FinitePolynomial.y,
    qAThree, Finset.prod_range_succ]
  ring_nf
  simp only [← Nat.cast_ofNat (R := P), cast_mod_three]
  norm_num
  rw [C_two_eq_neg_one]
  ring

end InitialPolynomial

/-- The initial `F` congruence, checked by a finite polynomial certificate.-/
theorem F_three_hasLeading : HasLeading 1 (-1) (F 3) := by
  rw [HasLeading, ← InitialPolynomial.coe_f, InitialPolynomial.f_three_exact]
  refine ⟨((InitialPolynomial.qFThree : InitialPolynomial.P) : PS), ?_⟩
  simp [InitialPolynomial.qFThree, FinitePolynomial.y, Y]

/-- The initial congruence for `A₃²-1`, checked by a finite polynomial certificate.-/
theorem A_three_sq_sub_one_hasLeading : HasLeading 2 (-1) (A 3 ^ 2 - 1) := by
  have hcoe : A 3 ^ 2 - 1 =
      (((FinitePolynomial.a 3 ^ 2 - 1 : InitialPolynomial.P) : PS)) := by simp
  rw [HasLeading, hcoe, InitialPolynomial.a_three_sq_exact]
  refine ⟨((InitialPolynomial.qAThree : InitialPolynomial.P) : PS), ?_⟩
  simp [InitialPolynomial.qAThree, FinitePolynomial.y, Y]

theorem HasLeading.vanishes {n : ℕ} {c : 𝔽₃} {f : PS}
    (h : HasLeading n c f) : Vanishes n f := by
  obtain ⟨q, hq⟩ := h
  refine ⟨PowerSeries.C c + Y * q, ?_⟩
  rw [eq_add_of_sub_eq hq, pow_succ]
  ring

theorem hasLeading_mul {m n : ℕ} {c d : 𝔽₃} {f g : PS}
    (hf : HasLeading m c f) (hg : HasLeading n d g) :
    HasLeading (m + n) (c * d) (f * g) := by
  obtain ⟨q, hq⟩ := hf
  obtain ⟨r, hr⟩ := hg
  have hf' : f = PowerSeries.C c * Y ^ m + Y ^ (m + 1) * q := by
    rw [eq_add_of_sub_eq hq]
    ring
  have hg' : g = PowerSeries.C d * Y ^ n + Y ^ (n + 1) * r := by
    rw [eq_add_of_sub_eq hr]
    ring
  refine ⟨PowerSeries.C c * r + PowerSeries.C d * q + Y * q * r, ?_⟩
  rw [hf', hg']
  simp only [map_mul]
  rw [show m + n + 1 = m + (n + 1) by omega]
  simp only [pow_add]
  ring

theorem hasLeading_pow {n : ℕ} {c : 𝔽₃} {f : PS}
    (h : HasLeading n c f) : ∀ k : ℕ,
    HasLeading (k * n) (c ^ k) (f ^ k)
  | 0 => by simp [HasLeading, ModY.refl]
  | k + 1 => by
      simpa [pow_succ, Nat.succ_mul, add_comm] using hasLeading_mul (hasLeading_pow h k) h

private theorem L_one_sub_cube_vanishes : Vanishes 1 (L 1 - L 1 ^ 3) := by
  have hinv : (2 : 𝔽₃)⁻¹ = 2 :=
    ZMod.inv_eq_of_mul_eq_one 3 2 2 (by decide)
  have hc : constantCoeff (L 1 - L 1 ^ 3) = 0 := by
    simp [L, hinv]
  obtain ⟨q, hq⟩ := PowerSeries.X_dvd_iff.mpr hc
  exact ⟨q, by simpa [Y] using hq⟩

/-- The logarithmic sum vanishes to the full block length at the initial level.-/
theorem L_three_vanishes : Vanishes 3 (L 3) := by
  have hrec := L_three_block_precise (N := 1) ⟨0, by norm_num⟩
  have hdelta : Vanishes 2 (delta 1 ^ 2) := by
    simpa [pow_two] using Vanishes.mul (delta_vanishes 1) (delta_vanishes 1)
  have hrhs : Vanishes 3 (delta 1 ^ 2 * (L 1 - L 1 ^ 3)) := by
    simpa using Vanishes.mul hdelta L_one_sub_cube_vanishes
  exact Vanishes.of_modY_zero (ModY.trans hrec (Vanishes.modY_zero hrhs))

theorem Vanishes.pow {n : ℕ} {f : PS} (h : Vanishes n f) : ∀ k : ℕ,
    Vanishes (k * n) (f ^ k)
  | 0 => by simp [Vanishes.one_zero]
  | k + 1 => by
      simpa [pow_succ, Nat.succ_mul, add_comm] using Vanishes.mul (Vanishes.pow h k) h

theorem HasLeading.of_modY {n : ℕ} {c : 𝔽₃} {f g : PS}
    (hfg : ModY (n + 1) f g) (hg : HasLeading n c g) : HasLeading n c f :=
  ModY.trans hfg hg

private theorem cube_sq_sub_one (a : PS) :
    (a ^ 3) ^ 2 - 1 = (a ^ 2 - 1) ^ 3 := by
  have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
  linear_combination hthree * (a ^ 4 - a ^ 2)

/-- The four assertions propagated simultaneously at level `3^(b+1)`.-/
structure TowerData (b : ℕ) : Prop where
  fLead : HasLeading (2 * 3 ^ b - 1) (-1) (F (3 ^ (b + 1)))
  aLead : HasLeading (2 * 3 ^ b) (-1) (A (3 ^ (b + 1)) ^ 2 - 1)
  lVanish : Vanishes (3 ^ (b + 1)) (L (3 ^ (b + 1)))
  wVanish : Vanishes (3 ^ b) (W (3 ^ (b + 1)))

set_option maxHeartbeats 1000000 in
private theorem tower_step (b : ℕ) (ih : TowerData b) : TowerData (b + 1) := by
  let p := 3 ^ b
  let N := 3 ^ (b + 1)
  have hNp : N = 3 * p := by simp [N, p, pow_succ, mul_comm]
  have hNpos : 0 < N := by simp [N]
  have hNdiv : 3 ∣ N := by rw [hNp]; exact dvd_mul_right 3 p
  have hNpow : ∃ a, N = 3 ^ a := ⟨b + 1, rfl⟩
  let D := A N ^ 2 - 1
  have hDlead : HasLeading (2 * p) (-1) D := by
    simpa [D, N, p] using ih.aLead
  have hDvan : Vanishes (2 * p) D := hDlead.vanishes

  have hArec := A_three_block_cube hNpos hNdiv hNpow
  have hArecSq := ModY.pow hArec 2
  have hDrec : ModY (2 * N + 1) (A (3 * N) ^ 2 - 1) (D ^ 3) := by
    have hsub := ModY.sub hArecSq (ModY.refl (2 * N + 1) 1)
    simpa [D, cube_sq_sub_one] using hsub
  have hDcube₀ := hasLeading_pow hDlead 3
  have hDcube : HasLeading (2 * N) (-1) (D ^ 3) := by
    convert hDcube₀ using 1
    · rw [hNp]
      omega
    · decide
  have hAnext : HasLeading (2 * N) (-1) (A (3 * N) ^ 2 - 1) :=
    hDcube.of_modY hDrec

  have hLcube : Vanishes (3 * N) (L N ^ 3) := by
    simpa using ih.lVanish.pow 3
  have hLdiff : Vanishes N (L N - L N ^ 3) :=
    Vanishes.sub ih.lVanish (Vanishes.mono (by omega) hLcube)
  have hdeltaSq : Vanishes (2 * N) (delta N ^ 2) := by
    rw [pow_two]
    convert Vanishes.mul (delta_vanishes N) (delta_vanishes N) using 1 <;> omega
  have hLrhs : Vanishes (3 * N) (delta N ^ 2 * (L N - L N ^ 3)) := by
    convert Vanishes.mul hdeltaSq hLdiff using 1 <;> omega
  have hLnext : Vanishes (3 * N) (L (3 * N)) := by
    exact Vanishes.of_modY_zero
      (ModY.trans (L_three_block_precise hNpow) (Vanishes.modY_zero hLrhs))

  have hS : 1 + A N ^ 2 + A N ^ 4 = D ^ 2 := by
    have hthree : (3 : PS) = 0 := CharP.cast_eq_zero (R := PS) 3
    dsimp [D]
    linear_combination hthree * A N ^ 2
  have hDsqVan : Vanishes (4 * p) (D ^ 2) := by
    have := hDvan.pow 2
    convert this using 1 <;> omega
  have hWmain : Vanishes N (W N * (1 + A N ^ 2 + A N ^ 4)) := by
    rw [hS]
    have hprod := Vanishes.mul ih.wVanish hDsqVan
    exact Vanishes.mono (by rw [hNp]; omega) hprod
  have hWlog : Vanishes N (L N * F N * (A N ^ 2 - A N ^ 4)) :=
    by simpa [N, mul_assoc] using
      Vanishes.mul_right (F N * (A N ^ 2 - A N ^ 4)) ih.lVanish
  have hWrhs : Vanishes N
      (W N * (1 + A N ^ 2 + A N ^ 4) -
        L N * F N * (A N ^ 2 - A N ^ 4)) :=
    Vanishes.sub hWmain hWlog
  have hWnext : Vanishes N (W (3 * N)) :=
    Vanishes.of_modY_zero
      (ModY.trans (W_three_block_coarse hNpow) (Vanishes.modY_zero hWrhs))

  have hDsqLead₀ := hasLeading_pow hDlead 2
  have hFmain₀ := hasLeading_mul ih.fLead hDsqLead₀
  have hFmain : HasLeading (2 * N - 1) (-1) (F N * D ^ 2) := by
    convert hFmain₀ using 1
    · rw [hNp]
      omega
    · decide
  have honeSub : Vanishes (2 * p) (1 - A N ^ 2) := by
    simpa [D] using Vanishes.neg hDvan
  have hinnerOne : Vanishes (3 * p)
      (A N ^ 2 * (1 - A N ^ 2) * W N) := by
    have hprod₀ := Vanishes.mul honeSub ih.wVanish
    have hprod : Vanishes (3 * p) ((1 - A N ^ 2) * W N) := by
      convert hprod₀ using 1
      simp [p]
      omega
    simpa [mul_assoc] using Vanishes.mul_left (A N ^ 2) hprod
  have hcorrOne : Vanishes (2 * N)
      (delta N * (A N ^ 2 * (1 - A N ^ 2) * W N)) := by
    have hprod := Vanishes.mul (delta_vanishes N) hinnerOne
    convert hprod using 1
    rw [hNp]
    omega
  have hcorrTwoInner : Vanishes N (A N ^ 4 * L N * F N) := by
    have hprod := Vanishes.mul_left (A N ^ 4 * F N) ih.lVanish
    convert hprod using 1
    ring
  have hcorrTwo : Vanishes (2 * N) (delta N * (A N ^ 4 * L N * F N)) := by
    convert Vanishes.mul (delta_vanishes N) hcorrTwoInner using 1 <;> omega
  have hcorr : Vanishes (2 * N)
      (delta N *
        (A N ^ 2 * (1 - A N ^ 2) * W N - A N ^ 4 * L N * F N)) := by
    rw [mul_sub]
    exact Vanishes.sub hcorrOne hcorrTwo
  have hFdrop : ModY (2 * N)
      (F N * (1 + A N ^ 2 + A N ^ 4) +
        delta N *
          (A N ^ 2 * (1 - A N ^ 2) * W N - A N ^ 4 * L N * F N))
      (F N * D ^ 2) := by
    rw [hS]
    simpa using ModY.add (ModY.refl (2 * N) (F N * D ^ 2))
      (Vanishes.modY_zero hcorr)
  have hFrec := F_three_block_precise hNpow
  have hFmainMod : ModY (2 * N) (F N * D ^ 2)
      (PowerSeries.C (-1) * Y ^ (2 * N - 1)) := by
    simpa only [HasLeading, show 2 * N - 1 + 1 = 2 * N by omega] using hFmain
  have hFchain := ModY.trans hFrec (ModY.trans hFdrop hFmainMod)
  have hFnext : HasLeading (2 * N - 1) (-1) (F (3 * N)) := by
    simpa only [HasLeading, show 2 * N - 1 + 1 = 2 * N by omega] using hFchain

  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hFnext
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hAnext
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hLnext
  · simpa [N, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hWnext

/-- Simultaneous characteristic-three induction.  In particular, the `F`
congruence is proved from the finite block identity rather than from a
multiplicative recurrence.-/
theorem tower_data (b : ℕ) : TowerData b := by
  induction b with
  | zero =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa using F_three_hasLeading
      · simpa using A_three_sq_sub_one_hasLeading
      · simpa using L_three_vanishes
      · exact Vanishes.mono (by omega) W_three_hasLeading.vanishes
  | succ b ih => simpa [Nat.succ_eq_add_one] using tower_step b ih

end IwasawaTower.Series
