import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_WeierstrassCurve_eval_PsiSq_variableChange.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange

set_option autoImplicit false

namespace KatzTransport

open Polynomial

def wt (n : ℕ) : ℕ := n ^ 2 - if Even n then 4 else 1

/--
@isnad1 id=eq.2h1v.s5.b439b4fb4ac6 from=translated src=- shape=1e4632e5 vocab=491f661e
-/
theorem wt_add_of_even {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) : wt k + 4 = k ^ 2 := by
  unfold wt
  rw [ite_eq_left hk]
  have h2 : 2 ≤ k := by obtain ⟨j, rfl⟩ := hk; omega
  have h4 : 4 ≤ k ^ 2 := by nlinarith
  exact Nat.sub_add_cancel h4

/--
@isnad1 id=eq.1h1v.s5.b59642389e81 from=translated src=- shape=2a317266 vocab=491f661e
-/
theorem wt_add_of_odd {k : ℕ} (hk : ¬Even k) : wt k + 1 = k ^ 2 := by
  unfold wt
  rw [ite_eq_right hk]
  have h1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact absurd (h ▸ Even.zero) hk
    · exact h
  have : 1 ≤ k ^ 2 := Nat.one_le_pow _ _ h1
  exact Nat.sub_add_cancel this

/--
@isnad1 id=eq.0h0v.s3.8a015fc24c20 from=translated src=- shape=3c26ae4f vocab=8420f48d
-/
@[scoped simp] theorem wt_zero : wt 0 = 0 := by simp [wt]
/--
@isnad1 id=eq.0h0v.s3.f0b6362043fe from=translated src=- shape=3c26ae4f vocab=8420f48d
-/
@[scoped simp] theorem wt_one : wt 1 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s3.c619f187d466 from=translated src=- shape=3c26ae4f vocab=8420f48d
-/
@[scoped simp] theorem wt_two : wt 2 = 0 := by decide
/--
@isnad1 id=eq.0h0v.s3.3e69371546cb from=translated src=- shape=3c26ae4f vocab=8420f48d
-/
@[scoped simp] theorem wt_three : wt 3 = 8 := by decide
/--
@isnad1 id=eq.0h0v.s3.4263a6e68c2d from=translated src=- shape=3c26ae4f vocab=8420f48d
-/
@[scoped simp] theorem wt_four : wt 4 = 12 := by decide

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h6v.s7.cfa7240e775c from=translated src=- shape=247665e4 vocab=f9db2273
-/
theorem preNormEDS'_smul (b c d μ : R) (n : ℕ) :
    preNormEDS' (μ ^ 12 * b) (μ ^ 8 * c) (μ ^ 12 * d) n = μ ^ wt n * preNormEDS' b c d n := by
  induction n using normEDSRec' with
  | zero => simp
  | one => simp
  | two => simp
  | three => simp [preNormEDS'_three]
  | four => simp [preNormEDS'_four]
  | even m ih =>
    have h1 := ih (m + 1) (by omega)
    have h2 := ih (m + 2) (by omega)
    have h3 := ih (m + 3) (by omega)
    have h4 := ih (m + 4) (by omega)
    have h5 := ih (m + 5) (by omega)
    rw [preNormEDS'_even, preNormEDS'_even, h1, h2, h3, h4, h5]

    set N := wt (2 * (m + 3)) with hN
    have hNe : N + 4 = (2 * (m + 3)) ^ 2 := wt_add_of_even (even_two_mul _) (by omega)
    rcases Nat.even_or_odd m with hm | hm
    · have p1 : ¬Even (m + 1) := by simpa [Nat.even_add_one] using hm
      have p2 : Even (m + 2) := hm.add even_two
      have p3 : ¬Even (m + 3) := by
        have : Even (m + 2) := p2; simpa [Nat.even_add_one] using this
      have p4 : Even (m + 4) := hm.add (by decide)
      have p5 : ¬Even (m + 5) := by
        have : Even (m + 4) := p4; simpa [Nat.even_add_one] using this
      have e1 := wt_add_of_odd p1
      have e2 := wt_add_of_even p2 (by omega)
      have e3 := wt_add_of_odd p3
      have e4 := wt_add_of_even p4 (by omega)
      have e5 := wt_add_of_odd p5
      have E1 : 2 * wt (m + 2) + wt (m + 3) + wt (m + 5) = N := by
        zify at e1 e2 e3 e4 e5 hNe ⊢; linear_combination 2 * e2 + e3 + e5 - hNe
      have E2 : wt (m + 1) + wt (m + 3) + 2 * wt (m + 4) = N := by
        zify at e1 e2 e3 e4 e5 hNe ⊢; linear_combination e1 + e3 + 2 * e4 - hNe
      have hX : (μ ^ wt (m + 2) * preNormEDS' b c d (m + 2)) ^ 2 *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) *
          (μ ^ wt (m + 5) * preNormEDS' b c d (m + 5)) =
          μ ^ N * (preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) *
            preNormEDS' b c d (m + 5)) := by
        rw [← E1]; ring
      have hY : μ ^ wt (m + 1) * preNormEDS' b c d (m + 1) *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) *
          (μ ^ wt (m + 4) * preNormEDS' b c d (m + 4)) ^ 2 =
          μ ^ N * (preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) *
            preNormEDS' b c d (m + 4) ^ 2) := by
        rw [← E2]; ring
      linear_combination hX - hY
    · have hm' : ¬Even m := Nat.not_even_iff_odd.mpr hm
      have p1 : Even (m + 1) := by simpa [Nat.even_add_one] using hm'
      have p2 : ¬Even (m + 2) := fun h => hm' ((Nat.even_add.mp h).mpr even_two)
      have p3 : Even (m + 3) := by
        have : ¬Even (m + 2) := p2; simpa [Nat.even_add_one] using this
      have p4 : ¬Even (m + 4) := fun h => hm' ((Nat.even_add.mp h).mpr (by decide))
      have p5 : Even (m + 5) := by
        have : ¬Even (m + 4) := p4; simpa [Nat.even_add_one] using this
      have e1 := wt_add_of_even p1 (by omega)
      have e2 := wt_add_of_odd p2
      have e3 := wt_add_of_even p3 (by omega)
      have e4 := wt_add_of_odd p4
      have e5 := wt_add_of_even p5 (by omega)
      have E1 : 2 * wt (m + 2) + wt (m + 3) + wt (m + 5) = N := by
        zify at e1 e2 e3 e4 e5 hNe ⊢; linear_combination 2 * e2 + e3 + e5 - hNe
      have E2 : wt (m + 1) + wt (m + 3) + 2 * wt (m + 4) = N := by
        zify at e1 e2 e3 e4 e5 hNe ⊢; linear_combination e1 + e3 + 2 * e4 - hNe
      have hX : (μ ^ wt (m + 2) * preNormEDS' b c d (m + 2)) ^ 2 *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) *
          (μ ^ wt (m + 5) * preNormEDS' b c d (m + 5)) =
          μ ^ N * (preNormEDS' b c d (m + 2) ^ 2 * preNormEDS' b c d (m + 3) *
            preNormEDS' b c d (m + 5)) := by
        rw [← E1]; ring
      have hY : μ ^ wt (m + 1) * preNormEDS' b c d (m + 1) *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) *
          (μ ^ wt (m + 4) * preNormEDS' b c d (m + 4)) ^ 2 =
          μ ^ N * (preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) *
            preNormEDS' b c d (m + 4) ^ 2) := by
        rw [← E2]; ring
      linear_combination hX - hY
  | odd m ih =>
    have h1 := ih (m + 1) (by omega)
    have h2 := ih (m + 2) (by omega)
    have h3 := ih (m + 3) (by omega)
    have h4 := ih (m + 4) (by omega)
    rw [preNormEDS'_odd, preNormEDS'_odd, h1, h2, h3, h4]
    set N := wt (2 * (m + 2) + 1) with hN
    have hNo : N + 1 = (2 * (m + 2) + 1) ^ 2 := wt_add_of_odd (Nat.not_even_iff_odd.mpr (odd_two_mul_add_one _))
    rcases Nat.even_or_odd m with hm | hm
    · have p1 : ¬Even (m + 1) := by simpa [Nat.even_add_one] using hm
      have p2 : Even (m + 2) := hm.add even_two
      have p3 : ¬Even (m + 3) := by
        have : Even (m + 2) := p2; simpa [Nat.even_add_one] using this
      have p4 : Even (m + 4) := hm.add (by decide)
      have e1 := wt_add_of_odd p1
      have e2 := wt_add_of_even p2 (by omega)
      have e3 := wt_add_of_odd p3
      have e4 := wt_add_of_even p4 (by omega)
      simp only [ite_eq_left hm]
      have E1 : wt (m + 4) + 3 * wt (m + 2) + 12 = N := by
        zify at e1 e2 e3 e4 hNo ⊢; linear_combination e4 + 3 * e2 - hNo
      have E2 : wt (m + 1) + 3 * wt (m + 3) = N := by
        zify at e1 e2 e3 e4 hNo ⊢; linear_combination e1 + 3 * e3 - hNo
      have hX : μ ^ wt (m + 4) * preNormEDS' b c d (m + 4) *
          (μ ^ wt (m + 2) * preNormEDS' b c d (m + 2)) ^ 3 * (μ ^ 12 * b) =
          μ ^ N * (preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * b) := by
        rw [← E1]; ring
      have hY : μ ^ wt (m + 1) * preNormEDS' b c d (m + 1) *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) ^ 3 * 1 =
          μ ^ N * (preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * 1) := by
        rw [← E2]; ring
      linear_combination hX - hY
    · have hm' : ¬Even m := Nat.not_even_iff_odd.mpr hm
      have p1 : Even (m + 1) := by simpa [Nat.even_add_one] using hm'
      have p2 : ¬Even (m + 2) := fun h => hm' ((Nat.even_add.mp h).mpr even_two)
      have p3 : Even (m + 3) := by
        have : ¬Even (m + 2) := p2; simpa [Nat.even_add_one] using this
      have p4 : ¬Even (m + 4) := fun h => hm' ((Nat.even_add.mp h).mpr (by decide))
      have e1 := wt_add_of_even p1 (by omega)
      have e2 := wt_add_of_odd p2
      have e3 := wt_add_of_even p3 (by omega)
      have e4 := wt_add_of_odd p4
      simp only [ite_eq_right hm']
      have E1 : wt (m + 4) + 3 * wt (m + 2) = N := by
        zify at e1 e2 e3 e4 hNo ⊢; linear_combination e4 + 3 * e2 - hNo
      have E2 : wt (m + 1) + 3 * wt (m + 3) + 12 = N := by
        zify at e1 e2 e3 e4 hNo ⊢; linear_combination e1 + 3 * e3 - hNo
      have hX : μ ^ wt (m + 4) * preNormEDS' b c d (m + 4) *
          (μ ^ wt (m + 2) * preNormEDS' b c d (m + 2)) ^ 3 * 1 =
          μ ^ N * (preNormEDS' b c d (m + 4) * preNormEDS' b c d (m + 2) ^ 3 * 1) := by
        rw [← E1]; ring
      have hY : μ ^ wt (m + 1) * preNormEDS' b c d (m + 1) *
          (μ ^ wt (m + 3) * preNormEDS' b c d (m + 3)) ^ 3 * (μ ^ 12 * b) =
          μ ^ N * (preNormEDS' b c d (m + 1) * preNormEDS' b c d (m + 3) ^ 3 * b) := by
        rw [← E2]; ring
      linear_combination hX - hY

end KatzTransport
open scoped _root_.P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange.KatzTransport

namespace KatzTransport

open Polynomial WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R)

/--
@isnad1 id=eq.0h4v.s7.e89ac6f1a1c5 from=translated src=- shape=be6cbe42 vocab=cfb172a8
-/
theorem eval_Ψ₂Sq_variableChange (x : R) :
    (C • W).Ψ₂Sq.eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ 6 * W.Ψ₂Sq.eval x := by
  simp only [WeierstrassCurve.Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆]
  ring

/--
@isnad1 id=eq.0h4v.s7.783cbca5805c from=translated src=- shape=be6cbe42 vocab=0942a42c
-/
theorem eval_Ψ₃_variableChange (x : R) :
    (C • W).Ψ₃.eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ 8 * W.Ψ₃.eval x := by
  simp only [WeierstrassCurve.Ψ₃, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat,
    WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈]
  ring

set_option maxHeartbeats 3200000 in
/--
@isnad1 id=eq.0h4v.s7.3dc6cd6c3066 from=translated src=- shape=be6cbe42 vocab=e5b12968
-/
theorem eval_preΨ₄_variableChange (x : R) :
    (C • W).preΨ₄.eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ 12 * W.preΨ₄.eval x := by
  simp only [WeierstrassCurve.preΨ₄, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    eval_ofNat, WeierstrassCurve.variableChange_b₂, WeierstrassCurve.variableChange_b₄,
    WeierstrassCurve.variableChange_b₆, WeierstrassCurve.variableChange_b₈]
  linear_combination (-(((C.u⁻¹ : Rˣ) : R) ^ 12) * (2 * x * C.r - C.r ^ 2)) * W.b_relation

/--
@isnad1 id=eq.0h5v.s7.96dd86438244 from=translated src=- shape=901c13a7 vocab=4ac2bade
-/
theorem eval_preΨ'_variableChange (n : ℕ) (x : R) :
    ((C • W).preΨ' n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ wt n * (W.preΨ' n).eval x := by
  rw [WeierstrassCurve.preΨ', WeierstrassCurve.preΨ', ← coe_evalRingHom, ← coe_evalRingHom,
    map_preNormEDS', map_preNormEDS', coe_evalRingHom, coe_evalRingHom, eval_pow, eval_pow,
    eval_Ψ₂Sq_variableChange, eval_Ψ₃_variableChange, eval_preΨ₄_variableChange, mul_pow,
    ← pow_mul, preNormEDS'_smul]

/--
@isnad1 id=eq.0h5v.s8.b58f1070a6fe from=translated src=- shape=23d20256 vocab=c1f34be3
-/
theorem eval_ΨSq_variableChange (n : ℕ) (x : R) :
    ((C • W).ΨSq n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (n ^ 2 - 1)) * (W.ΨSq n).eval x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [WeierstrassCurve.ΨSq_zero]
  rw [WeierstrassCurve.ΨSq_ofNat, WeierstrassCurve.ΨSq_ofNat, eval_mul, eval_mul, eval_pow, eval_pow,
    eval_preΨ'_variableChange]
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  split_ifs with he
  · rw [eval_Ψ₂Sq_variableChange]
    have e := wt_add_of_even he (by omega)
    have E : 2 * (n ^ 2 - 1) = 2 * wt n + 6 := by zify [h1] at e ⊢; linear_combination -2 * e
    rw [E, pow_add, pow_mul]; ring
  · rw [eval_one, eval_one]
    have e := wt_add_of_odd he
    have E : 2 * (n ^ 2 - 1) = 2 * wt n := by zify [h1] at e ⊢; linear_combination -2 * e
    rw [E, pow_mul]; ring

end KatzTransport
open scoped _root_.P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange.KatzTransport

namespace KatzTransport

open Polynomial

/--
@isnad1 id=eq.0h5v.s8.9c98ddf69511 from=translated src=- shape=ca5818b9 vocab=31185d74
-/
theorem eval_PsiSq_vc {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).ΨSq n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (n.natAbs ^ 2 - 1)) * (W.ΨSq n).eval x := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.natAbs_natCast, eval_ΨSq_variableChange]
  · rw [WeierstrassCurve.ΨSq_neg, WeierstrassCurve.ΨSq_neg, Int.natAbs_neg, Int.natAbs_natCast,
      eval_ΨSq_variableChange]

end KatzTransport
open scoped _root_.P2MW.S_WeierstrassCurve_eval_PsiSq_variableChange.KatzTransport

/--
@isnad1 id=eq.0h5v.s8.9c98ddf69511 from=translated src=- shape=ca5818b9 vocab=31185d74
-/
theorem solution {R : Type*} [CommRing R]
    (W : WeierstrassCurve R) (C : WeierstrassCurve.VariableChange R) (n : ℤ) (x : R) :
    ((C • W).ΨSq n).eval (((C.u⁻¹ : Rˣ) : R) ^ 2 * (x - C.r)) =
      ((C.u⁻¹ : Rˣ) : R) ^ (2 * (n.natAbs ^ 2 - 1)) * (W.ΨSq n).eval x :=
  KatzTransport.eval_PsiSq_vc W C n x
