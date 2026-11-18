import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_siegelFun_add_level.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_siegelFun_add_level

set_option autoImplicit false

open ModularCurve

noncomputable section

open Complex
open scoped Real

namespace SiegelPerE96

def qq (τ : ℂ) : ℂ := cexp (2 * π * I * τ)

def qa (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ := cexp (2 * π * I * ((r : ℂ) * τ + (s : ℂ)) / (N : ℂ))

def pref (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  -cexp (π * I * (s : ℂ) * ((r : ℂ) - (N : ℂ)) / (N : ℂ) ^ 2) *
    cexp (π * I * (((r : ℂ) / (N : ℂ)) ^ 2 - (r : ℂ) / (N : ℂ) + 1 / 6) * τ)

def sprod (N : ℕ) (r s : ℤ) (τ : ℂ) : ℂ :=
  (1 - qa N r s τ) * ∏' n : ℕ, ((1 - qq τ ^ (n + 1) * qa N r s τ) *
    (1 - qq τ ^ (n + 1) * (qa N r s τ)⁻¹))

/--
@isnad1 id=eq.0h4v.s5.17cf1395fe06 from=translated src=- shape=6b4addea vocab=4c2e7b79
-/
theorem siegelFun_eq (N : ℕ) (r s : ℤ) (τ : ℂ) :
    ModularCurve.siegelFun N r s τ = pref N r s τ * sprod N r s τ := by
  unfold ModularCurve.siegelFun pref sprod qq qa; simp only [mul_assoc]

/--
@isnad1 id=eq.0h3v.s4.152aee1f1c10 from=translated src=- shape=e59f7ef4 vocab=51dfd744
-/
theorem siegelFun_level_zero (r s : ℤ) (τ : ℂ) : ModularCurve.siegelFun 0 r s τ = 0 := by
  simp [ModularCurve.siegelFun]

/--
@isnad1 id=lt.1h1v.s4.a903b5544002 from=translated src=- shape=57faaa14 vocab=2cd68681
-/
theorem norm_qq_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖qq τ‖ < 1 := by
  unfold qq
  rw [Complex.norm_exp]
  have : (2 * π * I * τ).re = -(2 * π * τ.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [this, Real.exp_lt_one_iff]
  have := Real.pi_pos
  nlinarith

/--
@isnad1 id=ne.0h1v.s3.cf2fb1de0140 from=translated src=- shape=b14ee516 vocab=ae1329b0
-/
theorem qq_ne_zero (τ : ℂ) : qq τ ≠ 0 := Complex.exp_ne_zero _

/--
@isnad1 id=ne.0h4v.s4.37390b1b4ff4 from=translated src=- shape=d5cf3520 vocab=2f4bc774
-/
theorem qa_ne_zero (N : ℕ) (r s : ℤ) (τ : ℂ) : qa N r s τ ≠ 0 := Complex.exp_ne_zero _

/--
@isnad1 id=multipli.1h3v.s6.0f0a42d99f48 from=translated src=- shape=5e5b2675 vocab=b137e65d
-/
theorem multipliable_one_sub_pow_mul {q : ℂ} (hq : ‖q‖ < 1) (c : ℂ) (k : ℕ) :
    Multipliable fun n : ℕ => 1 - q ^ (n + k) * c := by
  have hs : Summable fun n : ℕ => ‖-(q ^ (n + k) * c)‖ := by
    simp only [norm_neg, norm_mul, norm_pow, pow_add]
    have := (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right (‖q‖ ^ k * ‖c‖)
    refine this.congr fun n => ?_
    ring
  simpa [sub_eq_add_neg] using multipliable_one_add_of_summable hs

/--
@isnad1 id=eq.1h4v.s5.a1311217c8a5 from=translated src=- shape=e0f2aa27 vocab=9024a728
-/
theorem qa_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N r (s + N) z = qa N r s z := by
  unfold qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [show 2 * (π : ℂ) * I * ((r : ℂ) * z + ((s : ℂ) + (N : ℂ))) / (N : ℂ)
      = 2 * π * I * ((r : ℂ) * z + (s : ℂ)) / (N : ℂ) + 2 * π * I by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/--
@isnad1 id=eq.1h4v.s6.98ee7d2a7709 from=translated src=- shape=46bc5b45 vocab=ce131231
-/
theorem pref_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N r (s + N) z = cexp (π * I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * pref N r s z := by
  unfold pref
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u : ℂ, cexp u * (-cexp x * cexp y) = -cexp (u + x) * cexp y from
    fun x y u => by rw [Complex.exp_add]; ring]
  congr 3
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.1h4v.s5.4364cfd4d361 from=translated src=- shape=e0f2aa27 vocab=1a789170
-/
theorem sprod_add_level (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    sprod N r (s + N) z = sprod N r s z := by
  unfold sprod
  simp only [qa_add_level N hN]

/--
@isnad1 id=eq.1h4v.s5.42418a839bcc from=translated src=- shape=6fa23a67 vocab=2b6052aa
-/
theorem qa_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    qa N (r + N) s z = qq z * qa N r s z := by
  unfold qa qq
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  push_cast
  rw [← Complex.exp_add]
  congr 1
  field_simp
  ring

/--
@isnad1 id=eq.1h4v.s6.c8a370fd6d44 from=translated src=- shape=f2bf2307 vocab=019b6bbb
-/
theorem pref_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) (z : ℂ) :
    pref N (r + N) s z = pref N r s z * (qa N r s z * cexp (-(π * I * (s : ℂ) / (N : ℂ)))) := by
  unfold pref qa
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  rw [show ∀ x y u v : ℂ, -cexp x * cexp y * (cexp u * cexp v) = -cexp (x + y + u + v) from
      fun x y u v => by rw [Complex.exp_add, Complex.exp_add, Complex.exp_add]; ring,
    show ∀ x y : ℂ, -cexp x * cexp y = -cexp (x + y) from fun x y => by rw [Complex.exp_add]; ring]
  congr 2
  push_cast
  field_simp
  ring

/--
@isnad1 id=eq.2h4v.s6.fcaa6ddb518e from=translated src=- shape=df14d033 vocab=d108fca2
-/
theorem sprod_add_level_left (N : ℕ) (hN : N ≠ 0) (r s : ℤ) {τ : ℂ} (hτ : 0 < τ.im) :
    sprod N (r + N) s τ = -(qa N r s τ)⁻¹ * sprod N r s τ := by
  have hq := norm_qq_lt_one hτ
  set q := qq τ with hqdef
  set w := qa N r s τ with hwdef
  have hq0 : q ≠ 0 := qq_ne_zero τ
  have hw0 : w ≠ 0 := qa_ne_zero N r s τ
  unfold sprod
  simp only [qa_add_level_left N hN, ← hqdef, ← hwdef]

  have ht : ∀ n : ℕ, (1 - q ^ (n + 1) * (q * w)) * (1 - q ^ (n + 1) * (q * w)⁻¹)
      = (1 - q ^ (n + 1 + 1) * w) * (1 - q ^ n * w⁻¹) := by
    intro n
    rw [mul_inv, pow_succ q (n + 1), pow_succ q n]
    field_simp
  rw [tprod_congr ht]

  have hA2 : Multipliable fun n : ℕ => 1 - q ^ (n + 1 + 1) * w := by
    simpa [add_assoc] using multipliable_one_sub_pow_mul hq w 2
  have hA1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w := multipliable_one_sub_pow_mul hq w 1
  have hB1 : Multipliable fun n : ℕ => 1 - q ^ (n + 1) * w⁻¹ := multipliable_one_sub_pow_mul hq w⁻¹ 1
  have hB0 : Multipliable fun n : ℕ => 1 - q ^ n * w⁻¹ := by
    simpa using multipliable_one_sub_pow_mul hq w⁻¹ 0

  rw [hA2.tprod_mul hB0, hA1.tprod_mul hB1,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ (n + 1) * w) hA2,
    tprod_eq_zero_mul' (f := fun n : ℕ => 1 - q ^ n * w⁻¹) hB1]
  simp only [zero_add, pow_one, pow_zero, one_mul]
  field_simp
  ring

end SiegelPerE96

open SiegelPerE96 in

/--
@isnad1 id=and.0h3v.s7.f35b595dcaa8 from=translated src=- shape=8d28570f vocab=ca4c1968
-/
theorem solution (N : ℕ) (r s : ℤ) :
    (∀ z : ℂ, siegelFun N r (s + N) z =
        Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) * siegelFun N r s z) ∧
    (∀ τ : UpperHalfPlane, siegelFun N (r + N) s (τ : ℂ) =
        -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) * siegelFun N r s (τ : ℂ)) := by
  rcases eq_or_ne N 0 with rfl | hN
  · refine ⟨fun z => ?_, fun τ => ?_⟩ <;> simp [SiegelPerE96.siegelFun_level_zero]
  refine ⟨fun z => ?_, fun τ => ?_⟩
  · rw [SiegelPerE96.siegelFun_eq, SiegelPerE96.siegelFun_eq, SiegelPerE96.pref_add_level N hN,
      SiegelPerE96.sprod_add_level N hN, mul_assoc]
  · rw [SiegelPerE96.siegelFun_eq, SiegelPerE96.siegelFun_eq, SiegelPerE96.pref_add_level_left N hN,
      SiegelPerE96.sprod_add_level_left N hN r s τ.2]
    have hw : SiegelPerE96.qa N r s (τ : ℂ) ≠ 0 := SiegelPerE96.qa_ne_zero N r s τ
    field_simp

end
