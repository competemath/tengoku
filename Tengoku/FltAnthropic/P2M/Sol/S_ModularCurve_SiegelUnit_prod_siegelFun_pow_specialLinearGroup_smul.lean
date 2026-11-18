import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SiegelFunction
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_siegelFun_specialLinearGroup_smul
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_SiegelUnit_prod_siegelFun_pow_specialLinearGroup_smul

set_option autoImplicit false

open ModularCurve

namespace SiegelTransport

open Complex

variable (N : ℕ) [NeZero N]

/--
@isnad1 id=ne.0h1v.s4.f60c7fd6440e from=translated src=- shape=07b313d4 vocab=5536c8a9
-/
theorem natCast_ne_zero : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N

noncomputable def dS (r : ℤ) : ℂ := Complex.exp (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ))

noncomputable def dR (s : ℤ) : ℂ := -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ)))

/--
@isnad1 id=ne.0h2v.s4.f985265a9b7c from=translated src=- shape=cc1e0f2d vocab=970e6c26
-/
theorem dS_ne_zero (r : ℤ) : dS N r ≠ 0 := Complex.exp_ne_zero _

/--
@isnad1 id=ne.0h2v.s4.503622332b06 from=translated src=- shape=cc1e0f2d vocab=25830ccf
-/
theorem dR_ne_zero (s : ℤ) : dR N s ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)

/--
@isnad1 id=eq.0h2v.s5.48a13a730385 from=translated src=- shape=d9d32544 vocab=123a7ac1
-/
theorem dS_pow (r : ℤ) : dS N r ^ (2 * N) = 1 := by
  rw [dS, ← Complex.exp_nat_mul]
  have h : ((2 * N : ℕ) : ℂ) * (Real.pi * Complex.I * ((r : ℂ) - (N : ℂ)) / (N : ℂ)) =
      ((r - N : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hN := natCast_ne_zero N
    push_cast
    field_simp
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I _

/--
@isnad1 id=eq.0h2v.s5.3b170d5e350f from=translated src=- shape=d9d32544 vocab=9dd21997
-/
theorem dR_pow (s : ℤ) : dR N s ^ (2 * N) = 1 := by
  rw [dR, neg_pow, show (-1 : ℂ) ^ (2 * N) = 1 from (even_two_mul N).neg_one_pow, one_mul, ← Complex.exp_nat_mul]
  have h : ((2 * N : ℕ) : ℂ) * (-(Real.pi * Complex.I * (s : ℂ) / (N : ℂ))) = ((-s : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hN := natCast_ne_zero N
    push_cast
    field_simp
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I _

/--
@isnad1 id=eq.0h5v.s6.701932c1f14b from=translated src=- shape=5abbd8a2 vocab=da14ed27
-/
theorem siegelFun_add_nat_mul_snd (r s : ℤ) (z : ℂ) :
    ∀ k : ℕ, siegelFun N r (s + k * N) z = dS N r ^ k * siegelFun N r s z
  | 0 => by simp
  | k + 1 => by
      have h := (ModularCurve.SiegelUnit.siegelFun_add_level N r (s + k * N)).1 z
      rw [show s + ((k + 1 : ℕ) : ℤ) * N = s + k * N + N by push_cast; ring, h,
        siegelFun_add_nat_mul_snd r s z k, pow_succ, dS]
      ring

/--
@isnad1 id=eq.0h5v.s6.46819d0eff0c from=translated src=- shape=a2b78cb0 vocab=da14ed27
-/
theorem siegelFun_add_int_mul_snd (r s : ℤ) (z : ℂ) (k : ℤ) :
    siegelFun N r (s + k * N) z = dS N r ^ k * siegelFun N r s z := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]; exact siegelFun_add_nat_mul_snd N r s z n
  · have h := siegelFun_add_nat_mul_snd N r (s + -(n : ℤ) * N) z n
    rw [show s + -(n : ℤ) * N + (n : ℤ) * N = s by ring] at h
    rw [zpow_neg, zpow_natCast, h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (dS_ne_zero N r)), one_mul]

/--
@isnad1 id=eq.0h5v.s6.9d74ff7a3f41 from=translated src=- shape=73c9cf12 vocab=27400dc3
-/
theorem siegelFun_add_nat_mul_fst (r s : ℤ) (τ : UpperHalfPlane) :
    ∀ k : ℕ, siegelFun N (r + k * N) s (τ : ℂ) = dR N s ^ k * siegelFun N r s (τ : ℂ)
  | 0 => by simp
  | k + 1 => by
      have h := (ModularCurve.SiegelUnit.siegelFun_add_level N (r + k * N) s).2 τ
      rw [show r + ((k + 1 : ℕ) : ℤ) * N = r + k * N + N by push_cast; ring, h,
        siegelFun_add_nat_mul_fst r s τ k, pow_succ, dR]
      ring

/--
@isnad1 id=eq.0h5v.s6.82efe0c80638 from=translated src=- shape=3464e2ac vocab=27400dc3
-/
theorem siegelFun_add_int_mul_fst (r s : ℤ) (τ : UpperHalfPlane) (k : ℤ) :
    siegelFun N (r + k * N) s (τ : ℂ) = dR N s ^ k * siegelFun N r s (τ : ℂ) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]; exact siegelFun_add_nat_mul_fst N r s τ n
  · have h := siegelFun_add_nat_mul_fst N (r + -(n : ℤ) * N) s τ n
    rw [show r + -(n : ℤ) * N + (n : ℤ) * N = r by ring] at h
    rw [zpow_neg, zpow_natCast, h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (dR_ne_zero N s)), one_mul]

/--
@isnad1 id=eq.0h2v.s5.e694286187a1 from=translated src=- shape=21c78f44 vocab=39e8a620
-/
theorem intCast_zmod_val (a : ℤ) : (((a : ZMod N).val : ℕ) : ℤ) = a % N := ZMod.val_intCast a

/--
@isnad1 id=ex.0h4v.s6.3607ab8ca64f from=translated src=- shape=c3512c02 vocab=dd3d0c83
-/
theorem exists_siegelFun_eq_mul_reduced (a b : ℤ) (τ : UpperHalfPlane) :
    ∃ ζ : ℂ, ζ ^ (2 * N) = 1 ∧
      siegelFun N a b (τ : ℂ) = ζ * siegelFun N (((a : ZMod N).val : ℕ) : ℤ) (((b : ZMod N).val : ℕ) : ℤ) (τ : ℂ) := by
  set a' : ℤ := (((a : ZMod N).val : ℕ) : ℤ) with ha'
  set b' : ℤ := (((b : ZMod N).val : ℕ) : ℤ) with hb'
  have ha : a = a' + (a / N) * N := by rw [ha', intCast_zmod_val, mul_comm]; exact (Int.emod_add_mul_ediv a N).symm
  have hb : b = b' + (b / N) * N := by rw [hb', intCast_zmod_val, mul_comm]; exact (Int.emod_add_mul_ediv b N).symm
  have h1 : siegelFun N a b (τ : ℂ) = dS N a ^ (b / N) * siegelFun N a b' (τ : ℂ) := by
    conv_lhs => rw [hb]
    exact siegelFun_add_int_mul_snd N a b' (τ : ℂ) (b / N)
  have h2 : siegelFun N a b' (τ : ℂ) = dR N b' ^ (a / N) * siegelFun N a' b' (τ : ℂ) := by
    conv_lhs => rw [ha]
    exact siegelFun_add_int_mul_fst N a' b' τ (a / N)
  refine ⟨dS N a ^ (b / N) * dR N b' ^ (a / N), ?_, ?_⟩
  · rw [mul_pow, ← zpow_natCast, ← zpow_natCast (dR N b' ^ (a / N)), ← zpow_mul, ← zpow_mul, mul_comm (b / N),
      mul_comm (a / N), zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, dS_pow, dR_pow, one_zpow, one_zpow, mul_one]
  · rw [h1, h2]
    ring

/--
@isnad1 id=eq.2h4v.s7.2382b13a3e76 from=translated src=- shape=b7ad7c12 vocab=9e4840bf
-/
theorem pow_twelve_mul_eq_one {μ ζ : ℂ} (hμ : μ ^ 12 = 1) (hζ : ζ ^ (2 * N) = 1) (m : ℕ) :
    (μ * ζ) ^ (12 * N * m) = 1 := by
  rw [mul_pow, show 12 * N * m = 12 * (N * m) by ring, pow_mul, hμ, one_pow, one_mul,
    show 12 * (N * m) = (2 * N) * (6 * m) by ring, pow_mul, hζ, one_pow]

end SiegelTransport

open SiegelTransport in
/--
@isnad1 id=and.0h2v.s10.d261ecfacd7e from=translated src=- shape=dcea81c3 vocab=dec110da
-/
theorem solution (N : ℕ) [NeZero N]
    (e : ZMod N → ZMod N → ℕ) :
    (∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s)) ∧
    ((∀ r s : ZMod N, e r (s + r) = e r s) →
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s)) := by
  classical

  have h1 : ∀ (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane),
      (∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N (r.val : ℤ) (s.val : ℤ) ((β • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
        ∏ r : ZMod N, ∏ s : ZMod N,
          siegelFun N
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
              ((((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
                  (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
              (τ : ℂ) ^ (12 * N * e r s) := by
    intro β τ
    obtain ⟨μ, hμ, hK⟩ := ModularCurve.siegelFun_specialLinearGroup_smul N β
    refine Finset.prod_congr rfl fun r _ => Finset.prod_congr rfl fun s _ => ?_
    obtain ⟨ζ, hζ, hred⟩ := exists_siegelFun_eq_mul_reduced N
      ((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
      ((r.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 0 1 + (s.val : ℤ) * (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1) τ
    rw [hK, hred, ← mul_assoc, mul_pow, pow_twelve_mul_eq_one N hμ hζ, one_mul]
  refine ⟨h1, ?_⟩

  intro he γ hγ τ
  rw [h1 γ τ]
  rw [CongruenceSubgroup.Gamma1_mem] at hγ
  obtain ⟨h00, h11, h10⟩ := hγ
  set b : ZMod N := ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod N) with hb

  have he' : ∀ (r s : ZMod N) (k : ℕ), e r (s + k • r) = e r s := by
    intro r s k
    induction k with
    | zero => rw [zero_smul, add_zero]
    | succ k ih => rw [succ_nsmul, ← add_assoc, he, ih]
  have heb : ∀ r s : ZMod N, e r (s + r * b) = e r s := by
    intro r s
    rw [show r * b = b.val • r by rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]]
    exact he' r s b.val
  refine Finset.prod_congr rfl fun r _ => ?_

  have hidx1 : ∀ s : ZMod N,
      ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
          (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N)) = r := by
    intro s
    push_cast
    rw [h00, h10, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_one, mul_zero, add_zero]
  have hidx2 : ∀ s : ZMod N,
      ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
          (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N)) = s + r * b := by
    intro s
    push_cast
    rw [h11, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_one, hb, add_comm]
  have hterm : ∀ s : ZMod N,
      siegelFun N
          ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
              (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N).val : ℤ)
          ((((r.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
              (s.val : ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N).val : ℤ)
          (τ : ℂ) ^ (12 * N * e r s) =
        siegelFun N (r.val : ℤ) ((s + r * b).val : ℤ) (τ : ℂ) ^ (12 * N * e r (s + r * b)) := by
    intro s
    rw [hidx1 s, hidx2 s, heb r s]
  rw [Finset.prod_congr rfl (fun s _ => hterm s)]
  exact Fintype.prod_equiv (Equiv.addRight (r * b)) _ _ (fun s => rfl)
