import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Residual
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_ComplexConjugation
import Tengoku.FltAnthropic.Definitions.Def_Deformations_MatrixRepresentation
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_ModThreeCyclotomic
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_det_map_comp_lift_eq_chiNegThree_of_isFrobeniusAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_det_map_comp_lift_eq_chiNegThree_of_isFrobeniusAt

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace B4Proof

theorem eq_one_or_eq_neg_one_of_isUnit (u : ℤ√(-2)) (hu : IsUnit u) : u = 1 ∨ u = -1 := by
  have hn : u.norm = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) u).mpr hu
  rw [Zsqrtd.norm_def] at hn
  have hre := mul_self_nonneg u.re
  have him := mul_self_nonneg u.im
  have him0 : u.im * u.im = 0 := by nlinarith
  have hre1 : u.re * u.re = 1 := by nlinarith
  rcases mul_self_eq_one_iff.mp hre1 with h | h
  · left; ext <;> simp [mul_self_eq_zero.mp him0, h]
  · right; ext <;> simp [mul_self_eq_zero.mp him0, h]

/--
@isnad1 id=eq.1h2v.s11.802b5a049195 from=translated src=- shape=8edf9b4b vocab=1c2cc1ce
-/
theorem red_mapMatrix (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (g : GL (Fin 2) (ZMod 3)) :
    red.mapMatrix ((Ψ g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  have := congrArg (fun x : GL (Fin 2) (ZMod 3) => (x : Matrix (Fin 2) (Fin 2) (ZMod 3))) (hΨ g)
  simpa using this

section Val

variable {L : Type*} [Field L] (A : ValuationSubring L)

/--
@isnad1 id=mem.1h3v.s6.8e4c3ea38ede from=translated src=- shape=e13bc6d4 vocab=1e96c8e9
-/
theorem mem_of_pow_three {μ : L} (h : μ ^ 3 = 1) : μ ∈ A := by
  rcases A.mem_or_inv_mem μ with hμ | hμ
  · exact hμ
  · have hinv : μ⁻¹ = μ ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h)
    rw [hinv] at hμ
    have h4 : μ = (μ ^ 2) ^ 2 := by
      rw [← pow_mul]
      norm_num
      rw [pow_succ, h, one_mul]
    rw [h4]
    exact pow_mem hμ 2

theorem eq_of_pow_three {μ ν : L} (hμ : μ ^ 3 = 1) (hν : ν ^ 3 = 1) (hcong : A.valuation (μ - ν) < 1)
    (h3 : ¬ A.valuation 3 < 1) : μ = ν := by
  by_contra hne
  have hq : μ ^ 2 + μ * ν + ν ^ 2 = 0 := by
    have h0 : (μ - ν) * (μ ^ 2 + μ * ν + ν ^ 2) = 0 := by linear_combination hμ - hν
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
  have hid : (3 : L) = μ * (μ - ν) * (2 * μ + ν) := by linear_combination (-3) * hμ + μ * hq
  apply h3
  rw [hid, Valuation.map_mul, Valuation.map_mul]
  have h1 : A.valuation μ ≤ 1 := (A.valuation_le_one_iff μ).mpr (mem_of_pow_three A hμ)
  have h2 : A.valuation (2 * μ + ν) ≤ 1 := by
    refine (A.valuation_le_one_iff _).mpr (add_mem (mul_mem ?_ (mem_of_pow_three A hμ)) (mem_of_pow_three A hν))
    exact_mod_cast natCast_mem A 2
  calc A.valuation μ * A.valuation (μ - ν) * A.valuation (2 * μ + ν)
      ≤ 1 * A.valuation (μ - ν) * 1 := mul_le_mul' (mul_le_mul' h1 le_rfl) h2
    _ = A.valuation (μ - ν) := by rw [one_mul, mul_one]
    _ < 1 := hcong

/--
@isnad1 id=not.3h3v.s8.773a3789eb71 from=translated src=- shape=6ddc1937 vocab=bce9d801
-/
theorem not_valuation_three_lt_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpA : A.valuation (p : L) < 1) : ¬ A.valuation 3 < 1 := by
  intro h3
  have hcop : IsCoprime ((3 : ℕ) : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (by norm_num) hp).mpr hp3.symm)
  obtain ⟨a, b, hab⟩ := hcop
  have habL : (a : L) * 3 + (b : L) * p = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → L) hab
  have hva : ∀ z : ℤ, A.valuation (z : L) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hlt : A.valuation ((a : L) * 3 + (b : L) * p) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_mul' (hva a) le_rfl) (by rwa [one_mul])
    · rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_mul' (hva b) le_rfl) (by rwa [one_mul])
  rw [habL, Valuation.map_one] at hlt
  exact lt_irrefl _ hlt

end Val

/--
@isnad1 id=eq.5h4v.s8.758a4b1e3ed4 from=translated src=- shape=d6a499b2 vocab=992eb244
-/
theorem frob_apply_eq_pow {A : ValuationSubring (AlgebraicClosure ℚ)} {σ : Γℚ} {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hA : A.LiesOverPrime p) (hσ : A.IsFrobeniusAt σ p) {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ 3 = 1) :
    σ ζ = ζ ^ p := by
  have hζA : ζ ∈ A := mem_of_pow_three A hζ
  set a : A := ⟨ζ, hζA⟩ with ha
  have hres := hσ.smul_residue_eq (IsLocalRing.residue A a)
  rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow] at hres
  have hmem : (⟨σ, hσ.mem_decompositionSubgroup⟩ : A.decompositionSubgroup ℚ) • a - a ^ p ∈
      IsLocalRing.maximalIdeal A :=
    Ideal.Quotient.eq.mp hres
  have hval : A.valuation (σ ζ - ζ ^ p) < 1 := (A.valuation_lt_one_iff _).mp hmem
  have hpval : A.valuation (p : AlgebraicClosure ℚ) < 1 := A.mem_nonunits_iff.mp hA
  refine eq_of_pow_three A ?_ ?_ hval (not_valuation_three_lt_one A hp hp3 hpval)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

end B4Proof

/--
@isnad1 id=eq.6h6v.s13.276eadf1f442 from=translated src=- shape=a7f8dc3c vocab=00fc7c6d
-/
theorem solution
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (ι : ℤ√(-2) →+* ℂ)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    (((Matrix.GeneralLinearGroup.map (n := Fin 2) ι).comp (Ψ.comp ρ) σ : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ).det = ((chiNegThree p : ℤ) : ℂ) := by

  have hchar : ((modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3) = (p : ZMod 3) := by
    rw [modThreeCyclotomicChar_apply]
    refine (modularCyclotomicCharacter.unique (AlgebraicClosure ℚ)
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 3)
      (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (c := (p : ZMod 3)) fun t ht => ?_).symm
    have ht3 : ((t : AlgebraicClosure ℚ)) ^ 3 = 1 := by
      have := (mem_rootsOfUnity _ _).mp ht
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    rw [ZMod.val_natCast]
    show σ (t : AlgebraicClosure ℚ) = (t : AlgebraicClosure ℚ) ^ (p % 3)
    rw [B4Proof.frob_apply_eq_pow hp hp3 hA hσ ht3]
    conv_lhs => rw [← Nat.mod_add_div p 3, pow_add, pow_mul, ht3, one_pow, mul_one]

  have hdetρ : (((ρ σ : GL (Fin 2) (ZMod 3))) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = (p : ZMod 3) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, hchar]

  have hunit : IsUnit (((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have hred : red (((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det = (p : ZMod 3) := by
    rw [RingHom.map_det, B4Proof.red_mapMatrix Ψ hΨ, hdetρ]

  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have hcoe : (((Matrix.GeneralLinearGroup.map (n := Fin 2) ι) (Ψ (ρ σ)) : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ι.mapMatrix ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) := rfl
  rw [hcoe, ← RingHom.map_det]
  have hp3' : p % 3 = 1 ∨ p % 3 = 2 := by
    have h0 : p % 3 ≠ 0 := fun h0 =>
      hp3 ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    have := Nat.mod_lt p (by norm_num : 3 > 0)
    omega
  rcases hp3' with h1 | h2
  · have hpz : (p : ZMod 3) = 1 := by
      rw [← ZMod.natCast_mod, h1, Nat.cast_one]
    rw [hpz] at hred
    have hd : (((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det = 1 := by
      rcases B4Proof.eq_one_or_eq_neg_one_of_isUnit _ hunit with h | h
      · exact h
      · exfalso
        rw [h, map_neg, map_one] at hred
        exact absurd hred (by decide)
    rw [hd, map_one]
    simp [chiNegThree, h1]
  · have hpz : (p : ZMod 3) = -1 := by
      rw [← ZMod.natCast_mod, h2]
      decide
    rw [hpz] at hred
    have hd : (((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)))).det = -1 := by
      rcases B4Proof.eq_one_or_eq_neg_one_of_isUnit _ hunit with h | h
      · exfalso
        rw [h, map_one] at hred
        exact absurd hred (by decide)
      · exact h
    rw [hd, map_neg, map_one]
    simp [chiNegThree, h2]
