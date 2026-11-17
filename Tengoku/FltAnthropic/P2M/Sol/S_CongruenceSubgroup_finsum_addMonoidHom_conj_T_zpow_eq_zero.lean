import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CongruenceSubgroup_finsum_addMonoidHom_conj_T_zpow_eq_zero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CongruenceSubgroup_finsum_addMonoidHom_conj_T_zpow_eq_zero

set_option autoImplicit false

open scoped MatrixGroups

namespace A2TRF

open CongruenceSubgroup Matrix.SpecialLinearGroup ModularGroup

section Abelianisation

variable {A : Type*} [AddCommGroup A] [IsAddTorsionFree A]

/--
@isnad1 id=eq.0h0v.s7.788b3cb52685 from=translated src=- shape=be816c72 vocab=dfc9fd34
-/
theorem S_pow_four : (S : SL(2, ℤ)) ^ 4 = 1 := by
  refine Subtype.ext ?_
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow,
    pow_two, S_mul_S_eq]
  simp

/--
@isnad1 id=eq.0h0v.s8.f26f42acbc01 from=translated src=- shape=5cc1983f vocab=9a2d3578
-/
theorem S_mul_T_pow_six : ((S : SL(2, ℤ)) * T) ^ 6 = 1 := by
  have h3 : ((S : SL(2, ℤ)) * T) ^ 3 = -1 := by
    refine Subtype.ext ?_
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul, coe_S, coe_T,
      Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
    rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, pow_add, pow_add, pow_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, h3]
  simp

/--
@isnad1 id=eq.0h2v.s9.14376410e634 from=translated src=- shape=c8d7173f vocab=2b7f54bd
-/
theorem addMonoidHom_SL2Z_eq_zero (ψ : Additive SL(2, ℤ) →+ A) : ψ = 0 := by
  have hS : ψ (Additive.ofMul S) = 0 := by
    have h : (4 : ℕ) • ψ (Additive.ofMul S) = 0 := by
      rw [← map_nsmul, ← ofMul_pow, S_pow_four, ofMul_one, map_zero]
    exact (nsmul_eq_zero_iff_right (by norm_num)).mp h
  have hT : ψ (Additive.ofMul T) = 0 := by
    have h : (6 : ℕ) • (ψ (Additive.ofMul S) + ψ (Additive.ofMul T)) = 0 := by
      rw [← map_add, ← ofMul_mul, ← map_nsmul, ← ofMul_pow, S_mul_T_pow_six, ofMul_one, map_zero]
    have h' := (nsmul_eq_zero_iff_right (by norm_num)).mp h
    rwa [hS, zero_add] at h'

  have hker : ∀ g : SL(2, ℤ), ψ (Additive.ofMul g) = 0 := by
    intro g
    have hg : g ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
      rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact hS
      · rw [Set.mem_singleton_iff] at hx; subst hx; exact hT
    | one => rw [ofMul_one, map_zero]
    | mul x y _ _ hx hy => rw [ofMul_mul, map_add, hx, hy, add_zero]
    | inv x _ hx => rw [ofMul_inv, map_neg, hx, neg_zero]
  ext g
  exact hker (Additive.toMul g)

end Abelianisation

section Transfer

variable (N : ℕ)

/--
@isnad1 id=mem.0h1v.s8.76563c9d2d3a from=translated src=- shape=9649aa7a vocab=796294be
-/
theorem T_zpow_mem_Gamma : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
  have h : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
    ModularGroup.coe_T_zpow _
  rw [Gamma_mem, h]
  simp

/--
@isnad1 id=mem.0h2v.s9.09ba79674489 from=translated src=- shape=ae12abfc vocab=19dce87c
-/
theorem conj_T_zpow_mem_Gamma0 (σ : SL(2, ℤ)) : σ⁻¹ * ModularGroup.T ^ (N : ℤ) * σ ∈ Gamma0 N := by
  have h : σ⁻¹ * ModularGroup.T ^ (N : ℤ) * σ⁻¹⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem _ (T_zpow_mem_Gamma N) σ⁻¹
  rw [inv_inv, Gamma_mem] at h
  rw [Gamma0_mem]
  exact h.2.2.1

/--
@isnad1 id=eq.0h2v.s10.eac457279414 from=translated src=- shape=c30ca3d9 vocab=4ed5bc16
-/
theorem T_zpow_smul_eq (q : SL(2, ℤ) ⧸ Gamma0 N) : (ModularGroup.T ^ (N : ℤ)) • q = q := by
  induction q using QuotientGroup.induction_on with
  | H σ =>
    change (QuotientGroup.mk (ModularGroup.T ^ (N : ℤ) * σ) : SL(2, ℤ) ⧸ Gamma0 N) = QuotientGroup.mk σ
    rw [QuotientGroup.eq]
    have : (ModularGroup.T ^ (N : ℤ) * σ)⁻¹ * σ = (σ⁻¹ * ModularGroup.T ^ (N : ℤ) * σ)⁻¹ := by group
    rw [this]
    exact Subgroup.inv_mem _ (conj_T_zpow_mem_Gamma0 N σ)

variable [NeZero N]

/--
@isnad1 id=eq.1h4v.s13.4354f7fd40df from=translated src=- shape=0b4d908c vocab=d2957cce
-/
theorem main {A : Type*} [AddCommGroup A] [IsAddTorsionFree A] (φ : Additive ↥(Gamma0 N) →+ A)
    (u : SL(2, ℤ) ⧸ Gamma0 N → ↥(Gamma0 N))
    (hu : ∀ q : SL(2, ℤ) ⧸ Gamma0 N, ((u q : ↥(Gamma0 N)) : SL(2, ℤ)) = q.out⁻¹ * ModularGroup.T ^ (N : ℤ) * q.out) :
    ∑ᶠ q : SL(2, ℤ) ⧸ Gamma0 N, φ (Additive.ofMul (u q)) = 0 := by
  letI := (Gamma0 N).fintypeQuotientOfFiniteIndex
  have hψ := addMonoidHom_SL2Z_eq_zero (HeckeEis.coresHom (Gamma0 N) φ)
  have h1 := HeckeEis.coresHom_apply (Gamma0 N) φ (ModularGroup.T ^ (N : ℤ))
  have h2 : ∀ q : SL(2, ℤ) ⧸ Gamma0 N, HeckeEis.transferAux (Gamma0 N) (ModularGroup.T ^ (N : ℤ)) q = u q := by
    intro q
    apply Subtype.ext
    rw [HeckeEis.coe_transferAux, T_zpow_smul_eq, hu, mul_assoc]
  rw [finsum_eq_sum_of_fintype]
  calc ∑ q : SL(2, ℤ) ⧸ Gamma0 N, φ (Additive.ofMul (u q))
      = ∑ q : SL(2, ℤ) ⧸ Gamma0 N, φ (Additive.ofMul (HeckeEis.transferAux (Gamma0 N) (ModularGroup.T ^ (N : ℤ)) q)) :=
          Finset.sum_congr rfl fun q _ => by rw [h2]
    _ = HeckeEis.coresHom (Gamma0 N) φ (Additive.ofMul (ModularGroup.T ^ (N : ℤ))) := h1.symm
    _ = 0 := by rw [hψ]; rfl

end Transfer

end A2TRF

/--
@isnad1 id=eq.1h4v.s13.4354f7fd40df from=translated src=- shape=0b4d908c vocab=d2957cce
-/
theorem solution (N : ℕ) [NeZero N] {A : Type*} [AddCommGroup A]
    [IsAddTorsionFree A] (φ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A)
    (u : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N → ↥(CongruenceSubgroup.Gamma0 N))
    (hu : ∀ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N,
      ((u q : ↥(CongruenceSubgroup.Gamma0 N)) : SL(2, ℤ)) = q.out⁻¹ * ModularGroup.T ^ (N : ℤ) * q.out) :
    ∑ᶠ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, φ (Additive.ofMul (u q)) = 0 :=
  A2TRF.main N φ u hu
