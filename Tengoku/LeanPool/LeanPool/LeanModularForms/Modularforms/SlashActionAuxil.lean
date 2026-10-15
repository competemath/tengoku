/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Tengoku

/-! # SlashActionAuxil -/

@[expose] public section

/-!
# Auxiliary theorems for the slash actions groups SL(2, ℤ) and Γ(2)

Define special generators S, T, -I (resp. α, β, -I) for SL(2,ℤ) (resp. Γ(2)) and prove that
they are indeed generators.
As a corollary, we only need to check the invariance under these special elements to check
the invariance under the whole group.
These theorems will be used to prove that 4-th powers of Jacobi theta functions Θ_2^4, Θ_3^4, Θ_4^4
are modular forms of weight 2 and level Γ(2).
-/

open scoped ModularForm MatrixGroups
open Matrix UpperHalfPlane CongruenceSubgroup ModularGroup

local notation "GL(" n ", " R ")" "⁺" => Matrix.GLPos (Fin n) R
local notation "Γ " n:100 => Gamma n

/-- The special-linear matrix underlying `α`. -/
def αMatrix : SL(2, ℤ) := ⟨!![1, 2; 0, 1], by simp⟩

/-- The generator `α = [[1, 2], [0, 1]]` of the congruence subgroup `Γ(2)`. -/
def α : Γ 2 := ⟨αMatrix, by
  rw [Gamma_mem]
  change ((1 : ℤ) : ZMod 2) = 1 ∧ ((2 : ℤ) : ZMod 2) = 0 ∧
    ((0 : ℤ) : ZMod 2) = 0 ∧ ((1 : ℤ) : ZMod 2) = 1
  decide⟩

/-- The special-linear matrix underlying `β`. -/
def βMatrix : SL(2, ℤ) := ⟨!![1, 0; 2, 1], by simp⟩

/-- The generator `β = [[1, 0], [2, 1]]` of the congruence subgroup `Γ(2)`. -/
def β : Γ 2 := ⟨βMatrix, by
  rw [Gamma_mem]
  change ((1 : ℤ) : ZMod 2) = 1 ∧ ((0 : ℤ) : ZMod 2) = 0 ∧
    ((2 : ℤ) : ZMod 2) = 0 ∧ ((1 : ℤ) : ZMod 2) = 1
  decide⟩

/-- The negative identity as a special-linear matrix. -/
def negIMatrix : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by simp⟩

/-- The element `-I = [[-1, 0], [0, -1]]` of the congruence subgroup `Γ(2)`. -/
def negI : Γ 2 := ⟨negIMatrix, by
  rw [Gamma_mem]
  change ((-1 : ℤ) : ZMod 2) = 1 ∧ ((0 : ℤ) : ZMod 2) = 0 ∧
    ((0 : ℤ) : ZMod 2) = 0 ∧ ((-1 : ℤ) : ZMod 2) = 1
  decide⟩

/--
@isnad1 id=eq.0h0v.s9.ee5c203a8d16 from=translated src=- shape=0d567a11 vocab=33c0285b
-/
theorem α_eq_T_sq :
    α = ⟨T ^ 2, by simp only [Gamma_mem, Fin.isValue, SpecialLinearGroup.coe_pow]; decide⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
    (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pow_two, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s10.f048900280bc from=translated src=- shape=720964dd vocab=2df03890
-/
theorem β_eq_negI_mul_S_mul_α_inv_mul_S : β = negI * S * α⁻¹ * S := by
  apply Subtype.ext
  change (!![1, 0; 2, 1] : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-1, 0; 0, -1] * !![0, -1; 1, 0] * Matrix.adjugate !![1, 2; 0, 1] *
      !![0, -1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Matrix.adjugate_fin_two]

/--
@isnad1 id=eq.0h0v.s11.e0cbc7935fc9 from=translated src=- shape=12a9ccc1 vocab=3beb35d9
-/
theorem ModularGroup.modular_negI_sq : negI ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = 1
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [pow_two, Matrix.mul_apply]

/--
@isnad1 id=eq.0h0v.s8.2dca712d9a33 from=translated src=- shape=6b7a4918 vocab=66358828
-/
theorem ModularGroup.modular_negI_inv : negI⁻¹ = negI := by
  apply Subtype.ext
  apply Subtype.ext
  change Matrix.adjugate (!![-1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℤ) =
    !![-1, 0; 0, -1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.adjugate_fin_two]

section slash_action

variable (f : ℍ → ℂ) (k : ℤ) (z : ℍ)

open ModularForm

/--
@isnad1 id=eq.0h1v.s8.a570421b53cc from=translated src=- shape=58367929 vocab=cdea3287
-/
theorem modular_negI_smul : negI.1 • z = z := by
  rw [specialLinearGroup_apply]
  simp [negI, negIMatrix]

/--
@isnad1 id=eq.1h2v.s8.1e6c76923044 from=translated src=- shape=43562b5c vocab=1c8cd05e
-/
theorem modular_slash_negI_of_even (hk : Even k) : f ∣[k] negI.1 = f := by
  ext x
  rw [slash_action_eq'_iff, modular_negI_smul]
  simp [negI, negIMatrix, hk.neg_one_zpow]

/--
@isnad1 id=eq.0h3v.s6.3e8442f9f2c6 from=translated src=- shape=22d5e078 vocab=ea6a159c
-/
theorem modular_slash_S_apply :
    (f ∣[k] S) z = f (UpperHalfPlane.mk (-z)⁻¹ z.im_inv_neg_coe_pos) * z ^ (-k) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_S_smul]
  simp only [SpecialLinearGroup.coe_GL_coe_matrix]
  rw [SpecialLinearGroup.map_apply_coe (Int.castRingHom ℝ) S]
  simp [S, RingHom.mapMatrix_apply]

/--
@isnad1 id=eq.0h3v.s6.d2b7d8591e57 from=translated src=- shape=1783b684 vocab=e3b07fd2
-/
theorem modular_slash_T_apply : (f ∣[k] T) z = f ((1 : ℝ) +ᵥ z) := by
  rw [SL_slash_apply, denom, UpperHalfPlane.modular_T_smul]
  simp only [SpecialLinearGroup.coe_GL_coe_matrix]
  rw [SpecialLinearGroup.map_apply_coe (Int.castRingHom ℝ) T]
  simp [T, RingHom.mapMatrix_apply]

end slash_action

section slashaction_generators

/- This part proves that `SL(2, ℤ)` and `Γ 2` are generated by `{S, T, -I}` and `{α, β, -I}`
respectively. -/

/--
@isnad1 id=eq.0h0v.s8.abdca41e72ac from=translated src=- shape=b32e9788 vocab=a25b98d7
-/
theorem SL2Z_generate : (⊤ : Subgroup SL(2, ℤ)) = Subgroup.closure {S, T} :=
  SpecialLinearGroup.SL2Z_generators.symm

/--
@isnad1 id=ex.3h2v.s6.5bbb0c19205e from=translated src=- shape=c9ab9cfc vocab=2e4b6d7d
-/
lemma Γ2_reduce_row (a c : ℤ) (ha : Odd a) (hc : Even c) (hc0 : c ≠ 0) :
    ∃ n, |a + 2 * n * c| < |c| := by
  have h2c : 2 * c ≠ 0 := by simp [hc0]
  obtain ⟨q, r, hqr, hr0, hr2c⟩ : ∃ q r, a = 2 * c * q + r ∧ 0 ≤ r ∧ r < 2 * |c| := by
    refine ⟨a / (2 * c), a % (2 * c), by rw [Int.mul_ediv_add_emod],
      Int.emod_nonneg _ h2c, ?_⟩
    simpa using Int.emod_lt_abs _ h2c
  by_cases hr_le : r ≤ |c|
  · refine ⟨-q, ?_⟩
    by_cases hr_eq : r = c ∨ r = -c <;> [grind; exact abs_lt.mpr ⟨by grind, by grind⟩]
  · refine ⟨-q - (if c > 0 then 1 else -1), ?_⟩
    split_ifs <;> cases abs_cases c <;> grind

/--
@isnad1 id=ex.3h2v.s6.30c2a51cf6fb from=translated src=- shape=2d6432fc vocab=2e4b6d7d
-/
lemma Γ2_reduce_col (a c : ℤ) (ha : Odd a) (hc : Even c) (ha0 : a ≠ 0) :
    ∃ m, |c + 2 * m * a| < |a| := by
  obtain ⟨q, r, hqr, hr0, hra⟩ : ∃ q r, c / 2 = q * a + r ∧ 0 ≤ r ∧ r < |a| :=
    ⟨c / 2 / a, c / 2 % a, by rw [Int.ediv_mul_add_emod],
      Int.emod_nonneg _ ha0, Int.emod_lt_abs _ ha0⟩
  have hm : ∃ m, |c / 2 + m * a| ≤ (|a| - 1) / 2 := by
    by_cases hr_case : r ≤ (|a| - 1) / 2
    · exact ⟨-q, by rw [abs_le]; constructor <;> grind⟩
    · refine ⟨if a > 0 then -q - 1 else -q + 1, ?_⟩
      split_ifs <;> cases abs_cases a <;> cases ha <;> exact abs_le.mpr ⟨by grind, by grind⟩
  obtain ⟨m, hm⟩ := hm
  refine ⟨m, ?_⟩
  norm_num [abs_le] at *
  cases abs_cases a <;> cases abs_cases (c + 2 * m * a) <;>
    nlinarith [Int.ediv_mul_cancel (show 2 ∣ c from even_iff_two_dvd.mp hc),
      Int.ediv_mul_cancel (show 2 ∣ |a| - 1 from even_iff_two_dvd.mp
        (by cases abs_cases a <;> simp [*, parity_simps]))]

/-- If `G` is generated by a set `s`, then the slash action by elements in G is
uniquely determined by the slash action by elements in s. See `slashaction_generators'` for a
version where `s` is a set of elements in `G`.
@isnad1 id=iff.1h4v.s9.83ffb96f5ff0 from=translated src=- shape=4b19cf08 vocab=d9ab2741
-/
theorem slashaction_generators
    (f : ℍ → ℂ) (G : Subgroup SL(2, ℤ)) (s : Set SL(2, ℤ)) (hG : G = Subgroup.closure s) (k : ℤ) :
    (∀ γ : G, f ∣[k] γ.1 = f) ↔ (∀ γ ∈ s, f ∣[k] γ = f) := by
  subst hG
  constructor <;> intro h
  · intro γ hγ
    convert h ⟨γ, Subgroup.subset_closure hγ⟩
  · simp only [Subtype.forall]
    intro ⟨γ, hγ⟩
    -- key idea: this lemma allows induction on the "words" of the group
    apply Subgroup.closure_induction (G := SL(2, ℤ)) (p := fun γ _ ↦ f ∣[k] γ = f) h --hγ h
    · exact SlashAction.slash_one _ _
    · intro _ _ _ _ hf₁ hf₂
      rw [SlashAction.slash_mul, hf₁, hf₂]
    · intro x _ hf
      rw [← hf, ← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one, hf]

/-- If `G` is generated by a set `s`, then the slash action by elements in G is
uniquely determined by the slash action by elements in s. See `slashaction_generators` for a
version where `s` is a set of elements in SL(2, ℤ).
@isnad1 id=iff.1h4v.s11.53d411d62776 from=translated src=- shape=6cca5c35 vocab=a77777e3
-/
theorem slashaction_generators'
    (f : ℍ → ℂ) {G : Subgroup SL(2, ℤ)} (s : Set G) (hG : ⊤ = Subgroup.closure s) (k : ℤ) :
    (∀ γ : G, f ∣[k] γ.1 = f) ↔ (∀ γ ∈ s, f ∣[k] γ.1 = f) := by
  constructor <;> intro h
  · simp_all
  · intro ⟨γ, hγ⟩
    -- key idea: this lemma allows induction on the "words" of the group
    apply Subgroup.closure_induction (G := G) (p := fun γ _ ↦ f ∣[k] γ.1 = f) (k := s) ?_ ?_
    · intro _ _ _ _ hf₁ hf₂
      rw [@Subgroup.coe_mul, SlashAction.slash_mul, hf₁, hf₂]
    · intro x _ hf
      rw [← hf, ← SlashAction.slash_mul]
      simp [hf]
    · simp [← hG]
    · simp_all
    · exact SlashAction.slash_one k f

/--
@isnad1 id=eq.2h3v.s7.097ba2f75733 from=translated src=- shape=da607012 vocab=3759ea33
-/
theorem slashaction_generators_SL2Z
    (f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] S = f) (hT : f ∣[k] T = f) :
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) := by
  intro γ
  refine (slashaction_generators f ⊤ _ SL2Z_generate k).mpr ?_ ⟨γ, by simp⟩
  simp_all

/--
@isnad1 id=eq.3h3v.s9.578320ade929 from=translated src=- shape=e0b94c2f vocab=45056d83
-/
theorem slashaction_generators_GL2R
    (f : ℍ → ℂ) (k : ℤ) (hS : f ∣[k] S = f) (hT : f ∣[k] T = f) :
    (∀ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1),
       f ∣[k] γ = f) := by
  intro γ hγ
  simp only [Subgroup.mem_map] at hγ
  obtain ⟨A, hA₁, hA₂⟩ := hγ
  rw [←hA₂]
  change f ∣[k] A = f
  refine (slashaction_generators f ⊤ _ SL2Z_generate k).mpr ?_ ⟨A, by simp⟩
  simp_all

end slashaction_generators
