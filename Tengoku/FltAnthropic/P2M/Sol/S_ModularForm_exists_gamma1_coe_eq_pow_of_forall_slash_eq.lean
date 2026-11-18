import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_exists_gamma1_coe_eq_pow_of_forall_slash_eq

set_option autoImplicit false

open scoped MatrixGroups ModularForm

/--
@isnad1 id=ex.1h4v.s11.03ace419b13a from=translated src=- shape=1ac73097 vocab=998e7815
-/
theorem solution
    (M : ℕ) [NeZero M] (k : ℤ) (i : ℕ)
    (F : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) k)
    (hF : ∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
      (⇑(F t) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(F (t * ((γ 1 1 : ℤ) : ZMod M)))) :
    ∃ P : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) ((i : ℤ) * k),
      (∀ t : ZMod M, (⇑(P t) : UpperHalfPlane → ℂ) = (⇑(F t) : UpperHalfPlane → ℂ) ^ i) ∧
      (∀ (t : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(P t) : UpperHalfPlane → ℂ) ∣[(i : ℤ) * k] γ = ⇑(P (t * ((γ 1 1 : ℤ) : ZMod M)))) := by
  induction i with
  | zero =>
    rw [show ((0 : ℕ) : ℤ) * k = 0 by simp]
    refine ⟨fun _ => ModularForm.const 1, fun t => ?_, fun t γ _ => ?_⟩
    · rw [pow_zero]; rfl
    · have h := ModularForm.is_invariant_const γ (1 : ℂ)
      exact h
  | succ i ih =>
    obtain ⟨P, hP1, hP2⟩ := ih
    rw [show ((i + 1 : ℕ) : ℤ) * k = (i : ℤ) * k + k by push_cast; ring]
    refine ⟨fun t => (P t).mul (F t), fun t => ?_, fun t γ hγ => ?_⟩
    · rw [ModularForm.coe_mul, hP1, pow_succ]
    · simp only [ModularForm.coe_mul]
      rw [ModularForm.mul_slash_SL2, hP2 t γ hγ, hF t γ hγ]
