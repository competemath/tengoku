import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Newforms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_exists_isNewform_descent.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_exists_isNewform_descent

open scoped CongruenceSubgroup
open _root_.CuspForm open _root_.ModularFormClass

namespace CuspForm
export _root_.CuspForm (GoodEigensystemOccursAt IsNewform IsNormalizedEigenform)
open _root_.CuspForm

private theorem exists_isNewform_descent_aux :
    ∀ N : ℕ, 0 < N → ∀ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform →
      ∃ (M : ℕ) (_ : M ∣ N) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNewform ∧
        ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
    intro hN f hf
    by_cases hnew : ∀ M : ℕ, M ∣ N → M ≠ N → ¬ GoodEigensystemOccursAt f M
    · exact ⟨N, dvd_refl N, f, ⟨hf, hnew⟩, fun _ _ _ => rfl⟩
    · push_neg at hnew
      obtain ⟨M, hMN, hMne, g, hg, hgf⟩ := hnew
      have hM0 : 0 < M := Nat.pos_of_dvd_of_pos hMN hN
      have hMlt : M < N := lt_of_le_of_ne (Nat.le_of_dvd hN hMN) hMne
      obtain ⟨M', hM'M, h, hhnew, hhg⟩ := IH M hMlt hM0 g hg
      refine ⟨M', hM'M.trans hMN, h, hhnew, fun ℓ hℓ hℓN => ?_⟩
      have hℓM : ¬ ℓ ∣ M := fun hd => hℓN (hd.trans hMN)
      rw [hhg ℓ hℓ hℓM, hgf ℓ hℓ hℓN]

end CuspForm

open CongruenceSubgroup ModularFormClass in
theorem solution {N : ℕ} [NeZero N]
    (f : CuspForm (Gamma0 N) 2) (hf : f.IsNormalizedEigenform) :
    ∃ (M : ℕ) (_ : M ∣ N) (g : CuspForm (Gamma0 M) 2),
      g.IsNewform ∧ ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → qCoeff g ℓ = qCoeff f ℓ :=
  CuspForm.exists_isNewform_descent_aux N (Nat.pos_of_ne_zero (NeZero.ne N)) f hf
