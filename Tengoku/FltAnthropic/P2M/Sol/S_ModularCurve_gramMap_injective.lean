import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_ComponentGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_gramMap_injective.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_gramMap_injective

open ModularCurve Finset

private theorem aux_eq_zero {ι : Type*} [Fintype ι] {e : ι → ℕ} (he : ∀ x, 0 < e x)
    {D : ι → ℤ} (h : widthPairing e D D = 0) : D = 0 := by
  rw [widthPairing_apply] at h
  have hterm : ∀ x ∈ Finset.univ, (0 : ℤ) ≤ (e x : ℤ) * (D x * D x) := fun x _ =>
    mul_nonneg (Int.natCast_nonneg _) (mul_self_nonneg _)
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h
  funext x
  rcases mul_eq_zero.mp (hzero x (Finset.mem_univ x)) with hx | hx
  · exact absurd (Int.natCast_eq_zero.mp hx) (he x).ne'
  · exact mul_self_eq_zero.mp hx

/--
@isnad1 id=injectiv.1h2v.s11.317bd5d9ffcd from=translated src=- shape=a8cb633c vocab=add33337
-/
theorem solution {ι : Type*} [Fintype ι] {e : ι → ℕ} (he : ∀ x, 0 < e x) :
    Function.Injective (gramMap e) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro D hD
  have hDD : widthPairing e D.1 D.1 = 0 := by
    have := congrArg (fun φ => φ D) hD
    simpa using this
  exact Subtype.ext (aux_eq_zero he hDD)
