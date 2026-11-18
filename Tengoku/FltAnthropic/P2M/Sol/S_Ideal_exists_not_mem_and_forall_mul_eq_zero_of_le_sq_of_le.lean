import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_exists_not_mem_and_forall_mul_eq_zero_of_le_sq_of_le

set_option autoImplicit false

/--
@isnad1 id=ex.2h3v.s8.e46350cd5941 from=translated src=- shape=fa7df402 vocab=bb375f05
-/
theorem solution
    {B : Type} [CommRing B] [IsNoetherianRing B] (I : Ideal B) (hI : I ≤ I ^ 2)
    (P : Ideal B) [P.IsPrime] (hIP : I ≤ P) :
    ∃ f : B, f ∉ P ∧ ∀ a ∈ I, f * a = 0 := by
  classical
  have hfg : I.FG := (isNoetherianRing_iff_ideal_fg B).1 inferInstance I
  have hle : I ≤ I • I := by
    intro a ha
    have := hI ha
    rwa [pow_two, ← Ideal.smul_eq_mul] at this
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I I hfg hle
  refine ⟨r, ?_, fun a ha => ?_⟩
  · intro hrP
    have h1 : r - (r - 1) ∈ P := P.sub_mem hrP (hIP hr1)
    rw [sub_sub_cancel] at h1
    exact (Ideal.ne_top_iff_one P).1 (Ideal.IsPrime.ne_top inferInstance) h1
  · have := hr a ha
    rwa [smul_eq_mul] at this
