import Tengoku.FltAnthropic.Definitions.Def_HeckeGalois_EichlerShimura

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_exists_sub_C_mem_eisensteinIdeal.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_exists_sub_C_mem_eisensteinIdeal

set_option autoImplicit false

open ModularCurve

namespace S09A1C

open ModularCurve

theorem exists_sub_C_mem_eisensteinIdeal (N : ℕ) (t : HeckeAlg) :
    ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by
  refine ⟨MvPolynomial.aeval (eisensteinSystem N) t, ?_⟩
  rw [eisensteinIdeal, mem_eigenIdeal_iff, map_sub, MvPolynomial.aeval_C]
  simp

end S09A1C

theorem solution (N : ℕ) (t : HeckeAlg) : ∃ n : ℤ, t - MvPolynomial.C n ∈ eisensteinIdeal N := by
  exact S09A1C.exists_sub_C_mem_eisensteinIdeal N t
