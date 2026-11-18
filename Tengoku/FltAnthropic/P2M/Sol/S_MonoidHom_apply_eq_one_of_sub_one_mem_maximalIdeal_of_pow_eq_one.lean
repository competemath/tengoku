import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_IsLocalRing_eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MonoidHom_apply_eq_one_of_sub_one_mem_maximalIdeal_of_pow_eq_one

set_option autoImplicit false

universe u w

open IsLocalRing

/--
@isnad1 id=eq.3h5v.s8.b8120eec84e4 from=translated src=- shape=35a75965 vocab=bace6393
-/
theorem solution {G : Type u} {A : Type w} [Group G] [CommRing A] [IsLocalRing A]
    (χ : G →* Aˣ) (g : G) (hprin : (χ g : A) - 1 ∈ IsLocalRing.maximalIdeal A)
    {n : ℕ} (hn : IsUnit (n : A)) (hgn : g ^ n = 1) : χ g = 1 := by
  ext
  refine IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hprin hn ?_
  have h := congrArg (Units.val) (map_pow χ g n ▸ (congrArg χ hgn).trans (map_one χ))
  simpa using h
