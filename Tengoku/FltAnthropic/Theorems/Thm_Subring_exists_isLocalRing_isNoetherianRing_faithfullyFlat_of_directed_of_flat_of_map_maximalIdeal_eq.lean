import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v

open IsLocalRing

theorem Subring.exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq
    (A : Type u) [CommRing A] {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    (S : ι → Subring A) (hS : Monotone S) (hcov : ∀ x : A, ∃ i, x ∈ S i)
    [∀ i, IsLocalRing (S i)] [∀ i, IsNoetherianRing (S i)]
    (hflat : ∀ ⦃i j : ι⦄ (h : i ≤ j), (Subring.inclusion (hS h)).Flat)
    (hmax : ∀ ⦃i j : ι⦄ (h : i ≤ j),
      Ideal.map (Subring.inclusion (hS h)) (maximalIdeal (S i)) = maximalIdeal (S j)) :
    ∃ _ : IsLocalRing A, IsNoetherianRing A ∧
      ∀ i, Module.FaithfullyFlat (S i) A ∧
        Ideal.map (algebraMap (S i) A) (maximalIdeal (S i)) = maximalIdeal A := by exact @_root_.P2MW.S_Subring_exists_isLocalRing_isNoetherianRing_faithfullyFlat_of_directed_of_flat_of_map_maximalIdeal_eq.solution A _ ι _ _ _ S hS hcov _ _ hflat hmax
