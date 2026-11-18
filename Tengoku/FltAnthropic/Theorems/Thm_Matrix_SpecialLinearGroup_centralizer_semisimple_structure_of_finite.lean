import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Matrix MatrixGroups

/--
@isnad1 id=and.3h4v.s12.c9fd14766748 from=translated src=- shape=ddcfff26 vocab=d6a1b335
-/
theorem Matrix.SpecialLinearGroup.centralizer_semisimple_structure_of_finite
    {K : Type} [Field K] (h2 : (2 : K) ≠ 0)
    {H : Type} [Group H] [Finite H] (ρ : H →* SL(2, K)) (hρ : Function.Injective ρ)
    (h : H) (hh : (((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
      ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4) :
    (∀ g : H, g ∈ Subgroup.centralizer ({h} : Set H) ↔
      ∃ x y : K, ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • ((ρ h : SL(2, K)) : Matrix (Fin 2) (Fin 2) K)) ∧
    (∀ g ∈ Subgroup.centralizer ({h} : Set H),
      ¬ (((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
         ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) →
      Subgroup.centralizer ({g} : Set H) = Subgroup.centralizer ({h} : Set H) ∧
      ((((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 0 0 +
        ((ρ g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) 1 1) ^ 2 ≠ 4)) ∧
    Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) ≤
      2 * Nat.card (Subgroup.centralizer ({h} : Set H)) ∧
    Nat.card {x : H // ¬ (((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) ∧
      ∃ s : H, ∀ g : H, g ∈ Subgroup.centralizer ({x} : Set H) ↔
        s⁻¹ * g * s ∈ Subgroup.centralizer ({h} : Set H)} *
      Nat.card (Subgroup.normalizer (Subgroup.centralizer ({h} : Set H) : Set H)) =
    Nat.card H * (Nat.card (Subgroup.centralizer ({h} : Set H)) -
      Nat.card {x : H // ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
        ((ρ x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1}) := by exact @_root_.P2MW.S_Matrix_SpecialLinearGroup_centralizer_semisimple_structure_of_finite.solution K _ h2 H _ _ ρ hρ h hh
