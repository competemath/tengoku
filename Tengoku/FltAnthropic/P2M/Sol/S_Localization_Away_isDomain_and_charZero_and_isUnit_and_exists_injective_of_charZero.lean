import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Localization_Away_isDomain_and_charZero_and_isUnit_and_exists_injective_of_charZero.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Localization_Away_isDomain_and_charZero_and_isUnit_and_exists_injective_of_charZero

set_option autoImplicit false

/--
@isnad1 id=and.0h2v.s8.2b08c73d8526 from=translated src=- shape=ff6cf997 vocab=28b87d96
-/
theorem solution
    (M : ℕ) [NeZero M] (k : Type) [Field k] [CharZero k] :
    IsDomain (Localization.Away ((M : ℕ) : ℤ)) ∧ CharZero (Localization.Away ((M : ℕ) : ℤ)) ∧
      IsUnit ((M : ℕ) : Localization.Away ((M : ℕ) : ℤ)) ∧
      ∃ sk : Localization.Away ((M : ℕ) : ℤ) →+* k, Function.Injective sk := by
  have hM : ((M : ℕ) : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hMk : IsUnit ((Int.castRingHom k) ((M : ℕ) : ℤ)) := by
    rw [isUnit_iff_ne_zero]
    show (((M : ℕ) : ℤ) : k) ≠ 0
    exact_mod_cast NeZero.ne M
  have hg : ∀ y : Submonoid.powers ((M : ℕ) : ℤ), IsUnit ((Int.castRingHom k) y) := by
    rintro ⟨y, n, rfl⟩
    rw [map_pow]
    exact hMk.pow n
  have hle : Submonoid.powers ((M : ℕ) : ℤ) ≤ nonZeroDivisors ℤ := powers_le_nonZeroDivisors_of_noZeroDivisors hM
  let sk : Localization.Away ((M : ℕ) : ℤ) →+* k := IsLocalization.lift (S := Localization.Away ((M : ℕ) : ℤ)) hg
  have hsk : Function.Injective sk := by
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h; rw [(IsLocalization.injective (Localization.Away ((M : ℕ) : ℤ)) hle) h]
    · intro h; rw [Int.cast_injective (α := k) h]
  have hdom : IsDomain (Localization.Away ((M : ℕ) : ℤ)) := Function.Injective.isDomain sk hsk
  refine ⟨hdom, sk.charZero, ?_, sk, hsk⟩
  have := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away ((M : ℕ) : ℤ)) ((M : ℕ) : ℤ)
  rwa [map_natCast] at this
