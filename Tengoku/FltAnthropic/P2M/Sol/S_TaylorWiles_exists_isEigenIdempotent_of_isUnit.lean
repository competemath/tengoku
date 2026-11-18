import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_LocalSplitting
import Tengoku.FltAnthropic.Theorems.Thm_TaylorWiles_isEigenIdempotent_smul_sub

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_TaylorWiles_exists_isEigenIdempotent_of_isUnit.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_TaylorWiles_exists_isEigenIdempotent_of_isUnit

set_option autoImplicit false

universe u v

open Matrix

open TaylorWiles in
theorem solution {A : Type u} [CommRing A] {M : Matrix (Fin 2) (Fin 2) A} {a b : A}
    (htr : M.trace = a + b) (hdet : M.det = a * b) (hu : IsUnit (a - b)) :
    ∃ e, TaylorWiles.IsEigenIdempotent M a b e := by
  obtain ⟨u, hu⟩ := hu
  refine ⟨_, TaylorWiles.isEigenIdempotent_smul_sub htr hdet (v := ((u⁻¹ : Aˣ) : A)) ?_⟩
  rw [← hu]
  exact u.inv_mul
