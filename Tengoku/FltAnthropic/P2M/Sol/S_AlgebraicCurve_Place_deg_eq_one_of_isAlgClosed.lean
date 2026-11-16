import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed

open AlgebraicCurve

/--
@isnad1 id=eq.1h3v.s6.f696068e8668 from=translated src=- shape=58dfcecf vocab=fcb3d844
-/
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] (v : Place K F) (hv : v.deg ≠ 0) : v.deg = 1 := by
  haveI : Module.Finite K v.ResidueField := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hv)
  have e : K ≃ₗ[K] v.ResidueField :=
    LinearEquiv.ofBijective (Algebra.linearMap K v.ResidueField) (IsAlgClosed.algebraMap_bijective_of_isIntegral)
  unfold Place.deg
  rw [← e.finrank_eq, Module.finrank_self]
