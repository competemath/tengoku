import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_modularFunctionFieldFull_algHom_ext.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_modularFunctionFieldFull_algHom_ext

set_option autoImplicit false

open _root_.ModularCurve open _root_.IntermediateField

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (qExpand jq modularFunctionFieldFull jqd_mem_full)
open _root_.ModularCurve

namespace W2B

section ExtFull

variable {N : ℕ}

/--
@isnad1 id=eq.1h4v.s13.770087307454 from=translated src=- shape=2afcfa05 vocab=3a46af12
-/
theorem algHom_ext_of_eq_on_divisorExpansions {A : Type*} [DivisionRing A] [Algebra ℚ A]
    {f g : modularFunctionFieldFull N →ₐ[ℚ] A}
    (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), f ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩ = g ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩) :
    f = g := by
  ext ⟨x, hx⟩
  induction hx using IntermediateField.adjoin_induction with
  | mem x hxS =>
      obtain ⟨d, hd, hdN, rfl⟩ := hxS
      exact h d hd hdN
  | algebraMap r =>
      have hr : (⟨algebraMap ℚ (LaurentSeries ℚ) r,
          (modularFunctionFieldFull N).algebraMap_mem r⟩ : modularFunctionFieldFull N)
          = algebraMap ℚ (modularFunctionFieldFull N) r := by
        apply Subtype.ext
        show algebraMap ℚ (LaurentSeries ℚ) r
          = ((algebraMap ℚ (modularFunctionFieldFull N) r : modularFunctionFieldFull N) : LaurentSeries ℚ)
        rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r, eq_ratCast (algebraMap ℚ (modularFunctionFieldFull N)) r]
        norm_cast
      exact (congrArg f hr).trans ((f.commutes r).trans ((g.commutes r).symm.trans (congrArg g hr.symm)))
  | add x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ + ⟨y, hy⟩) = g (⟨x, hx⟩ + ⟨y, hy⟩)
      rw [map_add, map_add, ihx, ihy]
  | inv x hx ih =>
      show f (⟨x, hx⟩⁻¹) = g (⟨x, hx⟩⁻¹)
      rw [map_inv₀, map_inv₀, ih]
  | mul x y hx hy ihx ihy =>
      show f (⟨x, hx⟩ * ⟨y, hy⟩) = g (⟨x, hx⟩ * ⟨y, hy⟩)
      rw [map_mul, map_mul, ihx, ihy]

end ExtFull

end W2B

end ModularCurve

/--
@isnad1 id=eq.1h4v.s13.770087307454 from=translated src=- shape=2afcfa05 vocab=3a46af12
-/
theorem solution {N : ℕ} {A : Type*} [DivisionRing A] [Algebra ℚ A] {f g : modularFunctionFieldFull N →ₐ[ℚ] A} (h : ∀ (d : ℕ) (_ : NeZero d) (hd : d ∣ N), f ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩ = g ⟨qExpand ℚ d jq, jqd_mem_full N hd⟩) : f = g :=
  ModularCurve.W2B.algHom_ext_of_eq_on_divisorExpansions h

end
