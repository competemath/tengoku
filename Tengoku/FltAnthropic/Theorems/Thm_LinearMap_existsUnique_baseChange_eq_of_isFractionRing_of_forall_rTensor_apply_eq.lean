import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
universe u

open scoped TensorProduct

/--
@isnad1 id=existsun.3h8v.s12.d7dd2357913a from=translated src=- shape=e723dbe8 vocab=dd444719
-/
theorem LinearMap.existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq
    (O : Type u) [CommRing O] [IsDomain O] (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K]
    (Oh : Type u) [CommRing Oh] [Algebra O Oh]
    (Kh : Type u) [CommRing Kh] [Algebra O Kh] [Algebra K Kh] [Algebra Oh Kh] [IsScalarTower O K Kh] [IsScalarTower O Oh Kh]
    (hinj : Function.Injective (algebraMap Oh Kh))
    (hcap : ∀ (x : K) (y : Oh), algebraMap K Kh x = algebraMap Oh Kh y → ∃ z : O, algebraMap O K z = x)
    (M : Type u) [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M]
    (N : Type u) [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N]
    (fK : K ⊗[O] M →ₗ[K] K ⊗[O] N) (fOh : Oh ⊗[O] M →ₗ[Oh] Oh ⊗[O] N)
    (hagree : ∀ m : M,
      ((IsScalarTower.toAlgHom O K Kh).toLinearMap.rTensor N) (fK ((1 : K) ⊗ₜ m)) =
        ((IsScalarTower.toAlgHom O Oh Kh).toLinearMap.rTensor N) (fOh ((1 : Oh) ⊗ₜ m))) :
    ∃! f : M →ₗ[O] N, f.baseChange K = fK ∧ f.baseChange Oh = fOh := by exact @_root_.P2MW.S_LinearMap_existsUnique_baseChange_eq_of_isFractionRing_of_forall_rTensor_apply_eq.solution O _ _ K _ _ _ Oh _ _ Kh _ _ _ _ _ _ hinj hcap M _ _ _ _ N _ _ _ _ fK fOh hagree
