import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u

/--
@isnad1 id=flat.1h3v.s11.4dfd1c4e19f8 from=translated src=- shape=26abc2b0 vocab=f1316dfa
-/
theorem Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (h : Function.Injective (LinearMap.rTensor M (maximalIdeal A).subtype)) :
    Module.Flat A M := by exact @_root_.P2MW.S_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom.solution A B _ _ _ _ _ _ _ _ M _ _ _ _ _ h
