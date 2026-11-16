import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w w'

theorem Algebra.FormallySmooth.exists_algHom_baseChange_eq_of_isAdicComplete
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    [IsAdicComplete (Ideal.span {(p : 𝓞)}) 𝓞]
    (ℛ : Type w) [CommRing ℛ] [Algebra 𝓞 ℛ] [Algebra.FormallySmooth 𝓞 ℛ]
    (Y : Type w') [CommRing Y] [Algebra 𝓞 Y] [Module.Finite 𝓞 Y] [Module.Free 𝓞 Y]
    (χ : TensorProduct 𝓞 k ℛ →ₐ[k] TensorProduct 𝓞 k Y) :
    ∃ x : ℛ →ₐ[𝓞] Y, Algebra.TensorProduct.map (AlgHom.id k k) x = χ := by exact @_root_.P2MW.S_Algebra_FormallySmooth_exists_algHom_baseChange_eq_of_isAdicComplete.solution 𝓞 _ p k _ _ hk hker _ ℛ _ _ _ Y _ _ _ _ χ
