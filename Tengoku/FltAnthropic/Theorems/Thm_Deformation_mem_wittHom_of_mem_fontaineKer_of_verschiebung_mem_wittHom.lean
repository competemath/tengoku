import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittHomColimit
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_FontaineHodge
import Tengoku.FltAnthropic.P2M.Sol.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

universe u v w

theorem Deformation.mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {k : Type v} [CommRing k] [Algebra 𝓞 k]
    (hk : Function.Surjective (algebraMap 𝓞 k))
    (hker : RingHom.ker (algebraMap 𝓞 k) = Ideal.span {(p : 𝓞)})
    (ℛ : Type w) [CommRing ℛ] [Bialgebra 𝓞 ℛ] [Module.Flat 𝓞 ℛ]
    {n : ℕ} {a : TruncatedWittVector p n (TensorProduct 𝓞 k ℛ)}
    (ha : a ∈ Deformation.TruncWitt.fontaineKer p n
      (Algebra.TensorProduct.includeRight : ℛ →ₐ[𝓞] TensorProduct 𝓞 k ℛ).toRingHom)
    (hVa : Deformation.TruncWitt.verschiebung a ∈
      Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ)) :
    a ∈ Deformation.wittHom k p n (TensorProduct 𝓞 k ℛ) := by exact @_root_.P2MW.S_Deformation_mem_wittHom_of_mem_fontaineKer_of_verschiebung_mem_wittHom.solution 𝓞 _ p _ hp k _ _ hk hker ℛ _ _ _ n a ha hVa
