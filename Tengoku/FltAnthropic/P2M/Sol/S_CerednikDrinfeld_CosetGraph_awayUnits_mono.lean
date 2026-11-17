import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_CosetGraph_awayUnits_mono.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_CosetGraph_awayUnits_mono

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

/--
@isnad1 id=le.1h4v.s10.14f124418e64 from=translated src=- shape=c67b678c vocab=4e1c78b4
-/
theorem localBox_mono' {D : Type*} [Ring D] [Algebra ℚ D] {Λ Λ' : Submodule ℤ D} (h : Λ' ≤ Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) : Submodule.localBox Λ' w ≤ Submodule.localBox Λ w := by
  apply AddSubgroup.closure_mono
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

/--
@isnad1 id=le.1h5v.s9.4976d5ccc60f from=translated src=- shape=553b5e3f vocab=601e5bab
-/
theorem solution
    {a b : ℚ} {R R' : Submodule ℤ ℍ[ℚ, a, b]} (h : R' ≤ R) (v : HeightOneSpectrum (𝓞 ℚ)) :
    CosetGraph.awayUnits R' v ≤ CosetGraph.awayUnits R v := by
  intro x hx
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun hw => Subgroup.mem_comap.2 ?_
  have hx' : CosetGraph.toLoc w x ∈ Subgroup.closure (Submodule.localBoxUnits R' w) :=
    Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx w) hw)
  refine Subgroup.closure_mono ?_ hx'
  rintro u ⟨hu, hu'⟩
  exact ⟨localBox_mono' h w hu, localBox_mono' h w hu'⟩
