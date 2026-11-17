import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Tengoku.FltAnthropic.Definitions.Def_Submodule_LocalBox
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_ReducedNorm
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

/--
@isnad1 id=and.2h5v.s10.e96c0e5b1bef from=translated src=- shape=8b9129c8 vocab=b3652a2b
-/
theorem CerednikDrinfeld.CosetGraph.padicValRat_nrd_eq_zero_of_mem_awayUnits
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    (∀ γ ∈ CosetGraph.awayUnits R v, ∀ p : ℕ, p.Prime → p ≠ r →
        padicValRat p (nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 0) ∧
      (∀ c : ℚˣ, (∀ p : ℕ, p.Prime → p ≠ r → padicValRat p (c : ℚ) = 0) →
        Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom c ∈ CosetGraph.awayUnits R v) := by exact @_root_.P2MW.S_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits.solution a b R hR r _ v hv
