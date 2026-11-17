import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2
import Tengoku.FltAnthropic.P2M.Sol.S_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid
attribute [-simp] MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast

set_option autoImplicit false

open MvPowerSeries

universe u

/--
@isnad1 id=mem.6h9v.s10.a4010aa5c4a8 from=translated src=- shape=54403e24 vocab=8250499e
-/
theorem Tengoku.FltAnthropic.MvFormalGroup.natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime] (hp : (p : 𝓞) ∈ nonZeroDivisors 𝓞)
    {d : ℕ} (F : MvFormalGroup d 𝓞) [F.IsComm]
    (Fp : Fin d → MvPowerSeries (Fin d ⊕ Fin d) 𝓞)
    (hFp : ∀ (i : Fin d) (m : (Fin d ⊕ Fin d) →₀ ℕ), m ≠ 0 →
      (Fp i).coeff m * (p : 𝓞) = (p : 𝓞) ^ m.degree * (F.toPowerSeries i).coeff m)
    (hFp0 : ∀ i, (Fp i).constantCoeff = 0)
    (φ : Fin d → MvPowerSeries (Fin d) 𝓞)
    (hφ0 : ∀ i, (φ i).constantCoeff = 0)
    (hφ1 : MvFormalGroup.linearPart φ = 1)
    (hφF : ∀ i, subst Fp (φ i) =
      subst (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i) +
        subst (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) 𝓞)) (φ i))
    (i j : Fin d) (m : Fin d →₀ ℕ) :
    ((m j + 1 : ℕ) : 𝓞) * (φ i).coeff (m + Finsupp.single j 1) ∈ Ideal.span {(p : 𝓞) ^ m.degree} := by exact @_root_.P2MW.S_MvFormalGroup_natCast_mul_coeff_add_single_mem_span_pow_degree_of_subst_rescale_eq_add.solution 𝓞 _ p _ hp d F _ Fp hFp hFp0 φ hφ0 hφ1 hφF i j m
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
