import Tengoku.FltAnthropic.Definitions.Def_HaarQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HaarQuotient_lintegral_density_mul_eq_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HaarQuotient_lintegral_density_mul_eq_one

set_option autoImplicit false

open MeasureTheory Topology
open scoped ENNReal Pointwise

namespace HaarQuotient
export _root_.HaarQuotient (weight density)
open _root_.HaarQuotient

namespace SEC

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

noncomputable def coef (n : ℕ) : ℝ≥0∞ :=
  (2⁻¹ : ℝ≥0∞) ^ n *
    (1 + μH (((↑) : H → G) ⁻¹'
      ((CompactExhaustion.choice G (n + 1) : Set G) * (CompactExhaustion.choice G (n + 1) : Set G)⁻¹)))⁻¹

noncomputable def orbit (g : G) : ℝ≥0∞ := ∫⁻ y : H, weight H μH ((y : G) * g) ∂μH

end SEC

end HaarQuotient
