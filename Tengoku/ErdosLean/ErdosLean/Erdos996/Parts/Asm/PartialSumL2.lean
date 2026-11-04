import Tengoku.ErdosLean.ErdosLean.Erdos996.Parts.Asm.Atoms

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Assembly sub-lemma 7 (PartialSumL2): `L²` norm of the partial sums

Blueprint §7. Ho Lemma 3.1 (3.3) and Prop. 4.3 (orthogonality of the blocks):
`‖∑_{k<K} F_k‖₂² = ∑_{k<K} λ_k ≤ 1`, via Parseval (`tsum_sq_fourierCoeff`), the disjoint
Fourier supports of the atoms (`fourierCoeff_atom_disjoint`), and `‖atom‖₂ = 1`
(`integral_spike_nsmul_sq`).
-/

open MeasureTheory AddCircle Filter Topology Asymptotics Finset Real
open scoped ENNReal

namespace Erdos996
namespace Asm

local notation "𝕋" => AddCircle (1 : ℝ)
local notation "μ𝕋" => haarAddCircle (T := 1)

private lemma measurable_atom' (A k q : ℕ) : Measurable (atom A k q) :=
  (Erdos996.measurable_spike _).comp (continuous_nsmul _).measurable

private lemma memLp_atomC (A k q : ℕ) : MemLp (fun x => (atom A k q x : ℂ)) 2 μ𝕋 :=
  MemLp.of_bound ((Complex.measurable_ofReal.comp (measurable_atom' A k q)).aestronglyMeasurable)
    (2 ^ depth A k)
    (Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_spike_le _ _)

/-- The atom as an element of `L²(𝕋; ℂ)`.-/
private noncomputable def aLp (A k q : ℕ) : Lp ℂ 2 μ𝕋 := (memLp_atomC A k q).toLp _

end Asm
end Erdos996
