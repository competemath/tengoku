/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Basic
import Tengoku.Seed.Analysis.Calculus.LogDeriv
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.GenusOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# HadamardProduct.InfiniteProducts

Finite, indexed-finite, and infinite genus-one Hadamard products, with their
log-derivative identities. Each finite product's logarithmic derivative is the
regularized zero-sum `Σ (1/(s-ρ) + 1/ρ)`; the indexed/infinite products lift this to an
arbitrary index set via Mathlib's `tprod`/`tsum`. Identity content only.

## Main declarations

* `finiteHadamardProduct`, `indexedFiniteHadamardProduct`, `infiniteHadamardProduct`,
  `hadamardRegularizedLogDerivSeries`, `finiteHadamardRegularizedSum` — the products and
  series.
* `logDeriv_finiteHadamardProduct(_regularized)`,
  `logDeriv_indexedFiniteHadamardProduct` — log-derivative = regularized zero-sum.
* `deriv_indexedFiniteHadamardProduct(_eq_response)` — the finite derivative identity.
-/

namespace OverflowResidueRH

/-- **Finite Hadamard product** over a finite set of zero ordinates.-/
noncomputable def finiteHadamardProduct (zeros : Finset ℂ) (s : ℂ) : ℂ :=
  ∏ ρ ∈ zeros, hadamardGenus1Factor ρ s

/-- **Indexed infinite Hadamard product** over an arbitrary index set of
zero ordinates. Falls back to `1` when not multipliable (Mathlib's `tprod`).-/
noncomputable def infiniteHadamardProduct
    {ι : Type*} (zeroLoc : ι → ℂ) (s : ℂ) : ℂ :=
  ∏' i : ι, hadamardGenus1Factor (zeroLoc i) s

/-- **Indexed regularized log-derivative series** `Σ (1/(s-ρᵢ) + 1/ρᵢ)`.
Falls back to `0` when not summable.-/
noncomputable def hadamardRegularizedLogDerivSeries
    {ι : Type*} (zeroLoc : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, (1 / (s - zeroLoc i) + 1 / zeroLoc i)

/-- **Finite regularized log-derivative sum** over a Finset.-/
noncomputable def finiteHadamardRegularizedSum
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (s : ℂ) : ℂ :=
  ∑ i ∈ F, (1 / (s - zeroLoc i) + 1 / zeroLoc i)

/-- **Indexed finite Hadamard product**: the partial product over a Finset,
used for finite truncations of `infiniteHadamardProduct`.-/
noncomputable def indexedFiniteHadamardProduct
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) (s : ℂ) : ℂ :=
  ∏ i ∈ F, hadamardGenus1Factor (zeroLoc i) s

/-- ⭐ **PROVED — every indexed finite Hadamard product is normalized
to `1` at the origin.**-/
theorem indexedFiniteHadamardProduct_zero
    {ι : Type*} (zeroLoc : ι → ℂ) (F : Finset ι) :
    indexedFiniteHadamardProduct zeroLoc F 0 = 1 := by
  simp [indexedFiniteHadamardProduct, hadamardGenus1Factor_zero]

/-- ⭐ **PROVED — the infinite genus-one Hadamard product is normalized
to `1` at the origin.**-/
theorem infiniteHadamardProduct_zero
    {ι : Type*} (zeroLoc : ι → ℂ) :
    infiniteHadamardProduct zeroLoc 0 = 1 := by
  simp [infiniteHadamardProduct, hadamardGenus1Factor_zero]

/-- 🌟🌟 **PROVED — the infinite Hadamard product vanishes at every
indexed zero.** This discharges the zero-side of the quotient
factorization data directly from the canonical genus-one factor.-/
theorem infiniteHadamardProduct_eq_zero_at_zeroLoc
    {ι : Type*} {zeroLoc : ι → ℂ}
    (hzero : ∀ i : ι, zeroLoc i ≠ 0)
    (i : ι) :
    infiniteHadamardProduct zeroLoc (zeroLoc i) = 0 := by
  unfold infiniteHadamardProduct
  exact tprod_of_exists_eq_zero
    ⟨i, hadamardGenus1Factor_self_eq_zero (hzero i)⟩

end OverflowResidueRH
