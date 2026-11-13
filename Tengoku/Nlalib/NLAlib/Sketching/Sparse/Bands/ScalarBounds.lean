/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit sparse-band scalar inequalities

Square-root and scalar envelope inequalities retain the numerical constants used by the concrete band estimates.
Ported from `SparseFockFormal.ScalarBounds` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

/-- The algebraic last step in the block-Gram estimate `d + ℓ - 1`.

The operator-specific hypotheses (diagonal block at most `d`, each off-diagonal
block at most `1`) are deliberately represented as scalar premises here.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h5v.s6.f18b4b29aa74 from=translated src=- shape=c5078c82 vocab=6bfb30e3
-/
theorem blockGram_row_bound
    {d ell energy diagonal cross : ℝ}
    (_henergy : 0 ≤ energy)
    (hdiag : diagonal ≤ d * energy)
    (hcross : cross ≤ (ell - 1) * energy) :
    diagonal + cross ≤ (d + ell - 1) * energy := by
  nlinarith

/-- A finite scalar row-majorization version of the block-Gram estimate.

One distinguished diagonal entry is bounded by `d * energy`; each of the other
`ell - 1` entries is bounded by `energy`. No operator-norm statement is hidden
in this lemma.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h5v.s6.2d714f4eb31e from=translated src=- shape=b1a8f5db vocab=e8736be7
-/
theorem blockGram_finite_row_bound
    {ell : ℕ} (diagonalIndex : Fin ell) (entry : Fin ell → ℝ)
    {d energy : ℝ}
    (hdiag : entry diagonalIndex ≤ d * energy)
    (hoff : ∀ j, j ≠ diagonalIndex → entry j ≤ energy) :
    (∑ j, entry j) ≤ (d + (ell : ℝ) - 1) * energy := by
  have hmem : diagonalIndex ∈ (Finset.univ : Finset (Fin ell)) := Finset.mem_univ _
  have hother :
      (∑ j ∈ (Finset.univ.erase diagonalIndex), entry j) ≤
        ∑ _j ∈ (Finset.univ.erase diagonalIndex), energy := by
    apply Finset.sum_le_sum
    intro j hj
    exact hoff j (Finset.ne_of_mem_erase hj)
  have hcard : (Finset.univ.erase diagonalIndex).card = ell - 1 := by
    simp [Finset.card_erase_of_mem hmem]
  have hell : 1 ≤ ell := Nat.one_le_iff_ne_zero.mpr (by
    intro hz
    simpa [hz] using diagonalIndex.isLt)
  calc
    (∑ j, entry j) = entry diagonalIndex +
        ∑ j ∈ (Finset.univ.erase diagonalIndex), entry j := by
          rw [← Finset.sum_erase_add _ _ hmem]
          ring
    _ ≤ d * energy + ∑ _j ∈ (Finset.univ.erase diagonalIndex), energy :=
      add_le_add hdiag hother
    _ = d * energy + ((ell - 1 : ℕ) : ℝ) * energy := by simp [hcard]
    _ = (d + (ell : ℝ) - 1) * energy := by
      rw [Nat.cast_sub hell]
      ring

/-- A joint mixed-band product estimate fits the corrected ladder envelope.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h2v.s6.ba9ee5e7ed4c from=translated src=- shape=3c26972e vocab=23d532ce
-/
theorem mixed_product_into_envelope
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt x * Real.sqrt y ≤ (x + y) / 2 := by
  have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have hx' : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hy' : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hy
  nlinarith [two_mul_le_add_sq (Real.sqrt x) (Real.sqrt y)]

/-- Exact arithmetic behind the final parameter substitution.

The hypotheses are the squared/denominator-cleared forms delivered by choices
`m ≥ (d+2q)/ε²` and `s ≥ (2q+1)/ε`.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.5h4v.s6.b95b47c6bde8 from=translated src=- shape=b3ada46b vocab=cef4cf1d
-/
theorem parameter_envelope
    {rootTerm linearTerm sparseTerm ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hroot : rootTerm ≤ ε)
    (hlinear : linearTerm ≤ ε ^ 2)
    (hsparse : sparseTerm ≤ ε) :
    rootTerm + linearTerm + sparseTerm ≤ 3 * ε := by
  nlinarith [mul_self_le_mul_self hε0 hε1]

/-- Division arithmetic for the sparsity term: `ν ≤ 2q` and
`s ≥ (2q+1)/ε` imply `(ν+1)/s ≤ ε`.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.4h4v.s7.f05a7dbdc7da from=translated src=- shape=9eb6cad1 vocab=70d00927
-/
theorem sparsity_parameter_arithmetic
    {ν q s ε : ℝ}
    (hν : ν + 1 ≤ 2 * q + 1)
    (_hε : 0 ≤ ε)
    (hs : 0 < s)
    (hscale : 2 * q + 1 ≤ ε * s) :
    (ν + 1) / s ≤ ε := by
  apply (div_le_iff₀ hs).2
  linarith

/-- Squared arithmetic for the dense term, before applying monotonicity of sqrt.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h4v.s6.05a53c83c661 from=translated src=- shape=4b2cf085 vocab=5c9d27ef
-/
theorem dense_parameter_arithmetic
    {d ν m ε : ℝ}
    (hm : 0 < m)
    (hscale : d + ν ≤ ε ^ 2 * m) :
    (d + ν) / m ≤ ε ^ 2 := by
  exact (div_le_iff₀ hm).2 hscale

/-- Dense-scale arithmetic after taking the square root.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.3h4v.s6.c232c0bfb1c6 from=translated src=- shape=119d1172 vocab=d44e7500
-/
theorem dense_sqrt_parameter_arithmetic
    {d ν m ε : ℝ}
    (hε : 0 ≤ ε)
    (hm : 0 < m)
    (hscale : d + ν ≤ ε ^ 2 * m) :
    Real.sqrt ((d + ν) / m) ≤ ε := by
  rw [Real.sqrt_le_iff]
  exact ⟨hε, dense_parameter_arithmetic hm hscale⟩

/-- Direct assembly for the normalized ladder envelope
`sqrt ((d+ν)/m) + (d+ν)/m + (ν+1)/s`.

Source: ported from `SparseFockFormal.ScalarBounds`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.7h6v.s7.b3fd1eac536e from=translated src=- shape=10ce33e2 vocab=d44e7500
-/
theorem final_parameter_envelope
    {d ν q m s ε : ℝ}
    (hν : ν ≤ 2 * q)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hm : 0 < m) (hs : 0 < s)
    (hmScale : d + ν ≤ ε ^ 2 * m)
    (hsScale : 2 * q + 1 ≤ ε * s) :
    Real.sqrt ((d + ν) / m) + (d + ν) / m + (ν + 1) / s ≤ 3 * ε := by
  apply parameter_envelope hε0 hε1
  · exact dense_sqrt_parameter_arithmetic hε0 hm hmScale
  · exact dense_parameter_arithmetic hm hmScale
  · exact sparsity_parameter_arithmetic (ν := ν) (q := q) (s := s) (ε := ε)
      (by linarith) hε0 hs hsScale

end NLAlib.SparseSketch
