/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Analysis.Normed.Module.Connected
import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional
import Tengoku.LanaOka.Oka.Uniformization.Cayley
import Tengoku.LanaOka.Oka.Uniformization.CoveringLimit
import Tengoku.LanaOka.Oka.Uniformization.ModularCovering

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The universal covering of the complement of a lattice

For a period lattice `Λ ⊆ ℂ` we construct a holomorphic covering map `Ψ : ℍ → ℂ ∖ Λ`, onto, with
nonvanishing derivative (`PeriodPair.exists_uniformization`).

The input covering for the Koebe iteration comes from the modular function: an affine map `T`
sends `0` and `ω₂` onto the branch values `j(i)`, `j(ρ)` of `j`, so `T(ℂ ∖ Λ) ⊆ ℂ ∖ jBranch` and
`p₀ = T⁻¹ ∘ j ∘ C⁻¹ ∘ mob t` (`C` the Cayley map `ℍ → 𝔻`, `mob t` a disc automorphism moving `0`
to a point over `T(ω₂ / 2)`) is a holomorphic covering of `ℂ ∖ Λ` by an open subset of `𝔻`
containing `0`: its sections are the sections of `j` (`Uniformization.exists_section_jC`)
transported by `T`, `C` and `mob t`. The plane uniformisation theorem
`Uniformization.PlaneData.exists_covering` then gives `ψ₀ : 𝔻 → ℂ ∖ Λ`, and `Ψ = ψ₀ ∘ C`.
-/

open Complex Metric Set Filter Topology
open UpperHalfPlane hiding I I_re I_im

namespace Uniformization

/-! ### The lattice complement -/

namespace LatticeData

variable (L : PeriodPair)

theorem ω₂_ne_zero : L.ω₂ ≠ 0 := by
  intro h
  have := L.ω₂_div_two_notMem_lattice
  rw [h, zero_div] at this
  exact this (zero_mem _)

/-- The domain `Ω = ℂ ∖ Λ`. -/
def Ω : Set ℂ := (L.lattice : Set ℂ)ᶜ

theorem isOpen_Ω : IsOpen (Ω L) := L.isClosed_lattice.isOpen_compl

theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : (L.lattice : Set ℂ) = Set.range (fun p : ℤ × ℤ ↦ (p.1 : ℂ) * L.ω₁ + p.2 * L.ω₂) := by
    ext x
    simp only [SetLike.mem_coe, PeriodPair.mem_lattice, mem_range, Prod.exists]
  rw [this]
  exact countable_range _

theorem isPreconnected_Ω : IsPreconnected (Ω L) :=
  ((countable_lattice L).isConnected_compl_of_one_lt_rank
    (by rw [rank_real_complex]; norm_num)).isPreconnected

theorem half_mem_Ω : L.ω₂ / 2 ∈ Ω L := L.ω₂_div_two_notMem_lattice

end LatticeData

end Uniformization
