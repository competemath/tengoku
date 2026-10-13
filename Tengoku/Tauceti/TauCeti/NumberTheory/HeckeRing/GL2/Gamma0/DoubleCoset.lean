/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Claude
-/
module

public import Tengoku.Tauceti.TauCeti.NumberTheory.HeckeRing.GL2.Gamma0.Basic

-- the gcd decomposition and `Γ(N) ≤ Γ₀(N)` are used only inside proofs here
import Tengoku.Tauceti.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The `Γ₀(N)` double coset of a coprime-determinant element

**Shimura, Lemma 3.29(3).** For `α ∈ Δ₀(N)` whose determinant is coprime to `N`,

`SL₂(ℤ) α SL₂(ℤ) ∩ Δ₀(N) = Γ₀(N) α Γ₀(N)`.

The right-hand side is always contained in the left, because `Γ₀(N) ≤ SL₂(ℤ)` and `Δ₀(N)` is a
submonoid containing both `Γ₀(N)` and `α`. The content is the other inclusion: an element
`σ₁ α σ₂` of the level-one double coset that happens to lie in `Δ₀(N)` can be rewritten with
`σ₁, σ₂` taken from `Γ₀(N)`.

The mechanism is the Chinese-remainder decomposition
`CongruenceSubgroup.Gamma_gcd_eq_sup`: coprimality of `det α` with `N` makes
`Γ(N) ⊔ Γ(det α) = ⊤`, so `σ₁` factors as `τ_N · τ_a` with `τ_N ∈ Γ(N) ≤ Γ₀(N)` and
`τ_a ∈ Γ(det α)`. The second factor is absorbed on the other side: `HeckeRing.GLn`'s
`inv_conjugate_mem_SLnZ_of_mem_ker` says `α⁻¹ τ_a α` is again integral, so
`τ_a α = α · (α⁻¹ τ_a α)`, and the new right factor is forced into `Γ₀(N)` by reading off the
lower-left entry of the product —
which is where `gcd(det α, N) = 1` is used a second time, through the lower-right entry.

Ported from the AINTLIB `LeanModularForms` project
(`LeanModularForms/HeckeRIngs/GLn/CongruenceHecke/Foundation.lean`, Chris Birkbeck,
<https://github.com/CBirkbeck/AINTLIB/tree/main/projects/LeanModularForms>).

## Main results

* `HeckeRing.GL2.Gamma0_map_le_SLnZ`: `Γ₀(N) ≤ SL₂(ℤ)` inside `GL₂(ℚ)`.
* `HeckeRing.GL2.doubleCoset_Gamma0_map_le_doubleCoset_SLnZ`: `Γ₀(N) α Γ₀(N) ⊆ Γ α Γ`.
* `HeckeRing.GL2.gcd_apply_one_one_eq_one`: for an integral matrix with `N ∣ c` and determinant
  coprime to `N`, the lower-right entry is coprime to `N`.
* `HeckeRing.GL2.doubleCoset_SLnZ_inter_Delta0_eq_doubleCoset_Gamma0_map`: the equality above.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Lemma 3.29(3).
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Subgroup HeckeRing.GLn

open scoped Pointwise MatrixGroups

namespace HeckeRing.GL2

variable (N : ℕ)

/-- `Γ₀(N) ≤ SL₂(ℤ)` as subgroups of `GL₂(ℚ)`: the image of any integral matrix of determinant
one lies in the range of `mapGL`.

Stated at the unfolded `(Gamma0 N).map (mapGL ℚ)` so the coset layer can use it directly: the
`HeckeCoset` types of `CosetMap.lean` are spelled that way, and transporting a folded
containment along `Gamma0Image_def` at each use site would hide the canonical form. -/
lemma Gamma0_map_le_SLnZ : (Gamma0 N).map (mapGL ℚ) ≤ SLnZ 2 := by
  rw [← Gamma0Image_def N]
  intro g hg
  obtain ⟨σ, -, rfl⟩ := (mem_Gamma0Image_iff N).mp hg
  exact (mem_SLnZ_iff 2).mpr ⟨σ, rfl⟩

/-- `Γ₀(N) α Γ₀(N) ⊆ Γ α Γ`: immediate from `Γ₀(N) ≤ SL₂(ℤ)`. -/
lemma doubleCoset_Gamma0_map_le_doubleCoset_SLnZ (α : GL (Fin 2) ℚ) :
    DoubleCoset.doubleCoset α ((Gamma0 N).map (mapGL ℚ)) ((Gamma0 N).map (mapGL ℚ)) ⊆
      DoubleCoset.doubleCoset α (SLnZ 2) (SLnZ 2) := fun _ hx ↦ by
  rw [DoubleCoset.mem_doubleCoset] at hx ⊢
  obtain ⟨γ₁, hγ₁, γ₂, hγ₂, hx_eq⟩ := hx
  exact ⟨γ₁, Gamma0_map_le_SLnZ N hγ₁, γ₂, Gamma0_map_le_SLnZ N hγ₂, hx_eq⟩

/-- If `N ∣ c` and `det` is coprime to `N`, then so is the lower-right entry: modulo `N` the
determinant is `a * d`, so `d` divides a unit. -/
lemma gcd_apply_one_one_eq_one (A : Matrix (Fin 2) (Fin 2) ℤ) (hAN : (N : ℤ) ∣ A 1 0)
    (hdet : Int.gcd A.det N = 1) : Int.gcd (A 1 1) N = 1 := by
  rw [← Int.isCoprime_iff_gcd_eq_one] at hdet ⊢
  obtain ⟨k, hk⟩ := hAN
  have hmul : A 0 0 * A 1 1 = A.det + A 0 1 * k * (N : ℤ) := by
    rw [Matrix.det_fin_two A, hk]; ring
  exact (IsCoprime.mul_left_iff.mp (hmul ▸ hdet.add_mul_right_left _)).2

end HeckeRing.GL2
