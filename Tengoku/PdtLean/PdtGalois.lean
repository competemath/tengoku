import Tengoku
import Tengoku.PdtLean.PdtIrreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Galois groups of `x³ − x − 1` and `x⁴ − x − 1`

* `galActionHom_bijective_of_quartic` — a general criterion: an irreducible monic quartic over `ℚ`
  with exactly two non-real roots and an irreducible resolvent cubic has Galois group `S₄`
  (its action on the four complex roots is the full symmetric group).
* `gal_cubic_bijective` — `Gal(x³ − x − 1) ≅ S₃`, via Mathlib's prime-degree criterion.
* `gal_quartic_bijective` — `Gal(x⁴ − x − 1) ≅ S₄`, via the criterion above with the resolvent
  cubic `x³ + 4x − 1` (irreducible mod `7`).
-/

namespace PDT

open Polynomial Module
open scoped IntermediateField

attribute [local instance] Polynomial.Gal.splits_ℚ_ℂ

/-! ### (A0) A subgroup of `S₄` of order divisible by `12` containing a transposition is `S₄` -/

theorem perm_four_eq_top {α : Type*} [Fintype α] [DecidableEq α] (hα : Fintype.card α = 4)
    (H : Subgroup (Equiv.Perm α)) (h4 : 4 ∣ Nat.card H) (h3 : 3 ∣ Nat.card H)
    {τ : Equiv.Perm α} (hτ : τ ∈ H) (hswap : τ.IsSwap) : H = ⊤ := by
  have h12 : 12 ∣ Nat.card H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h3
  have hcard : Nat.card (Equiv.Perm α) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, hα]; rfl
  have hmul := H.index_mul_card
  rw [hcard] at hmul
  obtain ⟨k, hk⟩ := h12
  have hik : H.index * k = 2 := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 12 by norm_num)
    rw [show 12 * (H.index * k) = H.index * (12 * k) by ring, ← hk, hmul]
  have hidx : H.index ∣ 2 := Dvd.intro k hik
  rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exfalso
    rw [Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2, Equiv.Perm.mem_alternatingGroup,
      hswap.sign_eq] at hτ
    exact units_ne_neg_self (1 : ℤˣ) hτ.symm

/-! ### (A1) The degree of an irreducible polynomial divides the order of its Galois group -/

theorem natDegree_dvd_card_gal {p : ℚ[X]} (p_irr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := (degree_pos_of_irreducible p_irr).ne'
  let α : p.SplittingField := rootOfSplits (SplittingField.splits p) (by rwa [degree_map])
  have hα : IsIntegral ℚ α := .of_finite ℚ α
  use Module.finrank ℚ⟮α⟯ p.SplittingField
  suffices (minpoly ℚ α).natDegree = p.natDegree by
    letI _ : AddCommGroup ℚ⟮α⟯ := Ring.toAddCommGroup
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly ℚ α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd ℚ α
  rw [← eval_map_algebraMap]
  exact eval_rootOfSplits (SplittingField.splits p) (by rwa [degree_map])

/-! ### (A2) The resolvent cubic -/

/-- The resolvent cubic `X³ − b X² + (ac − 4d) X − (a²d − 4bd + c²)` of a monic quartic
`X⁴ + a X³ + b X² + c X + d`.-/
noncomputable def resolventCubic (p : ℚ[X]) : ℚ[X] :=
  X ^ 3 - C (p.coeff 2) * X ^ 2 + C (p.coeff 3 * p.coeff 1 - 4 * p.coeff 0) * X
    - C (p.coeff 3 ^ 2 * p.coeff 0 - 4 * p.coeff 2 * p.coeff 0 + p.coeff 1 ^ 2)

/-! ### (A3) The criterion -/

/-- The number of complex roots of an irreducible rational polynomial is its degree.-/
theorem card_rootSet_complex {p : ℚ[X]} (p_irr : Irreducible p) :
    Fintype.card (p.rootSet ℂ) = p.natDegree := by
  classical
  simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
  rw [Multiset.toFinset_card_of_nodup, ← Splits.natDegree_eq_card_roots, natDegree_map]
  · exact IsAlgClosed.splits _
  · exact nodup_roots ((separable_map (algebraMap ℚ ℂ)).mpr p_irr.separable)

/-! ### (B1) The cubic `x³ − x − 1`: Galois group `S₃` -/

/-! ### (B2) The quartic `x⁴ − x − 1`: Galois group `S₄` -/

/-- `X³ + 4X − 1` over `ℤ`.-/
noncomputable def resZ : ℤ[X] := X ^ 3 + 4 * X - 1

/-! ### (C) Multiplicative independence of the two real roots

If `ρ > 1` and `Q > 1` are real with `ρ³ = ρ + 1` and `Q⁴ = Q + 1`, then `ρ^a Q^b = 1` with
integers `a, b` forces `a = b = 0`.  Proof: `ρ^a = Q^(−b)` lies in `ℚ(ρ) ∩ ℚ(Q) = ℚ` (coprime
degrees `3` and `4`), so `ρ^a` is rational; but `ρ` and `ρ⁻¹ = ρ² − 1` are algebraic integers, so
`ρ^a` and `ρ^(−a)` are rational algebraic integers, i.e. integers `m, k` with `m k = 1`, forcing
`ρ^a = ±1`, impossible for `a ≠ 0` since `ρ > 1`. -/

end PDT
