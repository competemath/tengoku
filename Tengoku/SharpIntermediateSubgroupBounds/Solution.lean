import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proved solution for the Palomar statement surface

The first four compared declarations are imported directly from the substantive
proof development.  The five declarations in the `Palomar` namespace are thin
`Nat.card` adapters.  Their only purpose is to remove local `Fintype` instance
terms from exported theorem statements; each is proved immediately from the
corresponding manuscript-facing theorem.
-/

namespace SharpIntermediateSubgroupBounds
namespace Palomar

open scoped BigOperators Topology
open Filter Finset Real

noncomputable section

/-- Palomar-facing form of the exact prime-power theorem.
@isnad1 id=and.0h2v.s8.75bb7b14adbf from=translated src=- shape=2c3e9c97 vocab=6aba5ac6
-/
theorem primePower_interval_bound_optimal (p a : ℕ) [Fact p.Prime] :
    (∀ {G : Type*} [Group G] [Fintype G] (H : Subgroup G), H.index = p ^ a →
      Nat.card (Set.Ici H) ≤ totalQBinom p a) ∧
    Nat.card
        (Set.Ici (⊥ : Subgroup (Multiplicative (Fin a → ZMod p)))) =
      totalQBinom p a := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.primePower_interval_bound_optimal p a)

/-- Palomar-facing `Nat.card` form of the elementary-abelian displayed-ratio
limit.
@isnad1 id=tendsto.0h1v.s9.5313a6d218a9 from=translated src=- shape=d803d4e3 vocab=19543512
-/
theorem manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index : ℝ) ^
          (indexLog p
            (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index / 4)))
      atTop (nhds (sharpConstant (p : ℝ))) := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_displayed_ratio_tendsto_sharpConstant
      (p := p))

/-- Palomar-facing `Nat.card` form of the finite-envelope asymptotic.
@isnad1 id=tendsto.0h1v.s8.dd069fd136e7 from=translated src=- shape=08a9e6ed vocab=5d244966
-/
theorem manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
    {p : ℕ} [Fact p.Prime] :
    Tendsto (fun a : ℕ ↦
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) /
        (((finiteUQ
          (⊥ : Subgroup (ElementaryAbelianGroup p (2 * a))).index p : ℚ) : ℝ)))
      atTop (nhds 1) := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.manuscript_elementaryAbelian_interval_div_finiteUQ_tendsto_one
      (p := p))

/-- Palomar-facing `Nat.card` form of optimality of the leading constant.
@isnad1 id=le.1h2v.s7.b95f08e545c0 from=translated src=- shape=e9ac67a0 vocab=007a6465
-/
theorem manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    {p : ℕ} [Fact p.Prime] {C : ℝ}
    (hC : ∀ a : ℕ, 0 < a →
      (p : ℝ)⁻¹ ^ (a * a) *
        (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤ C) :
    sharpConstant (p : ℝ) ≤ C := by
  apply SharpIntermediateSubgroupBounds.manuscript_sharpConstant_le_of_positive_elementaryAbelian_bound
    (p := p) (C := C)
  intro a ha
  simpa only [← Nat.card_eq_fintype_card] using hC a ha

/-- Palomar-facing `Nat.card` form of optimality of the exponent `1/4`.
@isnad1 id=not.1h3v.s7.ebf25970aa0c from=translated src=- shape=bd0d9c92 vocab=0ffaa8cd
-/
theorem manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
    {p : ℕ} [Fact p.Prime] {alpha C : ℝ} (halpha : alpha < 1 / 4) :
    ¬ ∀ a : ℕ, 0 < a →
      (Nat.card (elementaryAbelianInterval p (2 * a)) : ℝ) ≤
        C * Real.rpow (p : ℝ) (4 * alpha * (a : ℝ) ^ 2) := by
  simpa only [← Nat.card_eq_fintype_card] using
    (SharpIntermediateSubgroupBounds.manuscript_no_subquarter_positive_elementaryAbelian_rpow_bound
      (p := p) (alpha := alpha) (C := C) halpha)

end

end Palomar
end SharpIntermediateSubgroupBounds
