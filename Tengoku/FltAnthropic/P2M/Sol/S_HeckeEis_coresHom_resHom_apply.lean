import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coresHom_resHom_apply.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coresHom_resHom_apply

open Subgroup

/--
@isnad1 id=eq.0h5v.s12.73700adb306b from=translated src=- shape=238fc22e vocab=93837408
-/
theorem solution {G : Type*} [Group G] (H : Subgroup G) {A : Type*}
    [AddCommGroup A] [H.FiniteIndex] (φ : Additive G →+ A) (g : G) :
    HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g) =
      H.index • φ (Additive.ofMul g) := by
  letI := H.fintypeQuotientOfFiniteIndex
  have hmul : ∀ x y : G, φ (Additive.ofMul (x * y)) =
      φ (Additive.ofMul x) + φ (Additive.ofMul y) := fun x y => by rw [ofMul_mul, map_add]
  have hinv : ∀ x : G, φ (Additive.ofMul x⁻¹) = -φ (Additive.ofMul x) := fun x => by
    rw [ofMul_inv, map_neg]
  have hreindex := (MulAction.bijective g).sum_comp
    (fun q : G ⧸ H => φ (Additive.ofMul (Quotient.out q)))
  calc HeckeEis.coresHom H (HeckeEis.resHom H φ) (Additive.ofMul g)
      = ∑ q : G ⧸ H, φ (Additive.ofMul ((HeckeEis.transferAux H g q : G))) := rfl
    _ = ∑ q : G ⧸ H, (-φ (Additive.ofMul (g • q).out) +
          (φ (Additive.ofMul g) + φ (Additive.ofMul q.out))) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [HeckeEis.coe_transferAux, hmul, hmul, hinv]
    _ = -(∑ q : G ⧸ H, φ (Additive.ofMul (g • q).out)) +
          ((Fintype.card (G ⧸ H)) • φ (Additive.ofMul g) +
            ∑ q : G ⧸ H, φ (Additive.ofMul q.out)) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib,
          Finset.sum_const, Finset.card_univ]
    _ = H.index • φ (Additive.ofMul g) := by
        rw [hreindex, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
        abel
