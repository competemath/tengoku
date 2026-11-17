import Tengoku.FltAnthropic.Definitions.Def_Gamma0HeckeOperatorHom
import Tengoku.Seed.GroupTheory.Transfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_coresHom_eq_transfer.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_coresHom_eq_transfer

set_option autoImplicit false

namespace INH
namespace SolB0

open Subgroup Subgroup.leftTransversals

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
variable {A : Type*} [AddCommGroup A]

omit [H.FiniteIndex] in

theorem default_leftQuotientEquiv_apply (q : G ⧸ H) :
    ((default : H.LeftTransversal).2.leftQuotientEquiv q : G) = q.out :=
  IsComplement.leftQuotientEquiv_apply Quotient.out_eq' q

omit [H.FiniteIndex] in

theorem smul_default_leftQuotientEquiv_apply (g : G) (q : G ⧸ H) :
    ((g • (default : H.LeftTransversal)).2.leftQuotientEquiv q : G) = g * (g⁻¹ • q).out := by
  rw [smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  congr 1
  exact default_leftQuotientEquiv_apply H (g⁻¹ • q)

theorem solution_aux (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) := by
  letI := H.fintypeQuotientOfFiniteIndex
  ext g
  set g' := Additive.toMul g

  show (∑ q : G ⧸ H, φ (Additive.ofMul (HeckeEis.transferAux H g' q)))
    = Multiplicative.toAdd
        (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ) g')

  rw [MonoidHom.transfer_def (AddMonoidHom.toMultiplicativeRight φ) (g'⁻¹ • default),
    smul_inv_smul]
  unfold Subgroup.leftTransversals.diff
  simp only [toAdd_prod, AddMonoidHom.toMultiplicativeRight_apply_apply, toAdd_ofAdd]
  refine Finset.sum_congr rfl (fun q _ => congr_arg φ (congr_arg Additive.ofMul (Subtype.ext ?_)))
  simp only [HeckeEis.coe_transferAux, default_leftQuotientEquiv_apply,
    smul_default_leftQuotientEquiv_apply, inv_inv, mul_inv_rev, mul_assoc]

end INH.SolB0

theorem solution {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]
    {A : Type*} [AddCommGroup A] (φ : Additive ↥H →+ A) :
    HeckeEis.coresHom (H := H) φ
      = MonoidHom.toAdditiveLeft
          (MonoidHom.transfer (AddMonoidHom.toMultiplicativeRight φ)) :=
  INH.SolB0.solution_aux H φ

