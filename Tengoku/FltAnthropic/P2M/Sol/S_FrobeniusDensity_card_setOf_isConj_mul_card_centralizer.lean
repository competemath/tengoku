import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusDensity_card_setOf_isConj_mul_card_centralizer

set_option autoImplicit false

open scoped Classical

namespace FltWs24
namespace RationalClass

variable {G : Type*} [Group G]

/--
@isnad1 id=eq.0h2v.s5.8028b9006a81 from=translated src=- shape=d6907dc7 vocab=949f903d
-/
theorem setOf_isConj_eq_orbit_conjAct (σ : G) : {τ : G | IsConj σ τ} = MulAction.orbit (ConjAct G) σ := by
  ext τ
  rw [ConjAct.orbit_eq_carrier_conjClasses, Set.mem_ofPred_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

/--
@isnad1 id=eq.0h2v.s6.521ab2c3b8f9 from=translated src=- shape=ae101d4a vocab=7a131de5
-/
theorem card_stabilizer_conjAct_eq_card_centralizer (σ : G) :
    Nat.card (MulAction.stabilizer (ConjAct G) σ) = Nat.card (Subgroup.centralizer ({σ} : Set G)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv ConjAct.ofConjAct.toEquiv fun g => ?_)
  show g ∈ MulAction.stabilizer (ConjAct G) σ ↔ ConjAct.ofConjAct g ∈ Subgroup.centralizer ({σ} : Set G)
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_singleton_iff, ConjAct.smul_def]
  rw [mul_inv_eq_iff_eq_mul]

/--
@isnad1 id=eq.0h2v.s5.bc0439bf028b from=translated src=- shape=254aa539 vocab=e16b9aae
-/
theorem card_setOf_isConj_mul_card_centralizer (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G := by
  rw [setOf_isConj_eq_orbit_conjAct, ← card_stabilizer_conjAct_eq_card_centralizer,
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) σ),
    ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  rfl

end FltWs24.RationalClass

/--
@isnad1 id=eq.0h2v.s5.bc0439bf028b from=translated src=- shape=254aa539 vocab=e16b9aae
-/
theorem solution {G : Type*} [Group G] (σ : G) :
    Nat.card {τ : G | IsConj σ τ} * Nat.card (Subgroup.centralizer ({σ} : Set G)) = Nat.card G :=
  FltWs24.RationalClass.card_setOf_isConj_mul_card_centralizer σ
