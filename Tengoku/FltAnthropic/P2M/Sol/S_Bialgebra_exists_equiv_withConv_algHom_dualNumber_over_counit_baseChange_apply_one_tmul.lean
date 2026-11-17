import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Bialgebra_exists_equiv_withConv_algHom_dualNumber_over_counit_baseChange_apply_one_tmul

set_option autoImplicit false

open scoped TensorProduct

namespace A4TensorHom

variable (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
  (H : Type) [CommRing H] [Bialgebra R H]

noncomputable def beta0 : WithConv (H →ₐ[R] DualNumber k) ≃ (k ⊗[R] H →ₐ[k] DualNumber k) :=
  (WithConv.equiv (H →ₐ[R] DualNumber k)).trans (AlgHom.liftEquiv R k H (DualNumber k))

/--
@isnad1 id=eq.0h6v.s11.972ebaeb1458 from=translated src=- shape=36eeb6cc vocab=ca999b27
-/
theorem beta0_tmul (D : WithConv (H →ₐ[R] DualNumber k)) (s : k) (h : H) :
    beta0 R k H D (s ⊗ₜ[R] h) = s • D.ofConv h := rfl

/--
@isnad1 id=eq.0h5v.s11.a2e31da59f34 from=translated src=- shape=3064d402 vocab=3627fd98
-/
theorem beta0_one_tmul (D : WithConv (H →ₐ[R] DualNumber k)) (h : H) :
    beta0 R k H D ((1 : k) ⊗ₜ[R] h) = D.ofConv h := by
  rw [beta0_tmul, one_smul]

/--
@isnad1 id=iff.0h4v.s11.babd5593ca63 from=translated src=- shape=9c42d980 vocab=581e5e54
-/
theorem over_counit_iff (D : WithConv (H →ₐ[R] DualNumber k)) :
    (∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)) ↔
    ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (beta0 R k H D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b := by
  constructor
  · intro hD b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul s h =>
        rw [beta0_tmul, TrivSqZeroExt.fst_smul, hD h]
        simp only [Bialgebra.counitAlgHom_apply]
        rw [TensorProduct.counit_tmul, CommSemiring.counit_apply, smul_eq_mul, Algebra.smul_def, mul_comm]
    | add x y hx hy => rw [map_add, TrivSqZeroExt.fst_add, hx, hy, map_add]
  · intro hD h
    have := hD ((1 : k) ⊗ₜ[R] h)
    rw [beta0_one_tmul, Bialgebra.counitAlgHom_apply, TensorProduct.counit_tmul,
      CommSemiring.counit_apply] at this
    rw [this, Bialgebra.counitAlgHom_apply, Algebra.smul_def, mul_one]

noncomputable def beta :
    {D : WithConv (H →ₐ[R] DualNumber k) //
        ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
      {D : k ⊗[R] H →ₐ[k] DualNumber k //
        ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b} :=
  (beta0 R k H).subtypeEquiv (over_counit_iff R k H)

end A4TensorHom

open A4TensorHom in
/--
@isnad1 id=ex.0h3v.s14.35590e49e94b from=translated src=- shape=07c05479 vocab=5ba64db2
-/
theorem solution
    (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k]
    (H : Type) [CommRing H] [Bialgebra R H] :
    ∃ β : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)} ≃
          {D : k ⊗[R] H →ₐ[k] DualNumber k //
            ∀ b : k ⊗[R] H, TrivSqZeroExt.fst (D b) = Bialgebra.counitAlgHom k (k ⊗[R] H) b},
      ∀ (D : {D : WithConv (H →ₐ[R] DualNumber k) //
            ∀ h : H, TrivSqZeroExt.fst (D.ofConv h) = algebraMap R k (Bialgebra.counitAlgHom R H h)})
        (h : H), (β D).1 ((1 : k) ⊗ₜ[R] h) = D.1.ofConv h :=
  ⟨beta R k H, fun D h => beta0_one_tmul R k H D.1 h⟩
