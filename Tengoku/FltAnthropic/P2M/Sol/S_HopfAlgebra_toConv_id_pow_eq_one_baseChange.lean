import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_toConv_id_pow_eq_one_baseChange.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_toConv_id_pow_eq_one_baseChange

set_option autoImplicit false

universe u v w

namespace HopfAlgebra
namespace UniversalPointBC
open _root_.HopfAlgebra

open scoped TensorProduct

variable {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
variable {H : Type v} [CommRing H] [HopfAlgebra R H]

noncomputable abbrev bc (u : H →ₐ[R] H) : R' ⊗[R] H →ₐ[R'] R' ⊗[R] H :=
  Algebra.TensorProduct.map (AlgHom.id R' R') u

/--
@isnad1 id=eq.0h7v.s12.70e3d97efef8 from=translated src=- shape=509e16c2 vocab=555936f3
-/
theorem convMul_bc_tmul (u v : WithConv (H →ₐ[R] H)) (s : R') (h : H) :
    (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) =
      s ⊗ₜ[R] (u * v).ofConv h := by
  classical
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
  let ρ := Coalgebra.Repr.arbitrary R h
  rw [← ρ.eq]
  change (Algebra.TensorProduct.lift (bc R' u.ofConv) (bc R' v.ofConv) _)
      ((TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R' R R' R' R' H H)
        ((1 ⊗ₜ[R'] s) ⊗ₜ[R] ∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)) =
    s ⊗ₜ[R] (Algebra.TensorProduct.lift u.ofConv v.ofConv _) (∑ i ∈ ρ.index, ρ.left i ⊗ₜ[R] ρ.right i)
  rw [TensorProduct.tmul_sum, map_sum, map_sum, map_sum, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp [bc, Algebra.TensorProduct.tmul_mul_tmul]

/--
@isnad1 id=eq.0h5v.s12.1ba13a35c49b from=translated src=- shape=418a0d85 vocab=c96b5ae2
-/
theorem convMul_bc (u v : WithConv (H →ₐ[R] H)) :
    WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv) =
      WithConv.toConv (bc R' (u * v).ofConv) := by
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  change (WithConv.toConv (bc R' u.ofConv) * WithConv.toConv (bc R' v.ofConv)).ofConv (s ⊗ₜ[R] h) =
    (bc R' (u * v).ofConv) (s ⊗ₜ[R] h)
  rw [convMul_bc_tmul]
  simp [bc]

/--
@isnad1 id=eq.0h3v.s11.b85c5193a43a from=translated src=- shape=6f869944 vocab=c8c28101
-/
theorem convOne_bc :
    (1 : WithConv (R' ⊗[R] H →ₐ[R'] R' ⊗[R] H)) =
      WithConv.toConv (bc R' (1 : WithConv (H →ₐ[R] H)).ofConv) := by
  apply WithConv.ext
  apply AlgHom.toLinearMap_injective
  apply TensorProduct.AlgebraTensorModule.ext
  intro s h
  rw [AlgHom.convOne_def, AlgHom.convOne_def]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (s ⊗ₜ[R] h)) =
    s ⊗ₜ[R] algebraMap R H (Coalgebra.counit h)
  rw [TensorProduct.counit_tmul]
  change algebraMap R' (R' ⊗[R] H) (Coalgebra.counit (R := R) h • s) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

/--
@isnad1 id=eq.0h5v.s11.ac5f73282079 from=translated src=- shape=f782a70b vocab=d1935c20
-/
theorem pow_bc (u : WithConv (H →ₐ[R] H)) (k : ℕ) :
    (WithConv.toConv (bc R' u.ofConv)) ^ k = WithConv.toConv (bc R' (u ^ k).ofConv) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, convOne_bc]
  | succ k ih => rw [pow_succ, pow_succ, ih, convMul_bc]

end HopfAlgebra.UniversalPointBC

open scoped TensorProduct in
open HopfAlgebra.UniversalPointBC in
/--
@isnad1 id=eq.1h4v.s12.448fb65ac63b from=translated src=- shape=1df9023e vocab=fe8d521e
-/
theorem solution
    {R : Type u} [CommRing R] (R' : Type w) [CommRing R'] [Algebra R R']
    {H : Type v} [CommRing H] [HopfAlgebra R H] (m : ℕ)
    (h : (WithConv.toConv (AlgHom.id R H)) ^ m = 1) :
    (WithConv.toConv (AlgHom.id R' (TensorProduct R R' H))) ^ m = 1 := by
  have hid : AlgHom.id R' (R' ⊗[R] H) = bc R' (WithConv.toConv (AlgHom.id R H)).ofConv := by
    change AlgHom.id R' (R' ⊗[R] H) = Algebra.TensorProduct.map (AlgHom.id R' R') (AlgHom.id R H)
    exact Algebra.TensorProduct.map_id.symm
  rw [hid]
  change (WithConv.toConv (bc R' (WithConv.toConv (AlgHom.id R H)).ofConv)) ^ m = 1
  rw [pow_bc, h, ← convOne_bc]
