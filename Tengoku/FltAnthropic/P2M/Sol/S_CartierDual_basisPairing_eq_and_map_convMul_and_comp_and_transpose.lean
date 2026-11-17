import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDualInstances

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CartierDual_basisPairing_eq_and_map_convMul_and_comp_and_transpose

set_option autoImplicit false

open scoped TensorProduct

namespace CartierPairingLaws

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A]

section Canonical

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {L : Type*} [CommRing L] [Algebra R L]

/--
@isnad1 id=eq.0h4v.s11.70e31d3b7e48 from=translated src=- shape=45afc6d7 vocab=f53a8249
-/
theorem dualTensorHom_sum_coord_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι R A) :
    dualTensorHom R A A (∑ i, b.coord i ⊗ₜ[R] b i) = LinearMap.id := by
  classical
  apply LinearMap.ext
  intro m
  rw [map_sum, LinearMap.sum_apply, LinearMap.id_apply]
  simp_rw [dualTensorHom_apply, Module.Basis.coord_apply]
  rw [b.sum_repr m]

/--
@isnad1 id=eq.0h6v.s11.d6c57cc3eb8f from=translated src=- shape=ad186c25 vocab=b601c9fc
-/
theorem sum_coord_tmul_eq {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A) :
    (∑ i, b.coord i ⊗ₜ[R] b i) = ∑ j, b'.coord j ⊗ₜ[R] b' j := by
  classical
  apply (dualTensorHomEquivOfBasis (N := A) b).injective
  rw [dualTensorHomEquivOfBasis_apply, dualTensorHomEquivOfBasis_apply, dualTensorHom_sum_coord_tmul,
    dualTensorHom_sum_coord_tmul]

/--
@isnad1 id=eq.0h7v.s12.e4dcc596f081 from=translated src=- shape=ce616f12 vocab=f2ef5786
-/
theorem sum_eq_mul'_map {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L) :
    ∑ i, f (b i) * Ψ (b.coord i) =
      LinearMap.mul' R L (TensorProduct.map Ψ f (∑ i, b.coord i ⊗ₜ[R] b i)) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [TensorProduct.map_tmul, LinearMap.mul'_apply, mul_comm]

/--
@isnad1 id=eq.0h9v.s11.a62e2793f91b from=translated src=- shape=6ef70ebd vocab=5c0b016b
-/
theorem indep {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A)
    (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L) :
    ∑ i, f (b i) * Ψ (b.coord i) = ∑ j, f (b' j) * Ψ (b'.coord j) := by
  rw [sum_eq_mul'_map b f Ψ, sum_eq_mul'_map b' f Ψ, sum_coord_tmul_eq b b']

/--
@isnad1 id=eq.0h9v.s11.61b4bb119df7 from=translated src=- shape=65059169 vocab=615fa4c7
-/
theorem natural {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    {L' : Type*} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
    (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L) :
    φ (∑ i, f (b i) * Ψ (b.coord i)) = ∑ i, φ (f (b i)) * φ (Ψ (b.coord i)) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]

/--
@isnad1 id=eq.3h14v.s12.9ce0af63e6e0 from=translated src=- shape=c7eefe5c vocab=c7a84694
-/
theorem transpose {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    {A' : Type*} [AddCommGroup A'] [Module R A'] {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A')
    (t : A' →ₗ[R] A) (ht : Function.Surjective t) (N : A' →ₗ[R] A')
    (u : Module.Dual R A' →ₗ[R] Module.Dual R A)
    (hu : ∀ (φ' : Module.Dual R A') (a' : A'), u φ' (t a') = φ' (N a'))
    (f : A →ₗ[R] L) (F : A' →ₗ[R] L) (hF : ∀ a' : A', F (N a') = f (t a'))
    (Ψ : Module.Dual R A →ₗ[R] L) :
    ∑ k, F (b' k) * Ψ (u (b'.coord k)) = ∑ i, f (b i) * Ψ (b.coord i) := by
  classical

  choose a ha using fun i => ht (b i)

  have hexp : ∀ k, u (b'.coord k) = ∑ i, (b'.coord k) (N (a i)) • b.coord i := by
    intro k
    conv_lhs => rw [← b.sum_dual_apply_smul_coord (u (b'.coord k))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, hu]

  have hΨ : ∀ k, Ψ (u (b'.coord k)) = ∑ i, (b'.coord k) (N (a i)) • Ψ (b.coord i) := by
    intro k
    rw [hexp k, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  simp_rw [hΨ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_

  have hcollect : ∑ k, F (b' k) * ((b'.coord k) (N (a i)) • Ψ (b.coord i)) =
      F (∑ k, (b'.coord k) (N (a i)) • b' k) * Ψ (b.coord i) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, mul_smul_comm, smul_mul_assoc]
  rw [hcollect]
  have hsum : ∑ k, (b'.coord k) (N (a i)) • b' k = N (a i) := by
    simp_rw [Module.Basis.coord_apply]
    exact b'.sum_repr (N (a i))
  rw [hsum, hF, ha]

end Canonical

section MulLeft

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {L : Type*} [CommRing L] [Algebra R L]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)

noncomputable def cst (i : ι) (x : ι × ι) : R := (b.tensorProduct b).repr (Coalgebra.comul (R := R) (b i)) x

/--
@isnad1 id=eq.0h5v.s10.0f97471a4ce7 from=translated src=- shape=7228b3b3 vocab=ac4b1513
-/
theorem comul_basis_eq (i : ι) :
    Coalgebra.comul (R := R) (b i) = ∑ x : ι × ι, cst b i x • (b x.1 ⊗ₜ[R] b x.2) := by
  conv_lhs => rw [← (b.tensorProduct b).sum_repr (Coalgebra.comul (R := R) (b i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Module.Basis.tensorProduct_apply']
  rfl

/--
@isnad1 id=eq.0h8v.s9.2888e59581a9 from=translated src=- shape=a1b635ee vocab=4e08c1f4
-/
theorem convMul_basis (f g : WithConv (A →ₐ[R] L)) (i : ι) :
    (f * g) (b i) = ∑ x : ι × ι, cst b i x • (f (b x.1) * g (b x.2)) := by
  rw [AlgHom.convMul_apply, comul_basis_eq b i, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, Algebra.TensorProduct.lift_tmul]

/--
@isnad1 id=eq.0h6v.s8.d089551d2192 from=translated src=- shape=fef36a87 vocab=a7f759ca
-/
theorem coord_basis [DecidableEq ι] (i j : ι) : b.coord i (b j) = if j = i then 1 else 0 := by
  rw [Module.Basis.coord_apply, b.repr_self, Finsupp.single_apply]

/--
@isnad1 id=eq.0h7v.s11.579a31a29ae3 from=translated src=- shape=1460ad47 vocab=e2a813fd
-/
theorem coord_mul_coord_basis [DecidableEq ι] (j k i : ι) :
    (CartierDual.ofDual R A (b.coord j) * CartierDual.ofDual R A (b.coord k)) (b i) = cst b i (j, k) := by
  rw [CartierDual.mul_apply, CartierDual.toDual_ofDual, CartierDual.toDual_ofDual, comul_basis_eq b i,
    map_sum]
  simp_rw [map_smul, TensorProduct.dualDistrib_apply, coord_basis b, mul_ite, mul_one, mul_zero,
    smul_eq_mul]
  rw [Finset.sum_eq_single (j, k)]
  · simp
  · rintro ⟨j', k'⟩ - hne
    by_cases hj : j' = j
    · subst hj
      have hk : k' ≠ k := fun h => hne (by rw [h])
      simp [hk]
    · simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/--
@isnad1 id=eq.0h6v.s11.97a13c59e05a from=translated src=- shape=73805966 vocab=d6092721
-/
theorem coord_mul_coord [DecidableEq ι] (j k : ι) :
    CartierDual.ofDual R A (b.coord j) * CartierDual.ofDual R A (b.coord k) =
      ∑ i, cst b i (j, k) • CartierDual.ofDual R A (b.coord i) := by
  apply (CartierDual.toDual R A).injective
  apply b.ext
  intro i'
  rw [CartierDual.toDual_apply, coord_mul_coord_basis b j k i', map_sum, LinearMap.sum_apply]
  simp_rw [map_smul, LinearMap.smul_apply, CartierDual.toDual_ofDual, coord_basis b, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ i']
  simp

/--
@isnad1 id=eq.0h8v.s12.5ee328ccc786 from=translated src=- shape=eee098b6 vocab=ad142ec5
-/
theorem mul_left [DecidableEq ι] (f g : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L) :
    ∑ i, (f * g) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
      (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
        ∑ i, g (b i) * ψ (CartierDual.ofDual R A (b.coord i)) := by

  rw [Finset.sum_mul_sum]
  have hrhs : ∀ j k, f (b j) * ψ (CartierDual.ofDual R A (b.coord j)) *
      (g (b k) * ψ (CartierDual.ofDual R A (b.coord k))) =
        ∑ i, cst b i (j, k) • (f (b j) * g (b k) * ψ (CartierDual.ofDual R A (b.coord i))) := by
    intro j k
    have hψ : ψ (CartierDual.ofDual R A (b.coord j)) * ψ (CartierDual.ofDual R A (b.coord k)) =
        ∑ i, cst b i (j, k) • ψ (CartierDual.ofDual R A (b.coord i)) := by
      rw [← map_mul, coord_mul_coord b j k, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    calc f (b j) * ψ (CartierDual.ofDual R A (b.coord j)) * (g (b k) * ψ (CartierDual.ofDual R A (b.coord k)))
        = f (b j) * g (b k) *
            (ψ (CartierDual.ofDual R A (b.coord j)) * ψ (CartierDual.ofDual R A (b.coord k))) := by ring
      _ = ∑ i, cst b i (j, k) • (f (b j) * g (b k) * ψ (CartierDual.ofDual R A (b.coord i))) := by
          rw [hψ, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [mul_smul_comm]
  simp_rw [hrhs]

  calc ∑ i, (f * g) (b i) * ψ (CartierDual.ofDual R A (b.coord i))
      = ∑ i, ∑ x : ι × ι, cst b i x • (f (b x.1) * g (b x.2) * ψ (CartierDual.ofDual R A (b.coord i))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [convMul_basis b f g i, Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [smul_mul_assoc]
    _ = ∑ x : ι × ι, ∑ i, cst b i x • (f (b x.1) * g (b x.2) * ψ (CartierDual.ofDual R A (b.coord i))) :=
        Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, cst b i (j, k) •
          (f (b j) * g (b k) * ψ (CartierDual.ofDual R A (b.coord i))) := by
        rw [Fintype.sum_prod_type]

end MulLeft

section MulRight

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {L : Type*} [CommRing L] [Algebra R L]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)

/--
@isnad1 id=eq.0h7v.s11.e8b4f1480510 from=translated src=- shape=4bee4009 vocab=61a5c7f5
-/
theorem repr_mul_eq (a a' : A) (i : ι) :
    b.repr (a * a') i = ∑ x : ι × ι, b.repr (b x.1 * b x.2) i * (b.repr a x.1 * b.repr a' x.2) := by
  have hmul : a * a' = ∑ x : ι × ι, (b.repr a x.1 * b.repr a' x.2) • (b x.1 * b x.2) := by
    conv_lhs => rw [← b.sum_repr a, ← b.sum_repr a']
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [smul_mul_smul_comm]
  have h := congrArg (b.coord i) hmul
  rw [map_sum] at h
  simp_rw [map_smul, Module.Basis.coord_apply, smul_eq_mul] at h
  rw [h]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/--
@isnad1 id=eq.0h5v.s12.77dfecf26ae2 from=translated src=- shape=e96e4c03 vocab=5d2ee383
-/
theorem comul_coordDual (i : ι) :
    Coalgebra.comul (R := R) (CartierDual.ofDual R A (b.coord i)) =
      ∑ x : ι × ι, (b.repr (b x.1 * b x.2) i • CartierDual.ofDual R A (b.coord x.1)) ⊗ₜ[R]
        CartierDual.ofDual R A (b.coord x.2) := by
  apply CartierDual.tmul_eq_of_pairing_eq
  intro a a'
  rw [CartierDual.comul_pairing, CartierDual.ofDual_apply, Module.Basis.coord_apply, repr_mul_eq b a a' i,
    map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [TensorProduct.map_tmul, LinearEquiv.coe_toLinearMap, map_smul,
    CartierDual.toDual_ofDual, CartierDual.toDual_ofDual, TensorProduct.dualDistrib_apply, LinearMap.smul_apply,
    Module.Basis.coord_apply, Module.Basis.coord_apply, smul_eq_mul, mul_assoc]

/--
@isnad1 id=eq.0h8v.s12.f4ff360a08ac from=translated src=- shape=316ea34b vocab=8796a011
-/
theorem convMul_coordDual (ψ ψ' : WithConv (CartierDual R A →ₐ[R] L)) (i : ι) :
    (ψ * ψ') (CartierDual.ofDual R A (b.coord i)) =
      ∑ x : ι × ι, b.repr (b x.1 * b x.2) i •
        (ψ (CartierDual.ofDual R A (b.coord x.1)) * ψ' (CartierDual.ofDual R A (b.coord x.2))) := by
  rw [AlgHom.convMul_apply]

  erw [comul_coordDual b i]
  erw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  erw [Algebra.TensorProduct.lift_tmul]
  rw [map_smul, smul_mul_assoc]

/--
@isnad1 id=eq.0h8v.s12.457efd30d562 from=translated src=- shape=5b230bad vocab=edc23637
-/
theorem mul_right (f : A →ₐ[R] L) (ψ ψ' : WithConv (CartierDual R A →ₐ[R] L)) :
    ∑ i, f (b i) * (ψ * ψ') (CartierDual.ofDual R A (b.coord i)) =
      (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
        ∑ i, f (b i) * ψ' (CartierDual.ofDual R A (b.coord i)) := by
  calc ∑ i, f (b i) * (ψ * ψ') (CartierDual.ofDual R A (b.coord i))
      = ∑ i, ∑ x : ι × ι, b.repr (b x.1 * b x.2) i •
          (f (b i) * (ψ (CartierDual.ofDual R A (b.coord x.1)) * ψ' (CartierDual.ofDual R A (b.coord x.2)))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [convMul_coordDual b ψ ψ' i, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [mul_smul_comm]
    _ = ∑ x : ι × ι, ∑ i, b.repr (b x.1 * b x.2) i •
          (f (b i) * (ψ (CartierDual.ofDual R A (b.coord x.1)) * ψ' (CartierDual.ofDual R A (b.coord x.2)))) :=
        Finset.sum_comm
    _ = ∑ x : ι × ι, f (b x.1 * b x.2) *
          (ψ (CartierDual.ofDual R A (b.coord x.1)) * ψ' (CartierDual.ofDual R A (b.coord x.2))) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have hf : f (b x.1 * b x.2) = ∑ i, b.repr (b x.1 * b x.2) i • f (b i) := by
          conv_lhs => rw [← b.sum_repr (b x.1 * b x.2)]
          rw [map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_smul]
        rw [hf, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc]
    _ = ∑ j, ∑ k, f (b j) * ψ (CartierDual.ofDual R A (b.coord j)) *
          (f (b k) * ψ' (CartierDual.ofDual R A (b.coord k))) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul]
        ring
    _ = (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
          ∑ i, f (b i) * ψ' (CartierDual.ofDual R A (b.coord i)) := by
        rw [Finset.sum_mul_sum]

end MulRight

section Units

variable [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {L : Type*} [CommRing L] [Algebra R L]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)

/--
@isnad1 id=eq.0h6v.s10.06a5d2535b7e from=translated src=- shape=1e3c8382 vocab=edc23637
-/
theorem unit_left (ψ : CartierDual R A →ₐ[R] L) :
    ∑ i, (1 : WithConv (A →ₐ[R] L)) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) = 1 := by
  have hterm : ∀ i, (1 : WithConv (A →ₐ[R] L)) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
      ψ (Coalgebra.counit (R := R) (b i) • CartierDual.ofDual R A (b.coord i)) := by
    intro i
    rw [AlgHom.convOne_apply, map_smul, Algebra.smul_def]
  simp_rw [hterm]
  rw [← map_sum]
  have hsum : ∑ i, Coalgebra.counit (R := R) (b i) • CartierDual.ofDual R A (b.coord i) =
      CartierDual.ofDual R A (Coalgebra.counit (R := R) (A := A)) := by
    conv_rhs => rw [← b.sum_dual_apply_smul_coord (Coalgebra.counit (R := R) (A := A))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
  rw [hsum, ← CartierDual.one_def, map_one]

/--
@isnad1 id=eq.0h6v.s10.e72828d36c76 from=translated src=- shape=ff3040f3 vocab=edc23637
-/
theorem unit_right (f : A →ₐ[R] L) :
    ∑ i, f (b i) * (1 : WithConv (CartierDual R A →ₐ[R] L)) (CartierDual.ofDual R A (b.coord i)) = 1 := by
  have hterm : ∀ i, f (b i) * (1 : WithConv (CartierDual R A →ₐ[R] L)) (CartierDual.ofDual R A (b.coord i)) =
      f (b.repr 1 i • b i) := by
    intro i
    rw [AlgHom.convOne_apply]
    erw [CartierDual.counit_apply]
    rw [CartierDual.ofDual_apply, Module.Basis.coord_apply, map_smul, Algebra.smul_def, mul_comm]
  simp_rw [hterm]
  rw [← map_sum, b.sum_repr, map_one]

/--
@isnad1 id=eq.0h8v.s11.2d02d8c02747 from=translated src=- shape=90859b6c vocab=a2f386c1
-/
theorem torsion [DecidableEq ι] (f : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L) (n : ℕ) :
    ∑ i, (f ^ n) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
      (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    exact unit_left b ψ
  | succ n ih =>
    rw [pow_succ, pow_succ, mul_left b (f ^ n) f ψ, ih]

end Units

end CartierPairingLaws

/--
@isnad1 id=and.0h5v.s15.311daeb8dbb8 from=translated src=- shape=ce25aed0 vocab=1eba0391
-/
theorem solution
    {R : Type*} [CommRing R] {A : Type*} [CommRing A] [HopfAlgebra R A]
    [Module.Finite R A] [Module.Free R A]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    (L : Type*) [CommRing L] [Algebra R L] :

    (∀ {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A)
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ i, f (b i) * Ψ (b.coord i) = ∑ j, f (b' j) * Ψ (b'.coord j)) ∧

    (∀ {L' : Type*} [CommRing L'] [Algebra R L'] (φ : L →ₐ[R] L')
        (f : A →ₗ[R] L) (Ψ : Module.Dual R A →ₗ[R] L),
        φ (∑ i, f (b i) * Ψ (b.coord i)) = ∑ i, φ (f (b i)) * φ (Ψ (b.coord i))) ∧

    (∀ {A' : Type*} [AddCommGroup A'] [Module R A'] {ι' : Type*} [Fintype ι'] (b' : Module.Basis ι' R A')
        (t : A' →ₗ[R] A) (_ : Function.Surjective t) (N : A' →ₗ[R] A')
        (u : Module.Dual R A' →ₗ[R] Module.Dual R A) (_ : ∀ (φ' : Module.Dual R A') (a' : A'), u φ' (t a') = φ' (N a'))
        (f : A →ₗ[R] L) (F : A' →ₗ[R] L) (_ : ∀ a' : A', F (N a') = f (t a'))
        (Ψ : Module.Dual R A →ₗ[R] L),
        ∑ k, F (b' k) * Ψ (u (b'.coord k)) = ∑ i, f (b i) * Ψ (b.coord i)) ∧

    (∀ (f g : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L),
        ∑ i, (f * g) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, g (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ (f : A →ₐ[R] L) (ψ ψ' : WithConv (CartierDual R A →ₐ[R] L)),
        ∑ i, f (b i) * (ψ * ψ') (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) *
            ∑ i, f (b i) * ψ' (CartierDual.ofDual R A (b.coord i))) ∧

    (∀ ψ : CartierDual R A →ₐ[R] L,
        ∑ i, (1 : WithConv (A →ₐ[R] L)) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) = 1) ∧
    (∀ f : A →ₐ[R] L,
        ∑ i, f (b i) * (1 : WithConv (CartierDual R A →ₐ[R] L)) (CartierDual.ofDual R A (b.coord i)) = 1) ∧

    (∀ (f : WithConv (A →ₐ[R] L)) (ψ : CartierDual R A →ₐ[R] L) (n : ℕ),
        ∑ i, (f ^ n) (b i) * ψ (CartierDual.ofDual R A (b.coord i)) =
          (∑ i, f (b i) * ψ (CartierDual.ofDual R A (b.coord i))) ^ n) := by
  classical
  refine ⟨fun {ι'} _ b' f Ψ => CartierPairingLaws.indep b b' f Ψ,
    fun {L'} _ _ φ f Ψ => CartierPairingLaws.natural b φ f Ψ,
    fun {A'} _ _ {ι'} _ b' t ht N u hu f F hF Ψ => CartierPairingLaws.transpose b b' t ht N u hu f F hF Ψ,
    fun f g ψ => CartierPairingLaws.mul_left b f g ψ,
    fun f ψ ψ' => CartierPairingLaws.mul_right b f ψ ψ',
    fun ψ => CartierPairingLaws.unit_left b ψ,
    fun f => CartierPairingLaws.unit_right b f,
    fun f ψ n => CartierPairingLaws.torsion b f ψ n⟩
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
