import Tengoku.Seed.RingTheory.Flat.FaithfullyFlat.Basic
import Tengoku.Seed.RingTheory.TensorProduct.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Amitsur exactness in degree ≤ 1 for faithfully flat algebras

For a faithfully flat `R`-algebra `S`, the sequence

  `0 → R → S → S ⊗[R] S`,  `x ↦ 1 ⊗ x - x ⊗ 1`

is exact: an element of `S` whose two tensor-inclusions into `S ⊗[R] S` agree lies
in the image of `R`. This is the degree-`≤ 1` part of the Amitsur complex, i.e.
faithfully flat descent for *elements* (sections of the structure sheaf), and is the
algebraic engine behind descent of morphisms into affine schemes along faithfully
flat covers.

The proof is the classical one: after applying `S ⊗[R] -` the sequence acquires a
contracting homotopy (multiplication of the first two tensor factors), so it is
exact; faithful flatness reflects exactness (`Module.FaithfullyFlat.lTensor_reflects_exact`).
-/

namespace ModularCurves

open TensorProduct

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]

/-- The degree-one Amitsur coboundary `x ↦ 1 ⊗ x - x ⊗ 1`, as an `R`-linear map.-/
noncomputable def amitsurD : S →ₗ[R] S ⊗[R] S :=
  TensorProduct.mk R S S 1 - (TensorProduct.mk R S S).flip 1

/--
@isnad1 id=eq.0h3v.s9.73ba9b722824 from=translated src=- shape=f0cb0afd vocab=ce49aa6f
-/
@[simp] theorem amitsurD_apply (x : S) :
    amitsurD R S x = (1 : S) ⊗ₜ[R] x - x ⊗ₜ[R] (1 : S) := rfl

/-- The contraction `a ⊗ (x ⊗ y) ↦ (a * x) ⊗ y` of the first two tensor factors.-/
noncomputable def amitsurContract : S ⊗[R] (S ⊗[R] S) →ₗ[R] S ⊗[R] S :=
  TensorProduct.lift
    { toFun := fun a => LinearMap.rTensor S (LinearMap.mul R S a)
      map_add' := fun a b => by
        ext x y
        simp [LinearMap.rTensor, add_mul, TensorProduct.add_tmul]
      map_smul' := fun r a => by
        ext x y
        simp [LinearMap.rTensor, Algebra.smul_mul_assoc,
          TensorProduct.smul_tmul'] }

/--
@isnad1 id=eq.0h5v.s10.bafad9528e87 from=translated src=- shape=8e6f0b9a vocab=d4303123
-/
@[simp] theorem amitsurContract_tmul (a x y : S) :
    amitsurContract R S (a ⊗ₜ[R] (x ⊗ₜ[R] y)) = (a * x) ⊗ₜ[R] y := rfl

/-- The multiplication map `S ⊗[R] S →ₗ[R] S`.-/
noncomputable def amitsurMul : S ⊗[R] S →ₗ[R] S :=
  TensorProduct.lift (LinearMap.mul R S)

/--
@isnad1 id=eq.0h4v.s9.5782cb0100bc from=translated src=- shape=c0deb73f vocab=5da3d662
-/
@[simp] theorem amitsurMul_tmul (x y : S) :
    amitsurMul R S (x ⊗ₜ[R] y) = x * y := rfl

/-- The contracting-homotopy identity: contracting the tensored coboundary of `t`
recovers `t` minus the retraction `(μ t) ⊗ 1`.
@isnad1 id=eq.0h3v.s12.e6790f27468e from=translated src=- shape=c8d7db9b vocab=999f75d2
-/
theorem amitsurContract_lTensor_amitsurD (t : S ⊗[R] S) :
    amitsurContract R S (LinearMap.lTensor S (amitsurD R S) t) =
      t - (amitsurMul R S t) ⊗ₜ[R] (1 : S) := by
  induction t with
  | zero => simp
  | tmul a b =>
    rw [LinearMap.lTensor_tmul, amitsurD_apply, TensorProduct.tmul_sub,
      map_sub, amitsurContract_tmul, amitsurContract_tmul, amitsurMul_tmul,
      mul_one]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy, map_add, TensorProduct.add_tmul]
    abel

/-- The tensored Amitsur sequence is exact (split by the contraction).
@isnad1 id=exact.0h2v.s11.73ae78b0dbc2 from=translated src=- shape=3b0360ab vocab=252e1bf5
-/
theorem amitsur_lTensor_exact :
    Function.Exact (LinearMap.lTensor S (Algebra.linearMap R S))
      (LinearMap.lTensor S (amitsurD R S)) := by
  intro t
  constructor
  · intro ht
    refine ⟨(amitsurMul R S t) ⊗ₜ[R] (1 : R), ?_⟩
    have hc := amitsurContract_lTensor_amitsurD R S t
    rw [ht, map_zero] at hc
    rw [LinearMap.lTensor_tmul]
    show (amitsurMul R S t) ⊗ₜ[R] (algebraMap R S 1) = t
    rw [map_one]
    exact (sub_eq_zero.mp hc.symm).symm
  · rintro ⟨z, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have hz : (amitsurD R S).comp (Algebra.linearMap R S) = 0 := by
      refine LinearMap.ext fun r => ?_
      show (1 : S) ⊗ₜ[R] (algebraMap R S r) - (algebraMap R S r) ⊗ₜ[R] (1 : S) = 0
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul, TensorProduct.tmul_smul, sub_self]
    rw [hz, LinearMap.lTensor_zero, LinearMap.zero_apply]

/-- **Amitsur exactness in degree ≤ 1** for a faithfully flat algebra.
@isnad1 id=exact.0h2v.s9.6405187c4d04 from=translated src=- shape=c9b26bd5 vocab=627ead5f
-/
theorem amitsur_exact [Module.FaithfullyFlat R S] :
    Function.Exact (Algebra.linearMap R S) (amitsurD R S) :=
  Module.FaithfullyFlat.lTensor_reflects_exact R S _ _
    (amitsur_lTensor_exact R S)

/-- **Faithfully flat descent of elements**: an element of `S` whose two
tensor-inclusions into `S ⊗[R] S` agree comes from `R`.
@isnad1 id=ex.1h3v.s8.64502074d78b from=translated src=- shape=73c64f07 vocab=4f5e8bb4
-/
theorem exists_algebraMap_eq_of_tmul_eq [Module.FaithfullyFlat R S] (s : S)
    (h : (1 : S) ⊗ₜ[R] s = s ⊗ₜ[R] (1 : S)) :
    ∃ r : R, algebraMap R S r = s := by
  obtain ⟨r, hr⟩ := (amitsur_exact R S s).mp
    (by rw [amitsurD_apply, h, sub_self])
  exact ⟨r, hr⟩

end ModularCurves
