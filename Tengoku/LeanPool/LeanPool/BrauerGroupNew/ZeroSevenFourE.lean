/-
Copyright (c) 2026 Yunzhou Xie and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yichen Feng, Jujian Zhang, Yael Dillies
-/
module

public import Tengoku

public import Tengoku.LeanPool.LeanPool.BrauerGroupNew.MoritaEquivalence
public import Tengoku.LeanPool.LeanPool.BrauerGroupNew.Wedderburn

/-!
# The Stacks Project tag 074E

This file ports the upstream Wedderburn-Artin uniqueness arguments used by the Brauer group
development.
-/

@[expose] public section

open CategoryTheory DirectSum

universe u v w

section simple

variable (k : Type u) (A : Type v) [Field k] [Ring A] [Algebra k A]
    [IsSimpleRing A] [FiniteDimensional k A]

noncomputable section wedderburn

/-- Restricts endomorphisms along a Wedderburn equivalence with a matrix algebra. -/
abbrev endCatEquiv (n : ℕ)
    (D : Type v) [DivisionRing D] [Algebra k D] (wdb : A ≃ₐ[k] Matrix (Fin n) (Fin n) D)
    [Module A (Fin n → D)] (smul_def : ∀ (a : A) (v : Fin n → D), a • v = wdb a • v)
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)] [IsScalarTower k A (Fin n → D)]
    [SMulCommClass A k (Fin n → D)] :
    Module.End A (Fin n → D) ≃ₐ[k] Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) :=
  .ofAlgHom {
    toFun f := {
      __ := f
      map_smul' := fun a v => by
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, RingHom.id_apply]
        rw [show a • v = wdb.symm a • v by simp [smul_def], map_smul, smul_def]
        simp
    }
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' := by intros; ext; simp }
  { toFun f := {
      toFun := f
      map_add' := f.map_add
      map_smul' := fun a b => by
        simp only [smul_def, LinearMapClass.map_smul, RingHom.id_apply]
    }
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl
    commutes' := by intros; ext; simp }
  (by rfl) (by rfl)

omit [IsSimpleRing A] [FiniteDimensional k A] in
private lemma matrixModuleVectorDecomp {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D] (v : Fin n → D) :
    v = ∑ j : Fin n, (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) •
      Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D) := by
  ext t
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single t]
  · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single]
  · simp_all
  · simp_all

omit [IsSimpleRing A] [FiniteDimensional k A] in
private lemma matrixModuleEnd_apply {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D]
    (f : Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D)) (v : Fin n → D) (i : Fin n) :
    f v i = v i * f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0 := by
  let e₀ : Fin n → D := Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)
  let c : D := f e₀ 0
  have hfe₀ (j : Fin n) : f e₀ j = Pi.single (M := fun _ : Fin n => D) (0 : Fin n) c j := by
    by_cases h : j = 0
    · subst h
      simp [c]
    · have hzero : (Matrix.single (0 : Fin n) j (1 : D) :
          Matrix (Fin n) (Fin n) D) • e₀ = 0 := by
        ext t
        by_cases ht : (0 : Fin n) = t
        · subst ht
          simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, e₀, h]
        · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, e₀, ht]
      have hmap := congrFun (f.map_smul (Matrix.single (0 : Fin n) j (1 : D)) e₀) 0
      rw [hzero] at hmap
      simp [Matrix.mulVec, dotProduct, Matrix.single, e₀] at hmap
      simpa [e₀, Pi.single, h, c] using hmap.symm
  have hv := matrixModuleVectorDecomp D v
  calc
    f v i = f (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) • e₀) i := by
      simpa [e₀] using congrArg (fun w => f w i) hv
    _ = (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) • f e₀) i := by
      rw [map_sum]
      refine congrArg (fun w : Fin n → D => w i) ?_
      exact Finset.sum_congr rfl fun j _ => f.map_smul (Matrix.single j 0 (v j)) e₀
    _ = (∑ j : Fin n,
        (Matrix.single j (0 : Fin n) (v j) : Matrix (Fin n) (Fin n) D) •
          Pi.single (M := fun _ : Fin n => D) (0 : Fin n) c) i := by
      refine congrArg (fun w : Fin n → D => w i) ?_
      apply Finset.sum_congr rfl
      intro j _
      rw [funext hfe₀]
    _ = v i * c := by
      rw [Finset.sum_apply]
      rw [Finset.sum_eq_single i]
      · simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single]
      · intro j _ hj
        simp [Matrix.mulVec, dotProduct, Matrix.single, Pi.single, hj]
      · intro hi
        simp at hi
    _ = v i * f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0 := rfl

omit [IsSimpleRing A] [FiniteDimensional k A] in
/-- The endomorphism algebra of the standard matrix module is the opposite scalar algebra. -/
noncomputable def matrixModuleEndAlgEquivMop {n : ℕ} [NeZero n]
    (D : Type v) [DivisionRing D] [Algebra k D]
    [IsScalarTower k (Matrix (Fin n) (Fin n) D) (Fin n → D)]
    [SMulCommClass (Matrix (Fin n) (Fin n) D) k (Fin n → D)] :
    Module.End (Matrix (Fin n) (Fin n) D) (Fin n → D) ≃ₐ[k] Dᵐᵒᵖ where
  toFun f := MulOpposite.op (f (Pi.single (M := fun _ : Fin n => D) (0 : Fin n) (1 : D)) 0)
  invFun c :=
  { toFun v := fun i => v i * c.unop
    map_add' := by
      intro v w
      ext i
      simp [add_mul]
    map_smul' := by
      intro M v
      ext i
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc] }
  left_inv f := by
    ext v i
    simp [matrixModuleEnd_apply D f v i]
  right_inv c := by
    simp_all
  map_mul' f g := by
    apply MulOpposite.unop_injective
    simp [matrixModuleEnd_apply D f (g (Pi.single (0 : Fin n) (1 : D))) 0]
  map_add' f g := by
    simp_all
  commutes' a := by
    apply MulOpposite.unop_injective
    simp [Pi.single, Algebra.smul_def]

end wedderburn

instance instAlgebraEndOfIsScalarTowerLeanPool (M : Type v) [AddCommGroup M] [Module A M]
    [Module k M] [IsScalarTower k A M] :
    Algebra k (Module.End (Module.End A M) M) where
  algebraMap := {
    toFun a :=
    { toFun m := a • m
      map_add' := by simp only [smul_add, implies_true]
      map_smul' := by
        simp only [Module.End.smul_def, RingHom.id_apply, LinearMap.map_smul_of_tower,
          implies_true] }
    map_one' := by ext; simp only [one_smul, LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_apply]
    map_mul' := by
      intros; ext
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply, LinearMap.map_smul_of_tower]
      rw [mul_comm, mul_smul]
    map_zero' := by ext; simp
    map_add' := by
      intros; ext
      simp only [add_smul, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply]
  }
  commutes' := by
    intros r f
    ext m
    simp_all
  smul r f :=
  { toFun m := f <| r • m
    map_add' := by simp
    map_smul' := by
      intro g m
      simp only [Module.End.smul_def, RingHom.id_apply]
      let s : Module.End A M :=
      { toFun x := r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
      change f (s • g m) = g (f <| s • m)
      rw [f.map_smul, f.map_smul]
      simp only [Module.End.smul_def, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.map_smul_of_tower,
        s]
      change r • f (g • m) = _
      rw [f.map_smul]
      simp }
  smul_def' := by
    intro r f
    ext m
    simp only [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Module.End.mul_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    let s : Module.End A M :=
      { toFun x := r • x
        map_add' := by simp
        map_smul' := fun a x => by
          simp only [RingHom.id_apply]
          rw [algebra_compatible_smul A, ← mul_smul, algebra_compatible_smul A, ← mul_smul]
          congr 1
          exact Algebra.commutes r a }
    change _ = s • f m
    rw [← f.map_smul]
    rfl

omit [IsSimpleRing A] in
lemma exists_gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] :
    ∃ m : M, m ≠ 0 ∧ ∀ m', ∃ a : A, m' = a • m := by
    have i : Submodule.IsPrincipal (⊤ : Submodule A M) := inferInstance
    refine ⟨i.1.choose, ?_, fun m ↦ by
      classical
      have : m ∈ Submodule.span A {i.1.choose} := by
        rw [← i.1.choose_spec]; trivial
      rw [Submodule.mem_span_singleton] at this
      simpa [Eq.comm]⟩
    intro h
    have := i.1.choose_spec
    rw [h] at this
    simp only [Submodule.span_zero_singleton, top_ne_bot] at this

/-- A chosen nonzero generator for a simple module. -/
noncomputable def gen (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] : M :=
    (exists_gen A M).choose

omit [IsSimpleRing A] in
lemma gen_ne_zero (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    gen A M ≠ 0 := (exists_gen A M).choose_spec.1

omit [IsSimpleRing A] in
lemma gen_spec (M : Type v) [AddCommGroup M]
    [Module A M] [IsSimpleModule A M] (m' : M) :
    ∃ a : A, m' = a • gen A M := (exists_gen A M).choose_spec.2 m'

/-- The left action map into the double centralizer endomorphism algebra. -/
@[simps]
def toEndEnd (M : Type v) [AddCommGroup M] [Module A M] :
    A →ₗ[A] Module.End (Module.End A M) M where
  toFun a :=
  { toFun m := a • m
    map_add' := by simp
    map_smul' := fun f m => (f.map_smul a m).symm }
  map_add' := by intros; ext; simp [add_smul]
  map_smul' := by intros; ext; simp [mul_smul]

omit [IsSimpleRing A] in
@[simp]
lemma toEndEnd_apply (M : Type v) [AddCommGroup M] [Module A M] (a : A) (m : M) :
    toEndEnd A M a m = a • m := rfl

/-- The algebra homomorphism induced by the double centralizer action map. -/
def toEndEndAlgHom (M : Type v) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    A →ₐ[k] Module.End (Module.End A M) M where
  __ := toEndEnd A M
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_smul]
  map_zero' := by ext; simp
  commutes' a := by
    ext m
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, toEndEnd_apply, algebraMap_smul]
    rfl

instance (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M] :
    Nontrivial (Module.End (Module.End A M) M) where
  exists_pair_ne := ⟨0, 1, fun eq ↦ gen_ne_zero A M congr($eq (gen A M)).symm⟩

omit [FiniteDimensional k A] in
lemma toEndEnd_injective
    (M : Type v) [AddCommGroup M] [Module A M] [IsSimpleModule A M]
    [Module k M] [IsScalarTower k A M] :
    Function.Injective (toEndEnd A M) :=
  RingHom.injective (toEndEndAlgHom k A M).toRingHom

/-- A module is balanced when the double centralizer action map is surjective. -/
class IsBalanced (M : Type v) [AddCommGroup M] [Module A M] : Prop where
  surj : Function.Surjective (toEndEnd A M)

omit [IsSimpleRing A] in
lemma IsBalanced.congr_aux (M N : Type v) [AddCommGroup M] [AddCommGroup N] [Module A M]
    [Module A N] (l : M ≃ₗ[A] N) (h : IsBalanced A M) : IsBalanced A N := by
  refine ⟨fun a => ?_⟩
  let a' : Module.End (Module.End A M) M :=
  { toFun m := l.symm <| a (l m)
    map_add' := by simp
    map_smul' := fun x y => by
      simp only [Module.End.smul_def, RingHom.id_apply]
      let L := l.toLinearMap ∘ₗ x ∘ₗ l.symm.toLinearMap
      have := a.map_smul L (l y)
      simp only [Module.End.smul_def, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        LinearEquiv.symm_apply_apply, L] at this
      simp [this] }
  obtain ⟨b, hb⟩ := h.1 a'
  refine ⟨b, ?_⟩
  ext n
  have hb' := congrArg (fun f : Module.End (Module.End A M) M => f (l.symm n)) hb
  simp only [a', toEndEnd_apply_apply] at hb'
  apply_fun l at hb'
  simpa using hb'

omit [IsSimpleRing A] in
lemma IsBalanced.congr {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
    (l : M ≃ₗ[A] N) : IsBalanced A M ↔ IsBalanced A N := by
  constructor
  · apply IsBalanced.congr_aux; exact l
  · apply IsBalanced.congr_aux; exact l.symm

end simple
