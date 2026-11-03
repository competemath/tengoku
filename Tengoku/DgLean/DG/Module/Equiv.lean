import Tengoku.DgLean.DG.Module.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Isomorphisms of dg modules

* `DGModuleEquiv A M N` (notation `M ≃ᵈᵍ[A] N`): an `A`-linear equivalence of degree `0`
  commuting with the differentials. Its inverse is automatically a morphism of dg modules
  (`DGModuleEquiv.symm`): a bijective graded map of degree `0` has a graded inverse, which is
  proved through the uniqueness of homogeneous decompositions
  (`DGModuleHom.mem_grading_of_injective`).

The API is deliberately small: `refl`, `symm`, `trans`, `toDGModuleHom` and the evaluation
lemmas.
-/

open scoped DG

open DirectSum

namespace DG

section Decompose

variable {A : Type*} {M N : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]

/-- A morphism of dg modules commutes with the homogeneous decompositions.
@isnad1 id=eq.0h6v.s10.f4ecca60f765 from=translated src=- shape=85939934 vocab=ba712da6
-/
theorem DGModuleHom.coe_decompose_apply (f : M →ᵈᵍ[A] N) (m : M) (j : ℤ) :
    (decompose (grading (M := N)) (f m) j : N) = f (decompose (grading (M := M)) m j) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    rw [decompose_of_mem _ (f.map_mem x.2), decompose_coe]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm hij)]
  | h_add m m' hm hm' => simp [decompose_add, hm, hm']

/-- An injective morphism of dg modules reflects the grading: if `f m` is homogeneous of
degree `k`, so is `m`.
@isnad1 id=mem.2h6v.s7.030580135ab8 from=translated src=- shape=d5af47f4 vocab=419284ba
-/
theorem DGModuleHom.mem_grading_of_injective (f : M →ᵈᵍ[A] N) (hf : Function.Injective f)
    {k : ℤ} {m : M} (hm : f m ∈ grading k) : m ∈ grading k := by
  set ℳ := grading (M := M)
  have key : ∀ j, j ≠ k → decompose ℳ m j = 0 := fun j hj => by
    refine Subtype.ext (hf ?_)
    rw [← f.coe_decompose_apply, decompose_of_mem_ne _ hm (Ne.symm hj), ZeroMemClass.coe_zero,
      map_zero]
  have h : decompose ℳ m = DirectSum.of (fun i => ℳ i) k (decompose ℳ m k) := by
    refine DirectSum.ext fun j => ?_
    by_cases hjk : j = k
    · subst hjk
      rw [of_eq_same]
    · rw [of_eq_of_ne _ _ _ hjk, key j hjk]
  have h' := congrArg (decompose ℳ).symm h
  rw [Equiv.symm_apply_apply, decompose_symm_of] at h'
  rw [h']
  exact (decompose ℳ m k).2

end Decompose

/-- An isomorphism of dg `A`-modules: an `A`-linear equivalence of degree `0` commuting with
the differentials.-/
structure DGModuleEquiv (A : Type*) (M : Type*) (N : Type*) [Ring A] [DGAddCommGroup A]
    [AddCommGroup M] [DGAddCommGroup M] [Module A M]
    [AddCommGroup N] [DGAddCommGroup N] [Module A N] extends M ≃ₗ[A] N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)

@[inherit_doc]
scoped notation:25 M " ≃ᵈᵍ[" A "] " N => DGModuleEquiv A M N

namespace DGModuleEquiv

variable {A : Type*} {M N P : Type*} [Ring A] [DGAddCommGroup A]
  [AddCommGroup M] [DGAddCommGroup M] [Module A M]
  [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [AddCommGroup P] [DGAddCommGroup P] [Module A P]

instance : EquivLike (M ≃ᵈᵍ[A] N) M N where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    rcases e with ⟨e, _, _⟩
    rcases e' with ⟨e', _, _⟩
    obtain rfl : e = e' := LinearEquiv.ext (congrFun h)
    rfl

instance : LinearEquivClass (M ≃ᵈᵍ[A] N) A M N where
  map_add e := e.map_add'
  map_smulₛₗ e := e.map_smul'

/--
@isnad1 id=eq.0h4v.s7.6f361a000272 from=translated src=- shape=d8f4526c vocab=588b71c6
-/
@[simp]
theorem coe_toLinearEquiv (e : M ≃ᵈᵍ[A] N) : ⇑e.toLinearEquiv = e := rfl

/--
@isnad1 id=eq.1h5v.s7.3c5c8eb66dc7 from=translated src=- shape=11aaea2d vocab=827998a4
-/
@[ext]
theorem ext {e e' : M ≃ᵈᵍ[A] N} (h : ∀ m, e m = e' m) : e = e' :=
  DFunLike.ext e e' h

/--
@isnad1 id=mem.1h6v.s7.3180130ec4e3 from=translated src=- shape=3c45d893 vocab=192d2fca
-/
theorem map_mem (e : M ≃ᵈᵍ[A] N) {n : ℤ} {m : M} (hm : m ∈ grading n) : e m ∈ grading n :=
  e.map_mem' hm

/--
@isnad1 id=eq.0h5v.s8.ef201238e025 from=translated src=- shape=d6997d71 vocab=fb3b1abb
-/
@[simp]
theorem map_d (e : M ≃ᵈᵍ[A] N) (m : M) : e (d m) = d (e m) :=
  e.map_d' m

/-- The underlying morphism of dg modules of an isomorphism.-/
def toDGModuleHom (e : M ≃ᵈᵍ[A] N) : M →ᵈᵍ[A] N where
  __ := e.toLinearEquiv.toLinearMap
  map_mem' := e.map_mem'
  map_d' := e.map_d'

/--
@isnad1 id=eq.0h4v.s7.f8db44aa5b9d from=translated src=- shape=a2c0993c vocab=53f7dbff
-/
@[simp]
theorem coe_toDGModuleHom (e : M ≃ᵈᵍ[A] N) : ⇑e.toDGModuleHom = e := rfl

/--
@isnad1 id=injectiv.0h4v.s6.0fa1b39e9201 from=translated src=- shape=769fb268 vocab=22952efe
-/
theorem injective (e : M ≃ᵈᵍ[A] N) : Function.Injective e :=
  EquivLike.injective e

/--
@isnad1 id=surjecti.0h4v.s6.8104abec02b8 from=translated src=- shape=769fb268 vocab=6a4bdc7c
-/
theorem surjective (e : M ≃ᵈᵍ[A] N) : Function.Surjective e :=
  EquivLike.surjective e

/-- The identity isomorphism.-/
def refl : M ≃ᵈᵍ[A] M where
  __ := LinearEquiv.refl A M
  map_mem' hm := hm
  map_d' _ := rfl

/--
@isnad1 id=eq.0h3v.s6.ec05555df9ea from=translated src=- shape=ca333403 vocab=917350c8
-/
@[simp]
theorem refl_apply (m : M) : (refl : M ≃ᵈᵍ[A] M) m = m := rfl

/-- The inverse of an isomorphism of dg modules.-/
def symm (e : M ≃ᵈᵍ[A] N) : N ≃ᵈᵍ[A] M where
  __ := e.toLinearEquiv.symm
  map_mem' {_ y} hy := by
    refine e.toDGModuleHom.mem_grading_of_injective e.injective ?_
    change e (e.toLinearEquiv.symm y) ∈ grading _
    rwa [← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]
  map_d' y := by
    apply e.injective
    change e (e.toLinearEquiv.symm (d y)) = e (d (e.toLinearEquiv.symm y))
    rw [map_d, ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h5v.s7.09c71bb14e62 from=translated src=- shape=f87e0636 vocab=56def280
-/
@[simp]
theorem apply_symm_apply (e : M ≃ᵈᵍ[A] N) (y : N) : e (e.symm y) = y :=
  e.right_inv y

/--
@isnad1 id=eq.0h5v.s7.551e58a81267 from=translated src=- shape=07e2e662 vocab=56def280
-/
@[simp]
theorem symm_apply_apply (e : M ≃ᵈᵍ[A] N) (m : M) : e.symm (e m) = m :=
  e.left_inv m

/--
@isnad1 id=eq.0h4v.s6.774cd5e8ee3b from=translated src=- shape=95b39492 vocab=046b671c
-/
@[simp]
theorem symm_symm (e : M ≃ᵈᵍ[A] N) : e.symm.symm = e := rfl

/-- Composition of isomorphisms of dg modules.-/
def trans (e : M ≃ᵈᵍ[A] N) (e' : N ≃ᵈᵍ[A] P) : M ≃ᵈᵍ[A] P where
  __ := e.toLinearEquiv.trans e'.toLinearEquiv
  map_mem' hm := e'.map_mem (e.map_mem hm)
  map_d' m := by
    change e' (e (d m)) = d (e' (e m))
    rw [map_d, map_d]

/--
@isnad1 id=eq.0h7v.s7.0a6743cdef88 from=translated src=- shape=63151fa5 vocab=a336cdac
-/
@[simp]
theorem trans_apply (e : M ≃ᵈᵍ[A] N) (e' : N ≃ᵈᵍ[A] P) (m : M) : e.trans e' m = e' (e m) := rfl

end DGModuleEquiv

end DG
-- Tengoku: 1 notation(s) of this module made scoped so they do not change other libraries (generated)
