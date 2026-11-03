import Tengoku.DgLean.DG.Algebra.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Isomorphisms of dg abelian groups

* `DGAddEquiv M N`: an additive equivalence between dg abelian groups which has degree `0`
  (`Mⁿ` is mapped into `Nⁿ`) and commutes with the differentials. Its inverse is again of
  degree `0` (`DGAddEquiv.symm`): a bijective additive map of degree `0` reflects the grading,
  by uniqueness of homogeneous decompositions (`DG.mem_grading_of_injective`).

This is the notion of isomorphism for dg abelian groups (cochain complexes of abelian groups
with an internal grading); isomorphisms of dg modules additionally require linearity over the
dg ring. The API is deliberately small: `refl`, `symm`, `trans` and the evaluation lemmas.
-/

open DirectSum

namespace DG

section Decompose

variable {M N : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]

/-- An additive map of degree `0` commutes with the homogeneous decompositions.
@isnad1 id=eq.1h5v.s10.09bcf593dd5b from=translated src=- shape=87e4ca7a vocab=2548c823
-/
theorem coe_decompose_map_of_map_mem (f : M →+ N)
    (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n) (m : M) (j : ℤ) :
    (decompose (grading (M := N)) (f m) j : N) = f (decompose (grading (M := M)) m j) := by
  induction m using induction_on with
  | h_zero => simp
  | h_homogeneous x =>
    rename_i i
    rw [decompose_of_mem _ (hf x.2), decompose_coe]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [of_eq_of_ne _ _ _ (Ne.symm hij)]
  | h_add m m' hm hm' => simp [decompose_add, hm, hm']

/-- An injective additive map of degree `0` reflects the grading: if `f m` is homogeneous of
degree `k`, so is `m`.
@isnad1 id=mem.3h5v.s8.2dc6421681e5 from=translated src=- shape=f0e91c4b vocab=49f5a157
-/
theorem mem_grading_of_injective (f : M →+ N)
    (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n) (hinj : Function.Injective f)
    {k : ℤ} {m : M} (hm : f m ∈ grading k) : m ∈ grading k := by
  set ℳ := grading (M := M)
  have key : ∀ j, j ≠ k → decompose ℳ m j = 0 := fun j hj => by
    refine Subtype.ext (hinj ?_)
    rw [← coe_decompose_map_of_map_mem f hf, decompose_of_mem_ne _ hm (Ne.symm hj),
      ZeroMemClass.coe_zero, map_zero]
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

/-- An isomorphism of dg abelian groups: an additive equivalence of degree `0` commuting with
the differentials.-/
structure DGAddEquiv (M : Type*) (N : Type*) [AddCommGroup M] [DGAddCommGroup M]
    [AddCommGroup N] [DGAddCommGroup N] extends M ≃+ N where
  map_mem' : ∀ {n : ℤ} {m : M}, m ∈ grading n → toFun m ∈ grading n
  map_d' : ∀ m : M, toFun (d m) = d (toFun m)

namespace DGAddEquiv

variable {M N P : Type*} [AddCommGroup M] [DGAddCommGroup M] [AddCommGroup N] [DGAddCommGroup N]
  [AddCommGroup P] [DGAddCommGroup P]

instance : EquivLike (DGAddEquiv M N) M N where
  coe e := e.toFun
  inv e := e.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' e e' h _ := by
    rcases e with ⟨e, _, _⟩
    rcases e' with ⟨e', _, _⟩
    obtain rfl : e = e' := AddEquiv.ext (congrFun h)
    rfl

instance : AddEquivClass (DGAddEquiv M N) M N where
  map_add e := e.map_add'

/--
@isnad1 id=eq.0h3v.s7.02ef3213ba2a from=translated src=- shape=784c6025 vocab=33424d72
-/
@[simp]
theorem coe_toAddEquiv (e : DGAddEquiv M N) : ⇑e.toAddEquiv = e := rfl

/--
@isnad1 id=eq.1h4v.s6.407885c57537 from=translated src=- shape=86acd962 vocab=e41ea989
-/
@[ext]
theorem ext {e e' : DGAddEquiv M N} (h : ∀ m, e m = e' m) : e = e' :=
  DFunLike.ext e e' h

/--
@isnad1 id=mem.1h5v.s6.4ece76031c8e from=translated src=- shape=bdc52a53 vocab=a7e18fa3
-/
theorem map_mem (e : DGAddEquiv M N) {n : ℤ} {m : M} (hm : m ∈ grading n) : e m ∈ grading n :=
  e.map_mem' hm

/--
@isnad1 id=eq.0h4v.s7.cfe01e144e7c from=translated src=- shape=6aeb57b3 vocab=04d60fa0
-/
@[simp]
theorem map_d (e : DGAddEquiv M N) (m : M) : e (d m) = d (e m) :=
  e.map_d' m

/--
@isnad1 id=injectiv.0h3v.s5.4c7094a9bdf3 from=translated src=- shape=21e4185b vocab=951e2f2d
-/
theorem injective (e : DGAddEquiv M N) : Function.Injective e :=
  EquivLike.injective e

/--
@isnad1 id=surjecti.0h3v.s5.8df93ea979a7 from=translated src=- shape=21e4185b vocab=5972945c
-/
theorem surjective (e : DGAddEquiv M N) : Function.Surjective e :=
  EquivLike.surjective e

/-- The identity isomorphism.-/
def refl : DGAddEquiv M M where
  __ := AddEquiv.refl M
  map_mem' hm := hm
  map_d' _ := rfl

/--
@isnad1 id=eq.0h2v.s5.233dfff51e92 from=translated src=- shape=3147685f vocab=19d67ec1
-/
@[simp]
theorem refl_apply (m : M) : (refl : DGAddEquiv M M) m = m := rfl

/-- The inverse of an isomorphism of dg abelian groups.-/
def symm (e : DGAddEquiv M N) : DGAddEquiv N M where
  __ := e.toAddEquiv.symm
  map_mem' {_ y} hy := by
    refine mem_grading_of_injective e.toAddEquiv.toAddMonoidHom e.map_mem' e.injective ?_
    change e (e.toAddEquiv.symm y) ∈ grading _
    rwa [← coe_toAddEquiv, AddEquiv.apply_symm_apply]
  map_d' y := by
    apply e.injective
    change e (e.toAddEquiv.symm (d y)) = e (d (e.toAddEquiv.symm y))
    rw [map_d, ← coe_toAddEquiv, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h4v.s6.7924fa715e2d from=translated src=- shape=106c0e0f vocab=d23a9944
-/
@[simp]
theorem apply_symm_apply (e : DGAddEquiv M N) (y : N) : e (e.symm y) = y :=
  e.right_inv y

/--
@isnad1 id=eq.0h4v.s6.ff43fc659e97 from=translated src=- shape=adb0b6b9 vocab=d23a9944
-/
@[simp]
theorem symm_apply_apply (e : DGAddEquiv M N) (m : M) : e.symm (e m) = m :=
  e.left_inv m

/--
@isnad1 id=eq.0h3v.s5.1b2a2b044bbf from=translated src=- shape=01b1f24c vocab=362f53a9
-/
@[simp]
theorem symm_symm (e : DGAddEquiv M N) : e.symm.symm = e := rfl

/-- Composition of isomorphisms of dg abelian groups.-/
def trans (e : DGAddEquiv M N) (e' : DGAddEquiv N P) : DGAddEquiv M P where
  __ := e.toAddEquiv.trans e'.toAddEquiv
  map_mem' hm := e'.map_mem (e.map_mem hm)
  map_d' m := by
    change e' (e (d m)) = d (e' (e m))
    rw [map_d, map_d]

/--
@isnad1 id=eq.0h6v.s7.cb1175ac275a from=translated src=- shape=07bf8e51 vocab=488825d0
-/
@[simp]
theorem trans_apply (e : DGAddEquiv M N) (e' : DGAddEquiv N P) (m : M) :
    e.trans e' m = e' (e m) := rfl

/-- Construct an isomorphism of dg abelian groups from mutually inverse additive maps of
degree `0`, one of which commutes with the differentials.-/
def ofAddMonoidHom (f : M →+ N) (g : N →+ M) (hgf : ∀ m, g (f m) = m) (hfg : ∀ n, f (g n) = n)
    (hf : ∀ {n : ℤ} {m : M}, m ∈ grading n → f m ∈ grading n) (hd : ∀ m, f (d m) = d (f m)) :
    DGAddEquiv M N where
  toFun := f
  invFun := g
  left_inv := hgf
  right_inv := hfg
  map_add' := map_add f
  map_mem' := hf
  map_d' := hd

/--
@isnad1 id=eq.4h5v.s9.0b94124ae92a from=translated src=- shape=ae031e20 vocab=72e00bd8
-/
@[simp]
theorem ofAddMonoidHom_apply (f : M →+ N) (g : N →+ M) (hgf hfg) (hf) (hd) (m : M) :
    ofAddMonoidHom f g hgf hfg hf hd m = f m := rfl

/--
@isnad1 id=eq.4h5v.s9.5e0d35481ec3 from=translated src=- shape=186bf64e vocab=0d0c228a
-/
@[simp]
theorem ofAddMonoidHom_symm_apply (f : M →+ N) (g : N →+ M) (hgf hfg) (hf) (hd) (n : N) :
    (ofAddMonoidHom f g hgf hfg hf hd).symm n = g n := rfl

end DGAddEquiv

end DG
