/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.SkewMonoidAlgebra.Basic
public import Tengoku.Seed.Algebra.Module.BigOperators
public import Tengoku.Seed.Algebra.Algebra.Equiv

/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
def liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A →ₐ[k] B)
    (g : G →* B) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra A G →ₐ[k] B where
  __ := liftNCRingHom (f : A →+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
  `SkewMonoidAlgebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  invFun f := (f : SkewMonoidAlgebra k G →* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show ∀ (g : G) (r : k), g • r = r by
        exact fun _ _ ↦ smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G A}

/--
@isnad1 id=eq.0h5v.s9.45267e79a035 from=seed src=0 shape=39353104 vocab=b093c2c0
-/
theorem lift_apply' (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ algebraMap k A b * F a := rfl

/--
@isnad1 id=eq.0h5v.s9.8295e874f98c from=seed src=0 shape=8cf48c79 vocab=c06ca02f
-/
theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ b • F a := by simp [lift_apply', Algebra.smul_def]

/--
@isnad1 id=eq.0h4v.s9.3fc8cf986eea from=seed src=0 shape=bc2fcf64 vocab=84e10f3b
-/
theorem lift_def (F : G →* A) : (lift k G A F : SkewMonoidAlgebra k G → A) =
    liftNC ((algebraMap k A : k →+* A) : k →+ A) F := rfl

/--
@isnad1 id=eq.0h5v.s9.2b95a4210a61 from=seed src=0 shape=f674543c vocab=43bca330
-/
@[simp]
theorem lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) :
    (lift k G A).symm F x = F (single x 1) := rfl

/--
@isnad1 id=eq.0h5v.s9.36a83ec5413f from=seed src=0 shape=d32f6758 vocab=bb4bf04e
-/
theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by
  rw [of_apply, ← lift_symm_apply, Equiv.symm_apply_apply]

/--
@isnad1 id=eq.0h6v.s9.b5c2c7441154 from=seed src=0 shape=03a5df76 vocab=e2fa3da7
-/
@[simp]
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]

/--
@isnad1 id=eq.0h4v.s9.d6327fac7b07 from=seed src=0 shape=869aa4cc vocab=326de8ec
-/
theorem lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) :
    F = lift k G A ((F : SkewMonoidAlgebra k G →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `SkewMonoidAlgebra k G` by
  its values on `F (single a 1)`.
@isnad1 id=eq.0h5v.s8.6504fd70e3e9 from=seed src=0 shape=598eae4e vocab=89eda85c
-/
theorem lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A)
    (f : SkewMonoidAlgebra k G) : F f = f.sum fun a b ↦ b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringAction G A]
    [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f : F}
    (hf : ∀ (a : G) (x : A), a • x = (f a) • x) :
    SkewMonoidAlgebra A G →ₐ[k] SkewMonoidAlgebra A H where
  __ := mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

end lift

section equivMapDomain

variable [AddCommMonoid k]

/-- Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support forwards
and the function backwards. -/
@[simps]
def equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra k H where
  coeff := l.coeff.equivMapDomain f

/--
@isnad1 id=eq.0h5v.s6.df22a9eb97ed from=seed src=0 shape=34a9611f vocab=675d6e51
-/
@[deprecated (since := "2026-07-06")] alias toFinsupp_equivMapDomain := coeff_equivMapDomain

/--
@isnad1 id=eq.0h5v.s8.4262e9966dc4 from=seed src=0 shape=2426355d vocab=02c1a7d5
-/
theorem equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    equivMapDomain f l = mapDomain f l := by
  apply coeff_injective
  ext x
  simp_rw [coeff_equivMapDomain, Finsupp.equivMapDomain_apply, coeff_mapDomain,
    Finsupp.mapDomain_equiv_apply]

/--
@isnad1 id=eq.0h7v.s6.88571e752648 from=seed src=0 shape=ef09926a vocab=efab5302
-/
theorem equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
    (l : SkewMonoidAlgebra k G) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x; rfl

/--
@isnad1 id=eq.0h3v.s5.9aa99f961928 from=seed src=0 shape=d1626bb8 vocab=6eacbf09
-/
@[simp]
theorem equivMapDomain_refl (l : SkewMonoidAlgebra k G) : equivMapDomain (Equiv.refl _) l = l := by
  ext x; rfl

/--
@isnad1 id=eq.0h6v.s6.68dd7aa1db4c from=seed src=0 shape=40755796 vocab=1d7abe13
-/
@[simp]
theorem equivMapDomain_single (f : G ≃ H) (a : G) (b : k) :
    equivMapDomain f (single a b) = single (f a) b := by
  apply coeff_injective
  simp_rw [coeff_equivMapDomain, single, Finsupp.equivMapDomain_single]

end equivMapDomain

section domCongr

variable {A : Type*}

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given `AddCommMonoid A` and `e : G ≃ H`, `domCongr e` is the corresponding `Equiv` between
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`. -/
@[simps apply]
def domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H where
  toFun        := equivMapDomain e
  invFun       := equivMapDomain e.symm
  left_inv v   := by simp [← equivMapDomain_trans]
  right_inv v  := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `domCongr` as a `LinearEquiv`. -/
def domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) :
    SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H :=
  (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv <| by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

variable (k A)

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids and
` ∀ (a : G) (x : A), a • x = (e a) • x`, then `SkewMonoidAlgebra.domCongr e` is an
algebra equivalence between their skew monoid algebras. -/
def domCongrAlg {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g ↦ (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)

/--
@isnad1 id=eq.1h5v.s9.5e4ecd6f51bc from=seed src=0 shape=d0b3ec0d vocab=ca5de89d
-/
theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he :=
  AlgHom.ext <| fun _ ↦ equivMapDomain_eq_mapDomain _ _

/--
@isnad1 id=eq.1h7v.s9.706632ee828a from=seed src=0 shape=278d7d33 vocab=fc38c221
-/
@[simp] theorem domCongrAlg_apply {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) (h : H) : (domCongrAlg k A he f).coeff h = f.coeff (e.symm h) :=
  rfl

/--
@isnad1 id=eq.1h6v.s9.2c7612b7d337 from=seed src=0 shape=84edcea6 vocab=39721659
-/
@[simp] theorem domCongr_support {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) : (domCongrAlg k A he f).support = f.support.map e :=
  rfl

/--
@isnad1 id=eq.1h7v.s9.bb83c04b9304 from=seed src=0 shape=c263d817 vocab=d0a2e1f4
-/
@[simp] theorem domCongr_single {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (g : G) (a : A) : domCongrAlg k A he (single g a) = single (e g) a :=
  equivMapDomain_single ..

/--
@isnad1 id=eq.0h3v.s7.c785d4adacc2 from=seed src=0 shape=d18485dd vocab=092fcb09
-/
theorem domCongr_refl :
    domCongrAlg k A (e := MulEquiv.refl G) (fun _ _ ↦ rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  aesop

/--
@isnad1 id=eq.1h5v.s9.e5a530aa7ed6 from=seed src=0 shape=17ed5b8a vocab=ef6f44b0
-/
@[simp] theorem domCongr_symm {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).symm =
      domCongrAlg (e := e.symm) _ _ (fun a x ↦ by rw [he, MulEquiv.apply_symm_apply]) :=
  rfl

end domCongr

section Submodule

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

variable {V : Type*} [AddCommMonoid V] [Module k V] [Module (SkewMonoidAlgebra k G) V]
  [IsScalarTower k (SkewMonoidAlgebra k G) V]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- A submodule over `k` which is stable under scalar multiplication by elements of `G` is a
submodule over `SkewMonoidAlgebra k G` -/
def submoduleOfSmulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (SkewMonoidAlgebra k G) V where
  carrier   := W
  zero_mem' := W.zero_mem'
  add_mem'  := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f, sum_def, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ ↦ h g v hv

end Submodule

end SkewMonoidAlgebra
