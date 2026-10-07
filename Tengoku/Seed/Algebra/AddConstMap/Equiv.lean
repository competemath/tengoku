/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.AddConstMap.Basic

/-!
# Equivalences conjugating `(· + a)` to `(· + b)`

In this file we define `AddConstEquiv G H a b` (notation: `G ≃+c[a, b] H`)
to be the type of equivalences such that `∀ x, f (x + a) = f x + b`.

We also define the corresponding typeclass and prove some basic properties.
-/

@[expose] public section

assert_not_exists Finset

open Function
open scoped AddConstMap

/-- An equivalence between `G` and `H` conjugating `(· + a)` to `(· + b)`,
denoted as `G ≃+c[a, b] H`. -/
structure AddConstEquiv (G H : Type*) [Add G] [Add H] (a : G) (b : H)
  extends G ≃ H, G →+c[a, b] H

/-- Interpret an `AddConstEquiv` as an `Equiv`. -/
add_decl_doc AddConstEquiv.toEquiv

/-- Interpret an `AddConstEquiv` as an `AddConstMap`. -/
add_decl_doc AddConstEquiv.toAddConstMap

@[inherit_doc]
scoped[AddConstMap] notation:25 G " ≃+c[" a ", " b "] " H => AddConstEquiv G H a b

namespace AddConstEquiv

variable {G H K : Type*} [Add G] [Add H] [Add K] {a : G} {b : H} {c : K}

/--
@isnad1 id=injectiv.0h4v.s5.2d342dd813fb from=seed src=0 shape=cfbd988b vocab=626e97dd
-/
lemma toEquiv_injective : Injective (toEquiv : (G ≃+c[a, b] H) → G ≃ H)
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    EquivLike (G ≃+c[a, b] H) G H where
  coe f := f.toEquiv
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ h _ := toEquiv_injective <| DFunLike.ext' h

instance {G H : Type*} [Add G] [Add H] {a : G} {b : H} :
    AddConstMapClass (G ≃+c[a, b] H) G H a b where
  map_add_const f x := f.map_add_const' x

/--
@isnad1 id=eq.1h6v.s6.ec44d95c46b7 from=seed src=0 shape=0d965dfb vocab=d0fe0bc9
-/
@[ext] lemma ext {e₁ e₂ : G ≃+c[a, b] H} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ := DFunLike.ext _ _ h

/--
@isnad1 id=iff.0h6v.s5.e8ebc4ace9bb from=seed src=0 shape=82e092d5 vocab=a22261da
-/
@[simp]
lemma toEquiv_inj {e₁ e₂ : G ≃+c[a, b] H} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

/--
@isnad1 id=eq.0h5v.s6.c1435dafeb7f from=seed src=0 shape=d6dd4bbc vocab=f2f4392c
-/
@[simp] lemma coe_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv = e := rfl

/-- Inverse map of an `AddConstEquiv`, as an `AddConstEquiv`. -/
def symm (e : G ≃+c[a, b] H) : H ≃+c[b, a] G where
  toEquiv := e.toEquiv.symm
  map_add_const' := (AddConstMapClass.semiconj e).inverse_left e.left_inv e.right_inv

/-- A custom projection for `simps`. -/
def Simps.symm_apply (e : G ≃+c[a, b] H) : H → G := e.symm

initialize_simps_projections AddConstEquiv (toFun → apply, invFun → symm_apply)

/--
@isnad1 id=eq.0h5v.s5.c30408e8ca4f from=seed src=0 shape=4132a684 vocab=f5d7d451
-/
@[simp] lemma symm_symm (e : G ≃+c[a, b] H) : e.symm.symm = e := rfl

/--
@isnad1 id=iff.0h7v.s6.caf2dca40137 from=seed src=0 shape=24896afd vocab=583f33a9
-/
theorem symm_apply_eq (e : G ≃+c[a, b] H) {a b} :
    e.symm a = b ↔ a = e b :=
  e.toEquiv.symm_apply_eq

theorem eq_symm_apply (e : G ≃+c[a, b] H) {a b} :
    b = e.symm a ↔ e b = a :=
  e.toEquiv.eq_symm_apply

/--
@isnad1 id=eq.0h6v.s6.37bc5813440d from=seed src=0 shape=22299f36 vocab=583f33a9
-/
@[simp] theorem apply_symm_apply (e : G ≃+c[a, b] H) (a) :
    e (e.symm a) = a :=
  e.toEquiv.apply_symm_apply _

/--
@isnad1 id=eq.0h6v.s6.1d60e7f17e52 from=seed src=0 shape=055e1e62 vocab=583f33a9
-/
@[simp] theorem symm_apply_apply (e : G ≃+c[a, b] H) (a) :
    e.symm (e a) = a :=
  e.toEquiv.symm_apply_apply _

/-- The identity map as an `AddConstEquiv`. -/
@[simps! toEquiv apply]
def refl (a : G) : G ≃+c[a, a] G where
  toEquiv := .refl G
  map_add_const' _ := rfl

/--
@isnad1 id=eq.0h2v.s4.c4627d6f8837 from=seed src=0 shape=58688174 vocab=00d6e451
-/
@[simp] lemma symm_refl (a : G) : (refl a).symm = refl a := rfl

/-- Composition of `AddConstEquiv`s, as an `AddConstEquiv`. -/
@[simps! +simpRhs toEquiv apply]
def trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) : G ≃+c[a, c] K where
  toEquiv := e₁.toEquiv.trans e₂.toEquiv
  map_add_const' := (AddConstMapClass.semiconj e₁).trans (AddConstMapClass.semiconj e₂)

/--
@isnad1 id=eq.0h5v.s5.efcf6e9d84fd from=seed src=0 shape=5658525f vocab=b2c4885b
-/
@[simp] lemma trans_refl (e : G ≃+c[a, b] H) : e.trans (.refl b) = e := rfl
/--
@isnad1 id=eq.0h5v.s5.a7b6931df2f6 from=seed src=0 shape=08553dae vocab=b2c4885b
-/
@[simp] lemma refl_trans (e : G ≃+c[a, b] H) : (refl a).trans e = e := rfl

/--
@isnad1 id=eq.0h5v.s5.c2398c2f3de0 from=seed src=0 shape=acbfad47 vocab=b9cb2ce0
-/
@[simp]
lemma self_trans_symm (e : G ≃+c[a, b] H) : e.trans e.symm = .refl a :=
  toEquiv_injective e.toEquiv.self_trans_symm

/--
@isnad1 id=eq.0h5v.s5.fd5d8bb0f421 from=seed src=0 shape=c7a2546e vocab=b9cb2ce0
-/
@[simp]
lemma symm_trans_self (e : G ≃+c[a, b] H) : e.symm.trans e = .refl b :=
  toEquiv_injective e.toEquiv.symm_trans_self

/--
@isnad1 id=eq.0h5v.s6.1b9f1714982b from=seed src=0 shape=a5225680 vocab=e9749dff
-/
@[simp]
lemma coe_symm_toEquiv (e : G ≃+c[a, b] H) : ⇑e.toEquiv.symm = e.symm := rfl

/--
@isnad1 id=eq.0h5v.s5.6a227cfc4779 from=seed src=0 shape=2b68a467 vocab=045ae682
-/
@[simp]
lemma toEquiv_symm (e : G ≃+c[a, b] H) : e.symm.toEquiv = e.toEquiv.symm := rfl

/--
@isnad1 id=eq.0h8v.s6.0d9154ecd381 from=seed src=0 shape=6d37727d vocab=db5bfc7f
-/
@[simp]
lemma toEquiv_trans (e₁ : G ≃+c[a, b] H) (e₂ : H ≃+c[b, c] K) :
    (e₁.trans e₂).toEquiv = e₁.toEquiv.trans e₂.toEquiv := rfl

instance instOne : One (G ≃+c[a, a] G) := ⟨.refl _⟩
instance instMul : Mul (G ≃+c[a, a] G) := ⟨fun f g ↦ g.trans f⟩
instance instInv : Inv (G ≃+c[a, a] G) := ⟨.symm⟩
instance instDiv : Div (G ≃+c[a, a] G) := ⟨fun f g ↦ f * g⁻¹⟩

instance instPowNat : Pow (G ≃+c[a, a] G) ℕ where
  pow e n := ⟨e^n, (e.toAddConstMap^n).map_add_const'⟩

instance instPowInt : Pow (G ≃+c[a, a] G) ℤ where
  pow e n := ⟨e^n,
    match n with
    | .ofNat n => (e^n).map_add_const'
    | .negSucc n => (e.symm^(n + 1)).map_add_const'⟩

instance instGroup : Group (G ≃+c[a, a] G) :=
  toEquiv_injective.group _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)
    fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to permutations `G ≃ G`, as a monoid homomorphism. -/
@[simps! apply]
def toPerm : (G ≃+c[a, a] G) →* Equiv.Perm G :=
  .mk' toEquiv fun _ _ ↦ rfl

/-- Projection from `G ≃+c[a, a] G` to `G →+c[a, a] G`, as a monoid homomorphism. -/
@[simps! apply]
def toAddConstMapHom : (G ≃+c[a, a] G) →* (G →+c[a, a] G) where
  toFun := toAddConstMap
  map_mul' _ _ := rfl
  map_one' := rfl

/-- Group equivalence between `G ≃+c[a, a] G` and the units of `G →+c[a, a] G`. -/
@[simps!]
def equivUnits : (G ≃+c[a, a] G) ≃* (G →+c[a, a] G)ˣ where
  toFun := toAddConstMapHom.toHomUnits
  invFun u :=
    { toEquiv := Equiv.Perm.equivUnitsEnd.symm <| Units.map AddConstMap.toEnd u
      map_add_const' := u.1.2 }
  map_mul' _ _ := rfl

end AddConstEquiv
