/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Tengoku.LeanPool.LeanPool.VirasoroProject.LieCohomologySmallDegree

/-!
# Central extensions of Lie algebras defined by 2-cocycles

This file defines the central extension of a Lie algebra determined by a 2-cocycle. It is proven
that two central extensions are isomorphic if the corresponding cocycles differ by a coboundary.

## Main definitions

* `LieTwoCocycle.CentralExtension`: The central extension of a Lie algebra 𝓰 by an abelian Lie
  algebra 𝓪 defined by a 2-cocycle γ ∈ H²(𝓰,𝓪).
* `LieTwoCocycle.CentralExtension.equivOfLieTwoCoboundary`: An isomorphism between the central
  extensions defined by two 2-cocycles which differ by a coboundary.

## Main statements

* `LieTwoCocycle.CentralExtension.instLieAlgebra`: The central extension defined by a 2-cocycle
  is a Lie algebra.

## Implementation notes

`LieTwoCocycle.CentralExtension` is the concrete construction of a central extension. The defining
property (characteristic predicate) of central extensions is `IsCentralExtension`
(see the file `IsCentralExtension.lean`.)

## Tags

Lie algebra, central extension, 2-cocycle

-/

@[expose] public section

namespace VirasoroProject

universe u
variable (𝕜 : Type*) [CommRing 𝕜]
variable (𝓰 𝓪 : Type u) [LieRing 𝓰] [AddCommGroup 𝓪] [LieAlgebra 𝕜 𝓰] [Module 𝕜 𝓪]

variable {𝕜 𝓰 𝓪}

section LieTwoCocycle.CentralExtension

/-! ### Lie algebra central extensions determined by 2-cocycles -/

namespace LieTwoCocycle

/-- The underlying type of the central extension of Lie algebras determined by a Lie
algebra 2-cocycle. -/
def CentralExtension (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :=
  let _ : LieTwoCocycle 𝕜 𝓰 𝓪 := γ
  𝓰 × 𝓪

variable {γ : LieTwoCocycle 𝕜 𝓰 𝓪}

namespace CentralExtension

/--
@isnad1 id=eq.2h6v.s6.b6d46ceb8281 from=translated src=- shape=09e32600 vocab=5126ec27
-/
@[ext] lemma ext {Z W : γ.CentralExtension} (hX : Z.1 = W.1) (hA : Z.2 = W.2) :
    Z = W := Prod.ext hX hA

/-- Coercion of an element in a central extension to a pair. -/
def coeProd (Z : γ.CentralExtension) : 𝓰 × 𝓪 := Z

instance : AddCommGroup (γ.CentralExtension) := Prod.instAddCommGroup

instance : Module 𝕜 (γ.CentralExtension) := Prod.instModule

/--
@isnad1 id=eq.0h6v.s7.7167fa8db414 from=translated src=- shape=70324f43 vocab=4e5e90ed
-/
lemma add_def (Z₁ Z₂ : γ.CentralExtension) :
  Z₁ + Z₂ = ⟨Z₁.1 + Z₂.1, Z₁.2 + Z₂.2⟩ := rfl

/--
@isnad1 id=eq.0h6v.s9.f7b5d61f05ca from=translated src=- shape=d97a8f0a vocab=67be37b5
-/
lemma smul_def (c : 𝕜) (Z : γ.CentralExtension) :
  c • Z = ⟨c • Z.1, c • Z.2⟩ := rfl

/--
@isnad1 id=eq.0h6v.s7.2c095f49de08 from=translated src=- shape=1071fb67 vocab=f9980a07
-/
@[simp] lemma add_fst (Z W : γ.CentralExtension) :
    (Z + W).1 = Z.1 + W.1 := rfl

/--
@isnad1 id=eq.0h6v.s7.191932cb07d2 from=translated src=- shape=a0e72eb1 vocab=9194d37f
-/
@[simp] lemma add_snd (Z W : γ.CentralExtension) :
    (Z + W).2 = Z.2 + W.2 := rfl

/--
@isnad1 id=eq.0h6v.s8.6c42bf12c9ea from=translated src=- shape=c8e587a8 vocab=d63d6036
-/
@[simp] lemma smul_fst (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).1 = c • Z.1 := rfl

/--
@isnad1 id=eq.0h6v.s8.6710d61d7f66 from=translated src=- shape=338b623e vocab=0e65cf48
-/
@[simp] lemma smul_snd (c : 𝕜) (Z : γ.CentralExtension) :
    (c • Z).2 = c • Z.2 := rfl

end CentralExtension -- namespace

variable (γ)

open LinearMapClass RingHom in
/-- The Lie bracket in a central extension defined by a Lie algebra 2-cocycle. -/
def bracket : γ.CentralExtension
      →ₗ[𝕜] γ.CentralExtension →ₗ[𝕜] γ.CentralExtension where
  toFun := fun ⟨X,_⟩ ↦ {
    toFun := fun ⟨Y,_⟩ ↦ ⟨⁅X,Y⁆, γ X Y⟩
    map_add' := by intros; simp_all only [lie_add, map_add]; rfl
    map_smul' := by
      rintro m ⟨Y, _⟩
      ext
      · change ⁅X, m • Y⁆ = m • ⁅X, Y⁆
        exact lie_smul m X Y
      · change (γ X) (m • Y) = m • (γ X) Y
        exact map_smul (γ X) m Y }
  map_add' := by
    intros
    simp_all only [add_lie, map_add, LinearMap.add_apply]
    rfl
  map_smul' := by
    rintro m ⟨X, _⟩
    ext ⟨Y, _⟩
    · change ⁅m • X, Y⁆ = m • ⁅X, Y⁆
      exact smul_lie m X Y
    · change (γ (m • X)) Y = m • (γ X) Y
      exact congrArg (fun f => f Y) (map_smul γ m X)

/--
@isnad1 id=eq.0h6v.s10.2bb4eec7ca53 from=translated src=- shape=975e18e4 vocab=88ed2957
-/
@[simp] lemma bracket_apply (Z W : γ.CentralExtension) :
    γ.bracket Z W = ⟨⁅Z.fst, W.fst⁆, γ Z.fst W.fst⟩ := rfl

/--
@isnad1 id=eq.0h5v.s10.f6fb879e490f from=translated src=- shape=c5b0c4c3 vocab=85f375a8
-/
lemma bracket_self (Z : γ.CentralExtension) :
    γ.bracket Z Z = 0 := by
  simp; rfl

/--
@isnad1 id=eq.0h7v.s11.d76ce1fd5591 from=translated src=- shape=eadd44ba vocab=4de71639
-/
lemma bracket_smul (c : 𝕜) (Z W : γ.CentralExtension) :
    γ.bracket Z (c • W) = c • γ.bracket Z W := by
  simp only [LinearMapClass.map_smul, LieTwoCocycle.bracket_apply]

/--
@isnad1 id=eq.0h7v.s12.42d193d1c71c from=translated src=- shape=16ce8f32 vocab=296b07f7
-/
lemma bracket_leibniz (Z W₁ W₂ : γ.CentralExtension) :
    γ.bracket Z (γ.bracket W₁ W₂)
      = γ.bracket (γ.bracket Z W₁) W₂ + γ.bracket W₁ (γ.bracket Z W₂) := by
  simp only [γ.bracket_apply]
  ext
  · exact leibniz_lie Z.1 W₁.1 W₂.1
  · apply γ.leibniz

namespace CentralExtension

/-- The central extension is a Lie ring. -/
instance : LieRing γ.CentralExtension where
  bracket Z W := γ.bracket Z W
  add_lie Z₁ Z₂ W := by simp
  lie_add Z W₁ W₂ := by simp; rfl
  lie_self := γ.bracket_self
  leibniz_lie Z₁ Z₂ W := γ.bracket_leibniz Z₁ Z₂ W

/-- The central extension is a Lie algebra. -/
instance : LieAlgebra 𝕜 γ.CentralExtension where
  lie_smul := γ.bracket_smul

/--
@isnad1 id=eq.0h6v.s8.96945bb8aa05 from=translated src=- shape=b992afed vocab=d2ddb12e
-/
lemma lie_def (Z W : γ.CentralExtension) :
    ⁅Z, W⁆ = ⟨⁅Z.1, W.1⁆, γ Z.1 W.1⟩ := rfl

/--
@isnad1 id=eq.0h6v.s7.e83c07da2f9b from=translated src=- shape=cfc2f0c2 vocab=1486df8e
-/
@[simp] lemma lie_fst (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.1 = ⁅Z.1, W.1⁆ := rfl

/--
@isnad1 id=eq.0h6v.s8.36e62c0ac672 from=translated src=- shape=8d62c3d5 vocab=e90fe2ee
-/
@[simp] lemma lie_snd (Z W : γ.CentralExtension) :
    ⁅Z, W⁆.2 = γ Z.1 W.1 := rfl

end CentralExtension -- namespace

end LieTwoCocycle -- namespace

variable (β : LieOneCochain 𝕜 𝓰 𝓪)
variable (γ)

/-- A Lie algebra homomorphism between two central extensions determined by cocycles
which differ by a coboundary. -/
def _root_.VirasoroProject.LieOneCochain.bdryHom :
    (γ.CentralExtension) →ₗ⁅𝕜⁆ (γ + β.bdry).CentralExtension where
  toFun := fun Z ↦ ⟨Z.1, Z.2 + β Z.1⟩
  map_add' Z W := by
    ext
    · rfl
    · change Z.2 + W.2 + β (Z.1 + W.1) = Z.2 + β Z.1 + (W.2 + β W.1)
      simp only [map_add]
      ac_rfl
  map_smul' c Z := by
    ext
    · rfl
    · change c • Z.2 + β (c • Z.1) = c • (Z.2 + β Z.1)
      rw [map_smul, smul_add]
  map_lie' := by
    intro Z W
    ext <;> rfl

namespace LieTwoCocycle.CentralExtension

/-- Annoyingly the dependent types make it difficult to identify central extensions with equal
but not definitionally equal cocycles (e.g. `γ + (β₁ + β₂).bdry` vs. `(γ + β₁.bdry) + β₂.bdry`).
This isomorphism transports central extensions across equal cocycles. -/
def congr {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂) :
    γ₁.CentralExtension ≃ₗ⁅𝕜⁆ γ₂.CentralExtension where
  toFun := fun Z ↦ ⟨Z.1, Z.2⟩
  map_add' Z₁ Z₂ := rfl
  map_smul' c Z := rfl
  map_lie' := by
    intro Z₁ Z₂
    ext <;>
    · simp only [lie_def, h]; rfl
  invFun := fun Z ↦ ⟨Z.1, Z.2⟩
  left_inv := by
    intro Z
    ext <;> dsimp only
  right_inv := by
    intro Z
    ext <;> dsimp only

/--
@isnad1 id=eq.1h6v.s8.4fd8e224f273 from=translated src=- shape=2df995d4 vocab=fdbbdfbc
-/
lemma congr_apply {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂) (Z : γ₁.CentralExtension) :
    congr h Z = ⟨Z.1, Z.2⟩ := rfl

/--
@isnad1 id=eq.2h6v.s8.ae10d7a10a6a from=translated src=- shape=b024cdc1 vocab=e4628d83
-/
@[simp] lemma congr_trans {γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓰 𝓪} (h₁₂ : γ₁ = γ₂) (h₂₃ : γ₂ = γ₃) :
    (congr h₁₂).trans (congr h₂₃) = (congr (h₁₂.trans h₂₃)) :=
  rfl

/--
@isnad1 id=eq.1h5v.s8.cdc710e69bc2 from=translated src=- shape=03111dca vocab=5951e016
-/
lemma congr_congr_symm {γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪} (h : γ₁ = γ₂) :
    (congr h).trans (congr h.symm) = LieEquiv.refl :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.500e986f7f69 from=translated src=- shape=57a18e5a vocab=3bbf1441
-/
lemma hom_of_coboundary_refl (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    congr (Eq.refl γ) = LieEquiv.refl (R := 𝕜) (L₁ := γ.CentralExtension) :=
  rfl

/--
@isnad1 id=eq.2h8v.s11.335bb3c63112 from=translated src=- shape=106d6757 vocab=03b0f91b
-/
lemma hom_of_coboundary_add (γ₁ γ₂ γ₃ : LieTwoCocycle 𝕜 𝓰 𝓪)
    (β₁ β₂ : LieOneCochain 𝕜 𝓰 𝓪) (h₂ : γ₁ + β₁.bdry = γ₂) (h₃ : γ₂ + β₂.bdry = γ₃) :
    ((congr h₃).toLieHom.comp (β₂.bdryHom γ₂)).comp ((congr h₂).toLieHom.comp (β₁.bdryHom γ₁))
      = (congr (show γ₁ + (β₁ + β₂).bdry = γ₃ by rw [← h₃, ← h₂]; ac_rfl)).toLieHom.comp
          ((β₁ + β₂).bdryHom γ₁) := by
  ext Z
  · rfl
  · change (Z.2 + β₁ Z.1) + β₂ Z.1 = Z.2 + (β₁ + β₂) Z.1
    rw [LieOneCochain.add_apply]
    ac_rfl

/-- A Lie algebra isomorphism between two central extensions determined by cocycles
which differ by a coboundary. -/
noncomputable def equivOfLieTwoCoboundary {γ' : LieTwoCocycle 𝕜 𝓰 𝓪}
    (h : γ' - γ ∈ LieTwoCoboundary 𝕜 𝓰 𝓪) :
    (γ.CentralExtension) ≃ₗ⁅𝕜⁆ (γ'.CentralExtension) :=
  let β := h.choose
  have obs : γ + β.bdry = γ' := by
    change γ + LieOneCochainBdryHom _ _ _ h.choose = γ'; simp [h.choose_spec]
  have obs' : γ' + -β.bdry = γ := by
    change γ' - LieOneCochainBdryHom _ _ _ h.choose = γ; simp [h.choose_spec]
  LieEquiv.mkOfCompEqId
      (f := (LieTwoCocycle.CentralExtension.congr obs).toLieHom.comp <| β.bdryHom γ)
      (g := (LieTwoCocycle.CentralExtension.congr obs').toLieHom.comp <| (-β).bdryHom γ')
      (by
        ext Z
        · rfl
        · change (Z.2 + β Z.1) + (-β) Z.1 = Z.2
          rw [LieOneCochain.neg_apply]
          exact add_neg_cancel_right Z.2 (β Z.1))
      (by
        ext Z
        · rfl
        · change (Z.2 + (-β) Z.1) + β Z.1 = Z.2
          rw [LieOneCochain.neg_apply]
          exact neg_add_cancel_right Z.2 (β Z.1))

end CentralExtension -- namespace

end LieTwoCocycle -- namespace

end LieTwoCocycle.CentralExtension -- section

end VirasoroProject -- namespace
