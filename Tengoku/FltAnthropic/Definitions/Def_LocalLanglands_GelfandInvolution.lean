import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_LocalLanglands_HeckePair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open scoped Pointwise

namespace HeckePair

noncomputable section

variable {G : Type*} [Group G] {U : Subgroup G}
variable {R₀ : Type*} [CommRing R₀]

/--
@isnad1 id=eq.1h6v.s9.b02906722c90 from=translated src=- shape=2ea567b7 vocab=a22200b5
-/
theorem apply_eq_of_mem_doubleCoset (f : HeckeAlgebra U R₀) {g x : G}
    (hx : x ∈ doubleCoset U g) : (f : G → R₀) x = (f : G → R₀) g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  rw [apply_mul_right f hv, apply_left_mul f hu]

/--
@isnad1 id=eq.1h4v.s5.fb70232fd00b from=translated src=- shape=dc945d58 vocab=64519650
-/
theorem doubleCoset_eq_of_mem {g x : G} (hx : x ∈ doubleCoset U g) :
    doubleCoset U x = doubleCoset U g := by
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hx
  ext w
  constructor
  · intro hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hw
    exact mem_doubleCoset_iff.mpr ⟨a * u, mul_mem ha hu, v * b, mul_mem hv hb, by group⟩
  · intro hw
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset_iff.mp hw
    exact mem_doubleCoset_iff.mpr
      ⟨a * u⁻¹, mul_mem ha (inv_mem hu), v⁻¹ * b, mul_mem (inv_mem hv) hb, by group⟩

variable (U) in

structure IsGelfandInvolution (τ : G → G) : Prop where

  map_mul : ∀ x y, τ (x * y) = τ y * τ x

  involutive : ∀ x, τ (τ x) = x

  map_mem : ∀ u ∈ U, τ u ∈ U

  mem_doubleCoset : ∀ g, τ g ∈ doubleCoset U g

namespace IsGelfandInvolution

variable {τ : G → G} (hτ : IsGelfandInvolution U τ)

include hτ

/--
@isnad1 id=eq.1h3v.s5.141fe133db2e from=translated src=- shape=d143a9ba vocab=0cb914b8
-/
theorem map_one : τ 1 = 1 := by
  have h := hτ.map_mul 1 1
  rw [one_mul] at h

  exact (mul_right_cancel (a := (1 : G)) (b := τ 1) (by rw [one_mul, ← h])).symm

/--
@isnad1 id=eq.1h4v.s5.b258796d4803 from=translated src=- shape=64a19021 vocab=d34a802c
-/
theorem map_inv (x : G) : τ x⁻¹ = (τ x)⁻¹ := by
  have h : τ x⁻¹ * τ x = 1 := by rw [← hτ.map_mul, mul_inv_cancel, hτ.map_one]
  exact eq_inv_of_mul_eq_one_left h

/--
@isnad1 id=bijectiv.1h3v.s4.f9f254375879 from=translated src=- shape=1435cdc9 vocab=2fe15359
-/
theorem bijective : Function.Bijective τ :=
  Function.Involutive.bijective hτ.involutive

/--
@isnad1 id=eq.1h6v.s9.ea8876ae1a16 from=translated src=- shape=5e15fd13 vocab=3b913069
-/
theorem apply_tau (f : HeckeAlgebra U R₀) (x : G) : (f : G → R₀) (τ x) = (f : G → R₀) x :=
  apply_eq_of_mem_doubleCoset f (hτ.mem_doubleCoset x)

protected def reindex (x : G) : G ⧸ U → G ⧸ U :=
  Quotient.lift (fun y => (QuotientGroup.mk (x * (τ y)⁻¹) : G ⧸ U)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    refine (QuotientGroup.eq.mpr ?_).symm

    rw [hτ.map_mul a u]
    have hgrp : (x * (τ u * τ a)⁻¹)⁻¹ * (x * (τ a)⁻¹) = τ u := by group
    rw [hgrp]
    exact hτ.map_mem u hu

/--
@isnad1 id=eq.1h5v.s6.24c3f9cee9d2 from=translated src=- shape=f5efcca7 vocab=4247d56f
-/
@[simp] theorem reindex_mk (x y : G) :
    hτ.reindex x (QuotientGroup.mk y) = QuotientGroup.mk (x * (τ y)⁻¹) := rfl

protected def reindexInv (x : G) : G ⧸ U → G ⧸ U :=
  Quotient.lift (fun z => (QuotientGroup.mk (τ (z⁻¹ * x)) : G ⧸ U)) <| by
    intro a b hab
    obtain ⟨u, hu, rfl⟩ : ∃ u ∈ U, a * u = b :=
      ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab, by group⟩
    refine (QuotientGroup.eq.mpr ?_).symm

    have hexp : (a * u)⁻¹ * x = u⁻¹ * (a⁻¹ * x) := by group
    rw [hexp, hτ.map_mul, hτ.map_inv]
    have hgrp : (τ (a⁻¹ * x) * (τ u)⁻¹)⁻¹ * τ (a⁻¹ * x) = τ u := by group
    rw [hgrp]
    exact hτ.map_mem u hu

/--
@isnad1 id=eq.1h5v.s6.7d7dbd7facda from=translated src=- shape=e0004c54 vocab=216167cd
-/
@[simp] theorem reindexInv_mk (x z : G) :
    hτ.reindexInv x (QuotientGroup.mk z) = QuotientGroup.mk (τ (z⁻¹ * x)) := rfl

/--
@isnad1 id=bijectiv.1h4v.s5.a968fe52a9f0 from=translated src=- shape=c9931e58 vocab=0d149313
-/
theorem bijective_reindex (x : G) : Function.Bijective (hτ.reindex x) := by
  have hleft : ∀ c, hτ.reindexInv x (hτ.reindex x c) = c := by
    refine fun c => Quotient.inductionOn c fun y => ?_
    rw [reindex_mk, reindexInv_mk]
    refine congrArg _ ?_
    have h1 : (x * (τ y)⁻¹)⁻¹ * x = τ y := by group
    rw [h1, hτ.involutive]
  have hright : ∀ c, hτ.reindex x (hτ.reindexInv x c) = c := by
    refine fun c => Quotient.inductionOn c fun z => ?_
    rw [reindexInv_mk, reindex_mk]
    refine congrArg _ ?_
    rw [hτ.involutive]
    group
  exact Function.bijective_iff_has_inverse.mpr ⟨hτ.reindexInv x, hleft, hright⟩

/--
@isnad1 id=eq.1h8v.s8.8ec3b7d44534 from=translated src=- shape=19de24ab vocab=8b8591ca
-/
theorem convTerm_tau (f₁ f₂ : HeckeAlgebra U R₀) (x : G) (c : G ⧸ U) :
    convTerm f₁ f₂ (τ x) c = convTerm f₂ f₁ x (hτ.reindex x c) := by
  refine Quotient.inductionOn c fun y => ?_
  rw [reindex_mk, convTerm_mk, convTerm_mk]

  have h2 : (x * (τ y)⁻¹)⁻¹ * x = τ y := by group
  rw [h2, hτ.apply_tau f₁ y]

  have h1 : (f₂ : G → R₀) (y⁻¹ * τ x) = (f₂ : G → R₀) (x * (τ y)⁻¹) := by
    conv_lhs => rw [← hτ.apply_tau f₂ (y⁻¹ * τ x)]
    rw [hτ.map_mul, hτ.involutive, hτ.map_inv]
  rw [h1, mul_comm]

/--
@isnad1 id=eq.1h7v.s10.535e35d02bf3 from=translated src=- shape=43bbb6e5 vocab=8a08f185
-/
theorem mul_apply_tau (f₁ f₂ : HeckeAlgebra U R₀) (x : G) :
    ((f₁ * f₂ : HeckeAlgebra U R₀) : G → R₀) (τ x)
      = ((f₂ * f₁ : HeckeAlgebra U R₀) : G → R₀) x := by
  rw [mul_apply, mul_apply]
  exact finsum_eq_of_bijective (hτ.reindex x) (hτ.bijective_reindex x)
    (hτ.convTerm_tau f₁ f₂ x)

/--
@isnad1 id=eq.1h6v.s10.bb768b29a98f from=translated src=- shape=b854fb50 vocab=52785206
-/
theorem heckeMul_comm (f₁ f₂ : HeckeAlgebra U R₀) : f₁ * f₂ = f₂ * f₁ := by
  ext x

  rw [← hτ.apply_tau (f₁ * f₂) x, hτ.mul_apply_tau f₁ f₂ x]

@[reducible] protected def commRing : CommRing (HeckeAlgebra U R₀) :=
  { (inferInstance : Ring (HeckeAlgebra U R₀)) with
    mul_comm := hτ.heckeMul_comm }

end IsGelfandInvolution

/--
@isnad1 id=isgelfan.4h3v.s7.a760625353c3 from=translated src=- shape=7bf1f2a8 vocab=15610f73
-/
theorem IsGelfandInvolution.of_forall_exists_fixedRep {τ : G → G}
    (hmul : ∀ x y, τ (x * y) = τ y * τ x) (hinv : ∀ x, τ (τ x) = x)
    (hU : ∀ u ∈ U, τ u ∈ U)
    (hrep : ∀ g : G, ∃ d, τ d = d ∧ g ∈ doubleCoset U d) :
    IsGelfandInvolution U τ := by
  refine ⟨hmul, hinv, hU, fun g => ?_⟩
  obtain ⟨d, hd, hgd⟩ := hrep g

  rw [doubleCoset_eq_of_mem hgd]
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_doubleCoset_iff.mp hgd
  rw [hmul, hmul, hd]
  exact mem_doubleCoset_iff.mpr ⟨τ v, hU v hv, τ u, hU u hu, by group⟩

end

end HeckePair
