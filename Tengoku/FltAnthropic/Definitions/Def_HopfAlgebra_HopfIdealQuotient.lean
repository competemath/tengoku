import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped TensorProduct
open Coalgebra Bialgebra WithConv

namespace HopfAlgebra

section AntipodeAlgHom

variable (R : Type*) [CommSemiring R] (H : Type*) [CommSemiring H] [HopfAlgebra R H]

/--
@isnad1 id=eq.0h2v.s7.7d98d5546003 from=translated src=- shape=fd832425 vocab=3f9c9c53
-/
theorem antipodeAlgHom_toLinearMap : (antipodeAlgHom R H).toLinearMap = antipode R := rfl

variable {R H}
variable {A : Type*} [CommSemiring A] [Algebra R A]

/--
@isnad1 id=eq.0h5v.s11.56a995eac0a8 from=translated src=- shape=72befa50 vocab=35dbd8b1
-/
theorem lift_comp_antipodeAlgHom_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift φ (φ.comp (antipodeAlgHom R H)) (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).lTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.lTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

/--
@isnad1 id=eq.0h5v.s11.5728d81bee48 from=translated src=- shape=c34052dc vocab=461d0177
-/
theorem lift_antipodeAlgHom_comp_apply (φ : H →ₐ[R] A) (z : H ⊗[R] H) :
    Algebra.TensorProduct.lift (φ.comp (antipodeAlgHom R H)) φ (fun _ _ => .all _ _) z =
      φ (LinearMap.mul' R H ((antipode R).rTensor H z)) := by
  induction z with
  | zero => simp
  | tmul x y => simp [LinearMap.rTensor_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

/--
@isnad1 id=eq.0h4v.s8.ecc015e42f05 from=translated src=- shape=eed2f737 vocab=90c61015
-/
theorem convMul_comp_antipodeAlgHom (φ : H →ₐ[R] A) :
    toConv φ * toConv (φ.comp (antipodeAlgHom R H)) = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv φ * toConv (φ.comp (antipodeAlgHom R H))) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_comp_antipodeAlgHom_apply, mul_antipode_lTensor_comul_apply, AlgHom.commutes]

/--
@isnad1 id=eq.0h4v.s8.f3a8934c85e1 from=translated src=- shape=915f079c vocab=90c61015
-/
theorem comp_antipodeAlgHom_convMul (φ : H →ₐ[R] A) :
    toConv (φ.comp (antipodeAlgHom R H)) * toConv φ = 1 := by
  refine WithConv.ext (AlgHom.ext fun x => ?_)
  change (toConv (φ.comp (antipodeAlgHom R H)) * toConv φ) x = (1 : WithConv (H →ₐ[R] A)) x
  rw [AlgHom.convMul_apply, AlgHom.convOne_apply, ofConv_toConv, ofConv_toConv,
    lift_antipodeAlgHom_comp_apply, mul_antipode_rTensor_comul_apply, AlgHom.commutes]

/--
@isnad1 id=isunit.0h4v.s7.a26f6baa331e from=translated src=- shape=292e6aa9 vocab=d4e26cb5
-/
theorem isUnit_toConv_algHom (φ : H →ₐ[R] A) : IsUnit (toConv φ) :=
  isUnit_iff_exists.2 ⟨_, convMul_comp_antipodeAlgHom φ, comp_antipodeAlgHom_convMul φ⟩

end AntipodeAlgHom

section ConvComp

variable {R : Type*} [CommSemiring R] {H G : Type*} [CommSemiring H] [CommSemiring G]
  [Bialgebra R H] [Bialgebra R G]
variable (A : Type*) [CommSemiring A] [Algebra R A]

def convCompMonoidHom (π : H →ₐc[R] G) : WithConv (G →ₐ[R] A) →* WithConv (H →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (π : H →ₐ[R] G))
  map_one' := by
    refine WithConv.ext ?_
    simp only [ofConv_toConv, AlgHom.convOne_def, AlgHom.comp_assoc, BialgHom.counitAlgHom_comp]
  map_mul' f g := by
    rw [AlgHom.convMul_comp_bialgHom_distrib]

/--
@isnad1 id=eq.0h6v.s9.5aac3ab2f787 from=translated src=- shape=3895fec4 vocab=655ef04b
-/
@[simp] theorem convCompMonoidHom_apply (π : H →ₐc[R] G) (f : WithConv (G →ₐ[R] A)) :
    convCompMonoidHom A π f = toConv (f.ofConv.comp (π : H →ₐ[R] G)) := rfl

end ConvComp

end HopfAlgebra

section IsHopfIdeal'

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

class Ideal.IsHopfIdeal' (I : Ideal H) : Prop where
  map_mkₐ_comul_eq_zero : ∀ x ∈ I,
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) x) = 0
  counit_eq_zero : ∀ x ∈ I, Coalgebra.counit (R := R) x = 0
  antipode_mem : ∀ x ∈ I, HopfAlgebra.antipode R x ∈ I

/--
@isnad1 id=ishopfid.0h2v.s5.b8ae1696ca0f from=translated src=- shape=811023aa vocab=04a3b506
-/
instance Ideal.isHopfIdeal_bot : (⊥ : Ideal H).IsHopfIdeal' R where
  map_mkₐ_comul_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  counit_eq_zero x hx := by rw [(Ideal.mem_bot).1 hx]; simp
  antipode_mem x hx := by rw [(Ideal.mem_bot).1 hx]; simp

end IsHopfIdeal'

namespace HopfAlgebra

namespace HopfIdealQuotient

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]
variable (I : Ideal H) [hI : I.IsHopfIdeal' R]

def comul : H ⧸ I →ₐ[R] (H ⧸ I) ⊗[R] (H ⧸ I) :=
  Ideal.Quotient.liftₐ I
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
      (comulAlgHom R H))
    (fun x hx => hI.map_mkₐ_comul_eq_zero x hx)

/--
@isnad1 id=eq.0h3v.s11.a16b18ea1564 from=translated src=- shape=60b49a87 vocab=c35b2ea4
-/
theorem comul_comp_mkₐ :
    (comul R I).comp (Ideal.Quotient.mkₐ R I) =
      (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)).comp
        (comulAlgHom R H) :=
  Ideal.Quotient.liftₐ_comp _ _ _

/--
@isnad1 id=eq.0h4v.s12.c73e8c1f613a from=translated src=- shape=3d8be8e7 vocab=7afd2dad
-/
@[simp] theorem comul_mk (x : H) :
    comul R I (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

def counit : H ⧸ I →ₐ[R] R :=
  Ideal.Quotient.liftₐ I (counitAlgHom R H) (fun x hx => hI.counit_eq_zero x hx)

/--
@isnad1 id=eq.0h3v.s8.7b77a325d016 from=translated src=- shape=f5dad658 vocab=106e3b9b
-/
theorem counit_comp_mkₐ : (counit R I).comp (Ideal.Quotient.mkₐ R I) = counitAlgHom R H :=
  Ideal.Quotient.liftₐ_comp _ _ _

/--
@isnad1 id=eq.0h4v.s9.9ae6ff30e74d from=translated src=- shape=6ebb6733 vocab=f4689a98
-/
@[simp] theorem counit_mk (x : H) :
    counit R I (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

def antipode : H ⧸ I →ₐ[R] H ⧸ I :=
  Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R I).comp (antipodeAlgHom R H)) (fun x hx => by
    simp only [AlgHom.comp_apply, antipodeAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hI.antipode_mem x hx)

/--
@isnad1 id=eq.0h4v.s9.859d9777cbd3 from=translated src=- shape=70fe99e7 vocab=627d0f41
-/
@[simp] theorem antipode_mk (x : H) :
    antipode R I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

private theorem map_apply_eq_linearMap {A B C D : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    (f : A →ₐ[R] C) (g : B →ₐ[R] D) (z : A ⊗[R] B) :
    Algebra.TensorProduct.map f g z = TensorProduct.map f.toLinearMap g.toLinearMap z := rfl

/--
@isnad1 id=eq.0h3v.s11.46af21964232 from=translated src=- shape=381919b2 vocab=dd8c53db
-/
theorem rTensor_counit_comul :
    (Algebra.TensorProduct.map (counit R I) (.id R (H ⧸ I))).comp (comul R I) =
      (Algebra.TensorProduct.lid R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.lid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (counitAlgHom R H).toLinearMap (Ideal.Quotient.mkₐ R I).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.lTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.rTensor H) from
      (LinearMap.lTensor_comp_rTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.rTensor H) (Coalgebra.comul x) = 1 ⊗ₜ x from
    Coalgebra.rTensor_counit_comul x]
  simp

/--
@isnad1 id=eq.0h3v.s11.d4033f5f644c from=translated src=- shape=4e3270ee vocab=6d535d70
-/
theorem lTensor_counit_comul :
    (Algebra.TensorProduct.map (.id R (H ⧸ I)) (counit R I)).comp (comul R I) =
      (Algebra.TensorProduct.rid R R (H ⧸ I)).symm := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp,
    counit_comp_mkₐ, AlgHom.id_comp]
  refine AlgHom.ext fun x => ?_
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.rid_symm_apply,
    map_apply_eq_linearMap, Bialgebra.comulAlgHom_apply]
  rw [show TensorProduct.map (Ideal.Quotient.mkₐ R I).toLinearMap (counitAlgHom R H).toLinearMap
      = ((Ideal.Quotient.mkₐ R I).toLinearMap.rTensor R) ∘ₗ
          ((counitAlgHom R H).toLinearMap.lTensor H) from
      (LinearMap.rTensor_comp_lTensor _ _ _).symm, LinearMap.comp_apply]
  rw [show ((counitAlgHom R H).toLinearMap.lTensor H) (Coalgebra.comul x) = x ⊗ₜ 1 from
    Coalgebra.lTensor_counit_comul x]
  simp

private theorem assoc_map_map_apply {A B : Type*} [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (z : (A ⊗[R] A) ⊗[R] A) :
    (Algebra.TensorProduct.assoc R R R B B B)
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f f) f z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map f f)
        (Algebra.TensorProduct.assoc R R R A A A z) := by
  induction z with
  | zero => simp
  | tmul xy c =>
    induction xy with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

/--
@isnad1 id=eq.0h3v.s14.988e25eb10e0 from=translated src=- shape=3606fc10 vocab=465a226e
-/
theorem coassoc :
    (Algebra.TensorProduct.assoc R R R (H ⧸ I) (H ⧸ I) (H ⧸ I)).toAlgHom.comp
        ((Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I))).comp (comul R I)) =
      (Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I)).comp (comul R I) := by
  refine Ideal.Quotient.algHom_ext R ?_
  refine AlgHom.ext fun x => ?_
  set π := Ideal.Quotient.mkₐ R I

  have hL : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (comul R I) (.id R (H ⧸ I)) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.map π π) π
          (Algebra.TensorProduct.map (comulAlgHom R H) (.id R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hR : ∀ z : H ⊗[R] H,
      Algebra.TensorProduct.map (.id R (H ⧸ I)) (comul R I) (Algebra.TensorProduct.map π π z) =
        Algebra.TensorProduct.map π (Algebra.TensorProduct.map π π)
          (Algebra.TensorProduct.map (.id R H) (comulAlgHom R H) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul a b => simp [π, Ideal.Quotient.mkₐ_eq_mk]
    | add z w hz hw => simp only [map_add, hz, hw]
  have hx : comul R I (π x) = Algebra.TensorProduct.map π π (comulAlgHom R H x) := by
    simp [π, Ideal.Quotient.mkₐ_eq_mk]
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, hx, hL, hR, assoc_map_map_apply]
  congr 1
  have hassoc : ∀ z : (H ⊗[R] H) ⊗[R] H,
      Algebra.TensorProduct.assoc R R R H H H z = TensorProduct.assoc R H H H z := by
    intro z
    induction z with
    | zero => simp
    | tmul xy c =>
      induction xy with
      | zero => simp
      | tmul a b => simp
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [map_apply_eq_linearMap, map_apply_eq_linearMap, hassoc]
  exact Coalgebra.coassoc_apply x

instance instBialgebra : Bialgebra R (H ⧸ I) :=
  Bialgebra.ofAlgHom (comul R I) (counit R I) (coassoc R I) (rTensor_counit_comul R I)
    (lTensor_counit_comul R I)

/--
@isnad1 id=eq.0h3v.s8.7f71d5ad0c3c from=translated src=- shape=568b0b9d vocab=b6f9e29b
-/
theorem comulAlgHom_eq : comulAlgHom R (H ⧸ I) = comul R I := rfl

/--
@isnad1 id=eq.0h3v.s7.4359d413db9a from=translated src=- shape=a28c52fd vocab=acb93d14
-/
theorem counitAlgHom_eq : counitAlgHom R (H ⧸ I) = counit R I := rfl

/--
@isnad1 id=eq.0h4v.s12.c77107b3b180 from=translated src=- shape=8952f89a vocab=21335bd7
-/
theorem coalgebra_comul_mk (x : H) :
    Coalgebra.comul (R := R) (Ideal.Quotient.mk I x) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
        (Coalgebra.comul (R := R) x) := rfl

/--
@isnad1 id=eq.0h4v.s10.6a14f70319b3 from=translated src=- shape=10e5f9e6 vocab=97b1577e
-/
theorem coalgebra_counit_mk (x : H) :
    Coalgebra.counit (R := R) (Ideal.Quotient.mk I x) = Coalgebra.counit (R := R) x := rfl

private theorem lift_antipode_id_comp_map :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_id_antipode_comp_map :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)) =
      (Ideal.Quotient.mkₐ R I).comp
        (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _) := by
  ext x
  · simp [Ideal.Quotient.mkₐ_eq_mk]
  · simp [Ideal.Quotient.mkₐ_eq_mk]

private theorem lift_antipodeAlgHom_id_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (antipodeAlgHom R H) (.id R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_antipodeAlgHom_comp_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_rTensor_comul_apply]
  simp [Algebra.ofId_apply]

private theorem lift_id_antipodeAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (.id R H) (antipodeAlgHom R H) fun _ _ => .all _ _).comp
        (comulAlgHom R H) = (Algebra.ofId R H).comp (counitAlgHom R H) := by
  refine AlgHom.ext fun x => ?_
  have h := lift_comp_antipodeAlgHom_apply (AlgHom.id R H) (Coalgebra.comul (R := R) x)
  simp only [AlgHom.id_comp] at h
  rw [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, h, mul_antipode_lTensor_comul_apply]
  simp [Algebra.ofId_apply]

/--
@isnad1 id=eq.0h3v.s10.4baa7b1537bf from=translated src=- shape=2a4409e7 vocab=cd8a296c
-/
theorem mul_antipode_rTensor_comul :
    (Algebra.TensorProduct.lift (antipode R I) (.id R (H ⧸ I)) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_antipode_id_comp_map, AlgHom.comp_assoc, lift_antipodeAlgHom_id_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

/--
@isnad1 id=eq.0h3v.s10.229393bb5b89 from=translated src=- shape=945a185d vocab=cd8a296c
-/
theorem mul_antipode_lTensor_comul :
    (Algebra.TensorProduct.lift (.id R (H ⧸ I)) (antipode R I) fun _ _ => .all _ _).comp
        (comulAlgHom R (H ⧸ I)) =
      (Algebra.ofId R (H ⧸ I)).comp (counitAlgHom R (H ⧸ I)) := by
  refine Ideal.Quotient.algHom_ext R ?_
  rw [comulAlgHom_eq, counitAlgHom_eq, AlgHom.comp_assoc, comul_comp_mkₐ, ← AlgHom.comp_assoc,
    lift_id_antipode_comp_map, AlgHom.comp_assoc, lift_id_antipodeAlgHom_comp_comulAlgHom,
    AlgHom.comp_assoc, counit_comp_mkₐ, ← AlgHom.comp_assoc]
  congr 1

instance instHopfAlgebra : HopfAlgebra R (H ⧸ I) :=
  HopfAlgebra.ofAlgHom (antipode R I) (mul_antipode_rTensor_comul R I)
    (mul_antipode_lTensor_comul R I)

/--
@isnad1 id=eq.0h4v.s10.2897749b0738 from=translated src=- shape=02798dfb vocab=4ad164a7
-/
theorem hopf_antipode_mk (x : H) :
    HopfAlgebra.antipode R (Ideal.Quotient.mk I x) =
      Ideal.Quotient.mk I (HopfAlgebra.antipode R x) := rfl

/--
@isnad1 id=iscocomm.0h3v.s8.ad554b86169f from=translated src=- shape=47ee5942 vocab=c3c40258
-/
instance instIsCocomm [Coalgebra.IsCocomm R H] : Coalgebra.IsCocomm R (H ⧸ I) where
  comm_comp_comul := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearMap.comp_apply, coalgebra_comul_mk]
    conv_rhs => rw [← Coalgebra.comm_comp_comul R H]
    rw [LinearMap.comp_apply]
    generalize Coalgebra.comul (R := R) x = z
    induction z with
    | zero => simp
    | tmul a b => simp
    | add z w hz hw => simp only [map_add, hz, hw]

end HopfIdealQuotient

section Maps

variable (R : Type*) [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

def quotientBialgHom (I : Ideal H) [I.IsHopfIdeal' R] : H →ₐc[R] H ⧸ I :=
  BialgHom.ofAlgHom (Ideal.Quotient.mkₐ R I) (HopfIdealQuotient.counit_comp_mkₐ R I)
    (HopfIdealQuotient.comul_comp_mkₐ R I).symm

/--
@isnad1 id=eq.0h4v.s9.e42cbd23e7d5 from=translated src=- shape=fe65ff01 vocab=89100dea
-/
@[simp] theorem quotientBialgHom_apply (I : Ideal H) [I.IsHopfIdeal' R] (x : H) :
    quotientBialgHom R I x = Ideal.Quotient.mk I x := rfl

/--
@isnad1 id=eq.0h3v.s9.a7c04588e02a from=translated src=- shape=bcc347a0 vocab=568b910d
-/
theorem quotientBialgHom_toAlgHom (I : Ideal H) [I.IsHopfIdeal' R] :
    (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = Ideal.Quotient.mkₐ R I := rfl

/--
@isnad1 id=surjecti.0h3v.s9.6d510f5a5703 from=translated src=- shape=8550a48a vocab=d4aea755
-/
theorem quotientBialgHom_surjective (I : Ideal H) [I.IsHopfIdeal' R] :
    Function.Surjective (quotientBialgHom R I) :=
  Ideal.Quotient.mk_surjective

def quotientFactorBialgHom {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R] (hIJ : I ≤ J) :
    H ⧸ I →ₐc[R] H ⧸ J :=
  BialgHom.ofAlgHom (Ideal.Quotient.factorₐ R hIJ)
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk,
        HopfIdealQuotient.counitAlgHom_eq, HopfIdealQuotient.counitAlgHom_eq,
        HopfIdealQuotient.counit_comp_mkₐ, HopfIdealQuotient.counit_comp_mkₐ])
    (by
      refine Ideal.Quotient.algHom_ext R ?_
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk,
        HopfIdealQuotient.comulAlgHom_eq, HopfIdealQuotient.comulAlgHom_eq,
        HopfIdealQuotient.comul_comp_mkₐ, HopfIdealQuotient.comul_comp_mkₐ,
        ← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, Ideal.Quotient.factorₐ_comp_mk])

/--
@isnad1 id=eq.1h5v.s10.f5342243e283 from=translated src=- shape=37edec36 vocab=6b2e35dc
-/
@[simp] theorem quotientFactorBialgHom_apply_mk {I J : Ideal H} [I.IsHopfIdeal' R]
    [J.IsHopfIdeal' R] (hIJ : I ≤ J) (x : H) :
    quotientFactorBialgHom R hIJ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x := rfl

/--
@isnad1 id=eq.1h4v.s9.faea268c941a from=translated src=- shape=6e6152fd vocab=25b7a02d
-/
theorem quotientFactorBialgHom_toAlgHom {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ : H ⧸ I →ₐ[R] H ⧸ J) = Ideal.Quotient.factorₐ R hIJ := rfl

/--
@isnad1 id=eq.1h4v.s9.3e8051a2455c from=translated src=- shape=273ce2f5 vocab=3a226933
-/
theorem quotientFactorBialgHom_comp {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ).comp (quotientBialgHom R I) = quotientBialgHom R J := by
  ext x; rfl

/--
@isnad1 id=eq.1h4v.s10.fd10ee79311c from=translated src=- shape=92a98511 vocab=fb4de7b8
-/
theorem quotientFactorBialgHom_comp_toAlgHom {I J : Ideal H} [I.IsHopfIdeal' R]
    [J.IsHopfIdeal' R] (hIJ : I ≤ J) :
    (quotientFactorBialgHom R hIJ : H ⧸ I →ₐ[R] H ⧸ J).comp
        (quotientBialgHom R I : H →ₐ[R] H ⧸ I) = (quotientBialgHom R J : H →ₐ[R] H ⧸ J) := by
  ext x; rfl

/--
@isnad1 id=surjecti.1h4v.s9.826603216ea4 from=translated src=- shape=3532e1a9 vocab=c477746d
-/
theorem quotientFactorBialgHom_surjective {I J : Ideal H} [I.IsHopfIdeal' R] [J.IsHopfIdeal' R]
    (hIJ : I ≤ J) : Function.Surjective (quotientFactorBialgHom R hIJ) :=
  Ideal.Quotient.factor_surjective hIJ

variable {A : Type*} [CommRing A] [Algebra R A]

def quotientLiftPoint (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0) : H ⧸ I →ₐ[R] A :=
  Ideal.Quotient.liftₐ I f hf

/--
@isnad1 id=eq.1h6v.s9.250786f661fe from=translated src=- shape=28d2bfe8 vocab=183b6fc8
-/
@[simp] theorem quotientLiftPoint_mk (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0)
    (x : H) : quotientLiftPoint R I f hf (Ideal.Quotient.mk I x) = f x := rfl

/--
@isnad1 id=eq.1h5v.s8.4127ca115ac1 from=translated src=- shape=0d322c64 vocab=98aa97d5
-/
theorem quotientLiftPoint_comp_mkₐ (I : Ideal H) (f : H →ₐ[R] A) (hf : ∀ x ∈ I, f x = 0) :
    (quotientLiftPoint R I f hf).comp (Ideal.Quotient.mkₐ R I) = f :=
  Ideal.Quotient.liftₐ_comp _ _ _

/--
@isnad1 id=eq.1h6v.s8.642c7320a5c7 from=translated src=- shape=c07638e0 vocab=64b96903
-/
theorem comp_mkₐ_apply_eq_zero (I : Ideal H) (g : H ⧸ I →ₐ[R] A) (x : H) (hx : x ∈ I) :
    g.comp (Ideal.Quotient.mkₐ R I) x = 0 := by
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

/--
@isnad1 id=injectiv.0h4v.s8.54da747d2944 from=translated src=- shape=d6727e3e vocab=24b9b20b
-/
theorem comp_mkₐ_injective (I : Ideal H) :
    Function.Injective fun g : H ⧸ I →ₐ[R] A => g.comp (Ideal.Quotient.mkₐ R I) :=
  fun _ _ h => Ideal.Quotient.algHom_ext R h

/--
@isnad1 id=eq.0h5v.s8.a31ebcd50ab3 from=translated src=- shape=0ad76132 vocab=86de2427
-/
theorem quotientLiftPoint_comp (I : Ideal H) (g : H ⧸ I →ₐ[R] A) :
    quotientLiftPoint R I (g.comp (Ideal.Quotient.mkₐ R I))
      (fun x hx => comp_mkₐ_apply_eq_zero R I g x hx) = g :=
  comp_mkₐ_injective R I (quotientLiftPoint_comp_mkₐ R I _ _)

def quotientPointsEquiv (I : Ideal H) :
    (H ⧸ I →ₐ[R] A) ≃ {f : H →ₐ[R] A // ∀ x ∈ I, f x = 0} where
  toFun g := ⟨g.comp (Ideal.Quotient.mkₐ R I), fun x hx => comp_mkₐ_apply_eq_zero R I g x hx⟩
  invFun f := quotientLiftPoint R I f.1 f.2
  left_inv g := quotientLiftPoint_comp R I g
  right_inv f := Subtype.ext (quotientLiftPoint_comp_mkₐ R I f.1 f.2)

/--
@isnad1 id=finitety.0h3v.s7.a11809ce5c68 from=translated src=- shape=1919a84e vocab=27b75cc9
-/
instance finiteType_quotient (I : Ideal H) [Algebra.FiniteType R H] :
    Algebra.FiniteType R (H ⧸ I) :=
  Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ_surjective R I)

def quotientBotAlgEquiv : (H ⧸ (⊥ : Ideal H)) ≃ₐ[R] H :=
  (AlgEquiv.ofBijective (Ideal.Quotient.mkₐ R (⊥ : Ideal H))
    ⟨fun x y h => by
      simpa [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] using h,
      Ideal.Quotient.mkₐ_surjective R _⟩).symm

/--
@isnad1 id=flat.0h2v.s8.6c8c5315dd68 from=translated src=- shape=5dde880b vocab=69e15092
-/
instance flat_quotient_bot [Module.Flat R H] : Module.Flat R (H ⧸ (⊥ : Ideal H)) :=
  Module.Flat.of_linearEquiv (quotientBotAlgEquiv R (H := H)).toLinearEquiv

end Maps

end HopfAlgebra

end
