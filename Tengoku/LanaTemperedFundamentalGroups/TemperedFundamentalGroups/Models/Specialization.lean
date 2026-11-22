/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Tengoku.Seed.AlgebraicGeometry.ValuativeCriterion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Special fibre and specialization of geometric points

Let `O` be a local ring and `f : X ⟶ Spec O`. The *special fibre* of `f` is the preimage of the
closed point of `Spec O` (as a subspace of the underlying space of `X`).

Now let `O ⊆ K` be a valuation subring, `K → Ω` a field extension and `V ⊆ Ω` a valuation
subring with `V ∩ K = O`. For `f` universally closed and separated, every `Ω`-point
`x : Spec Ω ⟶ X` over `Spec K → Spec O` extends uniquely to `Spec V ⟶ X` (valuative criterion);
its value at the closed point of `Spec V` is the *specialization* `sp f V hV x hx` of `x`, a point
of the special fibre. Specialization is natural in morphisms over `Spec O`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups

section SpecialFibre

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The special fibre of `f : X ⟶ Spec R` for a local ring `R`: the preimage of the closed point,
as a set of points of `X`. -/
def specialFibre {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Set X :=
  f ⁻¹' {(closedPoint R : PrimeSpectrum R)}

/--
@isnad1 id=iff.0h4v.s8.9b62d09d48a6 from=translated src=- shape=4c6fd4fa vocab=f14d4be4
-/
lemma mem_specialFibre {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    x ∈ specialFibre f ↔ f x = (closedPoint R : PrimeSpectrum R) :=
  Iff.rfl

variable {X X' X'' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {f' : X' ⟶ Spec (CommRingCat.of R)} {f'' : X'' ⟶ Spec (CommRingCat.of R)}

/--
@isnad1 id=mem.2h7v.s8.03a51bd112b3 from=translated src=- shape=776df91e vocab=0c86ead0
-/
lemma mem_specialFibre_of_comp (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) {x : X}
    (hx : x ∈ specialFibre f) : ψ x ∈ specialFibre f' := by
  rw [mem_specialFibre, ← Scheme.Hom.comp_apply, hψ]
  exact hx

/-- A morphism `ψ : X ⟶ X'` over `Spec R` maps the special fibre of `X` into that of `X'`. -/
def specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) : specialFibre f → specialFibre f' :=
  fun x ↦ ⟨ψ x.1, mem_specialFibre_of_comp ψ hψ x.2⟩

/--
@isnad1 id=eq.1h7v.s8.541c6499924a from=translated src=- shape=d09790d7 vocab=8aae8b5d
-/
@[simp]
lemma coe_specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (x : specialFibre f) :
    (specialFibreMap ψ hψ x : X') = ψ x :=
  rfl

/--
@isnad1 id=continuo.1h6v.s8.381044c9e46c from=translated src=- shape=297700bd vocab=fc859bfb
-/
@[fun_prop]
lemma continuous_specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) :
    Continuous (specialFibreMap ψ hψ) :=
  (ψ.continuous.comp continuous_subtype_val).subtype_mk _

/--
@isnad1 id=eq.0h4v.s6.7b7f18855dc6 from=translated src=- shape=3a4ecf54 vocab=4247eed7
-/
@[simp]
lemma specialFibreMap_id (x : specialFibre f) :
    specialFibreMap (𝟙 X) (Category.id_comp f) x = x :=
  rfl

/--
@isnad1 id=eq.2h10v.s7.1336f71ae2c0 from=translated src=- shape=17368b08 vocab=58741269
-/
lemma specialFibreMap_comp (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (φ : X' ⟶ X'') (hφ : φ ≫ f'' = f')
    (x : specialFibre f) :
    specialFibreMap (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ]) x =
      specialFibreMap φ hφ (specialFibreMap ψ hψ x) :=
  rfl

/-- The map of special fibres induced by a morphism over `Spec R`, as a continuous map. -/
def specialFibreContinuousMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) :
    C(specialFibre f, specialFibre f') :=
  ⟨specialFibreMap ψ hψ, continuous_specialFibreMap ψ hψ⟩

/-- An isomorphism over `Spec R` induces a homeomorphism of special fibres. In particular an
automorphism `e : X ≅ X` with `e.hom ≫ f = f` acts on the special fibre of `f`. -/
def specialFibreHomeomorph (e : X ≅ X') (he : e.hom ≫ f' = f) :
    specialFibre f ≃ₜ specialFibre f' where
  toFun := specialFibreMap e.hom he
  invFun := specialFibreMap e.inv (by rw [← he, e.inv_hom_id_assoc])
  left_inv x := by
    ext
    simp [← Scheme.Hom.comp_apply]
  right_inv x := by
    ext
    simp [← Scheme.Hom.comp_apply]
  continuous_toFun := continuous_specialFibreMap _ _
  continuous_invFun := continuous_specialFibreMap _ _

/--
@isnad1 id=eq.1h7v.s9.150c496e5aef from=translated src=- shape=975b8b25 vocab=0e2586e9
-/
@[simp]
lemma coe_specialFibreHomeomorph (e : X ≅ X') (he : e.hom ≫ f' = f) (x : specialFibre f) :
    (specialFibreHomeomorph e he x : X') = e.hom x :=
  rfl

end SpecialFibre

section Specialization

variable {K : Type u} [Field K] (O : ValuationSubring K)
variable {Ω : Type u} [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
  (hV : V.comap (algebraMap K Ω) = O)

/-- The inclusion `O → Ω` (restriction of `K → Ω`). -/
def valToField : O →+* Ω :=
  (algebraMap K Ω).comp O.subtype

variable {O V} in
/--
@isnad1 id=iff.0h5v.s8.fe11f7a849a3 from=translated src=- shape=eef77a54 vocab=9f4c492b
-/
lemma valToField_mem (a : O) : valToField O a ∈ V ↔ (a : K) ∈ V.comap (algebraMap K Ω) :=
  (ValuationSubring.mem_comap).symm

include hV in
/-- The local homomorphism `O → V` induced by `K → Ω`, when `V ∩ K = O`. -/
def valToVal : O →+* V :=
  (valToField O).codRestrict V.toSubring fun a ↦ by
    change _ ∈ V
    rw [valToField_mem, hV]
    exact a.2

/--
@isnad1 id=eq.1h5v.s9.9cd9b5d615a0 from=translated src=- shape=48291d27 vocab=038ec959
-/
@[simp]
lemma coe_valToVal (a : O) : (valToVal O V hV a : Ω) = valToField O a :=
  rfl

/--
@isnad1 id=eq.1h4v.s8.744ab575d63c from=translated src=- shape=fcb38e81 vocab=f9baa20b
-/
lemma valToVal_comp_algebraMap :
    (algebraMap V Ω).comp (valToVal O V hV) = valToField O :=
  rfl

/--
@isnad1 id=islocalh.1h4v.s9.0e6a5065d95f from=translated src=- shape=f85b33e9 vocab=5ce40174
-/
instance isLocalHom_valToVal : IsLocalHom (valToVal O V hV) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨u, hu⟩ := ha.exists_left_inv
  have hu' : (u : Ω) * algebraMap K Ω a = 1 := congrArg Subtype.val hu
  have ha0 : (a : K) ≠ 0 := by
    rintro h
    simp [h] at hu'
  have hinv : (u : Ω) = algebraMap K Ω (a : K)⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hu'
  have hmem : (a : K)⁻¹ ∈ V.comap (algebraMap K Ω) := by
    rw [ValuationSubring.mem_comap, ← hinv]
    exact u.2
  rw [hV] at hmem
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/--
@isnad1 id=eq.1h4v.s7.4eef19288c42 from=translated src=- shape=618ad294 vocab=be5a40b3
-/
lemma valToVal_closedPoint :
    PrimeSpectrum.comap (valToVal O V hV) (closedPoint V) = closedPoint O :=
  comap_closedPoint _

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O))

/-- The valuative square attached to an `Ω`-point `x` of `X` over `Spec K → Spec O`. -/
noncomputable def spSquare (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) : ValuativeCommSq f where
  R := V
  K := Ω
  i₁ := x
  i₂ := Spec.map (CommRingCat.ofHom (valToVal O V hV))
  commSq := ⟨by
    rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, valToVal_comp_algebraMap]⟩

variable {O V hV f}

/-- The lift `Spec V ⟶ X` of an `Ω`-point given by the valuative criterion. -/
noncomputable def spLift [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (spSquare O V hV f x hx).commSq.LiftStruct :=
  have hf : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  (hf (spSquare O V hV f x hx)).exists_lift.some

/--
@isnad1 id=eq.2h7v.s10.721835daaea4 from=translated src=- shape=3357eaa7 vocab=b8e2a7cf
-/
lemma spLift_fac_left [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ (spLift (hV := hV) x hx).l = x :=
  (spLift x hx).fac_left

/--
@isnad1 id=eq.2h7v.s10.1cb0d287d96a from=translated src=- shape=3f7d0e71 vocab=a5367b60
-/
lemma spLift_fac_right [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (spLift (hV := hV) x hx).l ≫ f = Spec.map (CommRingCat.ofHom (valToVal O V hV)) :=
  (spLift x hx).fac_right

/--
@isnad1 id=eq.4h8v.s10.3fed7fd5db84 from=translated src=- shape=1f86870a vocab=48fa4356
-/
lemma spLift_unique [UniversallyClosed f] [IsSeparated f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O)))
    (ℓ : Spec (CommRingCat.of V) ⟶ X)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ ℓ = x)
    (h₂ : ℓ ≫ f = Spec.map (CommRingCat.ofHom (valToVal O V hV))) :
    ℓ = (spLift (hV := hV) x hx).l := by
  have := IsSeparated.valuativeCriterion f (spSquare O V hV f x hx)
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim (⟨ℓ, h₁, h₂⟩ :
    (spSquare O V hV f x hx).commSq.LiftStruct) _)

end Specialization

section Specialization

variable {K : Type u} [Field K] {O : ValuationSubring K}
variable {Ω : Type u} [Field Ω] [Algebra K Ω] {V : ValuationSubring Ω}
  {hV : V.comap (algebraMap K Ω) = O} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)}

/-- The restriction to `V` of an automorphism of `Ω` preserving `V`. -/
def restrictVal (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ x, σ x ∈ V ↔ x ∈ V) : V →+* V :=
  ((σ : Ω →+* Ω).comp V.subtype).codRestrict V.toSubring fun x ↦ (hσ x).2 x.2

end Specialization

end TemperedFundamentalGroups
