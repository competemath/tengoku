import Tengoku.StringDiagramsLean.StringDiagrams.Super.OrbitFunctorial
import Tengoku.StringDiagramsLean.StringDiagrams.Super.GradedTwo
import Tengoku.Seed.Tactic.CategoryTheory.Bicategory.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The 2-categorical orbit construction

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6, the
construction of the associated graded `(Q, Π)`-2-supercategory of a `(Q, Π)`-2-category
(after Definition 6.14, "which we leave to the reader"), in the generality of an arbitrary
2-supercategory with a central invertible family of 1-morphisms.

Let `𝔅` be a 2-supercategory with 1-morphisms `q_λ, q_λ⁻¹ : λ → λ`, even 2-isomorphisms
`ii_λ : q_λ q_λ⁻¹ ≅ 1`, `jj_λ : q_λ⁻¹ q_λ ≅ 1` satisfying a triangle identity, and even
2-isomorphisms `γ_F : F q_μ ≅ q_λ F` making `(q, γ)` an object of the Drinfeld center of `𝔅`
(natural with respect to all 2-morphisms), with `γ_{q_λ} = 1` (`StringDiagrams.CentralShift`).
Then each morphism supercategory `ℋom_𝔅(λ, μ)` carries the shift datum
`(- q_μ, - q_μ⁻¹)` (`CentralShift.homShift`), horizontal composition with a 1-morphism is a
morphism of shift data (`CentralShift.preShift`, `CentralShift.postShift`, with `γ` given by
the associator, resp. by `γ_F`), and the *orbit 2-supercategory* `Orbit2 R 𝔅` has

* the objects and 1-morphisms of `𝔅`, and the orbit supercategories
  `Orbit (homShift λ μ)` (`StringDiagrams.Super.Orbit`) as morphism supercategories: a
  2-morphism of degree `m` is a family `(x_{i,j} : F q_μ^i ⇒ G q_μ^j)_{i-j=m}` compatible with
  `- q_μ`, determined by `x_{0,-m} : F ⇒ G q_μ^{-m}`;
* horizontal composition with a 1-morphism induced by the morphisms of shift data
  (`Orbit.map`), and the coherence maps of `𝔅` in degree zero (`Orbit.ι`).

It is a graded 2-supercategory (`Orbit2.instTwoSupercategory`,
`Orbit2.instGradedTwoSupercategory`), a Π-2-supercategory when `𝔅` is one, with the same
`π` and `ζ` (`Orbit2.instPiTwoSupercategory`), and then a graded `(Q, Π)`-2-supercategory with
`q_λ`, `q_λ⁻¹` and `σ_λ : q_λ ⇒ 1_λ` of degree `-1` given by the identity of `q_λ` in degree `-1`
(`Orbit2.instQPiTwoSupercategory`).

The super interchange law of `Orbit2 R 𝔅` is reduced to that of `𝔅`: it holds for 2-morphisms
of degree zero by the supernaturality of orbit functors (`Orbit.map_map_comp_ι`), for the
2-isomorphisms `σ` by the naturality of `σ` (`Orbit.map_self_comp_σIso_hom`), and every
homogeneous 2-morphism is a composite of these.

The associated graded `(Q, Π)`-2-supercategory of a `(Q, Π)`-2-category `𝔄` is
`Orbit2 R (Associated2 R 𝔄)` (`StringDiagrams.Super.QAssociatedTwo`).
-/

noncomputable section

namespace StringDiagrams

open CategoryTheory Supercategory BicategoryStruct TwoSupercategory GradedSupercategory

universe w v u w₁

section Defs

variable (R : Type w₁) [CommRing R] (B : Type u) [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

/-- A central invertible family of 1-morphisms in a 2-supercategory: 1-morphisms
`q_λ, q_λ⁻¹`, even 2-isomorphisms `ii_λ : q_λ q_λ⁻¹ ≅ 1_λ`, `jj_λ : q_λ⁻¹ q_λ ≅ 1_λ` with
`q_λ ii_λ = jj_λ q_λ` (so that `(q_λ, q_λ⁻¹)` is an adjoint equivalence), and even
2-isomorphisms `γ_F : F q_μ ≅ q_λ F` natural in `F` with respect to all 2-morphisms, with
`γ_{GF} = G γ_F ∘ γ_G F`, `γ_{1} = 1` and `γ_{q_λ} = 1` (Brundan–Ellis, Definition 6.14(i),
(ii) and (iv), for the pair `(q, γ)`). Compositions of 1-morphisms are in diagrammatic
order.-/
class CentralShift where
  /-- The 1-morphisms `q_λ`.-/
  q : ∀ a : B, a ⟶ a
  /-- The 1-morphisms `q_λ⁻¹`.-/
  qinv : ∀ a : B, a ⟶ a
  /-- `ii_λ : q_λ q_λ⁻¹ ≅ 1_λ`.-/
  ii : ∀ a : B, q a ≫ qinv a ≅ 𝟙 a
  /-- `jj_λ : q_λ⁻¹ q_λ ≅ 1_λ`.-/
  jj : ∀ a : B, qinv a ≫ q a ≅ 𝟙 a
  ii_hom_mem : ∀ a : B, (ii a).hom ∈ parity (R := R) (q a ≫ qinv a) (𝟙 a) 0
  jj_hom_mem : ∀ a : B, (jj a).hom ∈ parity (R := R) (qinv a ≫ q a) (𝟙 a) 0
  /-- `q_λ ii_λ = jj_λ q_λ`.-/
  q_ii : ∀ a : B, (ii a).hom ▷ q a ≫ (leftUnitor (q a)).hom =
    (associator (q a) (qinv a) (q a)).hom ≫ q a ◁ (jj a).hom ≫ (rightUnitor (q a)).hom
  /-- The 2-isomorphisms `γ_F : F q_μ ≅ q_λ F`.-/
  γ : ∀ {a b : B} (f : a ⟶ b), f ≫ q b ≅ q a ≫ f
  γ_hom_mem : ∀ {a b : B} (f : a ⟶ b), (γ f).hom ∈ parity (R := R) (f ≫ q b) (q a ≫ f) 0
  /-- `γ` is natural with respect to all 2-morphisms.-/
  γ_naturality : ∀ {a b : B} {f g : a ⟶ b} (η : f ⟶ g),
    (γ f).hom ≫ q a ◁ η = η ▷ q b ≫ (γ g).hom
  /-- `γ_{GF} = G γ_F ∘ γ_G F`.-/
  γ_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c),
    (γ (f ≫ g)).hom = (associator f g (q c)).hom ≫ f ◁ (γ g).hom ≫
      (associator f (q b) g).inv ≫ (γ f).hom ▷ g ≫ (associator (q a) f g).hom
  /-- `γ_{1_λ} = 1_{q_λ}`.-/
  γ_id : ∀ a : B, (γ (𝟙 a)).hom = (leftUnitor (q a)).hom ≫ (rightUnitor (q a)).inv
  /-- `γ_{q_λ} = 1_{q_λ²}`.-/
  γ_q : ∀ a : B, (γ (q a)).hom = 𝟙 _

end Defs

namespace CentralShift

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] [CentralShift R B]

local notation "𝐪" => CentralShift.q (R := R)
local notation "𝐪⁻" => CentralShift.qinv (R := R)
local notation "𝛄" => CentralShift.γ (R := R)

variable {a b c d : B}

omit [TwoSupercategory R B] in
/--
@isnad1 id=mem.0h5v.s10.59cb94eed3bf from=translated src=- shape=613f2d4a vocab=85eb7169
-/
theorem γ_inv_mem (f : a ⟶ b) : (𝛄 f).inv ∈ parity (R := R) (𝐪 a ≫ f) (f ≫ 𝐪 b) 0 :=
  inv_mem _ (γ_hom_mem f)

omit [TwoSupercategory R B] in
/--
@isnad1 id=mem.0h3v.s10.2fa9ba660877 from=translated src=- shape=d46bab49 vocab=d8426d03
-/
theorem ii_inv_mem (a : B) : (ii (R := R) a).inv ∈ parity (R := R) (𝟙 a) (𝐪 a ≫ 𝐪⁻ a) 0 :=
  inv_mem _ (ii_hom_mem a)

omit [TwoSupercategory R B] in
/--
@isnad1 id=eq.0h7v.s9.112a0eb1a248 from=translated src=- shape=c88515a6 vocab=f945b024
-/
@[reassoc]
theorem γ_inv_naturality {f g : a ⟶ b} (η : f ⟶ g) :
    𝐪 a ◁ η ≫ (𝛄 g).inv = (𝛄 f).inv ≫ η ▷ 𝐪 b := by
  rw [Iso.eq_inv_comp, ← Category.assoc, γ_naturality, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-! ## Transfer to the underlying bicategory -/

section Underlying

open Bicategory

/-- `ii` as an isomorphism of the underlying bicategory.-/
def iiU (a : B) : (Underlying2.hom1 (R := R) (𝐪 a) ≫ Underlying2.hom1 (𝐪⁻ a)) ≅ 𝟙 _ :=
  Underlying.isoMk (ii (R := R) a) (ii_hom_mem a)

/-- `jj` as an isomorphism of the underlying bicategory.-/
def jjU (a : B) : (Underlying2.hom1 (R := R) (𝐪⁻ a) ≫ Underlying2.hom1 (𝐪 a)) ≅ 𝟙 _ :=
  Underlying.isoMk (jj (R := R) a) (jj_hom_mem a)

/-- `γ` as an isomorphism of the underlying bicategory.-/
def γU {a b : Underlying2 R B} (f : a ⟶ b) :
    (f ≫ Underlying2.hom1 (R := R) (𝐪 b.obj)) ≅ Underlying2.hom1 (𝐪 a.obj) ≫ f :=
  Underlying.isoMk (𝛄 f.obj) (γ_hom_mem f.obj)

/--
@isnad1 id=eq.0h3v.s11.13202d7c6cad from=translated src=- shape=a1f26d7a vocab=799b8a67
-/
theorem q_iiU (a : B) :
    Bicategory.whiskerRight (iiU (R := R) a).hom (Underlying2.hom1 (𝐪 a)) ≫ (λ_ _).hom =
      (α_ _ _ _).hom ≫ Bicategory.whiskerLeft (Underlying2.hom1 (𝐪 a)) (jjU a).hom ≫ (ρ_ _).hom :=
  Subtype.ext (q_ii a)

/--
@isnad1 id=eq.0h7v.s11.ddc6c700b1d4 from=translated src=- shape=3d11914b vocab=5592cec1
-/
theorem γU_comp {a b c : Underlying2 R B} (f : a ⟶ b) (g : b ⟶ c) :
    (γU (R := R) (f ≫ g)).hom = (α_ f g _).hom ≫ Bicategory.whiskerLeft f (γU g).hom ≫
      (α_ _ _ _).inv ≫ Bicategory.whiskerRight (γU f).hom g ≫ (α_ _ _ _).hom :=
  Subtype.ext (γ_comp f.obj g.obj)

/--
@isnad1 id=eq.0h3v.s10.df61125be67d from=translated src=- shape=3ed5d4cb vocab=4e32db17
-/
theorem γU_id (a : Underlying2 R B) : (γU (R := R) (𝟙 a)).hom =
    (λ_ (Underlying2.hom1 (𝐪 a.obj))).hom ≫ (ρ_ (Underlying2.hom1 (𝐪 a.obj))).inv :=
  Subtype.ext (γ_id a.obj)

/-- The triangle identity, in the underlying bicategory.
@isnad1 id=eq.0h5v.s12.520bfbf8d991 from=translated src=- shape=861b434b vocab=e96e04a0
-/
theorem unit_counit_triangleU {a b : B} (f' : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩) :
    Bicategory.whiskerRight ((ρ_ f').inv ≫ Bicategory.whiskerLeft f' (iiU (R := R) b).inv ≫
        (α_ f' _ _).inv) (Underlying2.hom1 (𝐪 b)) ≫
      (α_ (f' ≫ Underlying2.hom1 (𝐪 b)) _ _).hom ≫
        Bicategory.whiskerLeft (f' ≫ Underlying2.hom1 (𝐪 b)) (jjU (R := R) b).hom ≫
          (ρ_ _).hom = 𝟙 _ := by
  have c1 : Bicategory.whiskerRight ((ρ_ f').inv ≫ Bicategory.whiskerLeft f' (iiU (R := R) b).inv ≫
        (α_ f' _ _).inv) (Underlying2.hom1 (𝐪 b)) ≫
      (α_ (f' ≫ Underlying2.hom1 (𝐪 b)) _ _).hom ≫
        Bicategory.whiskerLeft (f' ≫ Underlying2.hom1 (𝐪 b)) (jjU (R := R) b).hom ≫
          (ρ_ _).hom =
      Bicategory.whiskerRight (ρ_ f').inv _ ≫ (α_ f' _ _).hom ≫
        Bicategory.whiskerLeft f' (Bicategory.whiskerRight (iiU (R := R) b).inv (Underlying2.hom1 (𝐪 b)) ≫
          (α_ _ _ _).hom ≫ Bicategory.whiskerLeft (Underlying2.hom1 (𝐪 b)) (jjU (R := R) b).hom) ≫
            (α_ f' _ _).inv ≫ (ρ_ _).hom := by
    bicategory
  have c2 : Bicategory.whiskerRight (iiU (R := R) b).inv (Underlying2.hom1 (𝐪 b)) ≫
      (α_ _ _ _).hom ≫ Bicategory.whiskerLeft (Underlying2.hom1 (𝐪 b)) (jjU (R := R) b).hom =
        (λ_ _).hom ≫ (ρ_ _).inv := by
    rw [← cancel_mono (ρ_ _).hom, Category.assoc, Category.assoc, ← q_iiU,
      Bicategory.inv_hom_whiskerRight_assoc]
    simp
  rw [c1, c2]
  bicategory

end Underlying

/-! ## The shift data on the morphism supercategories -/

set_option backward.isDefEq.respectTransparency false in
/-- The unit `F ≅ (F q_μ) q_μ⁻¹` of the adjoint equivalence `(- q_μ, - q_μ⁻¹)`.-/
def unitIso (a b : B) : 𝟭 (a ⟶ b) ≅ postcomp R (𝐪 b) ⋙ postcomp R (𝐪⁻ b) :=
  NatIso.ofComponents
    (fun f => (rightUnitor f).symm ≪≫ whiskerLeftIso (R := R) f (ii (R := R) b).symm ≪≫
      (associator f (𝐪 b) (𝐪⁻ b)).symm)
    (fun η => by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map,
        Functor.comp_map, postcomp_map, Iso.trans_hom, Iso.symm_hom, whiskerLeftIso_hom,
        Category.assoc]
      rw [rightUnitor_inv_naturality_assoc R, whisker_exchange_of_even_right_assoc _ (ii_inv_mem b),
        associator_inv_naturality_left R])

set_option backward.isDefEq.respectTransparency false in
/-- The counit `(F q_μ⁻¹) q_μ ≅ F` of the adjoint equivalence `(- q_μ, - q_μ⁻¹)`.-/
def counitIso (a b : B) : postcomp R (𝐪⁻ b) ⋙ postcomp R (𝐪 b) ≅ 𝟭 (a ⟶ b) :=
  NatIso.ofComponents
    (fun f => associator f (𝐪⁻ b) (𝐪 b) ≪≫ whiskerLeftIso (R := R) f (jj (R := R) b) ≪≫
      rightUnitor f)
    (fun η => by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map,
        Functor.comp_map, postcomp_map, Iso.trans_hom, whiskerLeftIso_hom, Category.assoc]
      rw [associator_naturality_left_assoc R, whisker_exchange_of_even_right_assoc _ (jj_hom_mem b),
        rightUnitor_naturality R])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s10.4611414f557a from=translated src=- shape=7f3d8e19 vocab=be8debe4
-/
theorem unitIso_hom_app (a b : B) (f : a ⟶ b) :
    (unitIso (R := R) a b).hom.app f = (rightUnitor f).inv ≫ f ◁ (ii (R := R) b).inv ≫
      (associator f (𝐪 b) (𝐪⁻ b)).inv := by
  simp [unitIso]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s10.0a66771ebb79 from=translated src=- shape=e0a50fbc vocab=ad07141c
-/
theorem counitIso_hom_app (a b : B) (f : a ⟶ b) :
    (counitIso (R := R) a b).hom.app f = (associator f (𝐪⁻ b) (𝐪 b)).hom ≫
      f ◁ (jj (R := R) b).hom ≫ (rightUnitor f).hom := by
  simp [counitIso]

/-- The triangle identity of the adjoint equivalence `(- q_μ, - q_μ⁻¹)`, from
`q_λ ii_λ = jj_λ q_λ`.
@isnad1 id=eq.0h5v.s10.e9636d36406e from=translated src=- shape=dd9e21d0 vocab=b15d3f63
-/
theorem unit_counit_triangle (a b : B) (f : a ⟶ b) :
    (unitIso (R := R) a b).hom.app f ▷ 𝐪 b ≫ (counitIso (R := R) a b).hom.app (f ≫ 𝐪 b) =
      𝟙 (f ≫ 𝐪 b) := by
  rw [unitIso_hom_app, counitIso_hom_app]
  exact congrArg Subtype.val (unit_counit_triangleU (R := R) (Underlying2.hom1 f))

variable (R) in
/-- The shift datum `(- q_μ, - q_μ⁻¹)` on the morphism supercategory `ℋom(λ, μ)`.-/
def homShift (a b : B) : ShiftData R (a ⟶ b) where
  e :=
    { functor := postcomp R (𝐪 b)
      inverse := postcomp R (𝐪⁻ b)
      unitIso := unitIso a b
      counitIso := counitIso a b
      functor_unitIso_comp := unit_counit_triangle a b }
  unit_mem f := by
    rw [unitIso_hom_app]
    have := comp_mem (comp_mem (inv_mem _ (rightUnitor_hom_mem (R := R) f))
      (whiskerLeft_mem f (ii_inv_mem (R := R) b))) (inv_mem _ (associator_hom_mem (R := R) f _ _))
    simpa using! this
  counit_mem f := by
    rw [counitIso_hom_app]
    have := comp_mem (comp_mem (associator_hom_mem (R := R) f _ _)
      (whiskerLeft_mem f (jj_hom_mem (R := R) b))) (rightUnitor_hom_mem (R := R) f)
    simpa using! this

/--
@isnad1 id=eq.0h4v.s7.f5e184770425 from=translated src=- shape=226239e0 vocab=bedd2ac4
-/
@[simp] theorem homShift_Q (a b : B) : (homShift R a b).Q = postcomp R (𝐪 b) := rfl

/--
@isnad1 id=eq.0h4v.s7.aba47b3500f2 from=translated src=- shape=226239e0 vocab=052b79f0
-/
@[simp] theorem homShift_Qi (a b : B) : (homShift R a b).Qi = postcomp R (𝐪⁻ b) := rfl

/-! ## Horizontal composition with a 1-morphism as morphisms of shift data -/

variable (R) in
/-- `- F : ℋom(μ, ν) → ℋom(λ, ν)` (i.e. `G ↦ F ≫ G`) as a morphism of shift data, with `γ`
the associator `(F G) q_ν ≅ F (G q_ν)`.-/
def preShift (c : B) (f : a ⟶ b) : ShiftFunctor R (homShift R b c) (homShift R a c) where
  F := precomp R f
  γ := NatIso.ofComponents (fun g => associator f g (𝐪 c)) (fun η => by
    simp only [Functor.comp_obj, Functor.comp_map, precomp_map]
    exact associator_naturality_middle R f η (𝐪 c))
  γ_mem g := associator_hom_mem (R := R) f g (𝐪 c)

/--
@isnad1 id=eq.0h6v.s8.e8e1e5df5955 from=translated src=- shape=3a9a644b vocab=9a20d7bf
-/
@[simp] theorem preShift_F (c : B) (f : a ⟶ b) : (preShift R c f).F = precomp R f := rfl

/--
@isnad1 id=eq.0h7v.s10.0c8a171ff708 from=translated src=- shape=0e61a897 vocab=e5dee1d9
-/
@[simp] theorem preShift_γ_hom_app (c : B) (f : a ⟶ b) (g : b ⟶ c) :
    (preShift R c f).γ.hom.app g = (associator f g (𝐪 c)).hom := rfl

/--
@isnad1 id=eq.0h7v.s10.5c9aab37737b from=translated src=- shape=8c7a7b94 vocab=d64897ab
-/
@[simp] theorem preShift_γ_inv_app (c : B) (f : a ⟶ b) (g : b ⟶ c) :
    (preShift R c f).γ.inv.app g = (associator f g (𝐪 c)).inv := rfl

/-- The isomorphism `(G H) q_ν ≅ (G q_μ) H` built from `γ_H`.-/
def γR (g : a ⟶ b) (h : b ⟶ c) : (g ≫ h) ≫ 𝐪 c ≅ (g ≫ 𝐪 b) ≫ h :=
  associator g h (𝐪 c) ≪≫ whiskerLeftIso (R := R) g (𝛄 h) ≪≫ (associator g (𝐪 b) h).symm

/--
@isnad1 id=eq.0h7v.s9.d3e711c47681 from=translated src=- shape=c8d0fd6c vocab=a99ce443
-/
theorem γR_hom (g : a ⟶ b) (h : b ⟶ c) :
    (γR (R := R) g h).hom = (associator g h (𝐪 c)).hom ≫ g ◁ (𝛄 h).hom ≫
      (associator g (𝐪 b) h).inv := rfl

/--
@isnad1 id=eq.0h7v.s9.1477111a8ca4 from=translated src=- shape=9d31e0c9 vocab=a99ce443
-/
theorem γR_inv (g : a ⟶ b) (h : b ⟶ c) :
    (γR (R := R) g h).inv = (associator g (𝐪 b) h).hom ≫ g ◁ (𝛄 h).inv ≫
      (associator g h (𝐪 c)).inv := by
  simp [γR]

/--
@isnad1 id=mem.0h7v.s10.3f72dd337e4a from=translated src=- shape=7c41e01c vocab=765be15e
-/
theorem γR_hom_mem (g : a ⟶ b) (h : b ⟶ c) :
    (γR (R := R) g h).hom ∈ parity (R := R) ((g ≫ h) ≫ 𝐪 c) ((g ≫ 𝐪 b) ≫ h) 0 := by
  rw [γR_hom]
  have := comp_mem (comp_mem (associator_hom_mem (R := R) g h _)
    (whiskerLeft_mem g (γ_hom_mem (R := R) h))) (inv_mem _ (associator_hom_mem (R := R) g _ h))
  simpa using this

/--
@isnad1 id=eq.0h9v.s9.16ba588916b9 from=translated src=- shape=a01ab7fb vocab=4332e3e1
-/
@[reassoc]
theorem γR_naturality {g g' : a ⟶ b} (η : g ⟶ g') (h : b ⟶ c) :
    η ▷ h ▷ 𝐪 c ≫ (γR (R := R) g' h).hom = (γR (R := R) g h).hom ≫ η ▷ 𝐪 b ▷ h := by
  simp only [γR_hom, Category.assoc]
  rw [associator_naturality_left_assoc R, whisker_exchange_of_even_right_assoc _ (γ_hom_mem h),
    associator_inv_naturality_left R]

/-- `γR` is natural in the second variable with respect to all 2-morphisms.
@isnad1 id=eq.0h9v.s9.430a02fd3a5c from=translated src=- shape=0fd139f9 vocab=2e940d7b
-/
@[reassoc]
theorem γR_naturality_right (g : a ⟶ b) {h i : b ⟶ c} (θ : h ⟶ i) :
    (γR (R := R) g h).hom ≫ (g ≫ 𝐪 b) ◁ θ = (g ◁ θ) ▷ 𝐪 c ≫ (γR (R := R) g i).hom := by
  simp only [γR_hom, Category.assoc]
  rw [← associator_inv_naturality_right R, ← whiskerLeft_comp'_assoc R, γ_naturality,
    whiskerLeft_comp'_assoc R, associator_naturality_middle_assoc R]

variable (R) in
/-- `H - : ℋom(λ, μ) → ℋom(λ, ν)` (i.e. `G ↦ G ≫ H`) as a morphism of shift data, with `γ`
built from `γ_H`.-/
def postShift (a : B) (h : b ⟶ c) : ShiftFunctor R (homShift R a b) (homShift R a c) where
  F := postcomp R h
  γ := NatIso.ofComponents (fun g => γR (R := R) g h) (fun η => by
    simp only [Functor.comp_obj, Functor.comp_map, postcomp_map]
    exact γR_naturality η h)
  γ_mem g := γR_hom_mem g h

/--
@isnad1 id=eq.0h6v.s8.b0f5fbb01697 from=translated src=- shape=007e2239 vocab=6e57e9dd
-/
@[simp] theorem postShift_F (a : B) (h : b ⟶ c) : (postShift R a h).F = postcomp R h := rfl

/--
@isnad1 id=eq.0h7v.s10.2f161ac4cb05 from=translated src=- shape=ee4eadec vocab=85e17ebf
-/
@[simp] theorem postShift_γ_hom_app (a : B) (h : b ⟶ c) (g : a ⟶ b) :
    (postShift R a h).γ.hom.app g = (γR (R := R) g h).hom := rfl

/--
@isnad1 id=eq.0h7v.s10.973f6641a9df from=translated src=- shape=b7bf730d vocab=1f7f4bfa
-/
@[simp] theorem postShift_γ_inv_app (a : B) (h : b ⟶ c) (g : a ⟶ b) :
    (postShift R a h).γ.inv.app g = (γR (R := R) g h).inv := rfl

/-- `- q_ν` is the shift functor `(Q, 1)` of `ℋom(λ, ν)`.
@isnad1 id=eq.0h4v.s8.a133daecca57 from=translated src=- shape=077c8396 vocab=5fc920ab
-/
theorem map_postShift_q (a c : B) :
    Orbit.map (postShift R a (𝐪 c)) = Orbit.map (ShiftFunctor.self (homShift R a c)) := by
  refine Orbit.map_congr rfl fun g => ?_
  simp only [Category.id_comp, postShift_γ_hom_app,
    ShiftFunctor.self_γ_hom_app, γR_hom, γ_q, whiskerLeft_id (R := R), Category.id_comp,
    Iso.hom_inv_id]
  rfl

/--
@isnad1 id=eq.0h7v.s10.339734ecaec1 from=translated src=- shape=7fd6035c vocab=3bdbfba5
-/
theorem map_postShift_q_map (a c : B) {X Y : Orbit (homShift R a c)} (z : X ⟶ Y) :
    (Orbit.map (postShift R a (𝐪 c))).map z =
      (Orbit.map (ShiftFunctor.self (homShift R a c))).map z := by
  have := CategoryTheory.Functor.congr_hom (map_postShift_q (R := R) a c) z
  rw [this]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

/-! ## The coherence maps as compatible natural transformations -/

section Coherence

variable (R)

/-- `λ` as a natural transformation `1 ≫ - ⟶ -`.-/
def lNat (a b : B) : precomp R (𝟙 a) ⟶ 𝟭 (a ⟶ b) where
  app g := (leftUnitor g).hom
  naturality _ _ η := leftUnitor_naturality R η

/-- `ρ` as a natural transformation `- ≫ 1 ⟶ -`.-/
def rNat (a b : B) : postcomp R (𝟙 b) ⟶ 𝟭 (a ⟶ b) where
  app f := (rightUnitor f).hom
  naturality _ _ η := rightUnitor_naturality R η

/-- `α_{F,G,-}` as a natural transformation `(F ≫ G) ≫ - ⟶ F ≫ G ≫ -`.-/
def αNatRight (d : B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) :
    precomp R (c := d) (f ≫ g) ⟶ precomp R g ⋙ precomp R f where
  app h := (associator f g h).hom
  naturality _ _ η := associator_naturality_right R f g η

/-- `α_{-,G,H}` as a natural transformation `(- ≫ G) ≫ H ⟶ - ≫ G ≫ H`.-/
def αNatLeft (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) :
    postcomp R (a := a) g ⋙ postcomp R h ⟶ postcomp R (g ≫ h) where
  app f := (associator f g h).hom
  naturality _ _ η := associator_naturality_left R η g h

/-- `α_{F,-,H}` as a natural transformation `(F ≫ -) ≫ H ⟶ F ≫ (- ≫ H)`.-/
def αNatMiddle {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) :
    precomp R (c := c) f ⋙ postcomp R h ⟶ postcomp R h ⋙ precomp R f where
  app g := (associator f g h).hom
  naturality _ _ η := associator_naturality_middle R f η h

variable {R}

set_option backward.isDefEq.respectTransparency false in
open Bicategory in
/--
@isnad1 id=eq.0h5v.s11.16f5166b8067 from=translated src=- shape=e319b2ad vocab=2ea9af1e
-/
theorem lNat_compat (a b : B) (g : a ⟶ b) :
    (preShift R b (𝟙 a)).γ.hom.app g ≫ (lNat R a b).app ((homShift R a b).Q.obj g) =
      (homShift R a b).Q.map ((lNat R a b).app g) ≫ (ShiftFunctor.id (homShift R a b)).γ.hom.app g := by
  simp only [preShift_γ_hom_app, lNat, Functor.id_obj, homShift_Q, postcomp_map,
    ShiftFunctor.id_γ_hom_app, Category.comp_id]
  exact (leftUnitor_whiskerRight R g (𝐪 b)).symm

set_option backward.isDefEq.respectTransparency false in
open Bicategory in
/--
@isnad1 id=eq.0h5v.s11.0338430e50cf from=translated src=- shape=9c4f1233 vocab=e0ae2048
-/
theorem rNat_compat (a b : B) (g : a ⟶ b) :
    (postShift R a (𝟙 b)).γ.hom.app g ≫ (rNat R a b).app ((homShift R a b).Q.obj g) =
      (homShift R a b).Q.map ((rNat R a b).app g) ≫ (ShiftFunctor.id (homShift R a b)).γ.hom.app g := by
  simp only [postShift_γ_hom_app, rNat, Functor.id_obj, homShift_Q, postcomp_map,
    ShiftFunctor.id_γ_hom_app, Category.comp_id, γR_hom, Category.assoc]
  have key : ∀ g' : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩,
      (α_ g' (𝟙 _) (Underlying2.hom1 (𝐪 b))).hom ≫
        Bicategory.whiskerLeft g' (γU (R := R) (𝟙 (⟨b⟩ : Underlying2 R B))).hom ≫
          (α_ g' (Underlying2.hom1 (𝐪 b)) (𝟙 _)).inv ≫ (ρ_ (g' ≫ Underlying2.hom1 (𝐪 b))).hom =
      Bicategory.whiskerRight (ρ_ g').hom (Underlying2.hom1 (𝐪 b)) := by
    intro g'
    rw [γU_id]
    bicategory
  exact congrArg Subtype.val (key (Underlying2.hom1 g))

open Bicategory in
/--
@isnad1 id=eq.0h9v.s12.14b680e9fe73 from=translated src=- shape=3ee93e4c vocab=9b39ef78
-/
theorem αNatRight_compat (d : B) {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (preShift R d (f ≫ g)).γ.hom.app h ≫ (αNatRight R d f g).app ((homShift R c d).Q.obj h) =
      (homShift R a d).Q.map ((αNatRight R d f g).app h) ≫
        ((preShift R d g).comp (preShift R d f)).γ.hom.app h := by
  simp only [preShift_γ_hom_app, αNatRight, Functor.comp_obj, homShift_Q,
    ShiftFunctor.comp_γ_hom_app, preShift_F]
  have key : ∀ (f' : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩) (g' : (⟨b⟩ : Underlying2 R B) ⟶ ⟨c⟩)
      (h' : (⟨c⟩ : Underlying2 R B) ⟶ ⟨d⟩),
      (α_ (f' ≫ g') h' (Underlying2.hom1 (𝐪 d))).hom ≫ (α_ f' g' (h' ≫ Underlying2.hom1 (𝐪 d))).hom =
        Bicategory.whiskerRight (α_ f' g' h').hom (Underlying2.hom1 (𝐪 d)) ≫
          (α_ f' (g' ≫ h') (Underlying2.hom1 (𝐪 d))).hom ≫
            Bicategory.whiskerLeft f' (α_ g' h' (Underlying2.hom1 (𝐪 d))).hom := by
    intro f' g' h'
    bicategory
  exact congrArg Subtype.val (key (Underlying2.hom1 f) (Underlying2.hom1 g) (Underlying2.hom1 h))

set_option backward.isDefEq.respectTransparency false in
open Bicategory in
/--
@isnad1 id=eq.0h9v.s12.3edf6dfe8890 from=translated src=- shape=efe64904 vocab=a6f3e907
-/
theorem αNatLeft_compat (a : B) {b c d : B} (g : b ⟶ c) (h : c ⟶ d) (f : a ⟶ b) :
    ((postShift R a g).comp (postShift R a h)).γ.hom.app f ≫
        (αNatLeft R a g h).app ((homShift R a b).Q.obj f) =
      (homShift R a d).Q.map ((αNatLeft R a g h).app f) ≫ (postShift R a (g ≫ h)).γ.hom.app f := by
  simp only [postShift_γ_hom_app, αNatLeft, Functor.comp_obj, homShift_Q,
    postcomp_map, ShiftFunctor.comp_γ_hom_app, postShift_F, γR_hom, Category.assoc]
  have key : ∀ (f' : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩) (g' : (⟨b⟩ : Underlying2 R B) ⟶ ⟨c⟩)
      (h' : (⟨c⟩ : Underlying2 R B) ⟶ ⟨d⟩),
      (α_ (f' ≫ g') h' (Underlying2.hom1 (𝐪 d))).hom ≫
          Bicategory.whiskerLeft (f' ≫ g') (γU (R := R) h').hom ≫
            (α_ (f' ≫ g') (Underlying2.hom1 (𝐪 c)) h').inv ≫
        Bicategory.whiskerRight ((α_ f' g' (Underlying2.hom1 (𝐪 c))).hom ≫
          Bicategory.whiskerLeft f' (γU (R := R) g').hom ≫
            (α_ f' (Underlying2.hom1 (𝐪 b)) g').inv) h' ≫
          (α_ (f' ≫ Underlying2.hom1 (𝐪 b)) g' h').hom =
      Bicategory.whiskerRight (α_ f' g' h').hom (Underlying2.hom1 (𝐪 d)) ≫
        (α_ f' (g' ≫ h') (Underlying2.hom1 (𝐪 d))).hom ≫
          Bicategory.whiskerLeft f' (γU (R := R) (g' ≫ h')).hom ≫
            (α_ f' (Underlying2.hom1 (𝐪 b)) (g' ≫ h')).inv := by
    intro f' g' h'
    rw [γU_comp]
    bicategory
  exact congrArg Subtype.val (key (Underlying2.hom1 f) (Underlying2.hom1 g) (Underlying2.hom1 h))

set_option backward.isDefEq.respectTransparency false in
open Bicategory in
/--
@isnad1 id=eq.0h9v.s12.26271d18383b from=translated src=- shape=eff5e3e4 vocab=58f8f78f
-/
theorem αNatMiddle_compat {a b c d : B} (f : a ⟶ b) (h : c ⟶ d) (g : b ⟶ c) :
    ((preShift R c f).comp (postShift R a h)).γ.hom.app g ≫
        (αNatMiddle R f h).app ((homShift R b c).Q.obj g) =
      (homShift R a d).Q.map ((αNatMiddle R f h).app g) ≫
        ((postShift R b h).comp (preShift R d f)).γ.hom.app g := by
  simp only [postShift_γ_hom_app, preShift_γ_hom_app, αNatMiddle, Functor.comp_obj,
    homShift_Q, postcomp_map, precomp_map, ShiftFunctor.comp_γ_hom_app, postShift_F,
    preShift_F, γR_hom, Category.assoc]
  have key : ∀ (f' : (⟨a⟩ : Underlying2 R B) ⟶ ⟨b⟩) (g' : (⟨b⟩ : Underlying2 R B) ⟶ ⟨c⟩)
      (h' : (⟨c⟩ : Underlying2 R B) ⟶ ⟨d⟩),
      (α_ (f' ≫ g') h' (Underlying2.hom1 (𝐪 d))).hom ≫
          Bicategory.whiskerLeft (f' ≫ g') (γU (R := R) h').hom ≫
            (α_ (f' ≫ g') (Underlying2.hom1 (𝐪 c)) h').inv ≫
        Bicategory.whiskerRight (α_ f' g' (Underlying2.hom1 (𝐪 c))).hom h' ≫
          (α_ f' (g' ≫ Underlying2.hom1 (𝐪 c)) h').hom =
      Bicategory.whiskerRight (α_ f' g' h').hom (Underlying2.hom1 (𝐪 d)) ≫
        (α_ f' (g' ≫ h') (Underlying2.hom1 (𝐪 d))).hom ≫
          Bicategory.whiskerLeft f' ((α_ g' h' (Underlying2.hom1 (𝐪 d))).hom ≫
            Bicategory.whiskerLeft g' (γU (R := R) h').hom ≫
              (α_ g' (Underlying2.hom1 (𝐪 c)) h').inv) := by
    intro f' g' h'
    bicategory
  exact congrArg Subtype.val (key (Underlying2.hom1 f) (Underlying2.hom1 g) (Underlying2.hom1 h))

end Coherence

end CentralShift

/-! ## The orbit 2-supercategory -/

/-- The objects of the orbit 2-supercategory `Orbit2 R 𝔅`: the objects of `𝔅`.-/
@[ext]
structure Orbit2 (R : Type w₁) (B : Type u) where
  /-- The object of `𝔅`.-/
  obj : B

namespace Orbit2

open CentralShift Orbit

variable {R : Type w₁} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B] [CentralShift R B]

local notation "𝐪" => CentralShift.q (R := R)
local notation "𝐪⁻" => CentralShift.qinv (R := R)

/-- The bicategory data of `Orbit2 R 𝔅`: the morphism supercategories are the orbit
supercategories of the shift data `(- q_μ, - q_μ⁻¹)`, horizontal composition with a 1-morphism
is induced by the morphisms of shift data `preShift` and `postShift`, and the coherence maps are
those of `𝔅` in degree zero.-/
instance instBicategoryStruct : BicategoryStruct.{w, v} (Orbit2 R B) where
  Hom a b := Orbit (homShift R a.obj b.obj)
  id a := ⟨𝟙 a.obj⟩
  comp f g := ⟨f.obj ≫ g.obj⟩
  homCategory _ _ := inferInstance
  whiskerLeft f _ _ η := (Orbit.map (preShift R _ f.obj)).map η
  whiskerRight η h := (Orbit.map (postShift R _ h.obj)).map η
  associator f g h := (Orbit.ι _).mapIso (associator f.obj g.obj h.obj)
  leftUnitor f := (Orbit.ι _).mapIso (leftUnitor f.obj)
  rightUnitor f := (Orbit.ι _).mapIso (rightUnitor f.obj)

instance (a b : Orbit2 R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (Orbit (homShift R a.obj b.obj)))

instance (a b : Orbit2 R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (Orbit (homShift R a.obj b.obj)))

instance (a b : Orbit2 R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (Orbit (homShift R a.obj b.obj)))

instance (a b : Orbit2 R B) : GradedSupercategory R (a ⟶ b) :=
  inferInstanceAs (GradedSupercategory R (Orbit (homShift R a.obj b.obj)))

variable {a b c d : Orbit2 R B}

/--
@isnad1 id=eq.0h3v.s7.4815c004d3bb from=translated src=- shape=d68ce944 vocab=cb38e595
-/
@[simp] theorem id_obj (a : Orbit2 R B) : (𝟙 a : a ⟶ a).obj = 𝟙 a.obj := rfl

/--
@isnad1 id=eq.0h7v.s8.54487ed4e65f from=translated src=- shape=423c1255 vocab=77b9351e
-/
@[simp] theorem comp_obj (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).obj = f.obj ≫ g.obj := rfl

/--
@isnad1 id=eq.0h9v.s9.4c63da139e40 from=translated src=- shape=c80011bc vocab=3ed5a785
-/
theorem whiskerLeft_def (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ◁ η = (Orbit.map (preShift R c.obj f.obj)).map η := rfl

/--
@isnad1 id=eq.0h9v.s9.e51b2ba16aad from=translated src=- shape=4d143f63 vocab=a4812368
-/
theorem whiskerRight_def {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    η ▷ h = (Orbit.map (postShift R a.obj h.obj)).map η := rfl

/--
@isnad1 id=eq.0h9v.s11.43b92d632719 from=translated src=- shape=afd7e509 vocab=4d2419bc
-/
theorem associator_hom_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).hom = (Orbit.ι (homShift R a.obj d.obj)).map (associator f.obj g.obj h.obj).hom :=
  rfl

/--
@isnad1 id=eq.0h9v.s11.2ec8e8aec423 from=translated src=- shape=24954aae vocab=828862c4
-/
theorem associator_inv_def (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (associator f g h).inv = (Orbit.ι (homShift R a.obj d.obj)).map (associator f.obj g.obj h.obj).inv :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.7e71f01da71e from=translated src=- shape=782dc0a0 vocab=aa3aa775
-/
theorem leftUnitor_hom_def (f : a ⟶ b) :
    (leftUnitor f).hom = (Orbit.ι (homShift R a.obj b.obj)).map (leftUnitor f.obj).hom := rfl

/--
@isnad1 id=eq.0h5v.s10.628e1a59b870 from=translated src=- shape=414176a2 vocab=5a22e4be
-/
theorem leftUnitor_inv_def (f : a ⟶ b) :
    (leftUnitor f).inv = (Orbit.ι (homShift R a.obj b.obj)).map (leftUnitor f.obj).inv := rfl

/--
@isnad1 id=eq.0h5v.s10.19eb47a1ecf3 from=translated src=- shape=154d9390 vocab=050aecbf
-/
theorem rightUnitor_hom_def (f : a ⟶ b) :
    (rightUnitor f).hom = (Orbit.ι (homShift R a.obj b.obj)).map (rightUnitor f.obj).hom := rfl

/-- Whiskering of a 2-morphism of degree zero.
@isnad1 id=eq.0h9v.s11.818396dd12e7 from=translated src=- shape=05b19dab vocab=a789bc6e
-/
theorem whiskerLeft_ι (f : a ⟶ b) {g h : b.obj ⟶ c.obj} (η : g ⟶ h) :
    f ◁ (Orbit.ι (homShift R b.obj c.obj)).map η = (Orbit.ι (homShift R a.obj c.obj)).map (f.obj ◁ η) :=
  map_ι_map _ η

/--
@isnad1 id=eq.0h9v.s11.0f80ad652341 from=translated src=- shape=51507b87 vocab=2b113b3b
-/
theorem whiskerRight_ι {f g : a.obj ⟶ b.obj} (η : f ⟶ g) (h : b ⟶ c) :
    (Orbit.ι (homShift R a.obj b.obj)).map η ▷ h = (Orbit.ι (homShift R a.obj c.obj)).map (η ▷ h.obj) :=
  map_ι_map _ η

/-! ### The axioms of a 2-supercategory other than the super interchange law -/

/--
@isnad1 id=eq.0h7v.s9.e9d4d3aa85b9 from=translated src=- shape=4c73e1cf vocab=c8528b3c
-/
theorem id_whiskerLeft' {f g : a ⟶ b} (η : f ⟶ g) :
    𝟙 a ◁ η = (leftUnitor f).hom ≫ η ≫ (leftUnitor g).inv := by
  have e := map_map_comp_ι_map (Φ := preShift R b.obj (𝟙 a.obj)) (Ψ := ShiftFunctor.id _)
    (lNat R a.obj b.obj) (lNat_compat a.obj b.obj) η
  rw [map_map_id] at e
  change 𝟙 a ◁ η ≫ (leftUnitor g).hom = (leftUnitor f).hom ≫ η at e
  rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.0h11v.s10.1ca752cd2589 from=translated src=- shape=18d9ef68 vocab=64a9482a
-/
theorem comp_whiskerLeft' (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η = (associator f g h).hom ≫ f ◁ g ◁ η ≫ (associator f g h').inv := by
  have e := map_map_comp_ι_map (Φ := preShift R d.obj (f.obj ≫ g.obj))
    (Ψ := (preShift R d.obj g.obj).comp (preShift R d.obj f.obj))
    (αNatRight R d.obj f.obj g.obj) (αNatRight_compat d.obj f.obj g.obj) η
  rw [← map_map_comp] at e
  change (f ≫ g) ◁ η ≫ (associator f g h').hom = (associator f g h).hom ≫ f ◁ g ◁ η at e
  rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.0h7v.s9.cef4c7864658 from=translated src=- shape=eb2a28f9 vocab=58f9b96c
-/
theorem whiskerRight_id' {f g : a ⟶ b} (η : f ⟶ g) :
    η ▷ 𝟙 b = (rightUnitor f).hom ≫ η ≫ (rightUnitor g).inv := by
  have e := map_map_comp_ι_map (Φ := postShift R a.obj (𝟙 b.obj)) (Ψ := ShiftFunctor.id _)
    (rNat R a.obj b.obj) (rNat_compat a.obj b.obj) η
  rw [map_map_id] at e
  change η ▷ 𝟙 b ≫ (rightUnitor g).hom = (rightUnitor f).hom ≫ η at e
  rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/--
@isnad1 id=eq.0h11v.s10.7825233dee09 from=translated src=- shape=86427a74 vocab=476f406e
-/
theorem whiskerRight_comp' {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) = (associator f g h).inv ≫ η ▷ g ▷ h ≫ (associator f' g h).hom := by
  have e := map_map_comp_ι_map (Φ := (postShift R a.obj g.obj).comp (postShift R a.obj h.obj))
    (Ψ := postShift R a.obj (g.obj ≫ h.obj))
    (αNatLeft R a.obj g.obj h.obj) (αNatLeft_compat a.obj g.obj h.obj) η
  rw [← map_map_comp] at e
  change η ▷ g ▷ h ≫ (associator f' g h).hom = (associator f g h).hom ≫ η ▷ (g ≫ h) at e
  rw [e, Iso.inv_hom_id_assoc]

/--
@isnad1 id=eq.0h11v.s10.cfbfdcbb3468 from=translated src=- shape=95cd445b vocab=b57395f0
-/
theorem whisker_assoc' (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h = (associator f g h).hom ≫ f ◁ (η ▷ h) ≫ (associator f g' h).inv := by
  have e := map_map_comp_ι_map (Φ := (preShift R c.obj f.obj).comp (postShift R a.obj h.obj))
    (Ψ := (postShift R b.obj h.obj).comp (preShift R d.obj f.obj))
    (αNatMiddle R f.obj h.obj) (αNatMiddle_compat f.obj h.obj) η
  rw [← map_map_comp, ← map_map_comp] at e
  change (f ◁ η) ▷ h ≫ (associator f g' h).hom = (associator f g h).hom ≫ f ◁ (η ▷ h) at e
  rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h11v.s11.e82d0ac00871 from=translated src=- shape=a8e0a868 vocab=36e340df
-/
theorem pentagon' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) {e : Orbit2 R B} (i : d ⟶ e) :
    (associator f g h).hom ▷ i ≫ (associator f (g ≫ h) i).hom ≫ f ◁ (associator g h i).hom =
      (associator (f ≫ g) h i).hom ≫ (associator f g (h ≫ i)).hom := by
  rw [associator_hom_def, associator_hom_def, associator_hom_def, associator_hom_def,
    associator_hom_def, whiskerRight_ι, whiskerLeft_ι, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  exact congrArg _ (TwoSupercategory.pentagon (R := R) f.obj g.obj h.obj i.obj)

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h7v.s10.a1e1a17cacb7 from=translated src=- shape=73f0bb72 vocab=cf8999c1
-/
theorem triangle' (f : a ⟶ b) (g : b ⟶ c) :
    (associator f (𝟙 b) g).hom ≫ f ◁ (leftUnitor g).hom = (rightUnitor f).hom ▷ g := by
  rw [associator_hom_def, leftUnitor_hom_def, rightUnitor_hom_def, whiskerLeft_ι, whiskerRight_ι,
    ← Functor.map_comp]
  exact congrArg _ (TwoSupercategory.triangle (R := R) f.obj g.obj)

/--
@isnad1 id=eq.0h11v.s9.61c8b1088d4d from=translated src=- shape=095264ce vocab=449bc920
-/
theorem whiskerLeft_comp'' (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ :=
  (Orbit.map (preShift R c.obj f.obj)).map_comp η θ

/--
@isnad1 id=eq.0h7v.s8.aeecb01ae259 from=translated src=- shape=ee7e2d2d vocab=a3702360
-/
theorem whiskerLeft_id'' (f : a ⟶ b) (g : b ⟶ c) : f ◁ 𝟙 g = 𝟙 (f ≫ g) :=
  (Orbit.map (preShift R c.obj f.obj)).map_id g

/--
@isnad1 id=eq.0h11v.s9.a11ec7973365 from=translated src=- shape=b481fa42 vocab=77a339f6
-/
theorem comp_whiskerRight'' {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i :=
  (Orbit.map (postShift R a.obj i.obj)).map_comp η θ

/--
@isnad1 id=eq.0h10v.s11.071436d84b3e from=translated src=- shape=c4bbb96f vocab=6e48b201
-/
theorem whiskerLeft_add'' (f : a ⟶ b) {g h : b ⟶ c} (η θ : g ⟶ h) :
    f ◁ (η + θ) = f ◁ η + f ◁ θ :=
  (Orbit.map (preShift R c.obj f.obj)).map_add

/--
@isnad1 id=eq.0h8v.s10.260bc56941db from=translated src=- shape=f39b5c82 vocab=449bc920
-/
theorem whiskerLeft_zero'' (f : a ⟶ b) (g h : b ⟶ c) : f ◁ (0 : g ⟶ h) = 0 :=
  (Orbit.map (preShift R c.obj f.obj)).map_zero g h

/-! ### The super interchange law -/

section Interchange

variable {f g : a ⟶ b} {h i : b ⟶ c}

set_option backward.isDefEq.respectTransparency false in
/-- The super interchange law with a 2-morphism of degree zero on the right.
@isnad1 id=eq.2h13v.s13.a9e13d4265b3 from=translated src=- shape=ca109689 vocab=78f94e4f
-/
theorem interchange_ι {p q : ZMod 2} {x : f ⟶ g} (hx : x ∈ parity (R := R) f g p)
    {y : h.obj ⟶ i.obj} (hy : y ∈ parity (R := R) h.obj i.obj q) :
    x ▷ h ≫ g ◁ (Orbit.ι (homShift R b.obj c.obj)).map y =
      koszulSign p q • (f ◁ (Orbit.ι (homShift R b.obj c.obj)).map y ≫ x ▷ i) := by
  have hnat : IsSupernatural R q (F := (postShift R a.obj h.obj).F) (G := (postShift R a.obj i.obj).F)
      fun X => X ◁ y :=
    { mem := fun X => whiskerLeft_mem X hy
      naturality := fun {X X' r z} hz => by
        simp only [postShift_F, postcomp_map]
        rw [super_interchange hz hy, koszulSign_smul (R := R), mul_comm] }
  have hγ : ∀ X : a.obj ⟶ b.obj, (postShift R a.obj h.obj).γ.hom.app X ≫
      (homShift R a.obj b.obj).Q.obj X ◁ y =
        (homShift R a.obj c.obj).Q.map (X ◁ y) ≫ (postShift R a.obj i.obj).γ.hom.app X := fun X => by
    simp only [postShift_γ_hom_app, homShift_Q, postcomp_map]
    exact γR_naturality_right X y
  have e := map_map_comp_ι (Φ := postShift R a.obj h.obj) (Ψ := postShift R a.obj i.obj) hnat hγ hx
  rw [whiskerLeft_ι, whiskerLeft_ι, whiskerRight_def, whiskerRight_def, koszulSign_smul (R := R),
    mul_comm]
  exact e

set_option backward.isDefEq.respectTransparency false in
/-- The super interchange law with `σ` on the right.
@isnad1 id=eq.0h9v.s11.9a87edf18d16 from=translated src=- shape=b2905a22 vocab=dcad7d20
-/
theorem interchange_σ (x : f ⟶ g) :
    x ▷ (h ≫ (⟨𝐪 c.obj⟩ : c ⟶ c)) ≫ g ◁ (σIso h).hom = f ◁ (σIso h).hom ≫ x ▷ h := by
  have w : x ▷ (h ≫ (⟨𝐪 c.obj⟩ : c ⟶ c)) ≫
      (Orbit.ι (homShift R a.obj c.obj)).map (associator g.obj h.obj (𝐪 c.obj)).inv =
      (Orbit.ι (homShift R a.obj c.obj)).map (associator f.obj h.obj (𝐪 c.obj)).inv ≫
        (x ▷ h) ▷ (⟨𝐪 c.obj⟩ : c ⟶ c) := by
    rw [whiskerRight_comp', Category.assoc, Category.assoc]
    erw [Iso.hom_inv_id, Category.comp_id]
    rfl
  have s : (x ▷ h) ▷ (⟨𝐪 c.obj⟩ : c ⟶ c) ≫ (σIso (g ≫ h)).hom = (σIso (f ≫ h)).hom ≫ x ▷ h := by
    rw [whiskerRight_def]
    erw [map_postShift_q_map]
    exact map_self_comp_σIso_hom (x ▷ h)
  rw [whiskerLeft_def, whiskerLeft_def, map_σIso_hom, map_σIso_hom, preShift_γ_inv_app,
    preShift_γ_inv_app, ← Category.assoc, w, Category.assoc]
  erw [s]
  rw [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The super interchange law with `σ⁻¹` on the right.
@isnad1 id=eq.0h9v.s11.06b8a45067bb from=translated src=- shape=f88b0ba5 vocab=76e225e9
-/
theorem interchange_σ_inv (x : f ⟶ g) :
    x ▷ h ≫ g ◁ (σIso h).inv = f ◁ (σIso h).inv ≫ x ▷ (h ≫ (⟨𝐪 c.obj⟩ : c ⟶ c)) := by
  rw [← cancel_mono ((Orbit.map (preShift R c.obj g.obj)).mapIso (σIso h)).hom, Functor.mapIso_hom]
  change (x ▷ h ≫ g ◁ (σIso h).inv) ≫ g ◁ (σIso h).hom =
    (f ◁ (σIso h).inv ≫ x ▷ (h ≫ (⟨𝐪 c.obj⟩ : c ⟶ c))) ≫ g ◁ (σIso h).hom
  rw [Category.assoc, Category.assoc, ← whiskerLeft_comp'', Iso.inv_hom_id, whiskerLeft_id'',
    Category.comp_id, interchange_σ, ← Category.assoc, ← whiskerLeft_comp'', Iso.inv_hom_id,
    whiskerLeft_id'', Category.id_comp]

/-- The interchange law is closed under vertical composition on the right.
@isnad1 id=eq.2h16v.s12.6565a42ec4cf from=translated src=- shape=bfb22c90 vocab=d92115ea
-/
theorem interchange_comp {p q₁ q₂ : ZMod 2} {x : f ⟶ g} {h h' i : b ⟶ c} {y₁ : h ⟶ h'}
    {y₂ : h' ⟶ i}
    (e₁ : x ▷ h ≫ g ◁ y₁ = koszulSign p q₁ • (f ◁ y₁ ≫ x ▷ h'))
    (e₂ : x ▷ h' ≫ g ◁ y₂ = koszulSign p q₂ • (f ◁ y₂ ≫ x ▷ i)) :
    x ▷ h ≫ g ◁ (y₁ ≫ y₂) = koszulSign p (q₁ + q₂) • (f ◁ (y₁ ≫ y₂) ≫ x ▷ i) := by
  rw [whiskerLeft_comp'', whiskerLeft_comp'', ← Category.assoc, e₁, Linear.smul_comp,
    Category.assoc, e₂, Linear.comp_smul, smul_smul, ← koszulSign_add_right, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The super interchange law with a homogeneous 2-morphism of degree `n` on the right, by
induction on `n`.
@isnad1 id=eq.3h14v.s12.f940001de5c7 from=translated src=- shape=1aa80ce6 vocab=9d68c500
-/
theorem interchange_of_degree {p q : ZMod 2} {x : f ⟶ g} (hx : x ∈ parity (R := R) f g p)
    (n : ℤ) : ∀ {h i : b ⟶ c} (y : h ⟶ i), y ∈ degree (R := R) h i n →
      y ∈ parity (R := R) h i q → x ▷ h ≫ g ◁ y = koszulSign p q • (f ◁ y ≫ x ▷ i) := by
  induction n using Int.induction_on with
  | zero =>
    intro h i y hn hq
    have hq' : (⟨y, hn⟩ : (⟨h⟩ : DegreeZero R (Orbit (homShift R b.obj c.obj))) ⟶ ⟨i⟩) ∈
        parity (R := R) (⟨h⟩ : DegreeZero R (Orbit (homShift R b.obj c.obj))) ⟨i⟩ q := hq
    obtain ⟨y₀, hy₀, rfl⟩ : ∃ y₀ : h.obj ⟶ i.obj, y₀ ∈ parity (R := R) h.obj i.obj q ∧
        (Orbit.ι (homShift R b.obj c.obj)).map y₀ = y :=
      ⟨(π₀ (homShift R b.obj c.obj)).map (⟨y, hn⟩ : (⟨h⟩ : DegreeZero R (Orbit _)) ⟶ ⟨i⟩),
        map_mem (π₀ (homShift R b.obj c.obj)) hq',
        congrArg Subtype.val (π₀_comp_ιZ_map (⟨y, hn⟩ : (⟨h⟩ : DegreeZero R (Orbit _)) ⟶ ⟨i⟩))⟩
    exact interchange_ι hx hy₀
  | succ n ih =>
    intro h i y hn hq
    have hσ := σIso_hom_mem (R := R) h
    have hd := σIso_hom_mem_degree (R := R) h
    have e1 : (σIso h).hom ≫ y ∈ degree (R := R) _ _ n := by
      simpa using comp_mem_degree hd hn
    have e2 : (σIso h).hom ≫ y ∈ parity (R := R) _ _ q := by
      simpa using comp_mem hσ hq
    have := interchange_comp (q₁ := 0) (q₂ := q) (x := x) (y₁ := (σIso h).inv) (y₂ := (σIso h).hom ≫ y)
      (by rw [koszulSign_zero_right, one_smul]; exact interchange_σ_inv x) (ih _ e1 e2)
    simpa using this
  | pred n ih =>
    intro h i y hn hq
    have hσ := inv_mem _ (σIso_hom_mem (R := R) i)
    have hd := inv_mem_degree _ (σIso_hom_mem_degree (R := R) i)
    have e1 : y ≫ (σIso i).inv ∈ degree (R := R) _ _ (-(n : ℤ)) := by
      have := comp_mem_degree hn hd
      rwa [show -(n : ℤ) - 1 + - -1 = -n by ring] at this
    have e2 : y ≫ (σIso i).inv ∈ parity (R := R) _ _ q := by
      simpa using comp_mem hq hσ
    have := interchange_comp (q₁ := q) (q₂ := 0) (x := x) (y₁ := y ≫ (σIso i).inv) (y₂ := (σIso i).hom)
      (ih _ e1 e2) (by rw [koszulSign_zero_right, one_smul]; exact interchange_σ x)
    simpa using this

/-- **The super interchange law of the orbit 2-supercategory.**
@isnad1 id=eq.2h13v.s12.ceb956e8f07e from=translated src=- shape=2fcbb9a4 vocab=811bb110
-/
theorem super_interchange' {p q : ZMod 2} {x : f ⟶ g} {y : h ⟶ i}
    (hx : x ∈ parity (R := R) f g p) (hy : y ∈ parity (R := R) h i q) :
    x ▷ h ≫ g ◁ y = koszulSign p q • (f ◁ y ≫ x ▷ i) := by
  have key : ∀ y' : h ⟶ i, x ▷ h ≫ g ◁ proj R q y' = koszulSign p q • (f ◁ proj R q y' ≫ x ▷ i) := by
    intro y'
    refine induction_on_degree (R := R) y' ?_ (fun n z hz => ?_) (fun z z' hz hz' => ?_)
    · rw [map_zero, whiskerLeft_zero'', whiskerLeft_zero'', Limits.comp_zero, Limits.zero_comp,
        smul_zero]
    · exact interchange_of_degree hx n _ (proj_mem_degree q hz) (proj_mem q z)
    · rw [map_add, whiskerLeft_add'', whiskerLeft_add'']
      simp only [Preadditive.comp_add, Preadditive.add_comp, smul_add, hz, hz']
  have := key y
  rwa [proj_of_mem hy] at this

end Interchange

/-- **The orbit 2-supercategory.** `Orbit2 R 𝔅` is a 2-supercategory.
@isnad1 id=twosuper.0h2v.s7.eab297e89eb4 from=translated src=- shape=54a83846 vocab=320fd6fb
-/
instance instTwoSupercategory : TwoSupercategory R (Orbit2 R B) where
  whiskerLeft_id f g := (Orbit.map (preShift R _ f.obj)).map_id g
  whiskerLeft_comp f _ _ _ η θ := (Orbit.map (preShift R _ f.obj)).map_comp η θ
  id_whiskerLeft η := id_whiskerLeft' η
  comp_whiskerLeft f g _ _ η := comp_whiskerLeft' f g η
  id_whiskerRight f g := (Orbit.map (postShift R _ g.obj)).map_id f
  comp_whiskerRight η θ i := (Orbit.map (postShift R _ i.obj)).map_comp η θ
  whiskerRight_id η := whiskerRight_id' η
  whiskerRight_comp η g h := whiskerRight_comp' η g h
  whisker_assoc f _ _ η h := whisker_assoc' f η h
  pentagon f g h i := pentagon' f g h i
  triangle f g := triangle' f g
  whiskerLeft_add f _ _ _ _ := (Orbit.map (preShift R _ f.obj)).map_add
  add_whiskerRight _ _ h := (Orbit.map (postShift R _ h.obj)).map_add
  whiskerLeft_smul f _ _ r η := Functor.Linear.map_smul (F := Orbit.map (preShift R _ f.obj)) η r
  smul_whiskerRight r η h := Functor.Linear.map_smul (F := Orbit.map (postShift R _ h.obj)) η r
  whiskerLeft_mem f _ _ _ _ hη := map_mem (Orbit.map (preShift R _ f.obj)) hη
  whiskerRight_mem h hη := map_mem (Orbit.map (postShift R _ h.obj)) hη
  super_interchange hη hθ := super_interchange' hη hθ
  associator_hom_mem f g h := map_mem (Orbit.ι _) (associator_hom_mem (R := R) f.obj g.obj h.obj)
  leftUnitor_hom_mem f := map_mem (Orbit.ι _) (leftUnitor_hom_mem (R := R) f.obj)
  rightUnitor_hom_mem f := map_mem (Orbit.ι _) (rightUnitor_hom_mem (R := R) f.obj)

/-- `Orbit2 R 𝔅` is a graded 2-supercategory: whiskering preserves degrees and the coherence
maps have degree zero.
@isnad1 id=gradedtw.0h2v.s7.1ac85dfb7e06 from=translated src=- shape=fd7b6485 vocab=526b6e51
-/
instance instGradedTwoSupercategory : GradedTwoSupercategory R (Orbit2 R B) where
  whiskerLeft_mem_degree f _ _ _ _ hη := map_mem_degree (Orbit.map (preShift R _ f.obj)) hη
  whiskerRight_mem_degree h hη := map_mem_degree (Orbit.map (postShift R _ h.obj)) hη
  associator_hom_mem_degree _ _ _ := ι_map_mem_degree _
  leftUnitor_hom_mem_degree _ := ι_map_mem_degree _
  rightUnitor_hom_mem_degree _ := ι_map_mem_degree _

/-! ### The `(Q, Π)`-structure -/

/-- `σ_λ : q_λ ⇒ 1_λ` of `Orbit2 R 𝔅`: the identity of `q_λ` in degree `-1` (the isomorphism
`σ` of the orbit supercategory `ℋom(λ, λ)` at `1_λ`, with the unitor).-/
def σ (a : Orbit2 R B) : (⟨𝐪 a.obj⟩ : a ⟶ a) ≅ 𝟙 a :=
  (Orbit.ι _).mapIso (leftUnitor (𝐪 a.obj)).symm ≪≫ σIso (⟨𝟙 a.obj⟩ : a ⟶ a)

/--
@isnad1 id=eq.0h3v.s11.a29432c189cb from=translated src=- shape=7cfdb78e vocab=4c558d91
-/
theorem σ_hom (a : Orbit2 R B) :
    (σ a).hom = (Orbit.ι (homShift R a.obj a.obj)).map (leftUnitor (𝐪 a.obj)).inv ≫
      (σIso (⟨𝟙 a.obj⟩ : a ⟶ a)).hom := rfl

/--
@isnad1 id=mem.0h3v.s11.127865906d10 from=translated src=- shape=39be8592 vocab=8c7efe04
-/
theorem σ_hom_mem (a : Orbit2 R B) : (σ a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [σ_hom]
  simpa using! comp_mem (map_mem (Orbit.ι _) (inv_mem _ (leftUnitor_hom_mem (R := R) (𝐪 a.obj))))
    (σIso_hom_mem (⟨𝟙 a.obj⟩ : a ⟶ a))

/--
@isnad1 id=mem.0h3v.s11.11c14ba8e0da from=translated src=- shape=080e9b7b vocab=dfb86985
-/
theorem σ_hom_mem_degree (a : Orbit2 R B) : (σ a).hom ∈ degree (R := R) _ (𝟙 a) (-1) := by
  rw [σ_hom]
  simpa using!
    comp_mem_degree (ι_map_mem_degree (d := homShift R a.obj a.obj) (leftUnitor (𝐪 a.obj)).inv)
    (σIso_hom_mem_degree (⟨𝟙 a.obj⟩ : a ⟶ a))

/-- `σ̄_λ : q_λ⁻¹ ⇒ 1_λ` of `Orbit2 R 𝔅`: `σ⁻¹` followed by `jj_λ`, of degree `1`.-/
def σbar (a : Orbit2 R B) : (⟨𝐪⁻ a.obj⟩ : a ⟶ a) ≅ 𝟙 a :=
  (σIso (⟨𝐪⁻ a.obj⟩ : a ⟶ a)).symm ≪≫ (Orbit.ι _).mapIso (jj (R := R) a.obj)

/--
@isnad1 id=eq.0h3v.s11.80a0db5880b3 from=translated src=- shape=099adc14 vocab=9ac57f91
-/
theorem σbar_hom (a : Orbit2 R B) :
    (σbar a).hom = (σIso (⟨𝐪⁻ a.obj⟩ : a ⟶ a)).inv ≫
      (Orbit.ι (homShift R a.obj a.obj)).map (jj (R := R) a.obj).hom := rfl

/--
@isnad1 id=mem.0h3v.s11.b08c01ebdca2 from=translated src=- shape=39be8592 vocab=e4503af2
-/
theorem σbar_hom_mem (a : Orbit2 R B) : (σbar a).hom ∈ parity (R := R) _ (𝟙 a) 0 := by
  rw [σbar_hom]
  simpa using! comp_mem (inv_mem _ (σIso_hom_mem (⟨𝐪⁻ a.obj⟩ : a ⟶ a)))
    (map_mem (Orbit.ι _) (jj_hom_mem (R := R) a.obj))

/--
@isnad1 id=mem.0h3v.s11.94f1c3a14579 from=translated src=- shape=fb06b38f vocab=4a469701
-/
theorem σbar_hom_mem_degree (a : Orbit2 R B) : (σbar a).hom ∈ degree (R := R) _ (𝟙 a) 1 := by
  rw [σbar_hom]
  simpa using! comp_mem_degree (inv_mem_degree _ (σIso_hom_mem_degree (⟨𝐪⁻ a.obj⟩ : a ⟶ a)))
    (ι_map_mem_degree (d := homShift R a.obj a.obj) (jj (R := R) a.obj).hom)

section Pi

variable [PiTwoSupercategory R B]

/-- `Orbit2 R 𝔅` is a Π-2-supercategory with the `π` and `ζ` of `𝔅` (in degree zero).-/
instance instPiTwoSupercategory : PiTwoSupercategory R (Orbit2 R B) where
  pi a := ⟨PiTwoSupercategory.pi (R := R) a.obj⟩
  ζ a := (Orbit.ι _).mapIso (PiTwoSupercategory.ζ (R := R) a.obj)
  ζ_hom_mem a := map_mem (Orbit.ι _) (PiTwoSupercategory.ζ_hom_mem (R := R) a.obj)

/--
@isnad1 id=eq.0h3v.s9.b63b01fff9d3 from=translated src=- shape=8f8d2f1c vocab=71908c9a
-/
theorem ζ_hom_def (a : Orbit2 R B) :
    (PiTwoSupercategory.ζ (R := R) a).hom =
      (Orbit.ι (homShift R a.obj a.obj)).map (PiTwoSupercategory.ζ (R := R) a.obj).hom := rfl

/-- **The orbit 2-supercategory is a graded `(Q, Π)`-2-supercategory** (Brundan–Ellis, after
Definition 6.14): `q_λ`, `q_λ⁻¹` are those of `𝔅`, `σ_λ` is the identity of `q_λ` in degree
`-1`, and `σ̄_λ = jj_λ ∘ σ⁻¹`.-/
instance instQPiTwoSupercategory : QPiTwoSupercategory R (Orbit2 R B) where
  ζ_hom_mem_degree _ := ι_map_mem_degree _
  q a := ⟨𝐪 a.obj⟩
  qinv a := ⟨𝐪⁻ a.obj⟩
  σ := σ
  σbar := σbar
  σ_hom_mem := σ_hom_mem
  σ_hom_mem_degree := σ_hom_mem_degree
  σbar_hom_mem := σbar_hom_mem
  σbar_hom_mem_degree := σbar_hom_mem_degree

/--
@isnad1 id=eq.0h3v.s8.f13010956e33 from=translated src=- shape=547d294d vocab=819c5864
-/
theorem σ_eq (a : Orbit2 R B) : QPiTwoSupercategory.σ (R := R) a = σ a := rfl

/-! ### The underlying structures of `Orbit2 R 𝔅` are those of `𝔅` -/

set_option backward.isDefEq.respectTransparency false in
/-- The `β` of Lemma 3.2 for `Orbit2 R 𝔅` is that of `𝔅`, in degree zero.
@isnad1 id=eq.0h5v.s10.6cf9dc66e0dd from=translated src=- shape=51f625c2 vocab=30c2e26a
-/
theorem β_hom_eq (f : a ⟶ b) :
    (PiTwoSupercategory.β (R := R) f).hom =
      (Orbit.ι (homShift R a.obj b.obj)).map (PiTwoSupercategory.β (R := R) f.obj).hom := by
  rw [PiTwoSupercategory.β_hom, PiTwoSupercategory.β_hom, ζ_hom_def, whiskerLeft_ι,
    rightUnitor_hom_def, leftUnitor_inv_def]
  change _ ≫ _ ≫ _ ≫ (Orbit.ι (homShift R a.obj a.obj)).map (PiTwoSupercategory.ζ (R := R) a.obj).inv ▷ f = _
  rw [whiskerRight_ι, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The `ξ = ζζ` of Lemma 3.2(iv) for `Orbit2 R 𝔅` is that of `𝔅`, in degree zero.
@isnad1 id=eq.0h3v.s10.420ae17e225d from=translated src=- shape=3ce57829 vocab=803ee177
-/
theorem ξ_hom_eq (a : Orbit2 R B) :
    (PiTwoSupercategory.ξ (R := R) a).hom =
      (Orbit.ι (homShift R a.obj a.obj)).map (PiTwoSupercategory.ξ (R := R) a.obj).hom := by
  rw [PiTwoSupercategory.ξ_hom, PiTwoSupercategory.ξ_hom, ζ_hom_def, whiskerRight_ι,
    leftUnitor_hom_def, ← Functor.map_comp, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s12.30442d5e17f9 from=translated src=- shape=84afca06 vocab=8854875f
-/
theorem whiskerLeft_σ_hom (f : a ⟶ b) :
    f ◁ (QPiTwoSupercategory.σ (R := R) b).hom =
      (Orbit.ι (homShift R a.obj b.obj)).map (f.obj ◁ (leftUnitor (𝐪 b.obj)).inv ≫
        (associator f.obj (𝟙 b.obj) (𝐪 b.obj)).inv) ≫
        (σIso (⟨f.obj ≫ 𝟙 b.obj⟩ : a ⟶ b)).hom := by
  rw [σ_eq, σ_hom, whiskerLeft_comp'', whiskerLeft_ι, whiskerLeft_def]
  erw [map_σIso_hom]
  rw [preShift_γ_inv_app, Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.0h5v.s12.c1ad79eb472c from=translated src=- shape=ba5371fb vocab=188756df
-/
theorem σ_inv_whiskerRight (f : a ⟶ b) :
    (QPiTwoSupercategory.σ (R := R) a).inv ▷ f =
      (σIso (⟨𝟙 a.obj ≫ f.obj⟩ : a ⟶ b)).inv ≫ (Orbit.ι (homShift R a.obj b.obj)).map
        ((γR (R := R) (𝟙 a.obj) f.obj).hom ≫ (leftUnitor (𝐪 a.obj)).hom ▷ f.obj) := by
  have e : (QPiTwoSupercategory.σ (R := R) a).inv = (σIso (⟨𝟙 a.obj⟩ : a ⟶ a)).inv ≫
      (Orbit.ι (homShift R a.obj a.obj)).map (leftUnitor (𝐪 a.obj)).hom := by
    simp [σ_eq, σ]
  rw [e, comp_whiskerRight'', whiskerRight_ι, whiskerRight_def]
  erw [map_σIso_inv]
  rw [postShift_γ_hom_app, Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
open Bicategory in
/-- The half-braiding `γ_F = σ_μ F σ_λ⁻¹` of Lemma 6.6(ii) for `Orbit2 R 𝔅` is the `γ_F` of
`𝔅`, in degree zero.
@isnad1 id=eq.0h5v.s10.8a0f0c623b25 from=translated src=- shape=266e8e43 vocab=d5947746
-/
theorem γ_hom_eq (f : a ⟶ b) :
    (QPiTwoSupercategory.γ (R := R) f).hom =
      (Orbit.ι (homShift R a.obj b.obj)).map (CentralShift.γ (R := R) f.obj).hom := by
  have n : (σIso (⟨f.obj ≫ 𝟙 b.obj⟩ : Orbit (homShift R a.obj b.obj))).hom ≫
      (Orbit.ι _).map ((rightUnitor f.obj).hom ≫ (leftUnitor f.obj).inv) =
      _ ≫ (σIso (⟨𝟙 a.obj ≫ f.obj⟩ : Orbit (homShift R a.obj b.obj))).hom :=
    σIso_hom_naturality (d := homShift R a.obj b.obj)
      ((rightUnitor f.obj).hom ≫ (leftUnitor f.obj).inv)
  simp only [homShift_Q, postcomp_map] at n
  rw [QPiTwoSupercategory.γ_hom, whiskerLeft_σ_hom, σ_inv_whiskerRight, rightUnitor_hom_def,
    leftUnitor_inv_def]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc (Orbit.ι (homShift R a.obj b.obj)) (rightUnitor f.obj).hom]
  rw [reassoc_of% n, Iso.hom_inv_id_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 1
  simp only [γR_hom, Category.assoc]
  have key : ∀ f' : (⟨a.obj⟩ : Underlying2 R B) ⟶ ⟨b.obj⟩,
      Bicategory.whiskerLeft f' (λ_ (Underlying2.hom1 (𝐪 b.obj))).inv ≫ (α_ f' (𝟙 _) _).inv ≫
        Bicategory.whiskerRight ((ρ_ f').hom ≫ (λ_ f').inv) (Underlying2.hom1 (𝐪 b.obj)) ≫
          (α_ (𝟙 _) f' _).hom ≫ Bicategory.whiskerLeft (𝟙 _) (γU (R := R) f').hom ≫
            (α_ (𝟙 _) _ f').inv ≫ Bicategory.whiskerRight (λ_ (Underlying2.hom1 (𝐪 a.obj))).hom f' =
      (γU (R := R) f').hom := by
    intro f'
    bicategory
  exact congrArg Subtype.val (key (Underlying2.hom1 f.obj))

end Pi

end Orbit2

end StringDiagrams

end
