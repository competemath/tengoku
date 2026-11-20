import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nontrivial transport around loops (paper `sec:holonomy`, `prop:holonomy`)

Paper labels covered: `sec:holonomy` (the model and its transport laws), `prop:holonomy`
(the holonomy-controlled extension `1 → C_G(im ρ) → E_ρ → H_ρ → 1`), and the two examples
following it (the `S₃` transposition and the nonsplit `Q₈` extension).

For a group hom `ρ : Γ →* G` the model is
`S = SingleObj Γ`, `O = SingleObj Γ × Pair G`, `p = Prod.fst`, with transport
`γ^* (*, g) = (*, ρ(γ)⁻¹ g)` and chosen arrow `χ_{γ,g} = (γ, ⟨⟩)`.
This is deliberately NOT an `OEData` for general `ρ`: clause (N4) (parallel basepoints) is
exactly what fails, and `holReind_holBase_iff` proves it holds iff `ρ = 1`;
`holonomy_not_normalized` / `holonomy_not_OEData` state that for `ρ ≠ 1` no normalized datum
carries this transport and basepoint.  The remaining clauses hold: (N3) is the split,
right-equivariant transport (`holReind_id`, …, `holChi_act`), and (N1), (N2), (N5), (N6) are
bundled in `holonomy_N1_N2_N5_N6` (with `holLtrans_isIso` for invertibility in (N5)).
On the lift side, `holLiftProj` is the projection of the lift group to the base automorphism;
`holLift_exact` transfers `holonomy_exact` to it, with kernel `≃* C_G(im ρ)`
(`holLiftProjKerEquiv`).
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

universe u v

section Model

variable {Γ : Type u} {G : Type v} [Group Γ]

/-- The total category `O = BΓ × Pair(G)` of the holonomy model (paper `sec:holonomy`).-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.HolTotal (Γ : Type u) (G : Type v) [Group Γ] := SingleObj Γ × Pair G

/-- The projection `p = Prod.fst : BΓ × Pair(G) ⥤ BΓ` of the holonomy model
    (paper `sec:holonomy`).-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.holP (Γ : Type u) (G : Type v) [Group Γ] : HolTotal Γ G ⥤ SingleObj Γ :=
  CategoryTheory.Prod.fst (SingleObj Γ) (Pair G)

/-- The usual right `G`-action on objects of the holonomy model, `(*, g) · h = (*, g h)`
    (paper `sec:holonomy`, "the usual coordinates").-/
def _root_.Tengoku.ObserverEquivarianceLean.holAct [Mul G] (x : HolTotal Γ G) (h : G) : HolTotal Γ G := (x.1, ⟨x.2.pt * h⟩)

/-- The basepoint `b = 1` of the holonomy model (paper `sec:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holBase [One G] (s : SingleObj Γ) : HolTotal Γ G := (s, ⟨1⟩)

variable [Group G]

/-- The holonomy action agrees with the product-model action `normalFormProductAction`
    of Core (paper `sec:holonomy`).
@isnad1 id=eq.0h4v.s6.c74d8b88dbab from=translated src=- shape=8d9886f6 vocab=2775f0d8
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holAct_eq_normalFormProductAction (x : HolTotal Γ G) (h : G) :
    holAct x h = (normalFormProductAction (S := SingleObj Γ) h).obj x := rfl

/-- The holonomy transport `γ^* (*, g) = (*, ρ(γ)⁻¹ g)` over an arrow `γ : s ⟶ t` of `BΓ`
    (paper `sec:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holReind (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    HolTotal Γ G :=
  (s, ⟨(ρ γ)⁻¹ * y.2.pt⟩)

/-- The chosen arrow `χ_{γ,y} : γ^* y ⟶ y` over `γ`, namely `(γ, ⟨⟩)` (paper `sec:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holChi (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    holReind ρ γ y ⟶ y :=
  (γ, ⟨⟩)

/-- The transported object lies over the source of `γ` (paper `sec:holonomy`, (N3)).
@isnad1 id=eq.0h7v.s6.ee4571bf4b5c from=translated src=- shape=93098f2b vocab=8a25adb6
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.holP_obj_holReind (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holP Γ G).obj (holReind ρ γ y) = s := rfl

/-- The chosen arrow `χ_{γ,y}` lies over `γ` (paper `sec:holonomy`, (N3)).
@isnad1 id=eq.0h7v.s7.a7d84b3b2928 from=translated src=- shape=c90e64b8 vocab=781d170e
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.holP_map_holChi (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holP Γ G).map (holChi ρ γ y) = γ := rfl

/-- Coordinates of the transport: the `Pair G`-component of `γ^* y` is `ρ(γ)⁻¹ g`
    (paper `sec:holonomy`).
@isnad1 id=eq.0h7v.s7.a958ca30a87a from=translated src=- shape=213283ff vocab=91923154
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_pt (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t)
    (y : HolTotal Γ G) : (holReind ρ γ y).2.pt = (ρ γ)⁻¹ * y.2.pt := rfl

omit [Group G] in
/-- Local helper: two objects of `BΓ × Pair(G)` are equal iff their `Pair G`-points are
    (the `BΓ` component is a single object) (paper `sec:holonomy`).
@isnad1 id=eq.1h4v.s5.1abe404e5b85 from=translated src=- shape=b9e6edf5 vocab=5cab7b03
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holTotal_ext {x y : HolTotal Γ G} (h : x.2.pt = y.2.pt) : x = y := by
  obtain ⟨x1, ⟨a⟩⟩ := x
  obtain ⟨y1, ⟨b⟩⟩ := y
  cases x1; cases y1
  cases h
  rfl

/-- Local helper: an `eqToHom` of `BΓ` is the neutral element `1 : Γ`
    (paper `sec:holonomy`).
@isnad1 id=eq.1h3v.s6.fa20cc9e791e from=translated src=- shape=d4442c69 vocab=ffa0c887
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.singleObj_eqToHom {a b : SingleObj Γ} (h : a = b) : eqToHom h = (1 : Γ) := by
  subst h; rfl

omit [Group G] in
/-- Local helper: the `BΓ`-component of an `eqToHom` of `BΓ × Pair(G)` is `1 : Γ`
    (paper `sec:holonomy`).
@isnad1 id=eq.1h4v.s8.2edd270f7b69 from=translated src=- shape=3457fa16 vocab=3556fa9b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holEqToHom_fst {x y : HolTotal Γ G} (h : x = y) : ((eqToHom h).1 : Γ) = 1 := by
  subst h; rfl

omit [Group G] in
/-- Local helper: arrows of `BΓ × Pair(G)` are determined by their `BΓ`-component
    (paper `sec:holonomy`).
@isnad1 id=eq.1h6v.s8.8f4f4dba8b67 from=translated src=- shape=c4ec01e1 vocab=d541e518
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holHom_ext {x y : HolTotal Γ G} {f g : x ⟶ y} (h : (f.1 : Γ) = g.1) : f = g :=
  Prod.hom_ext h (Subsingleton.elim _ _)

/-! ### Split transport -/

/-- Splitness, identity law: `(𝟙 s)^* y = y` (paper `sec:holonomy`, "the homomorphism law
    makes this transport split").
@isnad1 id=eq.0h5v.s6.b4314fc13352 from=translated src=- shape=eca4607c vocab=0c7999cc
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_id (ρ : Γ →* G) (s : SingleObj Γ) (y : HolTotal Γ G) :
    holReind ρ (𝟙 s) y = y := by
  apply holTotal_ext
  show (ρ (1 : Γ))⁻¹ * y.2.pt = y.2.pt
  rw [map_one, inv_one, one_mul]

/-- Splitness, composition law: `(γ ≫ δ)^* y = γ^* (δ^* y)` (paper `sec:holonomy`).
@isnad1 id=eq.0h9v.s6.9441a1a28298 from=translated src=- shape=dd41c2f7 vocab=618a25f0
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_comp (ρ : Γ →* G) {s t r : SingleObj Γ} (γ : s ⟶ t) (δ : t ⟶ r)
    (y : HolTotal Γ G) : holReind ρ (γ ≫ δ) y = holReind ρ γ (holReind ρ δ y) := by
  apply holTotal_ext
  show (ρ (δ * γ))⁻¹ * y.2.pt = (ρ γ)⁻¹ * ((ρ δ)⁻¹ * y.2.pt)
  rw [map_mul, mul_inv_rev, mul_assoc]

/-- Splitness of the chosen arrows, identity law: `χ_{𝟙,y} = 𝟙` up to the cast
    (paper `sec:holonomy`).
@isnad1 id=eq.0h5v.s7.795af81afb11 from=translated src=- shape=c46cdc81 vocab=709cf6dc
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holChi_id (ρ : Γ →* G) (s : SingleObj Γ) (y : HolTotal Γ G) :
    holChi ρ (𝟙 s) y = eqToHom (holReind_id ρ s y) := by
  apply holHom_ext
  rw [holEqToHom_fst]
  rfl

/-- Splitness of the chosen arrows, composition law:
    `χ_{γ≫δ,y} = cast ≫ χ_{γ, δ^* y} ≫ χ_{δ,y}` (paper `sec:holonomy`).
@isnad1 id=eq.0h9v.s8.3f52d00b1495 from=translated src=- shape=11268012 vocab=78d0097b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holChi_comp (ρ : Γ →* G) {s t r : SingleObj Γ} (γ : s ⟶ t) (δ : t ⟶ r)
    (y : HolTotal Γ G) :
    holChi ρ (γ ≫ δ) y
      = eqToHom (holReind_comp ρ γ δ y) ≫ holChi ρ γ (holReind ρ δ y) ≫ holChi ρ δ y := by
  apply holHom_ext
  show ((γ ≫ δ : s ⟶ r) : Γ) = (eqToHom (holReind_comp ρ γ δ y)).1 ≫ (γ ≫ δ)
  rw [holEqToHom_fst]
  show δ * γ = (δ * γ) * 1
  rw [mul_one]

/-! ### Right equivariance of the transport -/

/-- The transport commutes with right multiplication: `γ^* (y · h) = (γ^* y) · h`
    (paper `sec:holonomy`).
@isnad1 id=eq.0h8v.s6.32a6474f4a19 from=translated src=- shape=8855dd3c vocab=aa78d475
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_act (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G)
    (h : G) : holReind ρ γ (holAct y h) = holAct (holReind ρ γ y) h := by
  apply holTotal_ext
  show (ρ γ)⁻¹ * (y.2.pt * h) = (ρ γ)⁻¹ * y.2.pt * h
  rw [mul_assoc]

/-- The chosen arrows are right equivariant: `χ_{γ, y·h} = cast ≫ R_h(χ_{γ,y})`, with `R_h` the
    product action functor (paper `sec:holonomy`).
@isnad1 id=eq.0h8v.s8.2adaf03353ce from=translated src=- shape=7feed396 vocab=7c4ec9c1
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holChi_act (ρ : Γ →* G) {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (h : G) :
    holChi ρ γ (holAct y h)
      = eqToHom (holReind_act ρ γ y h)
          ≫ (normalFormProductAction (S := SingleObj Γ) h).map (holChi ρ γ y) := by
  apply holHom_ext
  show (γ : Γ) = (eqToHom (holReind_act ρ γ y h)).1 ≫ γ
  rw [holEqToHom_fst]
  show γ = γ * 1
  rw [mul_one]

/-! ### Parallelity of the basepoint -/

/-- (N4) for the holonomy model holds exactly for trivial `ρ`: the basepoint `1` is parallel,
    `γ^* b_t = b_s` for all arrows, iff `ρ = 1` (paper `sec:holonomy`).
@isnad1 id=iff.0h3v.s7.3a3807bf9028 from=translated src=- shape=7f9a7541 vocab=b71f8214
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_holBase_iff (ρ : Γ →* G) :
    (∀ {s t : SingleObj Γ} (γ : s ⟶ t), holReind ρ γ (holBase t) = holBase s) ↔ ρ = 1 := by
  constructor
  · intro h
    ext γ
    have h1 := congrArg (fun x : HolTotal Γ G => x.2.pt)
      (h (s := SingleObj.star Γ) (t := SingleObj.star Γ) γ)
    simp only [holReind_pt, holBase, mul_one, inv_eq_one] at h1
    simpa using h1
  · rintro rfl s t γ
    apply holTotal_ext
    show ((1 : Γ →* G) γ)⁻¹ * 1 = 1
    simp

/-! ### The remaining clauses (N1), (N2), (N5), (N6) -/

/-- Coordinates of the holonomy model, `g_{(*, g)} = g` (paper `sec:holonomy`, "the usual
    coordinates"; `def:data` (N2)).-/
def _root_.Tengoku.ObserverEquivarianceLean.holCoord (x : HolTotal Γ G) : G := x.2.pt

/-- (N1), object unit law: `x · 1 = x` (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h3v.s5.fbccb9283a85 from=translated src=- shape=35eb2c89 vocab=a87fc966
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holAct_one (x : HolTotal Γ G) : holAct x 1 = x := holTotal_ext (mul_one _)

/-- (N1), object composition law: `(x · g) · h = x · (g h)`
    (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h5v.s6.b01a1e669686 from=translated src=- shape=50fcb65a vocab=54443fe6
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holAct_mul (x : HolTotal Γ G) (g h : G) : holAct (holAct x g) h = holAct x (g * h) :=
  holTotal_ext (mul_assoc _ _ _)

/-- (N1), the action is over `S` on objects: `p (x · g) = p x`
    (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h4v.s6.e887c7d33668 from=translated src=- shape=7a883762 vocab=63237639
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holP_holAct (x : HolTotal Γ G) (g : G) :
    (holP Γ G).obj (holAct x g) = (holP Γ G).obj x := rfl

/-- (N1), morphism unit law: `R_1` is the identity functor
    (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h2v.s6.db9ee83e6e5d from=translated src=- shape=1e2b4e74 vocab=4bd9465b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holAct_functor_one :
    normalFormProductAction (S := SingleObj Γ) (1 : G) = 𝟭 (HolTotal Γ G) :=
  CategoryTheory.Functor.ext (fun _ => holTotal_ext (mul_one _)) (fun _ _ _ => holHom_ext (by
    simp only [Functor.id_map, prod_comp_fst]; rw [holEqToHom_fst, holEqToHom_fst]
    simp only [SingleObj.comp_as_mul, mul_one, one_mul]; rfl))

/-- (N1), morphism composition law: `R_h R_g = R_{gh}`, i.e. `R_g ⋙ R_h = R_{g h}`
    (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h4v.s7.35cf09f2bcb0 from=translated src=- shape=7e3f53d4 vocab=2125c56c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holAct_functor_mul (g h : G) :
    normalFormProductAction (S := SingleObj Γ) g ⋙ normalFormProductAction h
      = normalFormProductAction (g * h) :=
  CategoryTheory.Functor.ext (fun _ => holTotal_ext (mul_assoc _ _ _)) (fun _ _ _ => holHom_ext (by
    simp only [Functor.comp_map, prod_comp_fst]; rw [holEqToHom_fst, holEqToHom_fst]
    simp only [SingleObj.comp_as_mul, mul_one, one_mul]; rfl))

/-- (N1), the action is over `S` on morphisms: `p R_g = p`
    (paper `sec:holonomy`, `def:data` (N1)).
@isnad1 id=eq.0h3v.s6.54a64e22cc5f from=translated src=- shape=0db5e6b9 vocab=6f5bb0e3
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holP_act_functor (g : G) :
    normalFormProductAction (S := SingleObj Γ) g ⋙ holP Γ G = holP Γ G := rfl

/-- (N2): `x = b_{p x} · g_x` (paper `sec:holonomy`, `def:data` (N2)).
@isnad1 id=eq.0h3v.s6.67141c00b288 from=translated src=- shape=198b7a22 vocab=babb8f8d
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holBase_coord (x : HolTotal Γ G) :
    holAct (holBase ((holP Γ G).obj x)) (holCoord x) = x := holTotal_ext (one_mul _)

/-- (N2): `g_{b_s · g} = g` (paper `sec:holonomy`, `def:data` (N2)).
@isnad1 id=eq.0h4v.s5.d4c7ffe9652c from=translated src=- shape=f621ea30 vocab=ff929f03
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holCoord_holAct_holBase (s : SingleObj Γ) (g : G) :
    holCoord (holAct (holBase s) g) = g := one_mul g

/-- (N5): the chosen vertical isomorphism `ℓ_{a,x} : x ≅ b_{p x} · (a g_x)`, with base
    component the identity (paper `sec:holonomy`, "the usual vertical translations";
    `def:data` (N5)).-/
def _root_.Tengoku.ObserverEquivarianceLean.holLtrans (a : G) (x : HolTotal Γ G) :
    x ≅ holAct (holBase ((holP Γ G).obj x)) (a * holCoord x) where
  hom := (𝟙 x.1, ⟨⟩)
  inv := (𝟙 x.1, ⟨⟩)
  hom_inv_id := holHom_ext (Category.id_comp _)
  inv_hom_id := holHom_ext (Category.id_comp _)

/-- (N5): `ℓ_{a,x}` is vertical, `p(ℓ_{a,x}) = 𝟙_{p x}` (paper `sec:holonomy`, `def:data` (N5)).
@isnad1 id=eq.0h4v.s8.61f5a16bbe16 from=translated src=- shape=a9abfa76 vocab=b0e2f925
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holP_map_holLtrans (a : G) (x : HolTotal Γ G) :
    (holP Γ G).map (holLtrans a x).hom = 𝟙 _ := rfl

/-- (N5): the arrow `ℓ_{a,x}` is an isomorphism (paper `sec:holonomy`, `def:data` (N5)).
@isnad1 id=isiso.0h4v.s7.ff220bfefecd from=translated src=- shape=1dee8986 vocab=3e6d5c09
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holLtrans_isIso (a : G) (x : HolTotal Γ G) : IsIso (holLtrans a x).hom :=
  inferInstance

omit [Group G] in
/-- (N6): the projection `p = Prod.fst` of the holonomy model is faithful
    (paper `sec:holonomy`, `def:data` (N6)).
@isnad1 id=faithful.0h2v.s5.9c9ddbc64958 from=translated src=- shape=0e44b31c vocab=05511bf1
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holP_faithful : (holP Γ G).Faithful := ⟨fun {_ _} _ _ h => holHom_ext h⟩

/-- The holonomy data satisfy (N1), (N2), (N5) and (N6) (paper `sec:holonomy`: "These data
    satisfy (N1)--(N3) and (N5)--(N6)"; (N3) is `holReind_id`, `holReind_comp`, `holChi_id`,
    `holChi_comp`, `holReind_act`, `holChi_act`, `holP_obj_holReind`, `holP_map_holChi`).
    The isomorphism part of (N5) is `holLtrans_isIso`.
@isnad1 id=and.0h2v.s10.c52f406e8e7b from=translated src=- shape=fa88b624 vocab=648d2aea
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holonomy_N1_N2_N5_N6 :
    ((∀ x : HolTotal Γ G, holAct x 1 = x) ∧
      (∀ (x : HolTotal Γ G) (g h : G), holAct (holAct x g) h = holAct x (g * h)) ∧
      (∀ (x : HolTotal Γ G) (g : G), (holP Γ G).obj (holAct x g) = (holP Γ G).obj x) ∧
      normalFormProductAction (S := SingleObj Γ) (1 : G) = 𝟭 (HolTotal Γ G) ∧
      (∀ g h : G, normalFormProductAction (S := SingleObj Γ) g ⋙ normalFormProductAction h
        = normalFormProductAction (g * h)) ∧
      (∀ g : G, normalFormProductAction (S := SingleObj Γ) g ⋙ holP Γ G = holP Γ G)) ∧
    ((∀ s : SingleObj Γ, (holP Γ G).obj (holBase (G := G) s) = s) ∧
      (∀ x : HolTotal Γ G, holAct (holBase ((holP Γ G).obj x)) (holCoord x) = x) ∧
      (∀ (s : SingleObj Γ) (g : G), holCoord (holAct (holBase s) g) = g)) ∧
    (∀ (a : G) (x : HolTotal Γ G), (holP Γ G).map (holLtrans a x).hom = 𝟙 _) ∧
    (holP Γ G).Faithful :=
  -- `holP_holAct` / `holBase_coord` are inlined: `Pair`'s hom universe is otherwise left free.
  ⟨⟨holAct_one, holAct_mul, fun _ _ => rfl, holAct_functor_one, holAct_functor_mul,
      holP_act_functor⟩,
    ⟨fun _ => rfl, fun _ => holTotal_ext (one_mul _), holCoord_holAct_holBase⟩,
    holP_map_holLtrans, holP_faithful⟩

/-- For nontrivial `ρ` the holonomy data are NOT normalized: no `NormalizedPreDatum` on
    `p = Prod.fst : BΓ × Pair(G) ⥤ BΓ` has the holonomy transport `γ^* (*, g) = (*, ρ(γ)⁻¹ g)`
    and the basepoint `b = 1`, since (N4) would force `ρ = 1` (paper `sec:holonomy`,
    "(N4) holds only when ρ is trivial").
@isnad1 id=not.1h3v.s8.198e2c626c84 from=translated src=- shape=5ac62c5f vocab=35ba8396
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holonomy_not_normalized (ρ : Γ →* G) (hρ : ρ ≠ 1) :
    ¬ ∃ d : NormalizedPreDatum G (holP Γ G),
      (∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (hy : (holP Γ G).obj y = t),
        d.reind γ y hy = holReind ρ γ y) ∧ ∀ s, d.base s = holBase s := by
  rintro ⟨d, hr, hb⟩
  apply hρ
  rw [← holReind_holBase_iff]
  intro s t γ
  have h := d.reind_base γ
  rw [hr, hb, hb] at h
  exact h

/-- For nontrivial `ρ` there is no `OEData G (holP Γ G)` whose transport is the holonomy
    transport and whose basepoint is `b = 1` (paper `sec:holonomy`, "(N4) holds only when ρ is
    trivial"); the same argument as `holonomy_not_normalized`, via the inherited `reind_base`.
@isnad1 id=not.1h3v.s8.936e067f57c2 from=translated src=- shape=b760e043 vocab=83e797f6
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holonomy_not_OEData (ρ : Γ →* G) (hρ : ρ ≠ 1) :
    ¬ ∃ d : OEData G (holP Γ G),
      (∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) (hy : (holP Γ G).obj y = t),
        d.reind γ y hy = holReind ρ γ y) ∧ ∀ s, d.base s = holBase s := by
  rintro ⟨d, hr, hb⟩
  apply hρ
  rw [← holReind_holBase_iff]
  intro s t γ
  have h := d.reind_base γ
  rw [hr, hb, hb] at h
  exact h

end Model

/-! ## The lift group and `E_ρ` (paper `prop:holonomy`) -/

section Lifts

variable {Γ : Type u} {G : Type v} [Group Γ] [Group G]

omit [Group G] in
/-- Local helper: a functor into `BΓ × Pair(G)` is determined by its objects and the
    `BΓ`-components of its arrows (paper `prop:holonomy`, "a lift is determined by ...").
@isnad1 id=eq.2h5v.s9.73d69d80f47a from=translated src=- shape=4b2968e0 vocab=eb5e5133
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holFunctor_ext {C : Type*} [Category C] {F F' : C ⥤ HolTotal Γ G}
    (hobj : ∀ x, F.obj x = F'.obj x)
    (hmap : ∀ {x y : C} (f : x ⟶ y), ((F.map f).1 : Γ) = (F'.map f).1) : F = F' := by
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  apply holHom_ext
  show ((F.map f).1 : Γ)
    = ((eqToHom (hobj y).symm).1 * (F'.map f).1) * (eqToHom (hobj x)).1
  rw [holEqToHom_fst, holEqToHom_fst, mul_one, one_mul, hmap]

/-- The conditions of paper `def:lifts` for the holonomy model (paper `prop:holonomy`):
    `F` covers the base functor `A` strictly, is (object-level) `G`-equivariant, and preserves
    the holonomy transport on objects, `F(γ^* y) = (A γ)^* F(y)`.-/
structure _root_.Tengoku.ObserverEquivarianceLean.IsHolLift (ρ : Γ →* G) (F : HolTotal Γ G ⥤ HolTotal Γ G)
    (A : SingleObj Γ ⥤ SingleObj Γ) : Prop where
  covers : F ⋙ holP Γ G = holP Γ G ⋙ A
  equiv : ∀ (x : HolTotal Γ G) (h : G), F.obj (holAct x h) = holAct (F.obj x) h
  pres : ∀ {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G),
    F.obj (holReind ρ γ y) = holReind ρ (A.map γ) (F.obj y)

/-- A lift has object map `g ↦ k g` with `k` the coordinate of the image of the basepoint
    (paper `prop:holonomy`, proof: "a lift ... is determined by `g ↦ kg` on objects").
@isnad1 id=eq.1h6v.s7.95fcd7eacc15 from=translated src=- shape=31b407ca vocab=ab34765e
-/
theorem Tengoku.ObserverEquivarianceLean.IsHolLift.obj_pt {ρ : Γ →* G} {F : HolTotal Γ G ⥤ HolTotal Γ G}
    {A : SingleObj Γ ⥤ SingleObj Γ} (hF : IsHolLift ρ F A) (x : HolTotal Γ G) :
    (F.obj x).2.pt = (F.obj (holBase (SingleObj.star Γ))).2.pt * x.2.pt := by
  have hx : x = holAct (holBase (SingleObj.star Γ)) x.2.pt :=
    holTotal_ext (by show x.2.pt = 1 * x.2.pt; rw [one_mul])
  calc (F.obj x).2.pt = (F.obj (holAct (holBase (SingleObj.star Γ)) x.2.pt)).2.pt :=
        congrArg (fun z => (F.obj z).2.pt) hx
    _ = _ := by rw [hF.equiv]; rfl

/-- The subgroup `E_ρ = {(k, α) ∈ G × Aut(Γ) | ∀ γ, ρ(α γ) = k ρ(γ) k⁻¹}` of the direct product
    `G × MulAut Γ` (multiplication `(k,α)(l,β) = (kl, αβ)`) (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.Eρ (ρ : Γ →* G) : Subgroup (G × MulAut Γ) where
  carrier := {e | ∀ γ : Γ, ρ (e.2 γ) = e.1 * ρ γ * e.1⁻¹}
  one_mem' := fun γ => by
    show ρ ((1 : MulAut Γ) γ) = 1 * ρ γ * 1⁻¹
    rw [MulAut.one_apply, one_mul, inv_one, mul_one]
  mul_mem' := fun {a b} ha hb γ => by
    show ρ ((a.2 * b.2) γ) = (a.1 * b.1) * ρ γ * (a.1 * b.1)⁻¹
    rw [MulAut.mul_apply, ha, hb]
    group
  inv_mem' := fun {a} ha γ => by
    show ρ (a.2⁻¹ γ) = a.1⁻¹ * ρ γ * a.1⁻¹⁻¹
    have h := ha (a.2⁻¹ γ)
    rw [MulAut.apply_inv_self] at h
    rw [h]
    group

/-- Membership in `E_ρ` unfolded (paper `prop:holonomy`).
@isnad1 id=iff.0h4v.s8.f8fe83a706b3 from=translated src=- shape=1ca95125 vocab=e6b1c2fa
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_Eρ (ρ : Γ →* G) (e : G × MulAut Γ) :
    e ∈ Eρ ρ ↔ ∀ γ : Γ, ρ (e.2 γ) = e.1 * ρ γ * e.1⁻¹ := Iff.rfl

/-- The subgroup `H_ρ = {α ∈ Aut(Γ) | ρ ∘ α is conjugate to ρ in G}` (paper `prop:holonomy`);
    see `mem_Hρ_iff_conj` for the literal "conjugate homomorphisms" form.-/
def _root_.Tengoku.ObserverEquivarianceLean.Hρ (ρ : Γ →* G) : Subgroup (MulAut Γ) where
  carrier := {α | ∃ k : G, ∀ γ : Γ, ρ (α γ) = k * ρ γ * k⁻¹}
  one_mem' := ⟨1, (Eρ ρ).one_mem⟩
  mul_mem' := fun {α β} ⟨k, hk⟩ ⟨l, hl⟩ =>
    ⟨k * l, (Eρ ρ).mul_mem (show (k, α) ∈ Eρ ρ from hk) (show (l, β) ∈ Eρ ρ from hl)⟩
  inv_mem' := fun {α} ⟨k, hk⟩ => ⟨k⁻¹, (Eρ ρ).inv_mem (show (k, α) ∈ Eρ ρ from hk)⟩

/-- `α ∈ H_ρ` iff `ρ ∘ α = Ad_k ∘ ρ` for some `k : G` (paper `prop:holonomy`).
@isnad1 id=iff.0h4v.s8.bdcd47def248 from=translated src=- shape=eff06a52 vocab=82926b79
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_Hρ_iff_conj (ρ : Γ →* G) (α : MulAut Γ) :
    α ∈ Hρ ρ ↔ ∃ k : G, ρ.comp α.toMonoidHom = (MulAut.conj k).toMonoidHom.comp ρ := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, MonoidHom.ext fun γ => by simpa [MulAut.conj_apply] using hk γ⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, fun γ => by simpa [MulAut.conj_apply] using DFunLike.congr_fun hk γ⟩

/-! ### Identification of the lift group with `E_ρ` -/

/-- The lift functor `(*, g) ↦ (*, k g)`, `(γ, ⟨⟩) ↦ (α γ, ⟨⟩)` (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holLiftFunctor (k : G) (α : MulAut Γ) : HolTotal Γ G ⥤ HolTotal Γ G where
  obj x := (x.1, ⟨k * x.2.pt⟩)
  map f := ((α f.1 : Γ), ⟨⟩)
  map_id _ := holHom_ext (map_one α)
  map_comp f g := holHom_ext (map_mul α g.1 f.1)

/-- The strict automorphism of `O` with object map `g ↦ k g` and base action `α`
    (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holLiftAut (k : G) (α : MulAut Γ) : StrictAut (HolTotal Γ G) where
  hom := holLiftFunctor k α
  inv := holLiftFunctor k⁻¹ α⁻¹
  hom_inv_id := holFunctor_ext (fun x => holTotal_ext (inv_mul_cancel_left k x.2.pt))
    (fun f => MulAut.inv_apply_self Γ α f.1)
  inv_hom_id := holFunctor_ext (fun x => holTotal_ext (mul_inv_cancel_left k x.2.pt))
    (fun f => MulAut.apply_inv_self Γ α f.1)

/-- The strict automorphism of `BΓ` induced by `α ∈ Aut(Γ)` (paper `prop:holonomy`, "a strict
    base automorphism is an `α ∈ Aut(Γ)`").-/
def _root_.Tengoku.ObserverEquivarianceLean.holBaseAut (α : MulAut Γ) : StrictAut (SingleObj Γ) where
  hom := SingleObj.mapHom Γ Γ α.toMonoidHom
  inv := SingleObj.mapHom Γ Γ (α⁻¹ : MulAut Γ).toMonoidHom
  hom_inv_id := by
    rw [← SingleObj.mapHom_comp]
    have : (α⁻¹ : MulAut Γ).toMonoidHom.comp α.toMonoidHom = MonoidHom.id Γ :=
      MonoidHom.ext fun g => MulAut.inv_apply_self Γ α g
    rw [this, SingleObj.mapHom_id]
  inv_hom_id := by
    rw [← SingleObj.mapHom_comp]
    have : α.toMonoidHom.comp (α⁻¹ : MulAut Γ).toMonoidHom = MonoidHom.id Γ :=
      MonoidHom.ext fun g => MulAut.apply_inv_self Γ α g
    rw [this, SingleObj.mapHom_id]

/-- `θSingleObjEquiv` recovers `α` from `holBaseAut α` (paper `prop:holonomy`).
@isnad1 id=eq.0h2v.s9.915692959210 from=translated src=- shape=360c8b92 vocab=4d58758e
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.θSingleObjEquiv_holBaseAut (α : MulAut Γ) :
    θSingleObjEquiv Γ (holBaseAut α) = α := by
  ext g; rfl

/-! ### The exact sequence `1 → C_G(im ρ) → E_ρ → H_ρ → 1` -/

/-- The projection `E_ρ →* Aut(Γ)`, `(k, α) ↦ α` (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.EρProj (ρ : Γ →* G) : Eρ ρ →* MulAut Γ :=
  (MonoidHom.snd G (MulAut Γ)).comp (Eρ ρ).subtype

/-- `EρProj` unfolded (paper `prop:holonomy`).
@isnad1 id=eq.0h4v.s11.31c6c97cd1be from=translated src=- shape=b0e99922 vocab=a0152058
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.EρProj_apply (ρ : Γ →* G) (e : Eρ ρ) : EρProj ρ e = e.1.2 := rfl

/-- The image of the projection `E_ρ → Aut(Γ)` is `H_ρ` (paper `prop:holonomy`).
@isnad1 id=eq.0h3v.s8.74e2f6292a31 from=translated src=- shape=527b722e vocab=0fbbfe9a
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.EρProj_range (ρ : Γ →* G) : (EρProj ρ).range = Hρ ρ := by
  ext α
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e.1.1, e.2⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨(k, α), hk⟩, rfl⟩

/-- The projection corestricted to `H_ρ` (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.EρToHρ (ρ : Γ →* G) : Eρ ρ →* Hρ ρ :=
  (EρProj ρ).codRestrict (Hρ ρ) (fun e => ⟨e.1.1, e.2⟩)

/-- `EρToHρ` unfolded (paper `prop:holonomy`).
@isnad1 id=eq.0h4v.s12.a1c78ea5f661 from=translated src=- shape=474fe09a vocab=605e15a6
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.EρToHρ_apply_coe (ρ : Γ →* G) (e : Eρ ρ) : (EρToHρ ρ e : MulAut Γ) = e.1.2 :=
  rfl

/-- The corestricted projection `E_ρ → H_ρ` is surjective (paper `prop:holonomy`).
@isnad1 id=surjecti.0h3v.s12.f44ed8d7af6a from=translated src=- shape=d365cef9 vocab=adc9015d
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.EρToHρ_surjective (ρ : Γ →* G) : Function.Surjective (EρToHρ ρ) := by
  rintro ⟨α, k, hk⟩
  exact ⟨⟨(k, α), hk⟩, rfl⟩

/-- The kernels of the projection and of its corestriction agree (paper `prop:holonomy`).
@isnad1 id=eq.0h3v.s10.5b4cc2fad76f from=translated src=- shape=0582658b vocab=c18ff4b1
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.EρToHρ_ker (ρ : Γ →* G) : (EρToHρ ρ).ker = (EρProj ρ).ker :=
  MonoidHom.ker_codRestrict _ _ _

/-- The inclusion `C_G(im ρ) →* E_ρ`, `k ↦ (k, id)` (paper `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.centralizerToEρ (ρ : Γ →* G) : Subgroup.centralizer (ρ.range : Set G) →* Eρ ρ where
  toFun k := ⟨(k.1, 1), fun γ => by
    show ρ γ = k.1 * ρ γ * k.1⁻¹
    rw [← Subgroup.mem_centralizer_iff.mp k.2 (ρ γ) (MonoidHom.mem_range.mpr ⟨γ, rfl⟩),
      mul_inv_cancel_right]⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `centralizerToEρ` is injective (paper `prop:holonomy`, exactness at `C_G(im ρ)`).
@isnad1 id=injectiv.0h3v.s11.f328b4ac6790 from=translated src=- shape=60357e9e vocab=a51252a9
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.centralizerToEρ_injective (ρ : Γ →* G) : Function.Injective (centralizerToEρ ρ) :=
  fun _ _ h => Subtype.ext (congrArg (fun e : Eρ ρ => e.1.1) h)

/-- The kernel of the projection `E_ρ → Aut(Γ)` is the image of `C_G(im ρ)`
    (paper `prop:holonomy`, exactness at `E_ρ`).
@isnad1 id=eq.0h3v.s9.cc6d30fb7d01 from=translated src=- shape=e7ec8b9b vocab=234910c9
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.centralizerToEρ_range (ρ : Γ →* G) : (centralizerToEρ ρ).range = (EρProj ρ).ker := by
  ext e
  rw [MonoidHom.mem_range, MonoidHom.mem_ker, EρProj_apply]
  constructor
  · rintro ⟨k, rfl⟩
    rfl
  · intro he
    refine ⟨⟨e.1.1, Subgroup.mem_centralizer_iff.mpr ?_⟩, ?_⟩
    · intro h hh
      obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
      have hγ := e.2 γ
      rw [he, MulAut.one_apply] at hγ
      calc ρ γ * e.1.1 = e.1.1 * ρ γ * e.1.1⁻¹ * e.1.1 := by rw [← hγ]
        _ = e.1.1 * ρ γ := by group
    · apply Subtype.ext
      exact Prod.ext rfl he.symm

/-- The kernel of the projection `E_ρ → Aut(Γ)` is the holonomy centralizer `C_G(im ρ)`
    (paper `prop:holonomy`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.EρProjKerEquiv (ρ : Γ →* G) :
    (EρProj ρ).ker ≃* Subgroup.centralizer (ρ.range : Set G) :=
  (MulEquiv.subgroupCongr (centralizerToEρ_range ρ)).symm.trans
    (MonoidHom.ofInjective (centralizerToEρ_injective ρ)).symm

/-- The holonomy-controlled extension `1 → C_G(im ρ) → E_ρ → H_ρ → 1` is exact
    (paper `prop:holonomy`).
@isnad1 id=and.0h3v.s13.9ad78cb806f9 from=translated src=- shape=1d4911d3 vocab=8e0504be
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holonomy_exact (ρ : Γ →* G) :
    Function.Injective (centralizerToEρ ρ) ∧ (centralizerToEρ ρ).range = (EρToHρ ρ).ker ∧
      Function.Surjective (EρToHρ ρ) :=
  ⟨centralizerToEρ_injective ρ, (centralizerToEρ_range ρ).trans (EρToHρ_ker ρ).symm,
    EρToHρ_surjective ρ⟩

/-! ### Transfer to the lift group `HolLift ρ` -/

/-! ### Special case: trivial `ρ` -/

/-- For trivial `ρ` the transport is the product-model one, `γ^* (*, g) = (*, g)`
    (paper `sec:holonomy`, "trivial `ρ` recovers the untwisted product classification").
@isnad1 id=eq.0h6v.s6.95c632d4367f from=translated src=- shape=58c9fca4 vocab=df2ff13e
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holReind_one {s t : SingleObj Γ} (γ : s ⟶ t) (y : HolTotal Γ G) :
    holReind (1 : Γ →* G) γ y = (s, y.2) := by
  apply holTotal_ext
  show ((1 : Γ →* G) γ)⁻¹ * y.2.pt = y.2.pt
  simp

/-- For trivial `ρ`, `E_ρ` is all of `G × Aut(Γ)` (paper `sec:holonomy`).
@isnad1 id=eq.0h2v.s7.a33e0e9b2d43 from=translated src=- shape=18904909 vocab=a24d6a49
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Eρ_one : Eρ (1 : Γ →* G) = ⊤ :=
  eq_top_iff.mpr fun e _ γ => by simp

/-- For trivial `ρ`, `H_ρ` is all of `Aut(Γ)` (paper `sec:holonomy`).
@isnad1 id=eq.0h2v.s7.5dfabc31336c from=translated src=- shape=872b1257 vocab=fb2030cc
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Hρ_one : Hρ (1 : Γ →* G) = ⊤ :=
  eq_top_iff.mpr fun _ _ => ⟨1, fun γ => by simp⟩

/-- For trivial `ρ`, the holonomy centralizer is all of `G` (paper `sec:holonomy`).
@isnad1 id=eq.0h2v.s6.208b6b9a936e from=translated src=- shape=26c214e5 vocab=99f9f33f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.centralizer_range_one : Subgroup.centralizer ((1 : Γ →* G).range : Set G) = ⊤ :=
  eq_top_iff.mpr fun g _ => Subgroup.mem_centralizer_iff.mpr fun h hh => by
    obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.mp hh
    simp

end Lifts

/-! ## Special case: a transposition in `S₃` (paper `sec:holonomy`, first example) -/

section S3

/-- `ρ : C₂ →* S₃` sending the generator to the transposition `(0 1)`
    (paper `sec:holonomy`, example after `prop:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holS3ρ : Multiplicative (ZMod 2) →* Equiv.Perm (Fin 3) where
  toFun a := if a = 1 then 1 else Equiv.swap 0 1
  map_one' := by decide
  map_mul' := by decide

/-- `holS3ρ` sends the generator to `(0 1)` (paper `sec:holonomy`).
@isnad1 id=eq.0h0v.s8.b6a21a065f31 from=translated src=- shape=e52512b1 vocab=f7d199ce
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holS3ρ_ofAdd_one : holS3ρ (Multiplicative.ofAdd 1) = Equiv.swap 0 1 := by decide

/-- `holS3ρ` is injective (paper `sec:holonomy`).
@isnad1 id=injectiv.0h0v.s8.218fb34cd868 from=translated src=- shape=977261aa vocab=665026a8
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holS3ρ_injective : Function.Injective holS3ρ := by
  intro a b
  revert a b
  decide

/-- The centralizer of the image of the transposition is the image itself
    (paper `sec:holonomy`).
@isnad1 id=eq.0h0v.s7.0c4e34cfb986 from=translated src=- shape=4402d9e4 vocab=9808393b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holS3_centralizer_eq :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) = holS3ρ.range := by
  ext g
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have h := hg (Equiv.swap 0 1) (MonoidHom.mem_range.mpr ⟨_, holS3ρ_ofAdd_one⟩)
    clear hg
    revert g
    decide
  · rintro ⟨a, rfl⟩ h hh
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hh
    rw [← map_mul, ← map_mul, mul_comm]

/-- `C_{S₃}(im ρ) ≃* C₂` for `ρ` the transposition (paper `sec:holonomy`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.holS3CentralizerEquiv :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr holS3_centralizer_eq).trans (MonoidHom.ofInjective holS3ρ_injective).symm

/-- `C_{S₃}(im ρ)` is a proper subgroup of `S₃` (paper `sec:holonomy`).
@isnad1 id=ne.0h0v.s7.33ecb2ee3ca9 from=translated src=- shape=57e69ea5 vocab=14513559
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holS3_centralizer_ne_top :
    Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) ≠ ⊤ := by
  intro htop
  have h : Equiv.swap (1 : Fin 3) 2 ∈
      Subgroup.centralizer (holS3ρ.range : Set (Equiv.Perm (Fin 3))) := htop ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_centralizer_iff.mp h (Equiv.swap 0 1)
    (MonoidHom.mem_range.mpr ⟨_, holS3ρ_ofAdd_one⟩)
  revert h2
  decide

/-- The kernel of `E_ρ → Aut(C₂)` for the `S₃` transposition is `C₂` (paper `sec:holonomy`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.holS3KerEquiv : (EρProj holS3ρ).ker ≃* Multiplicative (ZMod 2) :=
  (EρProjKerEquiv holS3ρ).trans holS3CentralizerEquiv

end S3

/-! ## Special case: `ρ = id` and the nonsplit `Q₈` extension (paper `sec:holonomy`) -/

section IdCase

variable (G : Type v) [Group G]

/-- For `ρ = id`, `E_ρ = {(q, Ad_q)}` (paper `sec:holonomy`, `Q₈` example).
@isnad1 id=iff.0h2v.s8.ddb1b7dc5bf0 from=translated src=- shape=0698a74c vocab=9c418b6e
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.mem_Eρ_id_iff (e : G × MulAut G) : e ∈ Eρ (MonoidHom.id G) ↔ e.2 = MulAut.conj e.1 := by
  constructor
  · intro h
    ext γ
    exact h γ
  · intro h γ
    rw [h]
    rfl

/-- For `ρ = id`, `E_ρ ≃* G` via `(q, Ad_q) ↦ q` (paper `sec:holonomy`, `Q₈` example).-/
def _root_.Tengoku.ObserverEquivarianceLean.EρIdEquiv : Eρ (MonoidHom.id G) ≃* G where
  toFun e := e.1.1
  invFun k := ⟨(k, MulAut.conj k), (mem_Eρ_id_iff G _).mpr rfl⟩
  left_inv e := by
    apply Subtype.ext
    exact Prod.ext rfl ((mem_Eρ_id_iff G _).mp e.2).symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- For `ρ = id`, `H_ρ = Inn(G)`, the range of `MulAut.conj` (paper `sec:holonomy`).
@isnad1 id=eq.0h1v.s6.6eef733aab71 from=translated src=- shape=afb4971f vocab=8bba6f82
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Hρ_id : Hρ (MonoidHom.id G) = (MulAut.conj : G →* MulAut G).range := by
  ext α
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, MulEquiv.ext fun γ => (hk γ).symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, fun γ => rfl⟩

end IdCase

section Q8

/-- The quotient map `Q₈ →* C₂ × C₂`, `a i ↦ (i mod 2, 0)`, `xa i ↦ (i mod 2, 1)`, with
    kernel the center `{±1}` (paper `sec:holonomy`, `Q₈` example).-/
def _root_.Tengoku.ObserverEquivarianceLean.holQ8Quot : QuaternionGroup 2 →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) where
  toFun
    | .a i => (Multiplicative.ofAdd (i.val : ZMod 2), 1)
    | .xa i => (Multiplicative.ofAdd (i.val : ZMod 2), Multiplicative.ofAdd 1)
  map_one' := by decide
  map_mul' := by decide

/-- `holQ8Quot` is surjective (paper `sec:holonomy`).
@isnad1 id=surjecti.0h0v.s8.dd333db2f0aa from=translated src=- shape=7030b88c vocab=ebb1125b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8Quot_surjective : Function.Surjective holQ8Quot := by
  intro b
  revert b
  decide

/-- The kernel of `Ad : Q₈ →* Aut(Q₈)` equals the kernel of `holQ8Quot` (paper `sec:holonomy`).
@isnad1 id=eq.0h0v.s8.80c4a6b084a4 from=translated src=- shape=43e08c24 vocab=405241de
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8_ker_conj :
    (MulAut.conj : QuaternionGroup 2 →* MulAut (QuaternionGroup 2)).ker = holQ8Quot.ker := by
  ext q
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, DFunLike.ext_iff]
  simp only [MulAut.conj_apply, MulAut.one_apply]
  revert q
  decide

/-- For `Γ = G = Q₈` and `ρ = id`: `E_ρ ≃* Q₈` (paper `sec:holonomy`).-/
def _root_.Tengoku.ObserverEquivarianceLean.holQ8EρEquiv : Eρ (MonoidHom.id (QuaternionGroup 2)) ≃* QuaternionGroup 2 :=
  EρIdEquiv (QuaternionGroup 2)

/-- For `Γ = G = Q₈` and `ρ = id`: `H_ρ = Inn(Q₈) ≃* C₂ × C₂` (paper `sec:holonomy`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.holQ8HρEquiv :
    Hρ (MonoidHom.id (QuaternionGroup 2)) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr (Hρ_id (QuaternionGroup 2))).trans
    ((QuotientGroup.quotientKerEquivRange MulAut.conj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq holQ8_ker_conj).trans
        (QuotientGroup.quotientKerEquivOfSurjective holQ8Quot holQ8Quot_surjective)))

/-- The `Q₈` extension `1 → C₂ → Q₈ → C₂ × C₂ → 1` has NO group-homomorphic section: there is
    no monoid hom `σ : H_ρ →* E_ρ` with `proj ∘ σ = id` (paper `sec:holonomy`, `Q₈` example).
@isnad1 id=not.0h0v.s15.2bae6bba02b5 from=translated src=- shape=0dc7404b vocab=5d9482cf
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8_no_section :
    ¬ ∃ σ : Hρ (MonoidHom.id (QuaternionGroup 2)) →* Eρ (MonoidHom.id (QuaternionGroup 2)),
      (EρToHρ (MonoidHom.id (QuaternionGroup 2))).comp σ = MonoidHom.id _ := by
  rintro ⟨σ, hσ⟩
  let i : QuaternionGroup 2 := QuaternionGroup.a 1
  let αi : Hρ (MonoidHom.id (QuaternionGroup 2)) := ⟨MulAut.conj i, i, fun _ => rfl⟩
  have hsq : αi * αi = 1 := by
    apply Subtype.ext
    show MulAut.conj i * MulAut.conj i = 1
    rw [← map_mul]
    ext γ
    show (i * i) * γ * (i * i)⁻¹ = γ
    revert γ
    decide
  have hproj : (σ αi).1.2 = MulAut.conj i :=
    congrArg Subtype.val (DFunLike.congr_fun hσ αi)
  have hq : (σ αi).1.1 * (σ αi).1.1 = 1 := by
    have h := congrArg (fun e : Eρ (MonoidHom.id (QuaternionGroup 2)) => e.1.1)
      (show σ αi * σ αi = 1 by rw [← map_mul, hsq, map_one])
    exact h
  have h1 := (σ αi).2 (QuaternionGroup.xa 0)
  rw [hproj] at h1
  simp only [MonoidHom.id_apply, MulAut.conj_apply] at h1
  generalize (σ αi).1.1 = q at hq h1
  revert q
  decide

/-- Every lift in `E_ρ ≃ Q₈` of a nonidentity element of `H_ρ` has order four
    (paper `sec:holonomy`, `Q₈` example).
@isnad1 id=eq.1h1v.s14.cd77d1f10fed from=translated src=- shape=bd17826d vocab=1f08d0aa
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8_orderOf_lift (e : Eρ (MonoidHom.id (QuaternionGroup 2)))
    (he : EρToHρ (MonoidHom.id (QuaternionGroup 2)) e ≠ 1) : orderOf e = 4 := by
  rw [← MulEquiv.orderOf_eq (holQ8EρEquiv) e]
  have hne : e.1.2 ≠ 1 := fun h => he (Subtype.ext h)
  rw [(mem_Eρ_id_iff _ _).mp e.2] at hne
  have hne' : ∃ γ, e.1.1 * γ * e.1.1⁻¹ ≠ γ := by
    by_contra hcon
    exact hne (MulEquiv.ext fun γ => by
      by_contra h
      exact hcon ⟨γ, h⟩)
  show orderOf e.1.1 = 2 ^ (1 + 1)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : ∀ q : QuaternionGroup 2, (∃ γ, q * γ * q⁻¹ ≠ γ) →
      ¬ q ^ 2 ^ 1 = 1 ∧ q ^ 2 ^ (1 + 1) = 1 := by
    decide
  obtain ⟨h1, h2⟩ := key e.1.1 hne'
  exact orderOf_eq_prime_pow h1 h2

/-- The inclusion `C₂ →* Q₈` onto the center `{±1}` (paper `sec:holonomy`, `Q₈` example).-/
def _root_.Tengoku.ObserverEquivarianceLean.holQ8Center : Multiplicative (ZMod 2) →* QuaternionGroup 2 where
  toFun a := if a = 1 then 1 else QuaternionGroup.a 2
  map_one' := by decide
  map_mul' := by decide

/-- `holQ8Center` is injective (paper `sec:holonomy`).
@isnad1 id=injectiv.0h0v.s7.c4d46d5e57d1 from=translated src=- shape=74e67028 vocab=f48cea12
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8Center_injective : Function.Injective holQ8Center := by
  intro a b
  revert a b
  decide

/-- The holonomy centralizer for `ρ = id` on `Q₈` is the center `{±1}` (paper `sec:holonomy`).
@isnad1 id=eq.0h0v.s7.d43c0dfef99c from=translated src=- shape=001cb580 vocab=a6b626b9
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.holQ8_centralizer_eq :
    Subgroup.centralizer ((MonoidHom.id (QuaternionGroup 2)).range : Set (QuaternionGroup 2))
      = holQ8Center.range := by
  ext g
  rw [Subgroup.mem_centralizer_iff, MonoidHom.mem_range]
  constructor
  · intro hg
    have h : ∀ x : QuaternionGroup 2, x * g = g * x := fun x =>
      hg x (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    clear hg
    revert g
    decide
  · rintro ⟨a, rfl⟩ x -
    revert a x
    decide

/-- For `ρ = id` on `Q₈`, the kernel `C_{Q₈}(im ρ)` of the extension is `C₂`
    (paper `sec:holonomy`, the sequence `1 → C₂ → Q₈ → C₂ × C₂ → 1`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.holQ8CentralizerEquiv :
    Subgroup.centralizer ((MonoidHom.id (QuaternionGroup 2)).range : Set (QuaternionGroup 2))
      ≃* Multiplicative (ZMod 2) :=
  (MulEquiv.subgroupCongr holQ8_centralizer_eq).trans
    (MonoidHom.ofInjective holQ8Center_injective).symm

/-- For `ρ = id` on `Q₈`, the kernel of `E_ρ → Aut(Q₈)` is `C₂` (paper `sec:holonomy`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.holQ8KerEquiv :
    (EρProj (MonoidHom.id (QuaternionGroup 2))).ker ≃* Multiplicative (ZMod 2) :=
  (EρProjKerEquiv _).trans holQ8CentralizerEquiv

end Q8
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
