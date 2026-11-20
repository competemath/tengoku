import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Descent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariant functors and residual actions (paper `prop:residual`)

Paper labels covered in this file:

* `prop:residual` (strict invariance on `O`): `OEData.IsInvariant d F` (`R_h ⋙ F = F`, distinct
  from `IsGEquivariant`; namespaced because mathlib already has a root `IsInvariant`), with clean
  object/arrow forms `OEData.IsInvariant.obj_eq`, `OEData.IsInvariant.map_eq`,
  `OEData.actFunctor_covers_id` (`R_h ⋙ p = p`) and `isInvariant_comp_p`.
* `prop:residual` (product coordinates): the functor `Q : S × Pair G ⥤ S × BG`,
  `Q(s,a) = (s,*)`, `Q(u : a → b) = (u, b a⁻¹)` (`residualQ`, `residualQ_invariant`); a functor
  `F : S × Pair G ⥤ C` is strictly invariant iff it factors UNIQUELY as `F = Q ⋙ Ecal`
  (`productInvariant_iff_factors`, explicit factor `IsProductInvariant.factor`,
  `IsProductInvariant.residualQ_comp_factor`, `residualQ_cancel`).
* The paragraph after `prop:residual`: invariant natural transformations `α R_h = α`, stated by
  component equalities with the transports along `R_h ⋙ F = F` (`IsInvariantNatTrans`, closed
  under identities and composition).

* `prop:residual` (residual data): `ResidualData S C G` (`E : S ⥤ C`,
  `σ_s : G →* Aut_C(E s)`, `E(u) σ_s(r) = σ_t(r) E(u)`), the equivalence
  `functorProdBGEquivResidualData : (S × BG ⥤ C) ≃ ResidualData S C G` with recovery lemmas
  `E(u) = Ecal(u, 1)`, `σ_s(r) = Ecal(𝟙_s, r)`; `productInvariant_iff_residualData`; the formula
  `F(s, a) = E(s)`, `F(u : a → b) = E(u) σ_s(b a⁻¹)` (`residualQ_comp_toFunctor_map`,
  `IsProductInvariant.map_pairArr_residualData`); product-level descent iff trivial `σ`
  (`productDescent_iff_residual_trivial`), and the same criterion for an arbitrary
  product-invariant `F` with its canonical data (`IsProductInvariant.descent_iff`).
* `prop:residual` on `O`: `OEData.isInvariant_iff_isProductInvariant`, `invariant_iff_factors`
  (`F = (N ⋙ Q) ⋙ Ecal` uniquely), the vertical arrows `OEData.vertArr` (`v_{s,r} : b_s ⟶ b_s · r`),
  `residualAction d F hF s : G →* Aut (F b_s)` with `residualAction_hom`
  (`σ_s(r) = F(v_{s,r}) ≫ cast`), `residualAction_eq_one_iff`, `residualAction_natural`,
  the bundled `OEData.IsInvariant.residualData`, agreement with the product-model `σ`
  (`residualAction_agrees`), `OEData.IsInvariant.verticallyTrivial_iff_residualAction_trivial`,
  and the descent criterion `invariant_descends_iff_residual_trivial`.
* `prop:residual` on `O` in terms of O-level data (`E = B ⋙ F`, `σ = residualAction`): the
  formula `F(f) = E(p f) σ_{p x}(g_y g_x⁻¹)` (`OEData.IsInvariant.map_eq_residualAction`,
  `OEData.IsInvariant.map_eq_residualData`), the factorization
  `(N ⋙ Q) ⋙ Ecal(hF.residualData) = F` (`OEData.IsInvariant.normalFormQ_comp_residualData`),
  and unique specification by residual data (`invariant_iff_residualData`,
  `OEData.IsInvariant.residualData_unique`).
* Not formalized: the remark after `cor:invariant-calibration` that the diagonal orbit category
  is `O/G ≅ S × BG` in the chosen coordinates.  No orbit category is constructed; the closest
  statements are the unique factorizations `invariant_iff_factors` and
  `invariant_iff_residualData` through `N ⋙ Q : O ⥤ S × BG`.
* Remark after `cor:invariant-calibration`: the residual action of `ex:invariant` is the identity
  homomorphism (`invariantPairFunctor_residualAction`, `invariantPairFunctor_residualAction_hom`).
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}
variable {C : Type*} [Category C]

/-! ## Strict invariance on `O` (paper `prop:residual`) -/

/-- The action functors cover the identity of the base: `R_h ⋙ p = p` (helper for paper
    `prop:residual`).  This DUPLICATES `LocalLifts.actFunctor_comp_p` of
    `ObserverEquivariance.LocalLifts` (same statement, same one-line proof from
    `MinSpec.actFunctor_comp_p`); it has a separate name because this module does not
    import `LocalLifts`, and the two declarations would clash if it did.-/
theorem Tengoku.ObserverEquivarianceLean.OEData.actFunctor_covers_id (d : OEData G p) (h : G) : d.actFunctor h ⋙ p = p := by
  rw [← d.toMinSpec_actFunctor]; exact d.toMinSpec.actFunctor_comp_p h

/-- A functor `F : O ⥤ C` is strictly `G`-invariant if `R_h ⋙ F = F` for every `h : G`
    (paper `prop:residual`, "`F R_h = F`").  This is a condition on functors OUT of `O`,
    distinct from `IsGEquivariant`, which concerns endofunctors of `O`.-/
def Tengoku.ObserverEquivarianceLean.OEData.IsInvariant (d : OEData G p) (F : O ⥤ C) : Prop :=
  ∀ h : G, d.actFunctor h ⋙ F = F

namespace Tengoku.ObserverEquivarianceLean.OEData.IsInvariant

variable {d : OEData G p} {F : O ⥤ C}

/-- The object part of invariance with clean endpoints: `F(x · h) = F(x)`
    (paper `prop:residual`).-/
theorem obj_eq (hF : OEData.IsInvariant d F) (h : G) (x : O) : F.obj (d.act x h) = F.obj x :=
  Functor.congr_obj (hF h) x

/-- The arrow part of invariance with clean endpoints: `F(R_h f) = F(f)` up to the object casts
    (paper `prop:residual`).-/
theorem map_eq (hF : OEData.IsInvariant d F) (h : G) {x y : O} (f : x ⟶ y) :
    F.map ((d.actFunctor h).map f)
      = eqToHom (hF.obj_eq h x) ≫ F.map f ≫ eqToHom (hF.obj_eq h y).symm :=
  Functor.congr_hom (hF h) f

/-- An invariant functor takes the same value on an object and on its basepoint:
    `F(b_{p x}) = F(x)`, since `x = b_{p x} · g_x` (paper `prop:residual`, "`F(s, a) = E(s)`").-/
theorem obj_base_eq (hF : OEData.IsInvariant d F) (x : O) : F.obj (d.base (p.obj x)) = F.obj x :=
  (hF.obj_eq (d.coord x) (d.base (p.obj x))).symm.trans (congrArg F.obj (d.base_coord x))

end Tengoku.ObserverEquivarianceLean.OEData.IsInvariant

/-- A strictly factored functor `p ⋙ L` is invariant, since `R_h ⋙ p = p`
    (paper `prop:residual` and `cor:invariant-calibration`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isInvariant_comp_p (d : OEData G p) (L : S ⥤ C) : OEData.IsInvariant d (p ⋙ L) := fun h => by
  rw [← Functor.assoc, d.actFunctor_covers_id]

/-- Invariant natural transformations (paragraph after paper `prop:residual`, "`α R_h = α`"):
    for invariant `F`, `F'`, the transformation `α : F ⟶ F'` satisfies
    `α_{x · h} = α_x` for all `h`, `x`, up to the transports `F(x · h) = F(x)` and
    `F'(x · h) = F'(x)` supplied by `hF h` and `hF' h`.  This is a genuine restriction: not
    every natural transformation between invariant functors is invariant.-/
def _root_.Tengoku.ObserverEquivarianceLean.IsInvariantNatTrans (d : OEData G p) {F F' : O ⥤ C} (hF : OEData.IsInvariant d F)
    (hF' : OEData.IsInvariant d F') (α : F ⟶ F') : Prop :=
  ∀ (h : G) (x : O),
    α.app (d.act x h) = eqToHom (hF.obj_eq h x) ≫ α.app x ≫ eqToHom (hF'.obj_eq h x).symm

/-- The identity transformation of an invariant functor is invariant (paragraph after paper
    `prop:residual`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isInvariantNatTrans_id (d : OEData G p) {F : O ⥤ C} (hF : OEData.IsInvariant d F) :
    IsInvariantNatTrans d hF hF (𝟙 F) := by
  intro h x
  simp

/-- Invariant transformations compose (paragraph after paper `prop:residual`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isInvariantNatTrans_comp (d : OEData G p) {F F' F'' : O ⥤ C} {hF : OEData.IsInvariant d F}
    {hF' : OEData.IsInvariant d F'} {hF'' : OEData.IsInvariant d F''} {α : F ⟶ F'} {β : F' ⟶ F''}
    (hα : IsInvariantNatTrans d hF hF' α) (hβ : IsInvariantNatTrans d hF' hF'' β) :
    IsInvariantNatTrans d hF hF'' (α ≫ β) := by
  intro h x
  simp [hα h x, hβ h x]

/-! ## Product coordinates: invariance and the functor `Q` (paper `prop:residual`) -/

/-- Strict invariance of a functor on the product model `S × Pair G`: `P_h ⋙ F = F` for every
    `h`, where `P_h (s, a) = (s, a h)` is `normalFormProductAction h` (paper `prop:residual`,
    "`F R_h = F`" in the product coordinates of `thm:normalform`).-/
def _root_.Tengoku.ObserverEquivarianceLean.IsProductInvariant (F : S × Pair G ⥤ C) : Prop :=
  ∀ h : G, normalFormProductAction h ⋙ F = F

namespace Residual

/-- The unique arrow `(s, a) ⟶ (t, b)` of `S × Pair G` over `u : s ⟶ t` (helper for paper
    `prop:residual`, the arrows `(u : a → b)`).-/
def pairArr {s t : S} (u : s ⟶ t) (a b : G) : ((s, Pair.mk a) : S × Pair G) ⟶ (t, Pair.mk b) :=
  (u, PUnit.unit)

omit [Group G] in
/-- Composition of the arrows `(u : a → b)` (helper for paper `prop:residual`).-/
theorem pairArr_comp {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (a b c : G) :
    pairArr u a b ≫ pairArr v b c = pairArr (u ≫ v) a c := rfl

omit [Group G] in
/-- Identities among the arrows `(u : a → b)` (helper for paper `prop:residual`).-/
theorem pairArr_id (s : S) (a : G) : pairArr (𝟙 s) a a = 𝟙 ((s, Pair.mk a) : S × Pair G) := rfl

omit [Group G] in
/-- Every arrow of `S × Pair G` is one of the arrows `(u : a → b)` (helper for paper
    `prop:residual`).-/
theorem eq_pairArr {X Y : S × Pair G} (f : X ⟶ Y) : f = pairArr f.1 X.2.pt Y.2.pt := rfl

end Residual

open Residual

namespace Tengoku.ObserverEquivarianceLean.IsProductInvariant

variable {F : S × Pair G ⥤ C}

/-- An invariant functor on the product takes the same value on all objects of one fiber:
    `F(s, a) = F(s, b)` (paper `prop:residual`).-/
theorem obj_eq (hF : IsProductInvariant F) (s : S) (a b : G) :
    F.obj (s, Pair.mk a) = F.obj (s, Pair.mk b) := by
  have h : F.obj (s, Pair.mk (a * (a⁻¹ * b))) = F.obj (s, Pair.mk a) :=
    Functor.congr_obj (hF (a⁻¹ * b)) (s, Pair.mk a)
  rw [mul_inv_cancel_left] at h
  exact h.symm

/-- Invariance on the arrows `(u : a → b)`: `F(u : a h → b h) = F(u : a → b)` up to the casts
    (paper `prop:residual`).-/
theorem map_pairArr_mul (hF : IsProductInvariant F) {s t : S} (u : s ⟶ t) (a b h : G) :
    F.map (pairArr u (a * h) (b * h))
      = eqToHom (hF.obj_eq s (a * h) a) ≫ F.map (pairArr u a b)
        ≫ eqToHom (hF.obj_eq t b (b * h)) :=
  Functor.congr_hom (hF h) (pairArr u a b)

/-- Translated form of `map_pairArr_mul` with arbitrary target coordinates (paper
    `prop:residual`).-/
theorem map_pairArr_of_mul (hF : IsProductInvariant F) {s t : S} (u : s ⟶ t) {a b a' b' : G}
    (h : G) (ha : a * h = a') (hb : b * h = b') :
    F.map (pairArr u a' b')
      = eqToHom (hF.obj_eq s a' a) ≫ F.map (pairArr u a b) ≫ eqToHom (hF.obj_eq t b b') := by
  subst ha hb
  exact hF.map_pairArr_mul u a b h

/-- The value of an invariant functor on `(u : a → b)` only depends on `u` and `b a⁻¹`:
    "`F(u : a → b) = F(u : 1 → b a⁻¹)`" (paper `prop:residual`, proof).-/
theorem map_pairArr_eq (hF : IsProductInvariant F) {s t : S} (u : s ⟶ t) {a b a' b' : G}
    (hab : b * a⁻¹ = b' * a'⁻¹) :
    F.map (pairArr u a' b')
      = eqToHom (hF.obj_eq s a' a) ≫ F.map (pairArr u a b) ≫ eqToHom (hF.obj_eq t b b') :=
  hF.map_pairArr_of_mul u (a⁻¹ * a') (mul_inv_cancel_left a a') (by
    rw [← mul_assoc, hab, mul_assoc, inv_mul_cancel, mul_one])

end Tengoku.ObserverEquivarianceLean.IsProductInvariant

variable (S G) in
/-- The functor `Q : S × Pair G ⥤ S × BG`, `Q(s, a) = (s, *)`, `Q(u : a → b) = (u, b a⁻¹)`
    (paper `prop:residual`; `BG = SingleObj G`, where `f ≫ g = g * f`, so functoriality is
    `(c b⁻¹)(b a⁻¹) = c a⁻¹`).-/
def _root_.Tengoku.ObserverEquivarianceLean.residualQ : S × Pair G ⥤ S × SingleObj G where
  obj X := (X.1, SingleObj.star G)
  map {X Y} f := (f.1, (Y.2.pt * X.2.pt⁻¹ : G))
  map_id X := by
    refine Prod.ext rfl ?_
    show X.2.pt * X.2.pt⁻¹ = (1 : G)
    exact mul_inv_cancel _
  map_comp {X Y Z} f g := by
    refine Prod.ext rfl ?_
    show Z.2.pt * X.2.pt⁻¹ = (Z.2.pt * Y.2.pt⁻¹) * (Y.2.pt * X.2.pt⁻¹)
    group

/-- `Q(s, a) = (s, *)` (paper `prop:residual`).-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.residualQ_obj (X : S × Pair G) : (residualQ S G).obj X = (X.1, SingleObj.star G) :=
  rfl

/-- `Q(u : a → b) = (u, b a⁻¹)` (paper `prop:residual`).-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.residualQ_map {X Y : S × Pair G} (f : X ⟶ Y) :
    (residualQ S G).map f = ((f.1, (Y.2.pt * X.2.pt⁻¹ : G)) : (X.1, SingleObj.star G) ⟶ (Y.1, SingleObj.star G)) :=
  rfl

/-! ## Strict invariance iff unique factorization through `Q` (paper `prop:residual`) -/

namespace Tengoku.ObserverEquivarianceLean.IsProductInvariant

variable {F : S × Pair G ⥤ C}

/-- The factor `Ecal : S × BG ⥤ C` of an invariant functor: `Ecal(s, *) = F(s, 1)` and
    `Ecal(u, r) = F(u : 1 → r)`, followed by the invariance cast `F(t, r) = F(t, 1)`
    (paper `prop:residual`, proof).-/
def factor (hF : IsProductInvariant F) : S × SingleObj G ⥤ C where
  obj X := F.obj (X.1, Pair.mk 1)
  map {X Y} f := F.map (pairArr f.1 1 (f.2 : G)) ≫ eqToHom (hF.obj_eq Y.1 (f.2 : G) 1)
  map_id X := by
    show F.map (pairArr (𝟙 X.1) 1 1) ≫ eqToHom (hF.obj_eq X.1 1 1) = 𝟙 _
    rw [pairArr_id, F.map_id]
    simp
  map_comp {X Y Z} f g := by
    show F.map (pairArr (f.1 ≫ g.1) 1 ((g.2 : G) * (f.2 : G)))
        ≫ eqToHom (hF.obj_eq Z.1 ((g.2 : G) * (f.2 : G)) 1)
      = (F.map (pairArr f.1 1 (f.2 : G)) ≫ eqToHom (hF.obj_eq Y.1 (f.2 : G) 1))
        ≫ F.map (pairArr g.1 1 (g.2 : G)) ≫ eqToHom (hF.obj_eq Z.1 (g.2 : G) 1)
    rw [← pairArr_comp f.1 g.1 1 (f.2 : G), F.map_comp,
      hF.map_pairArr_eq g.1 (a := 1) (b := (g.2 : G)) (a' := (f.2 : G))
        (b' := (g.2 : G) * (f.2 : G)) (by group)]
    simp

/-- `Ecal(s, *) = F(s, 1)` (paper `prop:residual`, proof).-/
@[simp] theorem factor_obj (hF : IsProductInvariant F) (X : S × SingleObj G) :
    hF.factor.obj X = F.obj (X.1, Pair.mk 1) := rfl

/-- `Ecal(u, r) = F(u : 1 → r)` up to the cast (paper `prop:residual`, proof).-/
theorem factor_map (hF : IsProductInvariant F) {X Y : S × SingleObj G} (f : X ⟶ Y) :
    hF.factor.map f = F.map (pairArr f.1 1 (f.2 : G)) ≫ eqToHom (hF.obj_eq Y.1 (f.2 : G) 1) :=
  rfl

/-- The factorization `Q ⋙ Ecal = F` (paper `prop:residual`: "`F = Ecal Q`").-/
theorem residualQ_comp_factor (hF : IsProductInvariant F) : residualQ S G ⋙ hF.factor = F := by
  fapply CategoryTheory.Functor.ext
  · intro X; exact hF.obj_eq X.1 1 X.2.pt
  · intro X Y f
    show F.map (pairArr f.1 1 (Y.2.pt * X.2.pt⁻¹)) ≫ eqToHom (hF.obj_eq Y.1 (Y.2.pt * X.2.pt⁻¹) 1)
      = eqToHom (hF.obj_eq X.1 1 X.2.pt) ≫ F.map (pairArr f.1 X.2.pt Y.2.pt)
        ≫ eqToHom (hF.obj_eq Y.1 1 Y.2.pt).symm
    rw [hF.map_pairArr_eq f.1 (a := X.2.pt) (b := Y.2.pt) (a' := 1)
      (b' := Y.2.pt * X.2.pt⁻¹) (by group)]
    simp

end Tengoku.ObserverEquivarianceLean.IsProductInvariant

/-- `Q` is an epimorphism of categories: functors agreeing after `Q` are equal (uniqueness part
    of paper `prop:residual`; every arrow `(u, r)` is `Q(u : 1 → r)`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.residualQ_cancel {E₁ E₂ : S × SingleObj G ⥤ C}
    (h : residualQ S G ⋙ E₁ = residualQ S G ⋙ E₂) : E₁ = E₂ := by
  fapply CategoryTheory.Functor.ext
  · intro X; exact Functor.congr_obj h (X.1, Pair.mk 1)
  · intro X Y f
    have hf : ((residualQ S G).map (pairArr f.1 1 (f.2 : G)) : X ⟶ Y) = f := by
      refine Prod.ext rfl ?_
      show (f.2 : G) * (1 : G)⁻¹ = f.2
      rw [inv_one, mul_one]
    have e : E₁.map ((residualQ S G).map (pairArr f.1 1 (f.2 : G)))
        = eqToHom (Functor.congr_obj h (X.1, Pair.mk 1))
          ≫ E₂.map ((residualQ S G).map (pairArr f.1 1 (f.2 : G)))
          ≫ eqToHom (Functor.congr_obj h (Y.1, Pair.mk (f.2 : G))).symm :=
      Functor.congr_hom h (pairArr f.1 1 (f.2 : G))
    rw [hf] at e
    exact e

/-! ## Residual data: functors on `S × BG` (paper `prop:residual`) -/

/-- Residual data (paper `prop:residual`): a functor `E : S ⥤ C` together with group
    homomorphisms `σ_s : G →* Aut_C(E s)` (automorphisms of the OBJECT `E s` in `C`, not strict
    automorphisms of a category), natural in `s`: `E(u) σ_s(r) = σ_t(r) E(u)` in the paper's
    operator order, i.e. `σ_s(r) ≫ E(u) = E(u) ≫ σ_t(r)`.-/
structure _root_.Tengoku.ObserverEquivarianceLean.ResidualData (S : Type*) [Category S] (C : Type*) [Category C] (G : Type*) [Group G] where
  /-- The base functor `E : S ⥤ C` (paper `prop:residual`).-/
  E : S ⥤ C
  /-- The residual actions `σ_s : G →* Aut_C(E s)` (paper `prop:residual`).-/
  σ : ∀ s : S, G →* Aut (E.obj s)
  /-- Naturality `E(u) σ_s(r) = σ_t(r) E(u)` (paper `prop:residual`, operator order).-/
  natural : ∀ {s t : S} (u : s ⟶ t) (r : G), (σ s r).hom ≫ E.map u = E.map u ≫ (σ t r).hom

/-- Extensionality for residual data: equal functors and equal actions up to the transport
    along the functor equality (helper for paper `prop:residual`).-/
theorem Tengoku.ObserverEquivarianceLean.ResidualData.ext' {D D' : ResidualData S C G} (hE : D.E = D'.E)
    (hσ : ∀ (s : S) (r : G), (D.σ s r).hom
      = eqToHom (Functor.congr_obj hE s) ≫ (D'.σ s r).hom ≫ eqToHom (Functor.congr_obj hE s).symm) :
    D = D' := by
  obtain ⟨E, σ, n⟩ := D
  obtain ⟨E', σ', n'⟩ := D'
  dsimp only at hE hσ
  subst hE
  have : σ = σ' := by
    funext s
    refine MonoidHom.ext fun r => Aut.ext ?_
    simpa using hσ s r
  subst this
  rfl

namespace Tengoku.ObserverEquivarianceLean.ResidualData

/-- The residual actions of a functor `Ecal : S × BG ⥤ C`: `σ_s(r) = Ecal(𝟙_s, r)`
    (paper `prop:residual`, proof).-/
def sigmaOf (Ecal : S × SingleObj G ⥤ C) (s : S) : G →* Aut (Ecal.obj (s, SingleObj.star G)) where
  toFun r :=
    { hom := Ecal.map ((𝟙 s, r) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
      inv := Ecal.map ((𝟙 s, r⁻¹) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
      hom_inv_id := by
        rw [← Ecal.map_comp, ← Ecal.map_id]
        congr 1
        refine Prod.ext (Category.comp_id _) ?_
        show r⁻¹ * r = (1 : G)
        exact inv_mul_cancel r
      inv_hom_id := by
        rw [← Ecal.map_comp, ← Ecal.map_id]
        congr 1
        refine Prod.ext (Category.comp_id _) ?_
        show r * r⁻¹ = (1 : G)
        exact mul_inv_cancel r }
  map_one' := Aut.ext (Ecal.map_id (s, SingleObj.star G))
  map_mul' r q := Aut.ext (by
    show Ecal.map ((𝟙 s, r * q) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
      = Ecal.map ((𝟙 s, q) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
        ≫ Ecal.map ((𝟙 s, r) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
    rw [← Ecal.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm rfl)

/-- The residual data of a functor `Ecal : S × BG ⥤ C`: `E(u) = Ecal(u, 1)`,
    `σ_s(r) = Ecal(𝟙_s, r)` (paper `prop:residual`, proof).-/
def ofFunctor (Ecal : S × SingleObj G ⥤ C) : ResidualData S C G where
  E :=
    { obj s := Ecal.obj (s, SingleObj.star G)
      map {s t} u := Ecal.map ((u, 𝟙 (SingleObj.star G)) : (s, SingleObj.star G) ⟶ (t, SingleObj.star G))
      map_id s := Ecal.map_id (s, SingleObj.star G)
      map_comp {s t r} u v := by
        rw [← Ecal.map_comp]
        congr 1
        exact Prod.ext rfl (Category.comp_id _).symm }
  σ := sigmaOf Ecal
  natural {s t} u r := by
    show Ecal.map ((𝟙 s, r) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
        ≫ Ecal.map ((u, 𝟙 (SingleObj.star G)) : (s, SingleObj.star G) ⟶ (t, SingleObj.star G))
      = Ecal.map ((u, 𝟙 (SingleObj.star G)) : (s, SingleObj.star G) ⟶ (t, SingleObj.star G))
        ≫ Ecal.map ((𝟙 t, r) : (t, SingleObj.star G) ⟶ (t, SingleObj.star G))
    rw [← Ecal.map_comp, ← Ecal.map_comp]
    congr 1
    refine Prod.ext ((Category.id_comp u).trans (Category.comp_id u).symm) ?_
    show (1 : G) * r = r * 1
    rw [one_mul, mul_one]

/-- Recovery of `E` on objects: `E(s) = Ecal(s, *)` (paper `prop:residual`, proof).-/
@[simp] theorem ofFunctor_E_obj (Ecal : S × SingleObj G ⥤ C) (s : S) :
    (ofFunctor Ecal).E.obj s = Ecal.obj (s, SingleObj.star G) := rfl

/-- Recovery of `E` on arrows: `E(u) = Ecal(u, 1)` (paper `prop:residual`, proof).-/
@[simp] theorem ofFunctor_E_map (Ecal : S × SingleObj G ⥤ C) {s t : S} (u : s ⟶ t) :
    (ofFunctor Ecal).E.map u
      = Ecal.map ((u, (1 : G)) : (s, SingleObj.star G) ⟶ (t, SingleObj.star G)) := rfl

/-- Recovery of `σ`: `σ_s(r) = Ecal(𝟙_s, r)` (paper `prop:residual`, proof).-/
@[simp] theorem ofFunctor_σ_hom (Ecal : S × SingleObj G ⥤ C) (s : S) (r : G) :
    ((ofFunctor Ecal).σ s r).hom
      = Ecal.map ((𝟙 s, r) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G)) := rfl

end Tengoku.ObserverEquivarianceLean.ResidualData

/-! ## The formula `F(u : a → b) = E(u) σ_s(b a⁻¹)` and descent (paper `prop:residual`) -/

namespace Tengoku.ObserverEquivarianceLean.IsProductInvariant

variable {F : S × Pair G ⥤ C}

end Tengoku.ObserverEquivarianceLean.IsProductInvariant

/-! ## Invariance on `O` through the normal form (paper `prop:residual`, `thm:normalform`) -/

/-- Transport of invariance to the product model: if `F` is invariant then so is `M ⋙ F`, since
    `P_h ⋙ M = M ⋙ R_h` (paper `prop:residual` "in the product coordinates of
    `thm:normalform`").-/
theorem Tengoku.ObserverEquivarianceLean.OEData.IsInvariant.isProductInvariant {d : OEData G p} {F : O ⥤ C}
    (hF : d.IsInvariant F) : IsProductInvariant (normalFormFrom d ⋙ F) := fun h => by
  rw [← Functor.assoc, normalFormFrom_equivariant, Functor.assoc, hF h]

/-- Converse transport: if `M ⋙ F` is invariant on the product model then `F` is invariant,
    since `R_h ⋙ N = N ⋙ P_h` and `N ⋙ M = 𝟭` (paper `prop:residual`, `thm:normalform`).-/
theorem Tengoku.ObserverEquivarianceLean.OEData.isInvariant_of_isProductInvariant {d : OEData G p} {F : O ⥤ C}
    (hP : IsProductInvariant (normalFormFrom d ⋙ F)) : d.IsInvariant F := fun h => by
  have hNM : F = normalFormTo d ⋙ normalFormFrom d ⋙ F := by
    rw [← Functor.assoc, normalFormTo_comp_normalFormFrom, Functor.id_comp]
  conv_lhs => rw [hNM]
  rw [← Functor.assoc, normalForm_equivariant, Functor.assoc, hP h, ← hNM]

/-- Invariance on `O` is invariance of `M ⋙ F` on the product model (paper `prop:residual`).-/
theorem Tengoku.ObserverEquivarianceLean.OEData.isInvariant_iff_isProductInvariant (d : OEData G p) (F : O ⥤ C) :
    d.IsInvariant F ↔ IsProductInvariant (normalFormFrom d ⋙ F) :=
  ⟨fun hF => hF.isProductInvariant, OEData.isInvariant_of_isProductInvariant⟩

/-! ## The vertical arrows `v_{s,r} : b_s ⟶ b_s · r` (paper `prop:residual`) -/

/-- The vertical arrow `v_{s,r} : b_s ⟶ b_s · r`, the unique arrow over `𝟙 s` (paper
    `prop:residual`, the vertical arrows `(id_s : 1 → r)`; `cor:invariant-calibration`, proof).-/
noncomputable def Tengoku.ObserverEquivarianceLean.OEData.vertArr (d : OEData G p) (s : S) (r : G) :
    d.base s ⟶ d.act (d.base s) r :=
  d.toMinSpec.liftOver (𝟙 s) (d.p_base s) ((d.p_act (d.base s) r).trans (d.p_base s))

namespace Tengoku.ObserverEquivarianceLean.OEData

variable (d : OEData G p)

/-- `v_{s,r}` lies over an identity (paper `prop:residual`).-/
theorem p_map_vertArr (s : S) (r : G) :
    p.map (d.vertArr s r)
      = eqToHom ((d.p_base s).trans ((d.p_act (d.base s) r).trans (d.p_base s)).symm) := by
  simp only [vertArr, MinSpec.p_map_liftOver, Category.id_comp, eqToHom_trans]

/-- `v_{s,r}` is vertical (paper `prop:residual`, `def:vertical-trivial`).-/
theorem vertArr_isVertical (s : S) (r : G) : IsVertical p (d.vertArr s r) :=
  ⟨_, d.p_map_vertArr s r⟩

/-- `v_{s,1}` is the identity up to the cast `b_s · 1 = b_s` (paper `prop:residual`).-/
theorem vertArr_one (s : S) : d.vertArr s 1 = eqToHom (d.act_one (d.base s)).symm :=
  d.toMinSpec.hom_ext (by rw [p_map_vertArr, eqToHom_map])

/-- `v_{s, r q}` is `v_{s,q}` followed by the translate `v_{s,r} · q` (paper `prop:residual`,
    proof: "replace the arrow by its right translate").-/
theorem vertArr_mul (s : S) (r q : G) :
    d.vertArr s (r * q)
      = d.vertArr s q ≫ d.actHom (d.vertArr s r) q ≫ eqToHom (d.act_mul (d.base s) r q) := by
  apply d.toMinSpec.hom_ext
  simp [p_map_vertArr, d.p_actHom, eqToHom_map]

end Tengoku.ObserverEquivarianceLean.OEData

/-! ## The residual action on `O` (paper `prop:residual`) -/

namespace Tengoku.ObserverEquivarianceLean.OEData.IsInvariant

variable {d : OEData G p} {F : O ⥤ C}

/-- The residual endomorphism `σ_s(r) : F(b_s) ⟶ F(b_s)`: `F(v_{s,r})` followed by the invariance
    cast `F(b_s · r) = F(b_s)` (paper `prop:residual`: "the images of the vertical arrows
    `(id_s : 1 → r)` are precisely `σ_s(r)`").-/
noncomputable def residualHom (hF : d.IsInvariant F) (s : S) (r : G) :
    F.obj (d.base s) ⟶ F.obj (d.base s) :=
  F.map (d.vertArr s r) ≫ eqToHom (hF.obj_eq r (d.base s))

/-- `σ_s(1) = id` (paper `prop:residual`).-/
theorem residualHom_one (hF : d.IsInvariant F) (s : S) : hF.residualHom s 1 = 𝟙 _ := by
  rw [residualHom, d.vertArr_one, eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- The group law `σ_s(r q) = σ_s(r) σ_s(q)` in operator order, i.e. `σ_s(q) ≫ σ_s(r)`
    (paper `prop:residual`, proof: invariance and functoriality).-/
theorem residualHom_mul (hF : d.IsInvariant F) (s : S) (r q : G) :
    hF.residualHom s (r * q) = hF.residualHom s q ≫ hF.residualHom s r := by
  have hmap : F.map (d.actHom (d.vertArr s r) q)
      = eqToHom (hF.obj_eq q (d.base s)) ≫ F.map (d.vertArr s r)
        ≫ eqToHom (hF.obj_eq q (d.act (d.base s) r)).symm :=
    hF.map_eq q (d.vertArr s r)
  simp only [residualHom]
  rw [d.vertArr_mul s r q, Functor.map_comp, Functor.map_comp, hmap, eqToHom_map]
  simp

end Tengoku.ObserverEquivarianceLean.OEData.IsInvariant

/-- The residual action `σ_s : G →* Aut_C(F(b_s))` of a strictly invariant `F : O ⥤ C` at `s`:
    `σ_s(r) = F(v_{s,r})` followed by the invariance cast `F(b_s · r) = F(b_s)`, with inverse
    `σ_s(r⁻¹)` (paper `prop:residual`; `cor:invariant-calibration` (iii)).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.residualAction (d : OEData G p) (F : O ⥤ C) (hF : d.IsInvariant F) (s : S) :
    G →* Aut (F.obj (d.base s)) where
  toFun r :=
    { hom := hF.residualHom s r
      inv := hF.residualHom s r⁻¹
      hom_inv_id := by rw [← hF.residualHom_mul, inv_mul_cancel, hF.residualHom_one]
      inv_hom_id := by rw [← hF.residualHom_mul, mul_inv_cancel, hF.residualHom_one] }
  map_one' := Aut.ext (hF.residualHom_one s)
  map_mul' r q := Aut.ext (hF.residualHom_mul s r q)

/-- `σ_s(r) = F(v_{s,r}) ≫ cast` (paper `prop:residual`, `cor:invariant-calibration`, proof).-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.residualAction_hom (d : OEData G p) (F : O ⥤ C) (hF : d.IsInvariant F) (s : S)
    (r : G) :
    (residualAction d F hF s r).hom = F.map (d.vertArr s r) ≫ eqToHom (hF.obj_eq r (d.base s)) :=
  rfl

/-- `σ_s(r)⁻¹ = σ_s(r⁻¹) = F(v_{s,r⁻¹}) ≫ cast` (paper `prop:residual`).-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.residualAction_inv (d : OEData G p) (F : O ⥤ C) (hF : d.IsInvariant F) (s : S)
    (r : G) :
    (residualAction d F hF s r).inv
      = F.map (d.vertArr s r⁻¹) ≫ eqToHom (hF.obj_eq r⁻¹ (d.base s)) :=
  rfl

/-- A residual action is trivial iff every `F(v_{s,r}) ≫ cast` is an identity (paper
    `prop:residual`, `cor:invariant-calibration` (iii)).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.residualAction_eq_one_iff (d : OEData G p) (F : O ⥤ C) (hF : d.IsInvariant F) (s : S) :
    residualAction d F hF s = 1
      ↔ ∀ r : G, F.map (d.vertArr s r) ≫ eqToHom (hF.obj_eq r (d.base s)) = 𝟙 _ := by
  constructor
  · intro h r
    exact congrArg (fun φ : G →* Aut (F.obj (d.base s)) => (φ r).hom) h
  · intro h
    exact MonoidHom.ext fun r => Aut.ext (h r)

namespace Residual

/-- An arrow `(f, c)` of `S × BG` whose base component is a cast of an identity and whose group
    component is `r` is `Ecal(𝟙_s, r)` up to the object casts (helper for paper
    `prop:residual`).-/
theorem prodBG_map_eq_of_eq (E : S × SingleObj G ⥤ C) {s₁ s₂ s : S} (h₁ : s₁ = s) (h₂ : s₂ = s)
    (f : s₁ ⟶ s₂) (hf : f = eqToHom (h₁.trans h₂.symm)) (c r : G) (hc : c = r) :
    E.map ((f, c) : (s₁, SingleObj.star G) ⟶ (s₂, SingleObj.star G))
      = eqToHom (congrArg (fun t => E.obj (t, SingleObj.star G)) h₁)
        ≫ E.map ((𝟙 s, r) : (s, SingleObj.star G) ⟶ (s, SingleObj.star G))
        ≫ eqToHom (congrArg (fun t => E.obj (t, SingleObj.star G)) h₂).symm := by
  subst h₁ h₂ hf hc
  simp

end Residual

/-- Vertical triviality of an invariant functor is triviality of all its residual actions
    (paper `prop:residual`, last paragraph of the proof: the vertical arrow `b_s · a ⟶ b_s · b` is
    the translate of `v_{s, b a⁻¹}`, and invariance moves it back).-/
theorem Tengoku.ObserverEquivarianceLean.OEData.IsInvariant.verticallyTrivial_iff_residualAction_trivial {d : OEData G p}
    {F : O ⥤ C} (hF : d.IsInvariant F) :
    VerticallyTrivial p F ↔ ∀ s, residualAction d F hF s = 1 := by
  constructor
  · intro hvt s
    refine (residualAction_eq_one_iff d F hF s).2 fun r => ?_
    obtain ⟨h, e⟩ := hvt (d.vertArr s r) (d.vertArr_isVertical s r)
    rw [e, eqToHom_trans, eqToHom_refl]
  · intro h1 x y v hv
    obtain ⟨hxy, hpv⟩ := hv
    obtain ⟨s, a, rfl⟩ : ∃ (s : S) (a : G), x = d.act (d.base s) a :=
      ⟨p.obj x, d.coord x, (d.base_coord x).symm⟩
    obtain ⟨t, b, rfl⟩ : ∃ (t : S) (b : G), y = d.act (d.base t) b :=
      ⟨p.obj y, d.coord y, (d.base_coord y).symm⟩
    have hst : s = t := (d.p_base s).symm.trans ((d.p_act (d.base s) a).symm.trans
      (hxy.trans ((d.p_act (d.base t) b).trans (d.p_base t))))
    subst hst
    have hobj : d.act (d.act (d.base s) (b * a⁻¹)) a = d.act (d.base s) b := by
      rw [d.act_mul, inv_mul_cancel_right]
    have hdec : v = d.actHom (d.vertArr s (b * a⁻¹)) a ≫ eqToHom hobj := by
      apply d.toMinSpec.hom_ext
      rw [hpv]
      simp [d.p_map_vertArr, d.p_actHom, eqToHom_map]
    subst hdec
    have hv0 : F.map (d.vertArr s (b * a⁻¹))
        = eqToHom (hF.obj_eq (b * a⁻¹) (d.base s)).symm := by
      have h := (residualAction_eq_one_iff d F hF s).mp (h1 s) (b * a⁻¹)
      calc F.map (d.vertArr s (b * a⁻¹))
          = (F.map (d.vertArr s (b * a⁻¹)) ≫ eqToHom (hF.obj_eq (b * a⁻¹) (d.base s)))
              ≫ eqToHom (hF.obj_eq (b * a⁻¹) (d.base s)).symm := by simp
        _ = eqToHom (hF.obj_eq (b * a⁻¹) (d.base s)).symm := by rw [h, Category.id_comp]
    have hmap : F.map (d.actHom (d.vertArr s (b * a⁻¹)) a)
        = eqToHom (hF.obj_eq a (d.base s)) ≫ F.map (d.vertArr s (b * a⁻¹))
          ≫ eqToHom (hF.obj_eq a (d.act (d.base s) (b * a⁻¹))).symm :=
      hF.map_eq a (d.vertArr s (b * a⁻¹))
    refine ⟨(hF.obj_eq a (d.base s)).trans (hF.obj_eq b (d.base s)).symm, ?_⟩
    rw [Functor.map_comp, hmap, hv0, eqToHom_map]
    simp

/-- Paper `prop:residual`, last assertion, on `O`: a strictly invariant `F : O ⥤ C` factors
    strictly through `p` iff every residual action `σ_s` is trivial (via `thm:descent`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.invariant_descends_iff_residual_trivial (d : OEData G p) (F : O ⥤ C)
    (hF : d.IsInvariant F) :
    (∃ E : S ⥤ C, p ⋙ E = F) ↔ ∀ s, residualAction d F hF s = 1 := by
  rw [← hF.verticallyTrivial_iff_residualAction_trivial]
  constructor
  · rintro ⟨E, rfl⟩
    exact verticallyTrivial_comp p E
  · intro hvt
    exact ((d.descent F).mp hvt).exists

/-! ## The formula `F(u : a → b) = E(u) σ_s(b a⁻¹)` on `O` (paper `prop:residual`) -/

/-- Every arrow `f : x ⟶ y` of `O` is the right translate by `g_x` of the vertical arrow
    `v_{s, g_y g_x⁻¹}`, followed by the right translate by `g_y` of the section arrow `B(p f)`,
    up to the object casts `x = b_{p x} · g_x`, `y = b_{p y} · g_y` (helper for paper
    `prop:residual`, formula `F(u : a → b) = E(u) σ_s(b a⁻¹)`).-/
theorem Tengoku.ObserverEquivarianceLean.OEData.hom_eq_actHom_vertArr_actHom_sectionFunctor (d : OEData G p) {x y : O}
    (f : x ⟶ y)
    (e : d.act (d.act (d.base (p.obj x)) (d.coord y * (d.coord x)⁻¹)) (d.coord x)
      = d.act (d.base (p.obj x)) (d.coord y)) :
    f = eqToHom (d.base_coord x).symm
      ≫ d.actHom (d.vertArr (p.obj x) (d.coord y * (d.coord x)⁻¹)) (d.coord x) ≫ eqToHom e
      ≫ d.actHom (d.sectionFunctor.map (p.map f)) (d.coord y) ≫ eqToHom (d.base_coord y) := by
  have key : ∀ (k : d.base (p.obj x) ⟶ d.base (p.obj y)),
      p.map k = eqToHom (d.p_base (p.obj x)) ≫ p.map f ≫ eqToHom (d.p_base (p.obj y)).symm →
      f = eqToHom (d.base_coord x).symm
        ≫ d.actHom (d.vertArr (p.obj x) (d.coord y * (d.coord x)⁻¹)) (d.coord x) ≫ eqToHom e
        ≫ d.actHom k (d.coord y) ≫ eqToHom (d.base_coord y) := by
    intro k hk
    apply d.toMinSpec.hom_ext
    simp only [Functor.map_comp, d.p_actHom, hk, d.p_map_vertArr, eqToHom_map]
    simp
  exact key _ (d.p_map_sectionFunctor_map (p.map f))

/-! ## The residual action of `ex:invariant` (remark after `cor:invariant-calibration`) -/

/-- The functor of paper `ex:invariant` is strictly invariant in the sense of
    `OEData.IsInvariant` (paper `ex:invariant`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.invariantPairFunctor_isInvariant (G : Type*) [Group G] :
    (witness G).IsInvariant (invariantPairFunctor G) :=
  invariantPairFunctor_invariant G

/-- The residual action of `ex:invariant` sends `r` to `r` itself, read as an arrow of `BG`
    (remark after paper `cor:invariant-calibration`).-/
theorem _root_.Tengoku.ObserverEquivarianceLean.invariantPairFunctor_residualAction_hom (G : Type*) [Group G] (s : Pair PUnit) (r : G) :
    ((residualAction (witness G) (invariantPairFunctor G) (invariantPairFunctor_isInvariant G)
      s r).hom : G) = r := by
  rw [residualAction_hom]
  show (1 : G) * ((1 * r) * (1 : G)⁻¹) = r
  simp

/-- The residual action of `ex:invariant` is the identity homomorphism `G → G`, read through the
    identification `G ≃* Aut_{BG}(*)` (remark after paper `cor:invariant-calibration`: "The
    residual action in Example `ex:invariant` is the identity homomorphism `G → G`").-/
theorem _root_.Tengoku.ObserverEquivarianceLean.invariantPairFunctor_residualAction (G : Type*) [Group G] (s : Pair PUnit) :
    residualAction (witness G) (invariantPairFunctor G) (invariantPairFunctor_isInvariant G) s
      = (Units.toAut G).toMonoidHom.comp (toUnits (G := G)).toMonoidHom :=
  MonoidHom.ext fun r => Aut.ext (invariantPairFunctor_residualAction_hom G s r)
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
