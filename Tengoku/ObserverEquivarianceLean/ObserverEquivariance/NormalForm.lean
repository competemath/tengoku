import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.MinSpec

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict product normal form and the chosen section
  (paper `thm:normalform`, `cor:section`, `rem:groupoid`; vertical arrows from `sec:data`)

Paper labels covered in this file:

* vertical arrows (paper `sec:data`, the unlabeled paragraph right after `def:data`: "an arrow
  `v : x → y` is vertical if `p(x) = p(y)` and `p(v) = id`"): the predicate `IsVertical p v`
  (`∃ h : p x = p y, p v = eqToHom h`) and its closure properties.  The notion is used in (N5)
  and in `def:vertical-trivial`, but it is defined in neither.
* `thm:normalform` (strict product normal form): for a minimal specification
  `m : MinSpec G p` the functors `m.normalFormTo : O ⥤ S × Pair G` (`N`) and
  `m.normalFormFrom : S × Pair G ⥤ O` (`M`, `M(s,g) = b_s · g`, arrows = unique lifts of the
  base component) are STRICT inverse functors: `N ⋙ M = 𝟭 O` and `M ⋙ N = 𝟭 (S × Pair G)`
  as equalities of functors (objects and morphisms), not natural isomorphisms.  Both lie over
  `S` strictly ("an isomorphism of categories over `S`"): `N ⋙ Prod.fst = p`
  (`normalFormTo_comp_fst`) and `M ⋙ p = Prod.fst` (`normalFormFrom_comp_fst`).  Both
  intertwine the right `G`-actions strictly.  The `OEData` versions (`normalFormTo d` from
  `Core`, `normalFormFrom d`) are derived from the `MinSpec` ones through `OEData.toMinSpec`,
  plus the arrow-level reindexing statement `normalFormTo_map_chi`.
* `cor:section`: the structure `StrictSection p` (a functor `B` with the STRICT section
  equation `B ⋙ p = 𝟭 S` and a natural isomorphism `η : p ⋙ B ≅ 𝟭 O` with vertical
  components, the other composite only up to isomorphism), the constructions
  `MinSpec.strictSection` and `OEData.strictSection` (`B.obj s = b_s` definitionally for
  `OEData`, `B.map u` = the unique lift, equal to `χ_{u,b_t}` after the (N4) endpoint rewrite,
  `η_x = ℓ_{g_x, b_{p x}}`), and the consequence that `p` is an equivalence.  We do NOT claim
  that `p` is a strict isomorphism: for nontrivial `G` and nonempty `S` no functor `B'`
  satisfies `p ⋙ B' = 𝟭 O` (`MinSpec.no_strict_retraction`).
* `rem:groupoid`: the `MinSpec` versions of both groupoid specializations (the `OEData`
  versions are `OEData.base_hom_isIso` and `OEData.hom_isIso_of_base_isIso` in `Core`).

Dependencies are separable: everything in the `MinSpec` namespace uses only `MinSpec`, so the
normal form and the section are available directly from the minimal specification.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## Vertical arrows (paper `sec:data`, paragraph after `def:data`) -/

/-- An arrow `v : x ⟶ y` of `O` is vertical for `p` if it lies over an identity: its
    endpoints have the same projection and `p v` is the identity of that object, expressed as
    an `eqToHom` (paper `sec:data`, the unlabeled paragraph right after `def:data`; the notion
    is used in `def:data` (N5) and in `def:vertical-trivial`).-/
def _root_.Tengoku.ObserverEquivarianceLean.IsVertical (p : O ⥤ S) {x y : O} (v : x ⟶ y) : Prop :=
  ∃ h : p.obj x = p.obj y, p.map v = eqToHom h

namespace Tengoku.ObserverEquivarianceLean.IsVertical

/-- Identities are vertical (paper `sec:data`, paragraph after `def:data`).
@isnad1 id=isvertic.0h4v.s5.837dc56d69eb from=translated src=- shape=744875a9 vocab=adf2c2bc
-/
theorem id (p : O ⥤ S) (x : O) : IsVertical p (𝟙 x) :=
  ⟨rfl, by simp⟩

/-- `eqToHom` arrows are vertical (paper `sec:data`, paragraph after `def:data`).
@isnad1 id=isvertic.1h5v.s5.27c7677147a4 from=translated src=- shape=fcb0a7df vocab=1b5820ac
-/
theorem eqToHom (p : O ⥤ S) {x y : O} (h : x = y) : IsVertical p (CategoryTheory.eqToHom h) :=
  ⟨congrArg p.obj h, eqToHom_map p h⟩

/-- Vertical arrows compose (paper `sec:data`, paragraph after `def:data`).
@isnad1 id=isvertic.2h8v.s6.2403caef70ce from=translated src=- shape=75d890b6 vocab=492cd0d7
-/
theorem comp {x y z : O} {v : x ⟶ y} {w : y ⟶ z} (hv : IsVertical p v) (hw : IsVertical p w) :
    IsVertical p (v ≫ w) := by
  obtain ⟨h₁, e₁⟩ := hv
  obtain ⟨h₂, e₂⟩ := hw
  exact ⟨h₁.trans h₂, by rw [p.map_comp, e₁, e₂, eqToHom_trans]⟩

/-- The inverse of a vertical isomorphism is vertical (vertical arrows: paper `sec:data`,
    paragraph after `def:data`; used for the vertical isomorphisms of `def:data` (N5)).
@isnad1 id=isvertic.1h6v.s5.82e02ab5d5e0 from=translated src=- shape=3a3c900b vocab=c052b28a
-/
theorem inv {x y : O} {v : x ⟶ y} [IsIso v] (hv : IsVertical p v) :
    IsVertical p (CategoryTheory.inv v) := by
  obtain ⟨h, e⟩ := hv
  refine ⟨h.symm, ?_⟩
  rw [p.map_inv]
  exact IsIso.inv_eq_of_hom_inv_id (by rw [e, eqToHom_trans, eqToHom_refl])

end Tengoku.ObserverEquivarianceLean.IsVertical

/-- The chosen vertical translations `ℓ_{g,x}` of normalized data are vertical
    (paper `def:data` (N5)).
@isnad1 id=isvertic.0h7v.s7.c2d974c784e3 from=translated src=- shape=2e87e5e8 vocab=0736849b
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.ltrans_isVertical (d : OEData G p) (g : G) (x : O) :
    IsVertical p (d.ltrans g x) :=
  ⟨_, d.p_ltrans g x⟩

/-! ## Local helpers about arrows of `S × Pair G` -/

namespace NormalForm

omit [Group G] in
/-- Arrows of `S × Pair G` are determined by their base component (helper for paper
    `thm:normalform`: the pair-groupoid hom-sets are singletons).
@isnad1 id=eq.1h6v.s7.616c059f9895 from=translated src=- shape=f0e02815 vocab=4833e689
-/
theorem prodPairHom_ext {X Y : S × Pair G} {f f' : X ⟶ Y} (h : f.1 = f'.1) : f = f' :=
  Prod.ext h (Subsingleton.elim _ _)

omit [Group G] in
/-- The base component of an `eqToHom` in `S × Pair G` (helper for paper `thm:normalform`).
@isnad1 id=eq.1h4v.s6.f5352d93e046 from=translated src=- shape=98ab9bdc vocab=72d1e657
-/
theorem eqToHom_prod_fst {X Y : S × Pair G} (h : X = Y) :
    (eqToHom h).1 = eqToHom (congrArg Prod.fst h) := by
  subst h; rfl

end NormalForm

open NormalForm

/-! ## The strict normal form for a minimal specification (paper `thm:normalform`) -/

namespace Tengoku.ObserverEquivarianceLean.MinSpec

variable (m : MinSpec G p)

/-- The comparison functor `N : O ⥤ S × Pair G`, `N(x) = (p(x), g_x)`, `N(f) = (p(f), *)`
    (paper `thm:normalform`).-/
def normalFormTo : O ⥤ S × Pair G where
  obj x := (p.obj x, ⟨m.coord x⟩)
  map f := (p.map f, ⟨⟩)
  map_id x := Prod.ext (p.map_id x) (Subsingleton.elim _ _)
  map_comp f g := Prod.ext (p.map_comp f g) (Subsingleton.elim _ _)

/-- (paper `thm:normalform`)
@isnad1 id=eq.0h6v.s6.22b1e479bc72 from=translated src=- shape=35c9e746 vocab=e99b77db
-/
@[simp] theorem normalFormTo_obj (x : O) : m.normalFormTo.obj x = (p.obj x, ⟨m.coord x⟩) := rfl

/-- (paper `thm:normalform`)
@isnad1 id=eq.0h8v.s8.27e97c3d845a from=translated src=- shape=8464122e vocab=f229b693
-/
@[simp] theorem normalFormTo_map {x y : O} (f : x ⟶ y) :
    m.normalFormTo.map f = (p.map f, ⟨⟩) := rfl

/-- The first projection composed with `N` is `p` strictly (paper `thm:normalform`).
@isnad1 id=eq.0h5v.s6.a7294d694dbf from=translated src=- shape=ab250e59 vocab=23c7fd93
-/
theorem normalFormTo_comp_fst : m.normalFormTo ⋙ CategoryTheory.Prod.fst S (Pair G) = p := rfl

/-- `N` sends the basepoint `b_s` to `(s, 1)` (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s6.274379405834 from=translated src=- shape=308315a5 vocab=ebb23249
-/
theorem normalFormTo_obj_base (s : S) : m.normalFormTo.obj (m.base s) = (s, ⟨1⟩) := by
  simp

/-- `N` intertwines the action on objects: `N(x · g) = (p(x), g_x g)` (paper `thm:normalform`).
@isnad1 id=eq.0h7v.s6.37234ddf1b92 from=translated src=- shape=f4ac0424 vocab=795af8b3
-/
theorem normalFormTo_obj_act (x : O) (g : G) :
    m.normalFormTo.obj (m.act x g) = (p.obj x, ⟨m.coord x * g⟩) := by
  simp

/-- The inverse functor `M : S × Pair G ⥤ O`, `M(s,g) = e⁻¹(s,g) = b_s · g`
    (`normalFormFrom_obj`); on arrows `M(u,*)` is the unique arrow `b_s · g ⟶ b_t · h`
    projecting to `u` (paper `thm:normalform`).-/
noncomputable def normalFormFrom : S × Pair G ⥤ O where
  obj X := m.e.symm (X.1, X.2.pt)
  map {X Y} f := m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)
  map_id _ := m.liftOver_id _
  map_comp f g := (m.liftOver_comp f.1 g.1 _ _ _).symm

/-- (paper `thm:normalform`)
@isnad1 id=eq.0h6v.s6.fff23d5681e5 from=translated src=- shape=91fc9b18 vocab=94d89ec6
-/
@[simp] theorem normalFormFrom_obj_eq_e_symm (X : S × Pair G) :
    m.normalFormFrom.obj X = m.e.symm (X.1, X.2.pt) := rfl

/-- `M(s,g) = b_s · g` (paper `thm:normalform`).
@isnad1 id=eq.0h7v.s6.1580882f9b47 from=translated src=- shape=63fb455a vocab=ebcd4660
-/
theorem normalFormFrom_obj (s : S) (g : G) :
    m.normalFormFrom.obj (s, ⟨g⟩) = m.act (m.base s) g :=
  m.e_symm_eq s g

/-- `M` lies over the first projection on objects (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s6.698a52f09dc3 from=translated src=- shape=5b31fc0c vocab=5296ee0f
-/
theorem p_normalFormFrom_obj (X : S × Pair G) : p.obj (m.normalFormFrom.obj X) = X.1 :=
  m.p_e_symm X.1 X.2.pt

/-- The morphism part of `M` is the unique lift of the base component (paper
    `thm:normalform`).
@isnad1 id=eq.0h8v.s8.85fd027ade6d from=translated src=- shape=85ec0727 vocab=b87e8e89
-/
@[simp] theorem normalFormFrom_map {X Y : S × Pair G} (f : X ⟶ Y) :
    m.normalFormFrom.map f = m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt) :=
  rfl

/-- Projection of `M` on arrows (paper `thm:normalform`).
@isnad1 id=eq.0h8v.s9.3f67d7f27790 from=translated src=- shape=27866266 vocab=2ecfdc7b
-/
theorem p_map_normalFormFrom_map {X Y : S × Pair G} (f : X ⟶ Y) :
    p.map (m.normalFormFrom.map f)
      = eqToHom (m.p_e_symm X.1 X.2.pt) ≫ f.1 ≫ eqToHom (m.p_e_symm Y.1 Y.2.pt).symm :=
  m.p_map_liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)

/-- Uniqueness: any arrow `M(X) ⟶ M(Y)` projecting to the base component of `f` equals
    `M(f)` (paper `thm:normalform`).
@isnad1 id=eq.1h9v.s9.f86235a8acd8 from=translated src=- shape=51305e2c vocab=2ecfdc7b
-/
theorem normalFormFrom_map_unique {X Y : S × Pair G} (f : X ⟶ Y)
    (φ : m.normalFormFrom.obj X ⟶ m.normalFormFrom.obj Y)
    (hφ : p.map φ
      = eqToHom (m.p_e_symm X.1 X.2.pt) ≫ f.1 ≫ eqToHom (m.p_e_symm Y.1 Y.2.pt).symm) :
    φ = m.normalFormFrom.map f :=
  (m.eq_liftOver_iff f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt) φ).2 hφ

/-- Strict inverse, first half: `N ⋙ M = 𝟭 O` as functors, i.e. on objects AND arrows
    (paper `thm:normalform`, `MN = id_O`).
@isnad1 id=eq.0h5v.s6.7b77fccb308f from=translated src=- shape=efa19d5e vocab=3ee98587
-/
theorem normalFormTo_comp_normalFormFrom : m.normalFormTo ⋙ m.normalFormFrom = 𝟭 O := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact m.e_symm_p_coord x
  · intro x y f
    have key : m.liftOver (p.map f) (m.p_e_symm (p.obj x) (m.coord x))
          (m.p_e_symm (p.obj y) (m.coord y))
        = eqToHom (m.e_symm_p_coord x) ≫ f ≫ eqToHom (m.e_symm_p_coord y).symm := by
      apply m.hom_ext
      simp [eqToHom_map]
    exact key

/-- Strict inverse, second half: `M ⋙ N = 𝟭 (S × Pair G)` as functors, i.e. on objects AND
    arrows (paper `thm:normalform`, `NM = id`).
@isnad1 id=eq.0h5v.s6.6e6de70047a9 from=translated src=- shape=db2065ca vocab=3ee98587
-/
theorem normalFormFrom_comp_normalFormTo :
    m.normalFormFrom ⋙ m.normalFormTo = 𝟭 (S × Pair G) := by
  have hobj : ∀ X : S × Pair G,
      ((p.obj (m.e.symm (X.1, X.2.pt)), ⟨m.coord (m.e.symm (X.1, X.2.pt))⟩) : S × Pair G) = X := by
    rintro ⟨s, ⟨g⟩⟩; simp
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro X Y f
    have key : ((p.map (m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)), ⟨⟩) :
          ((p.obj (m.e.symm (X.1, X.2.pt)), ⟨m.coord (m.e.symm (X.1, X.2.pt))⟩) : S × Pair G) ⟶
          (p.obj (m.e.symm (Y.1, Y.2.pt)), ⟨m.coord (m.e.symm (Y.1, Y.2.pt))⟩))
        = eqToHom (hobj X) ≫ f ≫ eqToHom (hobj Y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, p_map_liftOver]
    exact key

/-- `N` intertwines the right `G`-actions strictly:
    `R_g ⋙ N = N ⋙ ((s,a) ↦ (s, a g))` (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s7.2d1125c805ca from=translated src=- shape=c0064105 vocab=25df97d7
-/
theorem normalForm_equivariant (g : G) :
    m.actFunctor g ⋙ m.normalFormTo = m.normalFormTo ⋙ normalFormProductAction g := by
  have hobj : ∀ x : O,
      ((p.obj (m.act x g), ⟨m.coord (m.act x g)⟩) : S × Pair G) = (p.obj x, ⟨m.coord x * g⟩) :=
    fun x => by simp
  fapply CategoryTheory.Functor.ext
  · exact hobj
  · intro x y f
    have key : ((p.map (m.liftOver (p.map f) (m.p_act x g) (m.p_act y g)), ⟨⟩) :
          ((p.obj (m.act x g), ⟨m.coord (m.act x g)⟩) : S × Pair G) ⟶
            (p.obj (m.act y g), ⟨m.coord (m.act y g)⟩))
        = eqToHom (hobj x) ≫
          ((p.map f, ⟨⟩) : ((p.obj x, ⟨m.coord x * g⟩) : S × Pair G) ⟶
            (p.obj y, ⟨m.coord y * g⟩)) ≫ eqToHom (hobj y).symm := by
      apply prodPairHom_ext
      simp only [prod_comp_fst, eqToHom_prod_fst, p_map_liftOver]
    exact key

/-- `M` intertwines the right `G`-actions strictly:
    `((s,a) ↦ (s, a g)) ⋙ M = M ⋙ R_g` (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s7.cfa7d2617ee3 from=translated src=- shape=b00a91fe vocab=ad055623
-/
theorem normalFormFrom_equivariant (g : G) :
    normalFormProductAction g ⋙ m.normalFormFrom = m.normalFormFrom ⋙ m.actFunctor g := by
  fapply CategoryTheory.Functor.ext
  · intro X; exact (m.act_e_symm X.1 X.2.pt g).symm
  · intro X Y f
    have key : m.liftOver f.1 (m.p_e_symm X.1 (X.2.pt * g)) (m.p_e_symm Y.1 (Y.2.pt * g))
        = eqToHom (m.act_e_symm X.1 X.2.pt g).symm
          ≫ m.liftOver (p.map (m.liftOver f.1 (m.p_e_symm X.1 X.2.pt) (m.p_e_symm Y.1 Y.2.pt)))
              (m.p_act _ g) (m.p_act _ g)
          ≫ eqToHom (m.act_e_symm Y.1 Y.2.pt g) := by
      apply m.hom_ext
      simp
    exact key

/-- The strict isomorphism of categories `N`, `M` packaged as an equivalence whose unit and
    counit are `eqToIso`s of the strict functor equalities (paper `thm:normalform`).-/
noncomputable def normalFormEquivalence : O ≌ S × Pair G :=
  CategoryTheory.Equivalence.mk m.normalFormTo m.normalFormFrom
    (eqToIso m.normalFormTo_comp_normalFormFrom.symm) (eqToIso m.normalFormFrom_comp_normalFormTo)

/-- (paper `thm:normalform`)
@isnad1 id=eq.0h5v.s6.fb96cc189d0c from=translated src=- shape=8feaea2c vocab=0385fe61
-/
@[simp] theorem normalFormEquivalence_functor : m.normalFormEquivalence.functor = m.normalFormTo :=
  rfl

/-- (paper `thm:normalform`)
@isnad1 id=eq.0h5v.s6.be59acf2ad9e from=translated src=- shape=3252225e vocab=4fcd6e52
-/
@[simp] theorem normalFormEquivalence_inverse :
    m.normalFormEquivalence.inverse = m.normalFormFrom := rfl

/-- `M` lies over `S` strictly: `M ⋙ p = Prod.fst` as functors, on objects AND arrows (paper
    `thm:normalform`, "an isomorphism of categories over `S`"; the other half,
    `N ⋙ Prod.fst = p`, is `normalFormTo_comp_fst`).
@isnad1 id=eq.0h5v.s6.23060bfb6a58 from=translated src=- shape=70f3242c vocab=28ee6ccb
-/
theorem normalFormFrom_comp_fst :
    m.normalFormFrom ⋙ p = CategoryTheory.Prod.fst S (Pair G) :=
  calc m.normalFormFrom ⋙ p
      = m.normalFormFrom ⋙ (m.normalFormTo ⋙ CategoryTheory.Prod.fst S (Pair G)) := rfl
    _ = CategoryTheory.Prod.fst S (Pair G) := by
        rw [← Functor.assoc, m.normalFormFrom_comp_normalFormTo]; rfl

end Tengoku.ObserverEquivarianceLean.MinSpec

/-! ## Strict sections (paper `cor:section`) -/

/-- A strict section of `p` in the sense of paper `cor:section`: a functor `B : S ⥤ O` with the
    STRICT section equation `B ⋙ p = 𝟭 S` (paper `pB = id_S`) and a natural isomorphism
    `η : p ⋙ B ≅ 𝟭 O` (paper `η : Bp ⇒ id_O`) whose components are vertical.  Only the
    composite `B ⋙ p` is required to be an identity on the nose; `p ⋙ B` is only isomorphic
    to `𝟭 O` (it is not equal to it for nontrivial `G`, see `MinSpec.no_strict_retraction`).-/
structure _root_.Tengoku.ObserverEquivarianceLean.StrictSection (p : O ⥤ S) where
  /-- The section functor `B` (paper `cor:section`).-/
  B : S ⥤ O
  /-- The strict section equation `pB = id_S` (paper `cor:section`).-/
  B_comp_p : B ⋙ p = 𝟭 S
  /-- The comparison `η : Bp ≅ id_O` (paper `cor:section`).-/
  η : p ⋙ B ≅ 𝟭 O
  /-- The components of `η` are vertical (paper `cor:section`).-/
  η_vertical : ∀ x, IsVertical p (η.hom.app x)

namespace Tengoku.ObserverEquivarianceLean.StrictSection

variable (σ : StrictSection p)

/-- `B(s)` lies over `s` (paper `cor:section`).
@isnad1 id=eq.0h5v.s5.174aea45d12d from=translated src=- shape=7666e6d1 vocab=acf53a9d
-/
theorem p_obj_B (s : S) : p.obj (σ.B.obj s) = s :=
  Functor.congr_obj σ.B_comp_p s

/-- `B(u)` lies over `u` (paper `cor:section`).
@isnad1 id=eq.0h7v.s7.41803924254c from=translated src=- shape=caa45285 vocab=d929dd13
-/
theorem p_map_B_map {s t : S} (u : s ⟶ t) :
    p.map (σ.B.map u) = eqToHom (σ.p_obj_B s) ≫ u ≫ eqToHom (σ.p_obj_B t).symm := by
  have h := Functor.congr_hom σ.B_comp_p u
  exact h

/-- The inverse components of `η` are vertical (paper `cor:section`).
@isnad1 id=isvertic.0h5v.s6.f0908101b72b from=translated src=- shape=21f0d1f3 vocab=b5e6f712
-/
theorem η_inv_vertical (x : O) : IsVertical p (σ.η.inv.app x) := by
  have e : σ.η.inv.app x = CategoryTheory.inv (σ.η.hom.app x) :=
    (IsIso.inv_eq_of_hom_inv_id (σ.η.hom_inv_id_app x)).symm
  rw [e]
  exact (σ.η_vertical x).inv

/-- A vertical arrow between any two objects of one fiber, `η_x⁻¹ ≫ B(eqToHom) ≫ η_y`
    (paper `def:vertical-trivial`: "every pair of objects in one fiber is connected by a
    vertical isomorphism").-/
noncomputable def fiberHom {x y : O} (h : p.obj x = p.obj y) : x ⟶ y :=
  σ.η.inv.app x ≫ eqToHom (congrArg σ.B.obj h) ≫ σ.η.hom.app y

/-- The fiber arrow `σ.fiberHom h` is vertical (paper `def:vertical-trivial`).
@isnad1 id=isvertic.1h6v.s5.00fa45e98b05 from=translated src=- shape=196eda0b vocab=f301dde7
-/
theorem fiberHom_isVertical {x y : O} (h : p.obj x = p.obj y) : IsVertical p (σ.fiberHom h) :=
  (σ.η_inv_vertical x).comp ((IsVertical.eqToHom p _).comp (σ.η_vertical y))

/-- A strict section exhibits `p` as an equivalence of categories, with inverse `B`
    (paper `cor:section`: "Hence `p` is an equivalence of categories").-/
noncomputable def equivalence : O ≌ S :=
  CategoryTheory.Equivalence.mk p σ.B σ.η.symm (eqToIso σ.B_comp_p)

/-- (paper `cor:section`)
@isnad1 id=eq.0h4v.s5.2399864be793 from=translated src=- shape=9c802274 vocab=151b9b6b
-/
@[simp] theorem equivalence_functor : σ.equivalence.functor = p := rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h4v.s5.17e9226c6965 from=translated src=- shape=57e429ba vocab=9c40e198
-/
@[simp] theorem equivalence_inverse : σ.equivalence.inverse = σ.B := rfl

end Tengoku.ObserverEquivarianceLean.StrictSection

/-! ## The section of a minimal specification (paper `cor:section`, `rem:groupoid`) -/

namespace Tengoku.ObserverEquivarianceLean.MinSpec

variable (m : MinSpec G p)

/-- The section `B : S ⥤ O`, `B(s) = b_s`, `B(u)` the unique lift `b_s ⟶ b_t` of `u`
    (paper `cor:section`).-/
noncomputable def sectionFunctor : S ⥤ O where
  obj s := m.base s
  map {s t} u := m.liftOver u (m.p_base s) (m.p_base t)
  map_id _ := m.liftOver_id _
  map_comp u v := (m.liftOver_comp u v _ _ _).symm

/-- (paper `cor:section`)
@isnad1 id=eq.0h6v.s5.7aa473d76375 from=translated src=- shape=409bdd5b vocab=646ad84d
-/
@[simp] theorem sectionFunctor_obj (s : S) : m.sectionFunctor.obj s = m.base s := rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h8v.s7.4341a28376d3 from=translated src=- shape=2c7a5ed9 vocab=e7c9d83f
-/
@[simp] theorem sectionFunctor_map {s t : S} (u : s ⟶ t) :
    m.sectionFunctor.map u = m.liftOver u (m.p_base s) (m.p_base t) := rfl

/-- The strict section equation `B ⋙ p = 𝟭 S` (paper `cor:section`).
@isnad1 id=eq.0h5v.s5.84064c460833 from=translated src=- shape=e7fd3ca2 vocab=ec6b8f8a
-/
theorem sectionFunctor_comp_p : m.sectionFunctor ⋙ p = 𝟭 S := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact m.p_base s
  · intro s t u; exact m.p_map_liftOver u (m.p_base s) (m.p_base t)

/-- `B(u)` is the unique lift of `u` between the basepoints (paper `cor:section`).
@isnad1 id=eq.1h9v.s8.89bfaf2d0809 from=translated src=- shape=0b01dc4e vocab=21c536e7
-/
theorem sectionFunctor_map_unique {s t : S} (u : s ⟶ t) (f : m.base s ⟶ m.base t)
    (hf : p.map f = eqToHom (m.p_base s) ≫ u ≫ eqToHom (m.p_base t).symm) :
    f = m.sectionFunctor.map u :=
  (m.eq_liftOver_iff u (m.p_base s) (m.p_base t) f).2 hf

/-- Unique lifts of identities are vertical (paper `def:vertical-trivial`, `cor:section`).
@isnad1 id=isvertic.2h8v.s6.076f89656c22 from=translated src=- shape=1d8a3162 vocab=9474f7a6
-/
theorem liftOver_id_isVertical {s : S} {x y : O} (hx : p.obj x = s) (hy : p.obj y = s) :
    IsVertical p (m.liftOver (𝟙 s) hx hy) :=
  ⟨hx.trans hy.symm, by simp⟩

/-- The unique vertical arrow between two objects of one fiber (paper `cor:section`,
    `def:vertical-trivial`).-/
noncomputable def verticalHom {x y : O} (h : p.obj x = p.obj y) : x ⟶ y :=
  m.liftOver (𝟙 (p.obj y)) h rfl

/-- (paper `def:vertical-trivial`)
@isnad1 id=isvertic.1h7v.s6.6557e55a831e from=translated src=- shape=5b030262 vocab=94faacdf
-/
theorem verticalHom_isVertical {x y : O} (h : p.obj x = p.obj y) :
    IsVertical p (m.verticalHom h) :=
  m.liftOver_id_isVertical h rfl

/-- Every vertical arrow is the unique vertical arrow between its endpoints
    (paper `def:vertical-trivial`, uniqueness of lifts).-/
theorem eq_verticalHom_of_isVertical {x y : O} {v : x ⟶ y} (hv : IsVertical p v) :
    ∃ h : p.obj x = p.obj y, v = m.verticalHom h := by
  obtain ⟨h, e⟩ := hv
  exact ⟨h, (m.eq_liftOver_iff (𝟙 (p.obj y)) h rfl v).2 (by simp [e])⟩

/-- The vertical comparison `η : p ⋙ B ≅ 𝟭 O`, `η_x : b_{p x} ⟶ x` the unique vertical lift
    (paper `cor:section`).-/
noncomputable def sectionEta : p ⋙ m.sectionFunctor ≅ 𝟭 O :=
  NatIso.ofComponents
    (fun x => m.liftOverIso (Iso.refl (p.obj x)) (m.p_base (p.obj x)) rfl)
    (fun {x y} f => by
      have key : m.liftOver (p.map f) (m.p_base (p.obj x)) (m.p_base (p.obj y))
            ≫ m.liftOver (𝟙 (p.obj y)) (m.p_base (p.obj y)) rfl
          = m.liftOver (𝟙 (p.obj x)) (m.p_base (p.obj x)) rfl ≫ f := by
        apply m.hom_ext; simp
      exact key)

/-- (paper `cor:section`)
@isnad1 id=eq.0h6v.s7.992b110a8cc1 from=translated src=- shape=2561dd11 vocab=9131aef6
-/
@[simp] theorem sectionEta_hom_app (x : O) :
    m.sectionEta.hom.app x = m.liftOver (𝟙 (p.obj x)) (m.p_base (p.obj x)) rfl := rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h6v.s7.fe7167ac79c8 from=translated src=- shape=bf26ab43 vocab=e85eabf5
-/
@[simp] theorem sectionEta_inv_app (x : O) :
    m.sectionEta.inv.app x = m.liftOver (𝟙 (p.obj x)) rfl (m.p_base (p.obj x)) := rfl

/-- The strict section of a minimal specification: `B(s) = b_s`, `B(u)` the unique lift,
    `η` the unique vertical lifts (paper `cor:section`).-/
noncomputable def strictSection : StrictSection p where
  B := m.sectionFunctor
  B_comp_p := m.sectionFunctor_comp_p
  η := m.sectionEta
  η_vertical x := m.liftOver_id_isVertical (m.p_base (p.obj x)) rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h5v.s5.3e215461eb99 from=translated src=- shape=ef68e8dc vocab=153ad4eb
-/
@[simp] theorem strictSection_B : m.strictSection.B = m.sectionFunctor := rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h5v.s6.1a847d6413e9 from=translated src=- shape=f402b03c vocab=8b3fce57
-/
@[simp] theorem strictSection_η : m.strictSection.η = m.sectionEta := rfl

/-- `p` is NOT a strict isomorphism of categories in general: if `G` is nontrivial and `S` is
    nonempty, no functor `B'` satisfies `p ⋙ B' = 𝟭 O` (paper `cor:section`, which only
    asserts the strict equation `pB = id` and a natural isomorphism `Bp ≅ id`).
@isnad1 id=not.0h5v.s6.8b48f12a4832 from=translated src=- shape=013a46a9 vocab=f0e6126b
-/
theorem no_strict_retraction (m : MinSpec G p) [Nontrivial G] [Nonempty S] :
    ¬ ∃ B' : S ⥤ O, p ⋙ B' = 𝟭 O := by
  rintro ⟨B', hB'⟩
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  obtain ⟨g, hg⟩ := exists_ne (1 : G)
  have h1 : B'.obj (p.obj (m.base s)) = m.base s := Functor.congr_obj hB' (m.base s)
  have h2 : B'.obj (p.obj (m.act (m.base s) g)) = m.act (m.base s) g :=
    Functor.congr_obj hB' (m.act (m.base s) g)
  have hp : p.obj (m.act (m.base s) g) = p.obj (m.base s) := m.p_act _ _
  rw [hp, h1] at h2
  have := congrArg m.coord h2
  simp at this
  exact hg this.symm

/-- Groupoid specialization, first half (paper `rem:groupoid`), for a minimal specification:
    if every arrow of `O` is invertible, so is every arrow of `S`.
@isnad1 id=isiso.1h8v.s6.d7f39f450a38 from=translated src=- shape=d09a3c60 vocab=3b028195
-/
theorem base_hom_isIso (m : MinSpec G p) (hO : ∀ {x y : O} (f : x ⟶ y), IsIso f)
    {s t : S} (u : s ⟶ t) :
    IsIso u := by
  have hf := m.p_map_liftOver u (m.p_base s) (m.p_base t)
  haveI : IsIso (m.liftOver u (m.p_base s) (m.p_base t)) := hO _
  have hu : u = eqToHom (m.p_base s).symm ≫ p.map (m.liftOver u (m.p_base s) (m.p_base t))
      ≫ eqToHom (m.p_base t) := by
    rw [hf]; simp
  rw [hu]
  infer_instance

/-- Groupoid specialization, converse half (paper `rem:groupoid`), for a minimal
    specification: if every arrow of `S` is invertible, so is every arrow of `O`.
@isnad1 id=isiso.1h8v.s6.e4bc083a699c from=translated src=- shape=6f396791 vocab=3b028195
-/
theorem hom_isIso_of_base_isIso (m : MinSpec G p) (hS : ∀ {s t : S} (u : s ⟶ t), IsIso u)
    {x y : O} (f : x ⟶ y) :
    IsIso f := by
  haveI := m.full
  haveI := m.faithful
  haveI : IsIso (p.map f) := hS _
  exact isIso_of_reflects_iso f p

end Tengoku.ObserverEquivarianceLean.MinSpec

/-! ## The normal form for normalized data (paper `thm:normalform`) -/

/-- Core's comparison functor `normalFormTo d` is the `N` of the underlying minimal
    specification (paper `thm:normalform`, `rem:audit`).
@isnad1 id=eq.0h5v.s6.978d023762c4 from=translated src=- shape=81f77196 vocab=f4402ffb
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_eq_toMinSpec (d : OEData G p) :
    normalFormTo d = d.toMinSpec.normalFormTo := rfl

/-- The inverse functor `M : S × Pair G ⥤ O` of normalized data: `M(s,g) = b_s · g`
    DEFINITIONALLY, and `M(u,*)` is the unique lift of `u` (paper `thm:normalform`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom (d : OEData G p) : S × Pair G ⥤ O :=
  d.toMinSpec.normalFormFrom

/-- `M(s,g) = b_s · g`, definitionally (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s6.ffc5a045e9b3 from=translated src=- shape=bbdb0c61 vocab=945d065c
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_obj (d : OEData G p) (X : S × Pair G) :
    (normalFormFrom d).obj X = d.act (d.base X.1) X.2.pt := rfl

/-- `M` lies over the first projection on objects (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s6.13decad9b0e7 from=translated src=- shape=5b31fc0c vocab=e28b7946
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.p_normalFormFrom_obj (d : OEData G p) (X : S × Pair G) :
    p.obj ((normalFormFrom d).obj X) = X.1 :=
  (d.p_act _ _).trans (d.p_base _)

/-- The morphism part of `M` is the unique lift of the base component (paper
    `thm:normalform`).
@isnad1 id=eq.0h8v.s8.b2d4008c15fd from=translated src=- shape=4e6f3a14 vocab=c6008103
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_map (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y) :
    (normalFormFrom d).map f
      = d.toMinSpec.liftOver f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)) := rfl

/-- Projection of `M` on arrows (paper `thm:normalform`).
@isnad1 id=eq.0h8v.s9.6020a39b9ccd from=translated src=- shape=ead2b513 vocab=a709871f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.p_map_normalFormFrom_map (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y) :
    p.map ((normalFormFrom d).map f)
      = eqToHom ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ≫ f.1
        ≫ eqToHom ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)).symm :=
  d.toMinSpec.p_map_liftOver f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1))
    ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1))

/-- Uniqueness: the morphism part of `M` is the unique arrow with the given endpoints over the
    base component (paper `thm:normalform`).
@isnad1 id=eq.1h9v.s9.0eaaf50a3a1d from=translated src=- shape=6cdeb7da vocab=a709871f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_map_unique (d : OEData G p) {X Y : S × Pair G} (f : X ⟶ Y)
    (φ : (normalFormFrom d).obj X ⟶ (normalFormFrom d).obj Y)
    (hφ : p.map φ
      = eqToHom ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ≫ f.1 ≫ eqToHom ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)).symm) :
    φ = (normalFormFrom d).map f :=
  (d.toMinSpec.eq_liftOver_iff f.1 ((d.p_act (d.base X.1) X.2.pt).trans (d.p_base X.1)) ((d.p_act (d.base Y.1) Y.2.pt).trans (d.p_base Y.1)) φ).2 hφ

/-- Strict inverse, first half: `N ⋙ M = 𝟭 O` (paper `thm:normalform`).
@isnad1 id=eq.0h5v.s6.71a1946a1234 from=translated src=- shape=efa19d5e vocab=21b93617
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_comp_normalFormFrom (d : OEData G p) :
    normalFormTo d ⋙ normalFormFrom d = 𝟭 O :=
  d.toMinSpec.normalFormTo_comp_normalFormFrom

/-- Strict inverse, second half: `M ⋙ N = 𝟭 (S × Pair G)` (paper `thm:normalform`).
@isnad1 id=eq.0h5v.s6.0d1cd1ae711d from=translated src=- shape=db2065ca vocab=21b93617
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_comp_normalFormTo (d : OEData G p) :
    normalFormFrom d ⋙ normalFormTo d = 𝟭 (S × Pair G) :=
  d.toMinSpec.normalFormFrom_comp_normalFormTo

/-- `M` lies over `S` strictly for normalized data: `normalFormFrom d ⋙ p = Prod.fst` as
    functors, on objects AND arrows (paper `thm:normalform`, "an isomorphism of categories over
    `S`"; the other half, `normalFormTo d ⋙ Prod.fst = p`, is `normalFormTo_fst` in `Core`).
@isnad1 id=eq.0h5v.s6.7de5b7d4c6cb from=translated src=- shape=70f3242c vocab=41a83217
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_comp_fst (d : OEData G p) :
    normalFormFrom d ⋙ p = CategoryTheory.Prod.fst S (Pair G) :=
  d.toMinSpec.normalFormFrom_comp_fst

/-- `M` intertwines the right `G`-actions strictly (paper `thm:normalform`).
@isnad1 id=eq.0h6v.s7.cbf67de283f3 from=translated src=- shape=b00a91fe vocab=bbaa4292
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormFrom_equivariant (d : OEData G p) (g : G) :
    normalFormProductAction g ⋙ normalFormFrom d = normalFormFrom d ⋙ d.actFunctor g := by
  rw [← d.toMinSpec_actFunctor]
  exact d.toMinSpec.normalFormFrom_equivariant g

/-- `N` sends reindexing to `(t,g) ↦ (s,g)` on arrows: `N(χ_{u,y})` is the arrow
    `(u, *) : (s, g_y) ⟶ (t, g_y)`, up to the endpoint identifications
    `normalForm_reind` and `t = p(y)` (paper `thm:normalform`).
@isnad1 id=eq.1h9v.s9.e692d0449435 from=translated src=- shape=bb4312d0 vocab=d851bc8d
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_map_chi (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O)
    (hy : p.obj y = t) :
    (normalFormTo d).map (d.chi u y hy)
      = eqToHom (normalForm_reind d u y hy)
        ≫ ((u, ⟨⟩) : ((s, ⟨d.coord y⟩) : S × Pair G) ⟶ (t, ⟨d.coord y⟩))
        ≫ eqToHom (Prod.ext hy.symm rfl : ((t, ⟨d.coord y⟩) : S × Pair G) = (normalFormTo d).obj y) := by
  apply prodPairHom_ext
  simp only [normalFormTo_map, prod_comp_fst, eqToHom_prod_fst, d.p_chi]
  rfl

/-! ## The section of normalized data (paper `cor:section`) -/

namespace Tengoku.ObserverEquivarianceLean.OEData

variable (d : OEData G p)

/-- The section `B : S ⥤ O` of normalized data: `B(s) = b_s` DEFINITIONALLY, and `B(u)` is the
    unique lift `b_s ⟶ b_t` of `u` (paper `cor:section`).-/
noncomputable def sectionFunctor : S ⥤ O where
  obj s := d.base s
  map {s t} u := d.toMinSpec.liftOver u (d.p_base s) (d.p_base t)
  map_id _ := d.toMinSpec.liftOver_id _
  map_comp u v := (d.toMinSpec.liftOver_comp u v _ _ _).symm

/-- `B(s) = b_s` (definitional; paper `cor:section`).
@isnad1 id=eq.0h6v.s6.2acea8dfc341 from=translated src=- shape=26b8bb67 vocab=fc6a0cbb
-/
@[simp] theorem sectionFunctor_obj (s : S) : d.sectionFunctor.obj s = d.base s := rfl

/-- `B(u)` is the unique lift (definitional; paper `cor:section`).
@isnad1 id=eq.0h8v.s7.4cd5c3c892cc from=translated src=- shape=00b53932 vocab=5c4f9832
-/
theorem sectionFunctor_map {s t : S} (u : s ⟶ t) :
    d.sectionFunctor.map u = d.toMinSpec.liftOver u (d.p_base s) (d.p_base t) := rfl

/-- `B(u)` lies over `u` (paper `cor:section`).
@isnad1 id=eq.0h8v.s8.6ecc6985fa4e from=translated src=- shape=9c7011cd vocab=38bbfe5c
-/
@[simp] theorem p_map_sectionFunctor_map {s t : S} (u : s ⟶ t) :
    p.map (d.sectionFunctor.map u) = eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm :=
  d.toMinSpec.p_map_liftOver u (d.p_base s) (d.p_base t)

/-- The strict section equation `B ⋙ p = 𝟭 S` (paper `cor:section`).
@isnad1 id=eq.0h5v.s5.054326f2e4b8 from=translated src=- shape=e7fd3ca2 vocab=ee5943c5
-/
theorem sectionFunctor_comp_p : d.sectionFunctor ⋙ p = 𝟭 S := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact d.p_base s
  · intro s t u; exact d.p_map_sectionFunctor_map u

/-- `B(u)` is the unique arrow `b_s ⟶ b_t` over `u` (paper `cor:section`).
@isnad1 id=eq.1h9v.s8.289fb773d27f from=translated src=- shape=82f5d98c vocab=38bbfe5c
-/
theorem sectionFunctor_map_unique {s t : S} (u : s ⟶ t) (f : d.base s ⟶ d.base t)
    (hf : p.map f = eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm) :
    f = d.sectionFunctor.map u :=
  (d.toMinSpec.eq_liftOver_iff u (d.p_base s) (d.p_base t) f).2 hf

/-- For normalized data `B(u) = χ_{u,b_t}`, with the source rewritten by (N4)
    `u^* b_t = b_s` (paper `cor:section`).
@isnad1 id=eq.0h8v.s8.c90de05da7ed from=translated src=- shape=d52f4122 vocab=daa0b6ed
-/
theorem sectionFunctor_map_eq_chi {s t : S} (u : s ⟶ t) :
    d.sectionFunctor.map u = eqToHom (d.reind_base u).symm ≫ d.chi u (d.base t) (d.p_base t) := by
  symm
  apply d.sectionFunctor_map_unique
  simp [d.p_chi, eqToHom_map]

/-- The section of normalized data agrees with the section of its minimal specification
    (paper `cor:section`, `rem:audit`).
@isnad1 id=eq.0h5v.s5.99b2f275dd4f from=translated src=- shape=0e907da4 vocab=88769740
-/
theorem toMinSpec_sectionFunctor : d.toMinSpec.sectionFunctor = d.sectionFunctor := by
  fapply CategoryTheory.Functor.ext
  · intro s; exact d.toMinSpec_base s
  · intro s t u
    have key : d.toMinSpec.liftOver u (d.toMinSpec.p_base s) (d.toMinSpec.p_base t)
        = eqToHom (d.toMinSpec_base s) ≫ d.toMinSpec.liftOver u (d.p_base s) (d.p_base t)
          ≫ eqToHom (d.toMinSpec_base t).symm := by
      apply d.toMinSpec.hom_ext
      simp
    exact key

/-- The target of `ℓ_{g_x, b_{p x}}` is `x`, by (N2) (paper `cor:section`).
@isnad1 id=eq.0h6v.s7.954eb769a443 from=translated src=- shape=1d6ebb20 vocab=2b98a454
-/
theorem sectionEta_target_eq (x : O) :
    d.act (d.base (p.obj (d.base (p.obj x)))) (d.coord x * d.coord (d.base (p.obj x))) = x := by
  have hc : d.coord (d.base (p.obj x)) = 1 := by
    have := d.coord_base (p.obj x) 1; rwa [d.act_one] at this
  rw [hc, mul_one, d.p_base, d.base_coord]

/-- Naturality of `η` in clean endpoints: `B(p f) ≫ η_y = η_x ≫ f` (paper `cor:section`:
    both sides have the same endpoints and projection).
@isnad1 id=eq.0h8v.s9.899461950caf from=translated src=- shape=d984d6dc vocab=3ea1fc0d
-/
theorem sectionEta_naturality {x y : O} (f : x ⟶ y) :
    d.toMinSpec.liftOver (p.map f) (d.p_base (p.obj x)) (d.p_base (p.obj y))
        ≫ d.ltrans (d.coord y) (d.base (p.obj y)) ≫ eqToHom (d.sectionEta_target_eq y)
      = (d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x)) ≫ f := by
  apply d.toMinSpec.hom_ext
  simp [d.p_ltrans, eqToHom_map]

/-- The vertical comparison `η : p ⋙ B ≅ 𝟭 O` of normalized data, with components
    `η_x = ℓ_{g_x, b_{p x}}` followed by the (N2) identification of the target
    (paper `cor:section`).-/
noncomputable def sectionEta : p ⋙ d.sectionFunctor ≅ 𝟭 O :=
  NatIso.ofComponents
    (fun x => d.ltransIso (d.coord x) (d.base (p.obj x)) ≪≫ eqToIso (d.sectionEta_target_eq x))
    (fun f => d.sectionEta_naturality f)

/-- `η_x = ℓ_{g_x, b_{p x}}` up to the target identification (paper `cor:section`).
@isnad1 id=eq.0h6v.s9.b790f3f9c2d9 from=translated src=- shape=f4cc191d vocab=8cbf2182
-/
@[simp] theorem sectionEta_hom_app (x : O) :
    d.sectionEta.hom.app x
      = d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x) := rfl

/-- The components of `η` are vertical (paper `cor:section`).
@isnad1 id=isvertic.0h6v.s7.1cfa28dc3a61 from=translated src=- shape=bf65b8c1 vocab=aacfbca5
-/
theorem sectionEta_isVertical (x : O) : IsVertical p (d.sectionEta.hom.app x) := by
  have key : p.map (d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x))
      = eqToHom (d.p_base (p.obj x)) := by
    simp only [Functor.map_comp, d.p_ltrans, eqToHom_map, eqToHom_trans]
  exact ⟨d.p_base (p.obj x), key⟩

/-- `η_x` is the unique vertical arrow `b_{p x} ⟶ x` (paper `cor:section`).
@isnad1 id=eq.0h6v.s7.015d1cf57605 from=translated src=- shape=5cdd3c3f vocab=ef77c45b
-/
theorem sectionEta_hom_app_eq_liftOver (x : O) :
    d.sectionEta.hom.app x = d.toMinSpec.liftOver (𝟙 (p.obj x)) (d.p_base (p.obj x)) rfl := by
  have key : d.ltrans (d.coord x) (d.base (p.obj x)) ≫ eqToHom (d.sectionEta_target_eq x)
      = d.toMinSpec.liftOver (𝟙 (p.obj x)) (d.p_base (p.obj x)) rfl := by
    apply d.toMinSpec.hom_ext
    simp only [Functor.map_comp, d.p_ltrans, eqToHom_map, eqToHom_trans, MinSpec.p_map_liftOver,
      Category.id_comp]
  exact key

/-- The strict section of normalized data: `B = d.sectionFunctor` (`B(s) = b_s`
    definitionally), `η_x = ℓ_{g_x, b_{p x}}` (paper `cor:section`).-/
noncomputable def strictSection : StrictSection p where
  B := d.sectionFunctor
  B_comp_p := d.sectionFunctor_comp_p
  η := d.sectionEta
  η_vertical := d.sectionEta_isVertical

/-- (paper `cor:section`)
@isnad1 id=eq.0h5v.s5.57c065cf2b51 from=translated src=- shape=ef68e8dc vocab=890ea29c
-/
@[simp] theorem strictSection_B : d.strictSection.B = d.sectionFunctor := rfl

/-- (paper `cor:section`)
@isnad1 id=eq.0h5v.s6.7e5537415535 from=translated src=- shape=f402b03c vocab=a37ec67d
-/
@[simp] theorem strictSection_η : d.strictSection.η = d.sectionEta := rfl

end Tengoku.ObserverEquivarianceLean.OEData
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
