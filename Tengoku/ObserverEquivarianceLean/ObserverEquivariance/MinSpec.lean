import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The minimal specification (paper `rem:audit`, forward part)

Paper `rem:audit`: specifying a normalized presentation datum for `p : O ⥤ S` is equivalent to
requiring that `p` be fully faithful and specifying a bijection `Ob O ≅ Ob S × G` whose first
component is `Ob p`.

This file sets up
* the structure `MinSpec G p` (full and faithful `p`, and the based object trivialization
  `e : O ≃ S × G` with `(e x).1 = p.obj x`);
* the coordinate API derived from `e` (basepoints `b_s`, coordinates `g_x`, the right action
  `x · g` on objects, and the coordinate identities of paper `lem:coordinates`);
* the unique-lift API (`MinSpec.liftOver`): for prescribed endpoints, an arrow of `O` is
  determined uniquely by its projection (paper `prop:fullness` and the remark after it);
* the forward map `OEData.toMinSpec` (paper `rem:audit`: fullness is `prop:fullness`, the
  bijection is `x ↦ (p(x), g_x)` from (N1)–(N2));
* the right action by functors `MinSpec.actFunctor`, whose arrows are unique lifts.

The converse direction and the round trips live in `MinSpecCorrespondence.lean`.

## Simp normal form

`MinSpec.act`, `MinSpec.base`, `MinSpec.coord` are irreducible-by-simp definitions; the simp set
computes `p.obj` and `coord` of `act` / `base` / `e.symm` terms, and collapses composites of
unique lifts.  `MinSpec.e_symm_eq` (rewriting `e.symm` into `act`/`base`) is deliberately NOT a
simp lemma (it would loop against an unfolded `act`).
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-- The minimal specification of paper `rem:audit`: the projection `p` is full and faithful,
    and `e : Ob O ≃ Ob S × G` is a bijection whose first component is `Ob p`.
    Fullness is a HYPOTHESIS here, whereas for `OEData` it is derived (`OEData.isFull`).-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.MinSpec (G : Type*) [Group G] (p : O ⥤ S) where
  /-- `p` is full (paper `rem:audit`; derived as `prop:fullness` for normalized data).-/
  full : p.Full
  /-- `p` is faithful (paper `def:data` (N6)).-/
  faithful : p.Faithful
  /-- The based object trivialization `Ob O ≃ Ob S × G` (paper `rem:audit`).-/
  e : O ≃ S × G
  /-- The first component of `e` is `Ob p` (paper `rem:audit`).-/
  e_fst : ∀ x, (e x).1 = p.obj x

namespace Tengoku.ObserverEquivarianceLean.MinSpec

attribute [simp] e_fst

variable (m : MinSpec G p)

/-! ## Coordinates (paper `rem:audit`, `lem:coordinates`) -/

/-- The fiber coordinate `g_x` of an object (paper `rem:audit`).-/
def coord (x : O) : G := (m.e x).2

/-- The basepoint `b_s = e⁻¹(s, 1)` (paper `rem:audit`).-/
def base (s : S) : O := m.e.symm (s, 1)

/-- The right action on objects, `x · g = e⁻¹(p(x), g_x g)` (paper `rem:audit`).-/
def act (x : O) (g : G) : O := m.e.symm (p.obj x, m.coord x * g)

/-- `e x = (p(x), g_x)` (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.41717e0324ae from=translated src=- shape=20c34ef5 vocab=5e81c5b5
-/
@[simp] theorem e_apply (x : O) : m.e x = (p.obj x, m.coord x) :=
  Prod.ext (m.e_fst x) rfl

/-- Projection of an object given in product coordinates (paper `rem:audit`).
@isnad1 id=eq.0h7v.s6.b78ea9609d6a from=translated src=- shape=0f5a34b4 vocab=ea61e8af
-/
@[simp] theorem p_e_symm (s : S) (g : G) : p.obj (m.e.symm (s, g)) = s := by
  rw [← m.e_fst, Equiv.apply_symm_apply]

/-- Coordinate of an object given in product coordinates (paper `rem:audit`).
@isnad1 id=eq.0h7v.s6.7529a8bd6ae5 from=translated src=- shape=a54439af vocab=ec32cf82
-/
@[simp] theorem coord_e_symm (s : S) (g : G) : m.coord (m.e.symm (s, g)) = g := by
  simp only [coord, Equiv.apply_symm_apply]

/-- `e⁻¹(p(x), g_x) = x` (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.e329c69a059c from=translated src=- shape=6f645ea7 vocab=613b003f
-/
@[simp] theorem e_symm_p_coord (x : O) : m.e.symm (p.obj x, m.coord x) = x := by
  rw [← m.e_apply, Equiv.symm_apply_apply]

/-- Objects are determined by projection and coordinate (paper `rem:audit`).
@isnad1 id=eq.2h7v.s6.9bf801c5f876 from=translated src=- shape=b74981ea vocab=bed75dfa
-/
theorem ext_obj {x y : O} (hp : p.obj x = p.obj y) (hc : m.coord x = m.coord y) : x = y :=
  m.e.injective (by rw [m.e_apply, m.e_apply, hp, hc])

/-- Objects are equal iff projections and coordinates agree (paper `rem:audit`).
@isnad1 id=iff.0h7v.s6.cea3aa2498c1 from=translated src=- shape=14bf3e88 vocab=bed75dfa
-/
theorem obj_eq_iff {x y : O} : x = y ↔ p.obj x = p.obj y ∧ m.coord x = m.coord y :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => m.ext_obj h.1 h.2⟩

/-- The basepoint lies over `s` (paper `rem:audit`, (N2)).
@isnad1 id=eq.0h6v.s5.45c047a05eb8 from=translated src=- shape=9dac5c8c vocab=217a6fb3
-/
@[simp] theorem p_base (s : S) : p.obj (m.base s) = s := m.p_e_symm s 1

/-- The basepoint has coordinate `1`, `g_{b_s} = 1` (paper `lem:coordinates`).
@isnad1 id=eq.0h6v.s6.ad4c7aea335b from=translated src=- shape=16533aa0 vocab=79c7b2cf
-/
@[simp] theorem coord_base (s : S) : m.coord (m.base s) = 1 := m.coord_e_symm s 1

/-- The action preserves projections, `p(x · g) = p(x)` (paper `def:data` (N1)).
@isnad1 id=eq.0h7v.s5.72db6f175d48 from=translated src=- shape=bd094f0c vocab=8a7756c0
-/
@[simp] theorem p_act (x : O) (g : G) : p.obj (m.act x g) = p.obj x := m.p_e_symm _ _

/-- The action shifts coordinates, `g_{x · h} = g_x h` (paper `lem:coordinates`).
@isnad1 id=eq.0h7v.s6.498547f9e9a8 from=translated src=- shape=9f09e5b5 vocab=fef1765b
-/
@[simp] theorem coord_act (x : O) (g : G) : m.coord (m.act x g) = m.coord x * g :=
  m.coord_e_symm _ _

/-- `g_{b_s · g} = g` (paper `def:data` (N2)).
@isnad1 id=eq.0h7v.s6.e3f241439f17 from=translated src=- shape=228b3973 vocab=be35d0d4
-/
theorem coord_act_base (s : S) (g : G) : m.coord (m.act (m.base s) g) = g := by
  simp

/-- The unit acts trivially, `x · 1 = x` (paper `def:data` (N1)).
@isnad1 id=eq.0h6v.s5.d77303b928ce from=translated src=- shape=80b7828a vocab=61260343
-/
@[simp] theorem act_one (x : O) : m.act x 1 = x := by
  simp only [act, mul_one, e_symm_p_coord]

/-- The action is a right action, `(x · g) · h = x · (g h)` (paper `def:data` (N1)).
@isnad1 id=eq.0h8v.s6.110ac66fcb41 from=translated src=- shape=93c22372 vocab=7d6739ab
-/
@[simp] theorem act_mul (x : O) (g h : G) : m.act (m.act x g) h = m.act x (g * h) :=
  m.ext_obj (by simp) (by simp [mul_assoc])

/-- The action is free on objects (paper `lem:coordinates`).
@isnad1 id=eq.1h8v.s6.1d131cc691d1 from=translated src=- shape=ebd404d3 vocab=61260343
-/
theorem act_free (x : O) (g h : G) (hgh : m.act x g = m.act x h) : g = h := by
  have := congrArg m.coord hgh
  simpa using this

/-- Cancellation form of freeness (paper `lem:coordinates`).
@isnad1 id=iff.0h8v.s6.a33385d2f023 from=translated src=- shape=1d1ecfba vocab=61260343
-/
@[simp] theorem act_inj (x : O) (g h : G) : m.act x g = m.act x h ↔ g = h :=
  ⟨m.act_free x g h, fun h => h ▸ rfl⟩

/-- Every object is its basepoint translated by its coordinate, `x = b_{p(x)} · g_x`
    (paper `def:data` (N2)).
@isnad1 id=eq.0h6v.s6.ed02e49819a7 from=translated src=- shape=f344358c vocab=dce74d77
-/
@[simp] theorem base_coord (x : O) : m.act (m.base (p.obj x)) (m.coord x) = x :=
  m.ext_obj (by simp) (by simp)

/-- The inverse trivialization in terms of basepoints and action, `e⁻¹(s, g) = b_s · g`
    (paper `rem:audit`, `thm:normalform`: `M(s,g) = b_s · g`).  Not a simp lemma.
@isnad1 id=eq.0h7v.s6.e0d69dd0d661 from=translated src=- shape=c6bf25c1 vocab=5112f6b8
-/
theorem e_symm_eq (s : S) (g : G) : m.e.symm (s, g) = m.act (m.base s) g :=
  m.ext_obj (by simp) (by simp)

/-- Translating an object given in product coordinates (paper `rem:audit`).
@isnad1 id=eq.0h8v.s7.0ded70779ff1 from=translated src=- shape=98e273b2 vocab=025f67b8
-/
@[simp] theorem act_e_symm (s : S) (g h : G) : m.act (m.e.symm (s, g)) h = m.e.symm (s, g * h) :=
  m.ext_obj (by simp) (by simp)

/-! ## Unique lifts (paper `prop:fullness`, `prop:cartesian`, `thm:normalform` proof) -/

/-- The unique arrow `x ⟶ y` over a base arrow `u : s ⟶ t`, given `p(x) = s` and `p(y) = t`
    (paper `prop:fullness` and the remark after it: "an arrow upstairs is determined uniquely
    by its projection").  Built with fullness; uniqueness is `hom_ext` (faithfulness).-/
noncomputable def liftOver {s t : S} (u : s ⟶ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : x ⟶ y :=
  @Functor.preimage _ _ _ _ x y p m.full (eqToHom hx ≫ u ≫ eqToHom hy.symm)

/-- The unique lift sits over `u` (paper `prop:fullness`).
@isnad1 id=eq.2h10v.s7.cd817a7f6d15 from=translated src=- shape=da2ad51b vocab=b88a34fb
-/
@[simp] theorem p_map_liftOver {s t : S} (u : s ⟶ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) :
    p.map (m.liftOver u hx hy) = eqToHom hx ≫ u ≫ eqToHom hy.symm :=
  @Functor.map_preimage _ _ _ _ p m.full x y _

/-- Arrows with the same endpoints and the same projection are equal (paper `def:data` (N6)).
@isnad1 id=eq.1h9v.s6.2597f279ca50 from=translated src=- shape=5aa5eebc vocab=8af370d5
-/
theorem hom_ext (m : MinSpec G p) {x y : O} {f f' : x ⟶ y} (h : p.map f = p.map f') : f = f' :=
  @Functor.map_injective _ _ _ _ x y p m.faithful _ _ h

/-- Faithfulness as an iff (paper `def:data` (N6)).
@isnad1 id=iff.0h9v.s6.e9a6c247cb02 from=translated src=- shape=aafafbaa vocab=8af370d5
-/
theorem hom_ext_iff (m : MinSpec G p) {x y : O} {f f' : x ⟶ y} : f = f' ↔ p.map f = p.map f' :=
  ⟨fun h => h ▸ rfl, m.hom_ext⟩

/-- Characterization of the unique lift (paper `prop:fullness`, uniqueness).-/
theorem eq_liftOver_iff {s t : S} (u : s ⟶ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) (f : x ⟶ y) :
    f = m.liftOver u hx hy ↔ p.map f = eqToHom hx ≫ u ≫ eqToHom hy.symm := by
  rw [m.hom_ext_iff, p_map_liftOver]

/-- Characterization of the unique lift, other orientation (paper `prop:fullness`).
@isnad1 id=iff.2h11v.s7.c4e935f802be from=translated src=- shape=f6b99a13 vocab=b88a34fb
-/
theorem liftOver_eq_iff {s t : S} (u : s ⟶ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) (f : x ⟶ y) :
    m.liftOver u hx hy = f ↔ eqToHom hx ≫ u ≫ eqToHom hy.symm = p.map f := by
  rw [m.hom_ext_iff, p_map_liftOver]

/-- Any arrow is the unique lift of its projection (paper `prop:fullness`).-/
theorem eq_liftOver {s t : S} {u : s ⟶ t} {x y : O} {hx : p.obj x = s} {hy : p.obj y = t}
    (f : x ⟶ y) (hf : p.map f = eqToHom hx ≫ u ≫ eqToHom hy.symm) :
    f = m.liftOver u hx hy :=
  (m.eq_liftOver_iff u hx hy f).2 hf

/-- The unique lift of `p.map f` with its own endpoints is `f` (paper `prop:fullness`).
@isnad1 id=eq.0h8v.s6.273f876f799f from=translated src=- shape=21f94756 vocab=e8c440e5
-/
@[simp] theorem liftOver_map {x y : O} (f : x ⟶ y) : m.liftOver (p.map f) rfl rfl = f :=
  (m.eq_liftOver f (by simp)).symm

/-- The unique lift of an identity from an object to itself is the identity
    (paper `thm:normalform` proof: preservation of identities).
@isnad1 id=eq.1h7v.s6.0ba282a5a110 from=translated src=- shape=6d4e779c vocab=8b110bde
-/
@[simp] theorem liftOver_id {s : S} {x : O} (hx : p.obj x = s) :
    m.liftOver (𝟙 s) hx hx = 𝟙 x :=
  (m.eq_liftOver (𝟙 x) (by simp)).symm

/-- Lifts of `eqToHom` between equal objects are `eqToHom` (paper `thm:normalform` proof).
@isnad1 id=eq.4h9v.s6.afa4a67323e5 from=translated src=- shape=814948b9 vocab=46254db6
-/
@[simp] theorem liftOver_eqToHom {s t : S} (hst : s = t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) (hxy : x = y) :
    m.liftOver (eqToHom hst) hx hy = eqToHom hxy := by
  subst hxy hst hx
  exact m.liftOver_id rfl

/-- Unique lifts compose (paper `thm:normalform` proof: preservation of composition).
@isnad1 id=eq.3h13v.s7.63296a472cfa from=translated src=- shape=fd245b38 vocab=bd80795a
-/
@[reassoc (attr := simp)]
theorem liftOver_comp {s t r : S} (u : s ⟶ t) (v : t ⟶ r) {x y z : O} (hx : p.obj x = s)
    (hy : p.obj y = t) (hz : p.obj z = r) :
    m.liftOver u hx hy ≫ m.liftOver v hy hz = m.liftOver (u ≫ v) hx hz :=
  m.eq_liftOver _ (by simp)

/-- Precomposing a unique lift with an `eqToHom` (paper `thm:normalform` proof).
@isnad1 id=eq.3h11v.s7.8878a162f0b0 from=translated src=- shape=ae8722d4 vocab=a4bcfda6
-/
@[simp] theorem eqToHom_comp_liftOver {s t : S} (u : s ⟶ t) {x' x y : O} (h : x' = x)
    (hx : p.obj x = s) (hy : p.obj y = t) :
    eqToHom h ≫ m.liftOver u hx hy = m.liftOver u ((congrArg p.obj h).trans hx) hy := by
  subst h; simp

/-- Postcomposing a unique lift with an `eqToHom` (paper `thm:normalform` proof).
@isnad1 id=eq.3h11v.s7.552a157d1c55 from=translated src=- shape=ba85b1ac vocab=73c3f87b
-/
@[simp] theorem liftOver_comp_eqToHom {s t : S} (u : s ⟶ t) {x y y' : O} (h : y = y')
    (hx : p.obj x = s) (hy : p.obj y = t) :
    m.liftOver u hx hy ≫ eqToHom h = m.liftOver u hx ((congrArg p.obj h).symm.trans hy) := by
  subst h; simp

/-- Unique lifts only depend on the base arrow up to the endpoint identifications
    (paper `thm:normalform` proof): transport of the base endpoints.
@isnad1 id=eq.4h12v.s7.ad2fb4210c60 from=translated src=- shape=12e7ce4a vocab=45c9c3d8
-/
theorem liftOver_congr {s t s' t' : S} (u : s ⟶ t) (hs : s = s') (ht : t = t') {x y : O}
    (hx : p.obj x = s) (hy : p.obj y = t) :
    m.liftOver u hx hy
      = m.liftOver (eqToHom hs.symm ≫ u ≫ eqToHom ht) (hx.trans hs) (hy.trans ht) := by
  subst hs ht; simp

/-- The unique lift of an isomorphism is an isomorphism, with inverse the unique lift of the
    inverse (paper `rem:audit`: "its reverse lift is an inverse by faithfulness").
@isnad1 id=isiso.2h10v.s6.cceb11b69be7 from=translated src=- shape=83ebb813 vocab=efac2a65
-/
instance isIso_liftOver {s t : S} (u : s ⟶ t) [IsIso u] {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : IsIso (m.liftOver u hx hy) :=
  ⟨⟨m.liftOver (inv u) hy hx, by simp, by simp⟩⟩

/-- The inverse of a unique lift is the unique lift of the inverse (paper `rem:audit`).
@isnad1 id=eq.2h10v.s7.1144fdc25e9b from=translated src=- shape=c42c1942 vocab=ee3f8101
-/
@[simp] theorem inv_liftOver {s t : S} (u : s ⟶ t) [IsIso u] {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : inv (m.liftOver u hx hy) = m.liftOver (inv u) hy hx :=
  IsIso.inv_eq_of_hom_inv_id (by simp)

/-- The unique lift of an isomorphism, packaged as an isomorphism (paper `rem:audit`).-/
noncomputable def liftOverIso {s t : S} (u : s ≅ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : x ≅ y where
  hom := m.liftOver u.hom hx hy
  inv := m.liftOver u.inv hy hx

/-- (paper `rem:audit`)
@isnad1 id=eq.2h10v.s6.cb4d2309f06e from=translated src=- shape=b38ace04 vocab=81df3ee1
-/
@[simp] theorem liftOverIso_hom {s t : S} (u : s ≅ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : (m.liftOverIso u hx hy).hom = m.liftOver u.hom hx hy := rfl

/-- (paper `rem:audit`)
@isnad1 id=eq.2h10v.s6.1a8ebf2b2836 from=translated src=- shape=cf24a214 vocab=02b519ec
-/
@[simp] theorem liftOverIso_inv {s t : S} (u : s ≅ t) {x y : O} (hx : p.obj x = s)
    (hy : p.obj y = t) : (m.liftOverIso u hx hy).inv = m.liftOver u.inv hy hx := rfl

/-! ## The right action by functors (paper `rem:audit`: "the unique image of every arrow
       under `R_h`") -/

/-- The right action `R_g : O ⥤ O` of a minimal specification: objects `x ↦ x · g`, and an
    arrow `f` goes to the unique arrow with the translated endpoints and unchanged projection
    (paper `rem:audit`).-/
noncomputable def actFunctor (g : G) : O ⥤ O where
  obj x := m.act x g
  map {x y} f := m.liftOver (p.map f) (m.p_act x g) (m.p_act y g)
  map_id x := by simp
  map_comp f h := by simp

/-- (paper `rem:audit`)
@isnad1 id=eq.0h7v.s5.d0eb905bb420 from=translated src=- shape=0ad157f0 vocab=f8c4a692
-/
@[simp] theorem actFunctor_obj (g : G) (x : O) : (m.actFunctor g).obj x = m.act x g := rfl

/-- (paper `rem:audit`)
@isnad1 id=eq.0h9v.s7.7096be0240e7 from=translated src=- shape=d126ab72 vocab=15bc47ee
-/
@[simp] theorem actFunctor_map (g : G) {x y : O} (f : x ⟶ y) :
    (m.actFunctor g).map f = m.liftOver (p.map f) (m.p_act x g) (m.p_act y g) := rfl

/-- The action functor covers the identity: `R_g ⋙ p = p` (paper `rem:audit`).
@isnad1 id=eq.0h6v.s5.d85adac15b4f from=translated src=- shape=bed83558 vocab=2007577d
-/
theorem actFunctor_comp_p (g : G) : m.actFunctor g ⋙ p = p := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact m.p_act x g
  · intro x y f; exact m.p_map_liftOver (p.map f) (m.p_act x g) (m.p_act y g)

/-- Projection of the action on arrows (paper `rem:audit`).
@isnad1 id=eq.0h9v.s8.e8d5121c49a4 from=translated src=- shape=8df4fa83 vocab=a27bfdfa
-/
@[simp] theorem p_map_actFunctor_map (g : G) {x y : O} (f : x ⟶ y) :
    p.map ((m.actFunctor g).map f)
      = eqToHom (m.p_act x g) ≫ p.map f ≫ eqToHom (m.p_act y g).symm :=
  m.p_map_liftOver (p.map f) (m.p_act x g) (m.p_act y g)

/-- The unit acts as the identity functor, `R_1 = 𝟭` (paper `rem:audit`).
@isnad1 id=eq.0h5v.s5.8d49f7c85228 from=translated src=- shape=9ecb265a vocab=78acef9a
-/
theorem actFunctor_one : m.actFunctor 1 = 𝟭 O := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact m.act_one x
  · intro x y f
    have key : m.liftOver (p.map f) (m.p_act x 1) (m.p_act y 1)
        = eqToHom (m.act_one x) ≫ f ≫ eqToHom (m.act_one y).symm := by
      apply m.hom_ext
      simp [eqToHom_map]
    exact key

/-- The action by functors is a right action: `R_g ⋙ R_h = R_{g h}` (paper `rem:audit`),
    same order convention as `OEData.actFunctor_mul`.
@isnad1 id=eq.0h7v.s6.cf76d7c1d735 from=translated src=- shape=a1183c34 vocab=0056845a
-/
theorem actFunctor_mul (g h : G) : m.actFunctor g ⋙ m.actFunctor h = m.actFunctor (g * h) := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact m.act_mul x g h
  · intro x y f
    have key : m.liftOver (p.map (m.liftOver (p.map f) (m.p_act x g) (m.p_act y g)))
          (m.p_act (m.act x g) h) (m.p_act (m.act y g) h)
        = eqToHom (m.act_mul x g h) ≫ m.liftOver (p.map f) (m.p_act x (g * h))
            (m.p_act y (g * h)) ≫ eqToHom (m.act_mul y g h).symm := by
      apply m.hom_ext
      simp
    exact key

end Tengoku.ObserverEquivarianceLean.MinSpec

/-! ## The forward direction `OEData → MinSpec` (paper `rem:audit`) -/

namespace Tengoku.ObserverEquivarianceLean.OEData

/-- The minimal specification underlying normalized data (paper `rem:audit`, forward
    direction): fullness is `prop:fullness` (`OEData.isFull`), faithfulness is (N6), and the
    bijection is `x ↦ (p(x), g_x)` with inverse `(s, g) ↦ b_s · g` by (N1)–(N2).-/
def toMinSpec (d : OEData G p) : MinSpec G p where
  full := d.isFull
  faithful := d.p_faithful
  e :=
    { toFun := fun x => (p.obj x, d.coord x)
      invFun := fun sg => d.act (d.base sg.1) sg.2
      left_inv := fun x => d.base_coord x
      right_inv := fun _ => Prod.ext ((d.p_act _ _).trans (d.p_base _)) (d.coord_base _ _) }
  e_fst _ := rfl

variable (d : OEData G p)

/-- (paper `rem:audit`)
@isnad1 id=eq.0h6v.s6.9afc3a6f058c from=translated src=- shape=20cee78e vocab=debd2e9b
-/
@[simp] theorem toMinSpec_e_apply (x : O) : d.toMinSpec.e x = (p.obj x, d.coord x) := rfl

/-- (paper `rem:audit`)
@isnad1 id=eq.0h6v.s7.672af35fa148 from=translated src=- shape=ee17ef75 vocab=54dea1af
-/
@[simp] theorem toMinSpec_e_symm_apply (sg : S × G) :
    d.toMinSpec.e.symm sg = d.act (d.base sg.1) sg.2 := rfl

/-- The coordinates of the minimal specification are those of the data (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.aa0732010626 from=translated src=- shape=49d5825d vocab=9fa88aca
-/
@[simp] theorem toMinSpec_coord (x : O) : d.toMinSpec.coord x = d.coord x := rfl

/-- The basepoints of the minimal specification are those of the data (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.b3ac4c054a55 from=translated src=- shape=0be506dd vocab=db7a417b
-/
@[simp] theorem toMinSpec_base (s : S) : d.toMinSpec.base s = d.base s :=
  d.act_one (d.base s)

/-- The object action of the minimal specification is that of the data (paper `rem:audit`).
@isnad1 id=eq.0h7v.s6.fb21dba9af79 from=translated src=- shape=8de6c1cf vocab=07af554c
-/
@[simp] theorem toMinSpec_act (x : O) (g : G) : d.toMinSpec.act x g = d.act x g := by
  change d.act (d.base (p.obj x)) (d.coord x * g) = d.act x g
  rw [← d.act_mul, d.base_coord]

/-- The action functors agree: the morphism action `actHom` of normalized data is the unique
    lift of the projection with translated endpoints (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.864ba996f908 from=translated src=- shape=fa631b56 vocab=70db8d2f
-/
theorem toMinSpec_actFunctor (g : G) : d.toMinSpec.actFunctor g = d.actFunctor g := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact d.toMinSpec_act x g
  · intro x y f
    have key : d.toMinSpec.liftOver (p.map f) (d.toMinSpec.p_act x g) (d.toMinSpec.p_act y g)
        = eqToHom (d.toMinSpec_act x g) ≫ d.actHom f g ≫ eqToHom (d.toMinSpec_act y g).symm := by
      apply d.toMinSpec.hom_ext
      simp [eqToHom_map, d.p_actHom]
    exact key

end Tengoku.ObserverEquivarianceLean.OEData
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
