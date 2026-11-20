import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.MinSpec

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The minimal specification and normalized data are equivalent (paper `rem:audit`)

Paper labels covered: `rem:audit` (both directions, and "each specification uniquely recovers
the other"), `lem:coordinates` (for normalized data, with freeness derived from the coordinate
identities rather than read off a field).

* `MinSpec.toOEData`: the converse direction of `rem:audit`.  From a minimal specification
  `m` (full and faithful `p`, a bijection `e : Ob O ≃ Ob S × G` with first component `Ob p`) we
  recover the right action, basepoints and coordinates from `e`; the morphism action, the
  chosen arrows `χ_{u,y}` and the vertical arrows `ℓ_{a,x}` are the unique lifts
  (`MinSpec.liftOver`) with the prescribed endpoints; transport is `u* y = b_s · g_y`.
  All laws follow from object coordinates and uniqueness of lifts (faithfulness).
* `OEData.ext_of_data`: auxiliary extensionality lemma for the round trip: normalized data are
  determined by action, basepoints, coordinates and transport on objects (the morphism fields
  by faithfulness, the `Prop` fields by proof irrelevance).
* `OEData.ext_of_coord`: the precise Lean form of "(N3)–(N4) add no freely variable transport
  data": two normalized data for the same `p` with the same coordinate function are EQUAL
  (action, basepoints, transport, `χ`, `ℓ` are all determined), via injectivity of
  `oeDataEquivMinSpec`.
* The round trips `MinSpec.toOEData_toMinSpec` and `OEData.toMinSpec_toOEData` are equalities
  of structures, packaged as `oeDataEquivMinSpec : OEData G p ≃ MinSpec G p`.

Fullness: `OEData` has NO fullness field (structural fact, visible in the definition of
`OEData` in `Core`); for normalized data fullness is DERIVED (`OEData.isFull`, paper
`prop:fullness`), and `OEData.toMinSpec` is defined with `full := d.isFull`.  In `MinSpec`,
fullness is an explicit hypothesis (`MinSpec.full`).  The lemmas `OEData.toMinSpec_full` and
`MinSpec.toOEData_isFull` are equalities between proofs of the proposition `p.Full`; they hold
by proof irrelevance for ANY two proofs and are included only as sanity checks, not as evidence
of where fullness comes from.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## Coordinate identities for normalized data (paper `lem:coordinates`) -/

namespace Tengoku.ObserverEquivarianceLean.OEData

/-- The basepoint has coordinate one, `g_{b_s} = 1` (paper `lem:coordinates`, first identity;
    from (N1)–(N2)).
@isnad1 id=eq.0h6v.s6.b4a4ae6a5ed5 from=translated src=- shape=59bdb187 vocab=5ba5908b
-/
theorem coord_base_eq_one (d : OEData G p) (s : S) : d.coord (d.base s) = 1 := by
  have h := d.coord_base s 1
  rwa [d.act_one] at h

/-- Paper `lem:coordinates`, all four identities and freeness, for normalized data:
    `g_{b_s} = 1`, `g_{x·h} = g_x h`, `u*y = b_s · g_y`, `g_{u*y} = g_y`, and the action on each
    object fiber is free.  Freeness is proved from the coordinate identity `g_{x·h} = g_x h`
    (taking coordinates), NOT read off the redundant structure field `act_free`.
@isnad1 id=and.0h5v.s8.d3bef54c736f from=translated src=- shape=e680b5c8 vocab=ac95fc21
-/
theorem coordinate_identities (d : OEData G p) :
    (∀ s, d.coord (d.base s) = 1) ∧
    (∀ x h, d.coord (d.act x h) = d.coord x * h) ∧
    (∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d.reind u y hy = d.act (d.base s) (d.coord y) ∧ d.coord (d.reind u y hy) = d.coord y) ∧
    (∀ x a b, d.act x a = d.act x b → a = b) :=
  ⟨d.coord_base_eq_one, d.coord_act, fun u y hy => ⟨d.reind_eq u y hy, d.coord_reind u y hy⟩,
    fun x a b hab => by
      have h := congrArg d.coord hab
      rw [d.coord_act, d.coord_act] at h
      exact mul_left_cancel h⟩

end Tengoku.ObserverEquivarianceLean.OEData

/-! ## The converse direction `MinSpec → OEData` (paper `rem:audit`) -/

namespace Tengoku.ObserverEquivarianceLean.MinSpec

variable (m : MinSpec G p)

/-- The normalized presentation datum recovered from a minimal specification (paper
    `rem:audit`, converse direction).
    * action, basepoints and coordinates come from `e` (`MinSpec.act`, `MinSpec.base`,
      `MinSpec.coord`);
    * the morphism action `R_h(f)` is the unique arrow with translated endpoints and unchanged
      projection;
    * transport is `u* y = e⁻¹(s, g_y) = b_s · g_y` for `u : s ⟶ p(y)`;
    * `χ_{u,y}` is the unique arrow over `u` from `u* y` to `y`;
    * `ℓ_{a,x}` is the unique arrow over `𝟙 (p x)` from `x` to `b_{p(x)} · (a g_x)`;
    * faithfulness (N6) is `m.faithful`.
    Fullness is used to build the lifts but is NOT a field of `OEData`.-/
noncomputable def toOEData : OEData G p where
  act := m.act
  act_one := m.act_one
  act_mul := m.act_mul
  p_act := m.p_act
  act_free := m.act_free
  actHom {x y} f g := m.liftOver (p.map f) (m.p_act x g) (m.p_act y g)
  actHom_id x g := by simp
  actHom_comp f h g := by simp
  actHom_one {x y} f := by
    apply m.hom_ext
    simp [eqToHom_map]
  actHom_mul {x y} f g h := by
    apply m.hom_ext
    simp
  p_actHom {x y} f g := m.p_map_liftOver (p.map f) (m.p_act x g) (m.p_act y g)
  base := m.base
  p_base := m.p_base
  coord := m.coord
  base_coord := m.base_coord
  coord_base := m.coord_act_base
  reind {s _t} _u y _hy := m.e.symm (s, m.coord y)
  p_reind {s _t} _u y _hy := m.p_e_symm s (m.coord y)
  chi {s _t} u y hy := m.liftOver u (m.p_e_symm s (m.coord y)) hy
  p_chi {s _t} u y hy := m.p_map_liftOver u (m.p_e_symm s (m.coord y)) hy
  reind_base {s t} _u := by
    show m.e.symm (s, m.coord (m.base t)) = m.e.symm (s, 1)
    rw [m.coord_base]
  reind_act {s _t} _u y _hy g := by
    show m.e.symm (s, m.coord (m.act y g)) = m.act (m.e.symm (s, m.coord y)) g
    simp
  chi_act {s _t} u y hy g := by
    apply m.hom_ext
    simp
  ltrans a x := m.liftOver (𝟙 (p.obj x)) rfl
    ((m.p_act (m.base (p.obj x)) (a * m.coord x)).trans (m.p_base (p.obj x)))
  p_ltrans a x := by
    rw [m.p_map_liftOver]
    simp
  reind_id {s} y hy := by
    subst hy
    exact m.e_symm_p_coord y
  chi_id {s} y hy := by
    apply m.hom_ext
    simp [eqToHom_map]
  reind_comp {s t r} _u _v z _hz := by
    show m.e.symm (s, m.coord z) = m.e.symm (s, m.coord (m.e.symm (t, m.coord z)))
    rw [m.coord_e_symm]
  chi_comp {s t r} u v z hz := by
    apply m.hom_ext
    simp
  p_faithful := m.faithful

/-- The recovered action is the object action of `e` (paper `rem:audit`).
@isnad1 id=eq.0h7v.s6.16bfbcd499d3 from=translated src=- shape=8ac54ff1 vocab=15d3b20e
-/
@[simp] theorem toOEData_act (x : O) (g : G) : m.toOEData.act x g = m.act x g := rfl

/-- The recovered basepoints are `b_s = e⁻¹(s,1)` (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.070fed321be0 from=translated src=- shape=c83921d1 vocab=3d160e68
-/
@[simp] theorem toOEData_base (s : S) : m.toOEData.base s = m.base s := rfl

/-- The recovered coordinates are `g_x = (e x).2` (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.d7ac14042175 from=translated src=- shape=769e38fb vocab=f2db281a
-/
@[simp] theorem toOEData_coord (x : O) : m.toOEData.coord x = m.coord x := rfl

/-- The recovered transport is `u* y = b_s · g_y` (paper `rem:audit`).
@isnad1 id=eq.1h9v.s6.41a28a7b930a from=translated src=- shape=81267963 vocab=d3a2a605
-/
theorem toOEData_reind {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    m.toOEData.reind u y hy = m.act (m.base s) (m.coord y) :=
  m.e_symm_eq s (m.coord y)

/-- The recovered morphism action is the unique lift of the projection with translated
    endpoints (paper `rem:audit`).
@isnad1 id=eq.0h9v.s7.0f6c0a418eba from=translated src=- shape=dddec53f vocab=6d720720
-/
@[simp] theorem toOEData_actHom {x y : O} (f : x ⟶ y) (g : G) :
    m.toOEData.actHom f g = m.liftOver (p.map f) (m.p_act x g) (m.p_act y g) := rfl

/-- The recovered action functors are the action functors of the minimal specification
    (paper `rem:audit`).
@isnad1 id=eq.0h6v.s6.a5f4246f97ef from=translated src=- shape=fa631b56 vocab=0cacabeb
-/
theorem toOEData_actFunctor (g : G) : m.toOEData.actFunctor g = m.actFunctor g := rfl

/-- The recovered `χ_{u,y}` is the unique arrow over `u` from `u* y` to `y`
    (paper `rem:audit`).
@isnad1 id=eq.1h9v.s7.e0c7bc1b6ddc from=translated src=- shape=099746cc vocab=d6ef3c63
-/
@[simp] theorem toOEData_chi {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    m.toOEData.chi u y hy = m.liftOver u (m.p_e_symm s (m.coord y)) hy := rfl

/-- The recovered `ℓ_{a,x}` is the unique arrow over `𝟙 (p x)` from `x` to `b_{p(x)} · (a g_x)`
    (paper `rem:audit`).
@isnad1 id=eq.0h7v.s8.128535560ce3 from=translated src=- shape=2205d83b vocab=48cd449b
-/
@[simp] theorem toOEData_ltrans (a : G) (x : O) :
    m.toOEData.ltrans a x = m.liftOver (𝟙 (p.obj x)) rfl
      ((m.p_act (m.base (p.obj x)) (a * m.coord x)).trans (m.p_base (p.obj x))) := rfl

/-- Uniqueness of the recovered cleavage arrows: any arrow `u* y ⟶ y` over `u` is `χ_{u,y}`
    (paper `rem:audit`: "the unique arrow over `u` with these endpoints").
@isnad1 id=eq.2h10v.s8.fca38e00a0da from=translated src=- shape=b8699518 vocab=e3b7fc2b
-/
theorem toOEData_chi_unique {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t)
    (f : m.toOEData.reind u y hy ⟶ y)
    (hf : p.map f = eqToHom (m.toOEData.p_reind u y hy) ≫ u ≫ eqToHom hy.symm) :
    f = m.toOEData.chi u y hy :=
  (m.eq_liftOver_iff u (m.p_e_symm s (m.coord y)) hy f).2 hf

/-- Uniqueness of the recovered vertical arrows: any arrow `x ⟶ b_{p(x)} · (a g_x)` over the
    identity is `ℓ_{a,x}` (paper `rem:audit`).
@isnad1 id=eq.1h8v.s9.9edcde363cb5 from=translated src=- shape=6ebcfb65 vocab=fb76498f
-/
theorem toOEData_ltrans_unique (a : G) (x : O)
    (f : x ⟶ m.toOEData.act (m.toOEData.base (p.obj x)) (a * m.toOEData.coord x))
    (hf : p.map f = eqToHom (((m.toOEData.p_act (m.toOEData.base (p.obj x))
        (a * m.toOEData.coord x)).trans (m.toOEData.p_base (p.obj x))).symm)) :
    f = m.toOEData.ltrans a x := by
  apply m.hom_ext
  rw [hf, m.toOEData.p_ltrans]

/-- The reverse lift is an inverse of `ℓ_{a,x}` (paper `rem:audit`: "Its reverse lift is an
    inverse by faithfulness").
@isnad1 id=and.0h7v.s9.b4a73b0962b8 from=translated src=- shape=d2cb93e4 vocab=e7f585c0
-/
theorem toOEData_ltrans_inv (a : G) (x : O) :
    m.toOEData.ltrans a x
        ≫ m.liftOver (𝟙 (p.obj x))
          ((m.p_act (m.base (p.obj x)) (a * m.coord x)).trans (m.p_base (p.obj x))) rfl
      = 𝟙 x ∧
    m.liftOver (𝟙 (p.obj x))
          ((m.p_act (m.base (p.obj x)) (a * m.coord x)).trans (m.p_base (p.obj x))) rfl
        ≫ m.toOEData.ltrans a x
      = 𝟙 (m.act (m.base (p.obj x)) (a * m.coord x)) := by
  constructor <;> simp

end Tengoku.ObserverEquivarianceLean.MinSpec

/-! ## Normalized data are determined by their object data (paper `rem:audit`) -/

/-- Auxiliary extensionality lemma for the round trip of paper `rem:audit`: two normalized
    data for the same `p` with the same action, basepoints, coordinates and transport on objects
    are equal (the morphism fields `actHom`, `chi`, `ltrans` are determined by their projections
    via faithfulness, and all `Prop` fields by proof irrelevance).  Since it assumes equality of
    `act`, `base` and `reind`, it does not by itself show that these are determined; the
    stronger statement "(N3)–(N4) add no freely variable transport data" is
    `OEData.ext_of_coord`.
@isnad1 id=eq.4h6v.s7.78d9eb28db63 from=translated src=- shape=01f80b73 vocab=69435c01
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.ext_of_data (d d' : OEData G p) (hact : d.act = d'.act)
    (hbase : d.base = d'.base) (hcoord : d.coord = d'.coord)
    (hreind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      d.reind u y hy = d'.reind u y hy) : d = d' := by
  rcases d with ⟨⟨act, act_one, act_mul, p_act, act_free, actHom, actHom_id, actHom_comp,
    actHom_one, actHom_mul, p_actHom, base, p_base, coord, base_coord, coord_base, reind,
    p_reind, chi, p_chi, reind_base, reind_act, chi_act, ltrans, p_ltrans, reind_id, chi_id,
    reind_comp, chi_comp⟩, faithful⟩
  rcases d' with ⟨⟨act', act_one', act_mul', p_act', act_free', actHom', actHom_id',
    actHom_comp', actHom_one', actHom_mul', p_actHom', base', p_base', coord', base_coord',
    coord_base', reind', p_reind', chi', p_chi', reind_base', reind_act', chi_act', ltrans',
    p_ltrans', reind_id', chi_id', reind_comp', chi_comp'⟩, faithful'⟩
  dsimp only at hact hbase hcoord hreind
  subst hact hbase hcoord
  have hr : @reind = @reind' := by
    funext s t u y hy
    exact hreind u y hy
  subst hr
  have hA : @actHom = @actHom' := by
    funext x y f g
    apply faithful.map_injective
    rw [p_actHom, p_actHom']
  subst hA
  have hC : @chi = @chi' := by
    funext s t u y hy
    apply faithful.map_injective
    rw [p_chi, p_chi']
  subst hC
  have hL : @ltrans = @ltrans' := by
    funext a x
    apply faithful.map_injective
    rw [p_ltrans, p_ltrans']
  subst hL
  rfl

/-! ## The round trips and the equivalence (paper `rem:audit`) -/

/-- Minimal specification → normalized data → minimal specification is the identity
    (paper `rem:audit`: "each specification uniquely recovers the other").
@isnad1 id=eq.0h5v.s5.90c356c539ad from=translated src=- shape=42c7ab69 vocab=f4878113
-/
theorem Tengoku.ObserverEquivarianceLean.MinSpec.toOEData_toMinSpec (m : MinSpec G p) : m.toOEData.toMinSpec = m :=
  MinSpec.ext (Equiv.ext fun x => by
    rw [OEData.toMinSpec_e_apply, m.e_apply]
    rfl)

/-- Normalized data → minimal specification → normalized data is the identity, as an equality
    of structures (paper `rem:audit`: "each specification uniquely recovers the other").
@isnad1 id=eq.0h5v.s5.f1c90d835152 from=translated src=- shape=42c7ab69 vocab=386efd5a
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.toMinSpec_toOEData (d : OEData G p) : d.toMinSpec.toOEData = d := by
  apply OEData.ext_of_data
  · funext x g
    exact d.toMinSpec_act x g
  · funext s
    exact d.toMinSpec_base s
  · rfl
  · intro s t u y hy
    exact (d.reind_eq u y hy).symm

/-- The correspondence of data of paper `rem:audit`: normalized presentation data for `p` are
    in bijection with minimal specifications (full and faithful `p` plus a bijection
    `Ob O ≃ Ob S × G` with first component `Ob p`), via `OEData.toMinSpec` and
    `MinSpec.toOEData`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.oeDataEquivMinSpec : OEData G p ≃ MinSpec G p where
  toFun := OEData.toMinSpec
  invFun := MinSpec.toOEData
  left_inv := OEData.toMinSpec_toOEData
  right_inv := MinSpec.toOEData_toMinSpec

/-- (paper `rem:audit`)
@isnad1 id=eq.0h5v.s7.087f5a44576e from=translated src=- shape=103d5f8e vocab=27da10ff
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.oeDataEquivMinSpec_apply (d : OEData G p) :
    oeDataEquivMinSpec d = d.toMinSpec := rfl

/-- (paper `rem:audit`)
@isnad1 id=eq.0h5v.s7.5dd01b88ce9b from=translated src=- shape=640bb5fb vocab=6a0a23d4
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.oeDataEquivMinSpec_symm_apply (m : MinSpec G p) :
    oeDataEquivMinSpec.symm m = m.toOEData := rfl

/-- Normalized data are determined by their coordinate function alone: two `OEData G p` with
    the same `coord` are equal (paper `rem:audit`: "(N3)–(N4) add no freely variable transport
    data once this based object trivialization and full faithfulness are fixed").  The based
    trivialization `e x = (p x, g_x)` depends only on `coord`, and `oeDataEquivMinSpec` is
    injective, so action, basepoints, transport, `χ` and `ℓ` are all determined.
@isnad1 id=eq.1h6v.s6.b8e717a7ef76 from=translated src=- shape=a52cfb10 vocab=1810e401
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.ext_of_coord (d d' : OEData G p) (h : d.coord = d'.coord) : d = d' := by
  apply oeDataEquivMinSpec.injective
  apply MinSpec.ext
  apply Equiv.ext
  intro x
  simp [h]

/-! ## Fullness: hypothesis in `MinSpec`, derived for `OEData` (paper `rem:audit`) -/

/-- Proof-irrelevance sanity check (paper `rem:audit`, `prop:fullness`): the fullness proof
    carried by `d.toMinSpec` equals `d.isFull`.  As an equality of proofs of the proposition
    `p.Full` this holds for ANY two proofs, so it records nothing about their origin.  The
    structural facts are that `OEData` has no fullness field and that `OEData.toMinSpec` is
    defined with `full := d.isFull` (derived fullness, `prop:fullness`).
@isnad1 id=eq.0h5v.s5.ab277b50f36d from=translated src=- shape=81b965c3 vocab=11218a2f
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.toMinSpec_full (d : OEData G p) : d.toMinSpec.full = d.isFull := rfl

/-- Proof-irrelevance sanity check (paper `rem:audit`): derived fullness `m.toOEData.isFull`
    equals the hypothesis `m.full`.  As an equality of proofs of `p.Full` it holds for ANY two
    proofs; the structural fact is that `MinSpec.toOEData` uses `m.full` only to build the lifts
    and produces an `OEData`, which has no fullness field.
@isnad1 id=eq.0h5v.s5.82a74a575ff4 from=translated src=- shape=81b965c3 vocab=ca31212e
-/
theorem Tengoku.ObserverEquivarianceLean.MinSpec.toOEData_isFull (m : MinSpec G p) : m.toOEData.isFull = m.full := rfl
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
