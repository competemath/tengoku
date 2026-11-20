import Tengoku.Seed.CategoryTheory.ConnectedComponents
import Tengoku.Seed.CategoryTheory.SingleObj
import Tengoku.Seed.CategoryTheory.Products.Basic
import Tengoku.Seed.CategoryTheory.Pi.Basic
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.GroupTheory.SemidirectProduct
import Tengoku.Seed.GroupTheory.SpecificGroups.Quaternion
import Tengoku.Seed.GroupTheory.Perm.Fin
import Tengoku.Seed.Data.ZMod.Basic
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.Tactic.FinCases
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Core development: normalized presentation data over a category

The core of the formalization (paper `def:data`, `lem:coordinates`, `prop:fullness`,
`prop:cartesian`, `rem:groupoid`, and the strict / twisted lift classifications).
Both `S` and `O` are arbitrary categories: no groupoid hypothesis is made on either.  The
only invertible arrows used in general are the chosen vertical arrows `ltrans` of (N5),
whose invertibility is DERIVED (`OEData.ltrans_isIso`) from full faithfulness of `p`.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

universe v u w

variable {S O G : Type*} [Category S] [Category O] [Group G]
variable {p : O ⥤ S}

/-! ## 1. The bundle structure (paper `def:data`) -/

/-- The clauses (N1)–(N5) of a normalized presentation datum (paper `def:data`) for a
    functor `p : O ⥤ S` between arbitrary categories, WITHOUT the faithfulness clause (N6)
    and without the invertibility part of (N5): `ltrans` is only a vertical arrow here.
    (Under (N6), invertibility of `ltrans` is derived: `OEData.ltrans_isIso`.)
    Cleavage preservation (condition `eq:preserve` of the paper's `def:lifts`) lives downstream in the
    predicates on automorphisms, not here.-/
structure _root_.Tengoku.ObserverEquivarianceLean.NormalizedPreDatum (G : Type*) [Group G] (p : O ⥤ S) where
  -- Right `G`-action on objects of `O`. (paper `def:data` (N1), action part.)
  act       : O → G → O
  act_one   : ∀ x, act x 1 = x
  act_mul   : ∀ x g h, act (act x g) h = act x (g * h)
  -- Action preserves the projection on objects. (paper `def:data` (N1), object
  -- projection law `p(x·g) = p(x)`.)
  p_act     : ∀ x g, p.obj (act x g) = p.obj x
  -- Freeness of the action on objects within a fiber.  REDUNDANT: not a clause of paper
  -- `def:data`; it is derivable from `act_mul`, `base_coord` and `coord_base` (paper
  -- `lem:coordinates`; derived in `OEData.coordinate_identities`, MinSpecCorrespondence.lean).
  -- It is a field for convenience; it adds no hypothesis beyond `def:data`.
  act_free  : ∀ x g h, act x g = act x h → g = h
  -- Right `G`-action on morphisms, with functoriality in the morphism slot.
  actHom    : ∀ {x y : O}, (x ⟶ y) → (g : G) → (act x g ⟶ act y g)
  actHom_id : ∀ (x : O) (g : G), actHom (𝟙 x) g = 𝟙 (act x g)
  actHom_comp : ∀ {x y z : O} (f : x ⟶ y) (h : y ⟶ z) (g : G),
      actHom (f ≫ h) g = actHom f g ≫ actHom h g
  -- Action by the identity group element is the identity functor on morphisms,
  -- up to the object equalities `act_one`.
  actHom_one : ∀ {x y : O} (f : x ⟶ y),
      actHom f (1 : G)
        = eqToHom (act_one x) ≫ f ≫ eqToHom (act_one y).symm
  -- Compatibility of the morphism action with the right group law.
  -- The left side acts first by `g`, then by `h`; the right side acts by `g*h`,
  -- with endpoint casts supplied by `act_mul`.
  actHom_mul : ∀ {x y : O} (f : x ⟶ y) (g h : G),
      actHom (actHom f g) h
        = eqToHom (act_mul x g h) ≫ actHom f (g * h) ≫ eqToHom (act_mul y g h).symm
  -- Compatibility of `actHom` with `p`. (paper `def:data` (N1), morphism projection law.)
  p_actHom  : ∀ {x y : O} (f : x ⟶ y) (g : G),
      p.map (actHom f g)
        = eqToHom (p_act x g) ≫ p.map f ≫ eqToHom (p_act y g).symm
  -- `actHom` records the morphism part of the right `G`-action from paper
  -- `def:data`. The exact-sequence proofs use mainly endpoint/projection data
  -- and `p`-faithfulness, but `actHom_one` and `actHom_mul` are included so the
  -- action can be read as an action by functor automorphisms.

  -- Normalized, transport-compatible basepoint section `b : Ob S → Ob O`.
  base       : S → O
  p_base     : ∀ s, p.obj (base s) = s
  -- Coordinate of an object relative to its basepoint:  x = base (p.obj x) · coord x.
  coord      : O → G
  base_coord : ∀ x, act (base (p.obj x)) (coord x) = x
  coord_base : ∀ s g, coord (act (base s) g) = g

  -- Chosen split cleavage: reindexed object `u*y` and the chosen cartesian lift
  -- `χ_{u,y} : u*y → y`, defined for `y` in the fiber over `t`.
  reind   : ∀ {s t : S}, (s ⟶ t) → (y : O) → p.obj y = t → O
  p_reind : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      p.obj (reind u y hy) = s
  chi     : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      reind u y hy ⟶ y
  -- The chosen lift sits over `u`.
  p_chi   : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
      p.map (chi u y hy) = eqToHom (p_reind u y hy) ≫ u ≫ eqToHom hy.symm
  -- Normalization: the section is flat for the cleavage  (u*(b_t) = b_s).
  reind_base : ∀ {s t : S} (u : s ⟶ t),
      reind u (base t) (p_base t) = base s
  -- `G`-stability of reindexing on objects  (transport compatibility).
  reind_act  : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) (g : G),
      reind u (act y g) ((p_act y g).trans hy) = act (reind u y hy) g
  -- `G`-stability of the chosen cartesian lifts (paper `def:data` (N3): χ_{u,y·g} = χ_{u,y}·g).
  chi_act    : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) (g : G),
      chi u (act y g) ((p_act y g).trans hy)
        = eqToHom (reind_act u y hy g) ≫ actHom (chi u y hy) g

  -- Normalized fiber translation, morphism level (the principal/normalized datum
  -- the author chose: "icke-diskret" model).  `ltrans g x : x ⟶ b_{p x}·(g·coord x)`
  -- is the chosen vertical iso realizing left-translation by `g` in the fiber.  It
  -- is what lets `Λ_g` act on in-fiber (vertical) morphisms via the `G`-action,
  -- not only on cartesian arrows — repairing the discrete-fiber degeneracy.
  ltrans   : ∀ (g : G) (x : O), x ⟶ act (base (p.obj x)) (g * coord x)
  -- `ltrans` is vertical (projects to an identity, up to `eqToHom`).
  p_ltrans : ∀ (g : G) (x : O),
      p.map (ltrans g x)
        = eqToHom (((p_act (base (p.obj x)) (g * coord x)).trans (p_base (p.obj x))).symm)

  -- Splitness of the cleavage (theorem-level split-cleavage presentation: chosen lifts compatible with id and ∘).
  reind_id : ∀ {s : S} (y : O) (hy : p.obj y = s), reind (𝟙 s) y hy = y
  chi_id   : ∀ {s : S} (y : O) (hy : p.obj y = s),
      chi (𝟙 s) y hy = eqToHom (reind_id y hy)
  reind_comp : ∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      reind (u ≫ v) z hz = reind u (reind v z hz) (p_reind v z hz)
  chi_comp : ∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      chi (u ≫ v) z hz
        = eqToHom (reind_comp u v z hz) ≫ chi u (reind v z hz) (p_reind v z hz) ≫ chi v z hz

/-- A normalized presentation datum (paper `def:data`, (N1)–(N6)) for a functor
    `p : O ⥤ S` between arbitrary categories: the clauses (N1)–(N5) of
    `NormalizedPreDatum` together with faithfulness (N6).  The invertibility of the chosen
    vertical arrows `ltrans` required by (N5) is not a field: it is derived from (N6) and
    derived fullness (`OEData.ltrans_isIso`).-/
structure _root_.Tengoku.ObserverEquivarianceLean.OEData (G : Type*) [Group G] (p : O ⥤ S) extends NormalizedPreDatum G p where
  -- Faithfulness of `p` (N6):  fibers are "thin" — at most one morphism between two objects
  -- over each base morphism (the torsor content of the "non-discrete" model).
  -- This is a GENUINE extra assumption, NOT derivable from the fields above: nothing here
  -- forbids extra morphisms with the same projection (`chi` is data with a projection law
  -- `p_chi`, not a cartesian *universal* property).  It holds in the paper's examples
  -- and is required by the constructions (`Ã` well defined on morphisms; the morphism step
  -- of `rigidity`).
  -- NOTE: `p.Full` is NOT assumed — it is DERIVED in `OEData.isFull` (from `chi`+`ltrans`).
  p_faithful : p.Faithful

/-! ## 1b. Coordinates, derived fullness and cartesianness
       (paper `lem:coordinates`, `prop:fullness`, `prop:cartesian`) -/

/-- Strong (Grothendieck) cartesianness of `f` over `p`:  every arrow `g : z ⟶ y` whose
    projection factors through `p.map f` via a base arrow `h` lifts to a UNIQUE `k : z ⟶ x`
    with `p.map k = h` and `k ≫ f = g`.  This is the article's formal contract, stated
    directly (existence *and* uniqueness) rather than via mathlib's fibration API.-/
def _root_.Tengoku.ObserverEquivarianceLean.IsCartesianOver (p : O ⥤ S) {x y : O} (f : x ⟶ y) : Prop :=
  ∀ {z : O} (g : z ⟶ y) (h : p.obj z ⟶ p.obj x),
    h ≫ p.map f = p.map g →
      ∃! k : z ⟶ x, p.map k = h ∧ k ≫ f = g

namespace Tengoku.ObserverEquivarianceLean.OEData

/-- `coord` shifts on the right under the action:  `coord (x · g) = coord x * g`.
@isnad1 id=eq.0h7v.s6.6f1f0271df1e from=translated src=- shape=a435d0c5 vocab=d5043a09
-/
theorem coord_act (d : OEData G p) (x : O) (g : G) :
    d.coord (d.act x g) = d.coord x * g := by
  conv_lhs => rw [← d.base_coord x, d.act_mul, d.coord_base]

/-- Projection of the lift on objects:  `p (b_{A s} · coord x) = A s`.
@isnad1 id=eq.0h7v.s6.97530505e690 from=translated src=- shape=9c62dc52 vocab=9321adc6
-/
theorem p_liftObj (d : OEData G p) (A : S ⥤ S) (x : O) :
    p.obj (d.act (d.base (A.obj (p.obj x))) (d.coord x)) = A.obj (p.obj x) :=
  (d.p_act _ _).trans (d.p_base _)

/-- The reindexed object in coordinates:  `u*y = b_s · coord y`.
@isnad1 id=eq.1h9v.s7.eaee9cb381ca from=translated src=- shape=d9d48926 vocab=69435c01
-/
theorem reind_eq (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    d.reind u y hy = d.act (d.base s) (d.coord y) := by
  have hy2 : d.act (d.base t) (d.coord y) = y := by rw [← hy]; exact d.base_coord y
  have key := d.reind_act u (d.base t) (d.p_base t) (d.coord y)
  rw [d.reind_base] at key
  simp only [hy2] at key
  exact key

/-- The coordinate of a reindexed object is unchanged:  `coord (u*y) = coord y`.
@isnad1 id=eq.1h9v.s6.b16c0949c161 from=translated src=- shape=e3303f91 vocab=759d90e5
-/
theorem coord_reind (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    d.coord (d.reind u y hy) = d.coord y := by
  rw [d.reind_eq, d.coord_base]

/-- `p` is FULL — this is a DERIVED consequence, not a new assumption.  A lift of a base
    morphism `w : p x ⟶ p y` is the vertical translation `ltrans` of `x` into `w*y`,
    followed by the chosen cartesian arrow `chi w y`.
@isnad1 id=full.0h5v.s5.1621d8f15077 from=translated src=- shape=b13eb8df vocab=042e856d
-/
theorem isFull (d : OEData G p) : p.Full where
  map_surjective {x y} w := by
    refine ⟨d.ltrans (d.coord (d.reind w y rfl) * (d.coord x)⁻¹) x
              ≫ eqToHom ?_ ≫ d.chi w y rfl, ?_⟩
    · conv_rhs => rw [← d.base_coord (d.reind w y rfl), d.p_reind]
      rw [mul_assoc, inv_mul_cancel, mul_one]
    · simp [d.p_ltrans, d.p_chi, eqToHom_map]

/-- The right `G`-action by `g`, packaged as a genuine endofunctor of `O` using the
    coherence fields `actHom_id` / `actHom_comp`.  Together with `actFunctor_one` and
    `actFunctor_mul` this exhibits the action as one by functor automorphisms.-/
noncomputable def actFunctor (d : OEData G p) (g : G) : O ⥤ O where
  obj x := d.act x g
  map f := d.actHom f g
  map_id x := d.actHom_id x g
  map_comp f h := d.actHom_comp f h g

/-- The identity element acts as the identity functor (uses `actHom_one`).
@isnad1 id=eq.0h5v.s5.e6e5fb9af290 from=translated src=- shape=9ecb265a vocab=b0c226f5
-/
theorem actFunctor_one (d : OEData G p) : d.actFunctor (1 : G) = 𝟭 O := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact d.act_one x
  · intro X Y f; exact d.actHom_one f

/-- The morphism action is multiplicative:  `actFunctor g ⋙ actFunctor h = actFunctor (g*h)`
    (uses `actHom_mul`).  `⋙` is "first `g`, then `h`", matching `act_mul`.
@isnad1 id=eq.0h7v.s6.3b8857a81f45 from=translated src=- shape=a1183c34 vocab=59ccda64
-/
theorem actFunctor_mul (d : OEData G p) (g h : G) :
    d.actFunctor g ⋙ d.actFunctor h = d.actFunctor (g * h) := by
  fapply CategoryTheory.Functor.ext
  · intro x; exact d.act_mul x g h
  · intro X Y f; exact d.actHom_mul f g h

/-- Every arrow of `O` is `p`-cartesian, from DERIVED fullness (`isFull`) plus the assumed
    faithfulness (`p_faithful`).  This is the strong universal property `IsCartesianOver`,
    not merely a weak lift.  (Paper `prop:cartesian`, first sentence.)
@isnad1 id=iscartes.0h8v.s5.0d72fb0e53d9 from=translated src=- shape=a980389e vocab=45da4b04
-/
theorem isCartesian_of_fullyFaithful (d : OEData G p) {x y : O} (f : x ⟶ y) :
    IsCartesianOver p f := by
  haveI := d.isFull
  haveI := d.p_faithful
  intro z g h hgh
  refine ⟨p.preimage h, ⟨p.map_preimage h, ?_⟩, ?_⟩
  · apply p.map_injective
    rw [p.map_comp, p.map_preimage]; exact hgh
  · rintro k ⟨hk1, _⟩
    apply p.map_injective
    rw [hk1, p.map_preimage]

/-- The chosen cleavage arrows `χ_{u,y}` are `p`-cartesian in the strict normal-form regime.
@isnad1 id=iscartes.1h9v.s6.ed5a2c2b3791 from=translated src=- shape=c7c42a12 vocab=bf48f680
-/
theorem chi_isCartesian (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    IsCartesianOver p (d.chi u y hy) :=
  d.isCartesian_of_fullyFaithful _

/-- The chosen `χ` make `p` a split Grothendieck fibration (paper `prop:cartesian`, second
    sentence), bundled as one proposition: every chosen arrow `χ_{u,y}` is `p`-cartesian in the
    strong (existence and uniqueness) sense `IsCartesianOver`, and the chosen lifts satisfy the
    four splitting laws of paper `def:data` (N3): `(𝟙 s)^* y = y`, `χ_{𝟙,y} = 𝟙`,
    `(u ≫ v)^* z = u^*(v^* z)` and `χ_{u ≫ v, z} = χ_{u, v^* z} ≫ χ_{v,z}`, up to the displayed
    `eqToHom` casts.  The fibration notion is this file's `IsCartesianOver` together with the
    chosen cleavage; no connection to mathlib's `Functor.IsFibered` API is claimed here.
@isnad1 id=and.0h5v.s9.d70a69c4d807 from=translated src=- shape=1116872e vocab=e60e6647
-/
theorem chi_split_cartesian (d : OEData G p) :
    (∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t), IsCartesianOver p (d.chi u y hy)) ∧
    (∀ {s : S} (y : O) (hy : p.obj y = s), d.reind (𝟙 s) y hy = y) ∧
    (∀ {s : S} (y : O) (hy : p.obj y = s), d.chi (𝟙 s) y hy = eqToHom (d.reind_id y hy)) ∧
    (∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      d.reind (u ≫ v) z hz = d.reind u (d.reind v z hz) (d.p_reind v z hz)) ∧
    (∀ {s t r : S} (u : s ⟶ t) (v : t ⟶ r) (z : O) (hz : p.obj z = r),
      d.chi (u ≫ v) z hz = eqToHom (d.reind_comp u v z hz)
        ≫ d.chi u (d.reind v z hz) (d.p_reind v z hz) ≫ d.chi v z hz) :=
  ⟨fun u y hy => d.chi_isCartesian u y hy, fun y hy => d.reind_id y hy,
    fun y hy => d.chi_id y hy, fun u v z hz => d.reind_comp u v z hz,
    fun u v z hz => d.chi_comp u v z hz⟩

/-- The chosen vertical arrows `ltrans g x` are isomorphisms (the invertibility clause of
    paper `def:data` (N5)).  DERIVED, not assumed: `p.map (ltrans g x)` is an `eqToHom`
    (`p_ltrans`), hence an isomorphism, and the fully faithful `p` (`isFull` + `p_faithful`)
    reflects isomorphisms.
@isnad1 id=isiso.0h7v.s7.21b0030cf371 from=translated src=- shape=1906111f vocab=bbd20ed0
-/
instance ltrans_isIso (d : OEData G p) (g : G) (x : O) : IsIso (d.ltrans g x) := by
  haveI := d.isFull
  haveI := d.p_faithful
  haveI : IsIso (p.map (d.ltrans g x)) := by rw [d.p_ltrans]; infer_instance
  exact isIso_of_reflects_iso (d.ltrans g x) p

/-- The chosen vertical arrow `ltrans g x`, packaged as an isomorphism
    `x ≅ b_{p x} · (g · coord x)` (paper `def:data` (N5)).-/
noncomputable def ltransIso (d : OEData G p) (g : G) (x : O) :
    x ≅ d.act (d.base (p.obj x)) (g * d.coord x) :=
  asIso (d.ltrans g x)

/--
@isnad1 id=eq.0h7v.s7.7dee94ad7299 from=translated src=- shape=d06cb135 vocab=e2199ae9
-/
@[simp] theorem ltransIso_hom (d : OEData G p) (g : G) (x : O) :
    (d.ltransIso g x).hom = d.ltrans g x := rfl

/--
@isnad1 id=eq.0h7v.s8.5201986b5d2e from=translated src=- shape=e3551f08 vocab=62c1d9ac
-/
@[simp] theorem ltransIso_inv (d : OEData G p) (g : G) (x : O) :
    (d.ltransIso g x).inv = inv (d.ltrans g x) := rfl

/-- Projection of the inverse vertical arrow:  `p (ltrans g x)⁻¹` is the reverse `eqToHom`.
@isnad1 id=eq.0h7v.s8.15740f6c6bef from=translated src=- shape=1966293b vocab=0dcd9799
-/
theorem p_map_inv_ltrans (d : OEData G p) (g : G) (x : O) :
    p.map (inv (d.ltrans g x))
      = eqToHom ((d.p_act (d.base (p.obj x)) (g * d.coord x)).trans (d.p_base (p.obj x))) := by
  -- `rw [d.p_ltrans]` under `inv` is ill-typed (the `IsIso` instance depends on the arrow);
  -- characterize the inverse by `inv_eq_of_hom_inv_id` instead.
  rw [p.map_inv]
  exact IsIso.inv_eq_of_hom_inv_id (by rw [d.p_ltrans, eqToHom_trans, eqToHom_refl])

end Tengoku.ObserverEquivarianceLean.OEData

/-! ## 2. The fiber-translation functor Λ_g  (paper `thm:strict`) -/

/-- `Λ d g : O ⥤ O` is the normalized fiber translation by `g`.
    On objects: `x ↦ base (p.obj x) · (g · coord x)`.
    On morphisms it transports along the chosen vertical isomorphisms `ltrans`
    (invertible by `OEData.ltrans_isIso`): `f ↦ (ltrans g x)⁻¹ ≫ f ≫ ltrans g y`.
    This is a functor for any iso family (no naturality needed) and acts on in-fiber
    morphisms via the `G`-action.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.Λ (d : OEData G p) (g : G) : O ⥤ O where
  obj x := d.act (d.base (p.obj x)) (g * d.coord x)
  -- `Λ_g(f)` transports `f` along the translation isos.  This is a functor for ANY
  -- family of isos `ltrans` (no naturality needed); on a vertical `f` it gives the
  -- `g`-translate of `f`, which is the fix the non-discrete model requires.
  map {x y} f := inv (d.ltrans g x) ≫ f ≫ d.ltrans g y
  map_id x := by simp
  map_comp {x y z} f h := by simp

/-- `Λ d g` covers the identity on `S`:  `Λ d g ⋙ p = p`.  (So `Λ d g ∈ ker Φ`.)
@isnad1 id=eq.0h6v.s5.e295d7891cea from=translated src=- shape=bed83558 vocab=a1828a13
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_comp_p (d : OEData G p) (g : G) : Λ d g ⋙ p = p := by
  have hobj : ∀ x, (Λ d g ⋙ p).obj x = p.obj x := fun x =>
    (d.p_act (d.base (p.obj x)) (g * d.coord x)).trans (d.p_base (p.obj x))
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  show p.map (inv (d.ltrans g x) ≫ f ≫ d.ltrans g y) = _
  rw [p.map_comp, p.map_comp, d.p_map_inv_ltrans, d.p_ltrans]
  rfl

/-! ## 2a. Every strict fiber translation is naturally isomorphic to the identity -/

/-- Each strict fiber translation `Λ d g` is NATURALLY ISOMORPHIC to `𝟭 O`, via the chosen
    vertical translations `ltrans` (whose conjugation defines `Λ.map`).  So `Λ_g` is a
    nontrivial element (for `g ≠ 1`) of the STRICT presentation group `AutBoxG` — `ΛHom` is
    injective when `S` is nonempty (`ΛHom_injective` needs `[Nonempty S]`) — even
    though it is `≅ 𝟭` as an autoequivalence; that is the difference between strict presentation
    data and autoequivalences modulo natural isomorphism, not a contradiction.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.idIsoΛ (d : OEData G p) (g : G) : 𝟭 O ≅ Λ d g :=
  NatIso.ofComponents
    (fun x => d.ltransIso g x)
    (fun f => by simp [Λ])

/-- The reverse natural isomorphism `Λ d g ≅ 𝟭 O`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛIsoId (d : OEData G p) (g : G) : Λ d g ≅ 𝟭 O :=
  (idIsoΛ d g).symm

/-! ## 3. Predicates on bundle automorphisms -/

/-- Object-level `G`-equivariance, `F (x · g) = F x · g` — condition `eq:equiv` of the paper's
    `def:lifts`.  The paper's `Sym_H(p)` additionally requires morphism-level equivariance and
    cleavage preservation: the latter is the separate predicate `PreservesCleavage`, while the
    former is DERIVED — given `p` faithful, any object-equivariant `F` covering a base map is
    automatically morphism-equivariant (formalized as `isGEquivariant_map_actHom` in §11),
    exactly as the paper's `def:lifts` remarks.  So `Sym_H(p)` is faithfully
    captured by `IsGEquivariant ∧ PreservesCleavage` (see `AutBoxG` / `AutBoxGOver`).-/
def _root_.Tengoku.ObserverEquivarianceLean.IsGEquivariant (d : OEData G p) (F : O ⥤ O) : Prop :=
  ∀ (x : O) (g : G), F.obj (d.act x g) = d.act (F.obj x) g

/-- `F` covers the base autoequivalence `A`, i.e. `p ∘ F = A ∘ p` strictly.  Not used elsewhere
    in the development; the covering condition used throughout is the field
    `PreservesCleavage.covers` (over a plain functor `A : S ⥤ S`).-/
def _root_.Tengoku.ObserverEquivarianceLean.CoversBase (p : O ⥤ S) (F : O ⥤ O) (A : S ≌ S) : Prop :=
  F ⋙ p = p ⋙ A.functor

/-- Cleavage preservation — condition `eq:preserve` of the paper's `def:lifts` (paper `sec:symmetries`; the field `covers`
    is `eq:cover`), written `□`
    in this file's `Aut□_G` shorthand for `AutBoxG`.  `F` covers `A` and sends each
    chosen cartesian source `u*y` to the chosen cartesian source `(A u)*(F y)`.  This is
    the object-level shadow of "F maps chosen cartesian arrows to chosen cartesian arrows";
    given `p` faithful it is equivalent to the full morphism statement
    `F(χ_{u,y}) = χ_{A u, F y}` (formalized as `PreservesCleavage.map_chi` in §11).
    It is exactly what forces the local constant `g_s` in `rigidity`.-/
structure _root_.Tengoku.ObserverEquivarianceLean.PreservesCleavage (d : OEData G p) (F : O ⥤ O) (A : S ⥤ S) : Prop where
  covers : F ⋙ p = p ⋙ A
  src : ∀ {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t),
    F.obj (d.reind u y hy)
      = d.reind (A.map u) (F.obj y)
          ((Functor.congr_obj covers y).trans (congrArg A.obj hy))

/-! ## 4. The two key lemmas and the main theorem  (paper `sec:symmetries`: `lem:local`,
       `thm:strict`) -/

/-- The strict lift `Ã : O ⥤ O` of a base functor `A : S ⥤ S` (the canonical section
    `A ↦ Ã` of paper `thm:strict`).  On objects
    `x ↦ b_{A(p x)} · coord x`; on morphisms the unique lift (`p` is fully faithful) of
    `A (p f)`.  Functoriality is automatic from faithfulness.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftFunctor (d : OEData G p) (A : S ⥤ S) : O ⥤ O :=
  haveI := d.isFull
  haveI := d.p_faithful
  { obj := fun x => d.act (d.base (A.obj (p.obj x))) (d.coord x)
    map := fun {x y} f =>
      p.preimage (eqToHom (d.p_liftObj A x) ≫ A.map (p.map f) ≫ eqToHom (d.p_liftObj A y).symm)
    map_id := fun x => by
      refine p.map_injective ?_
      simp [eqToHom_trans]
    map_comp := fun {x y z} f g => by
      refine p.map_injective ?_
      simp [p.map_preimage, p.map_comp, Category.assoc] }

/-- The lift is `G`-equivariant.
@isnad1 id=isgequiv.0h6v.s5.a3b017ae80a3 from=translated src=- shape=7bb549ad vocab=626f9e49
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.lift_isGEquivariant (d : OEData G p) (A : S ⥤ S) :
    IsGEquivariant d (liftFunctor d A) := by
  intro x g
  show d.act (d.base (A.obj (p.obj (d.act x g)))) (d.coord (d.act x g))
     = d.act (d.act (d.base (A.obj (p.obj x))) (d.coord x)) g
  rw [d.p_act, d.coord_act, d.act_mul]

/-- The lift covers `A` and preserves the chosen cleavage.
@isnad1 id=preserve.0h6v.s5.02c420066bda from=translated src=- shape=96267c29 vocab=9207ab3b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.lift_preservesCleavage (d : OEData G p) (A : S ⥤ S) :
    PreservesCleavage d (liftFunctor d A) A where
  covers := by
    have hobj : ∀ x, (liftFunctor d A ⋙ p).obj x = (p ⋙ A).obj x := fun x => d.p_liftObj A x
    refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
    haveI := d.isFull
    haveI := d.p_faithful
    show p.map (p.preimage (eqToHom (d.p_liftObj A x) ≫ A.map (p.map f)
        ≫ eqToHom (d.p_liftObj A y).symm)) = _
    rw [p.map_preimage]
    rfl
  src u y hy := by
    simp only [liftFunctor, d.reind_eq, d.coord_base, d.p_act, d.p_base]

/-- Existence of lifts (paper `thm:strict`: the canonical section gives surjectivity of `Φ`).  Every base autoequivalence lifts to a
    `G`-equivariant, cleavage-preserving bundle *functor* covering it — a witness of the three
    predicates, NOT yet a bundled element of `AutBoxG` with a strict inverse (that packaging is
    `liftAut`).  The name reflects the ∃-statement it actually proves.
@isnad1 id=ex.0h6v.s6.547838521a92 from=translated src=- shape=46e4fb6c vocab=eb18bb7a
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.lift_exists (d : OEData G p) (A : S ≌ S) :
    ∃ F : O ⥤ O, IsGEquivariant d F ∧ PreservesCleavage d F A.functor :=
  ⟨liftFunctor d A.functor, lift_isGEquivariant d A.functor, lift_preservesCleavage d A.functor⟩

/-- Alias of `lift_exists`.
@isnad1 id=ex.0h6v.s6.547838521a92 from=translated src=- shape=46e4fb6c vocab=eb18bb7a
-/
alias Tengoku.ObserverEquivarianceLean.strict_lift := lift_exists

/-- Two equivariant functors covering the same base (i.e. equal after `⋙ p`) that agree on
    objects are equal (`p` faithful: the morphism values have equal source/target and
    projection).  Used by both `rigidity` and `rigidityθ`, and throughout §§6–9.
@isnad1 id=eq.2h7v.s6.6274aee6b23b from=translated src=- shape=eea32299 vocab=acca56f1
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.funct_ext (d : OEData G p) {F₁ F₂ : O ⥤ O} (hobj : ∀ x, F₁.obj x = F₂.obj x)
    (hcomp : F₁ ⋙ p = F₂ ⋙ p) : F₁ = F₂ := by
  haveI := d.p_faithful
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  apply p.map_injective
  rw [p.map_comp, p.map_comp, eqToHom_map, eqToHom_map]
  exact Functor.congr_hom hcomp f

/-- Lemma (Rigidity, paper `thm:strict`).  Two cleavage-preserving equivariant lifts of the same base
    autoequivalence differ by a unique normalized fiber translation.  (Uses `S` connected
    for the constancy of the local element `g_s`, and `p` faithful for the morphism step.)
@isnad1 id=existsun.4h8v.s7.be4296eca093 from=translated src=- shape=7313d696 vocab=4971afaf
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.rigidity (d : OEData G p) (A : S ≌ S) [IsConnected S] (F₁ F₂ : O ⥤ O)
    (h₁ : IsGEquivariant d F₁) (h₂ : IsGEquivariant d F₂)
    (pc₁ : PreservesCleavage d F₁ A.functor) (pc₂ : PreservesCleavage d F₂ A.functor) :
    ∃! g : G, F₂ = F₁ ⋙ Λ d g := by
  haveI := d.p_faithful
  -- Object form of an equivariant lift covering `A`:  F x = b_{A(p x)} · (k(p x) · coord x).
  have Fobj : ∀ (F : O ⥤ O), IsGEquivariant d F → F ⋙ p = p ⋙ A.functor → ∀ x,
      F.obj x = d.act (d.base (A.functor.obj (p.obj x)))
                  (d.coord (F.obj (d.base (p.obj x))) * d.coord x) := by
    intro F hF hc x
    have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (d.coord x) := by
      conv_lhs => rw [← d.base_coord x]
      exact hF _ _
    have e2 : F.obj (d.base (p.obj x))
        = d.act (d.base (A.functor.obj (p.obj x))) (d.coord (F.obj (d.base (p.obj x)))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base (p.obj x)))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base (p.obj x))).trans
        (congrArg A.functor.obj (d.p_base (p.obj x))))
    rw [e1, ← d.act_mul, ← e2]
  -- Local constancy of `k` from cleavage preservation:  u : s ⟶ t ⇒ k s = k t.
  have kconst : ∀ (F : O ⥤ O), F ⋙ p = p ⋙ A.functor → PreservesCleavage d F A.functor →
      ∀ {s t : S}, (s ⟶ t) → d.coord (F.obj (d.base s)) = d.coord (F.obj (d.base t)) := by
    intro F hc pc s t u
    have key := pc.src u (d.base t) (d.p_base t)
    rw [d.reind_base, d.reind_eq] at key
    have hFs : F.obj (d.base s)
        = d.act (d.base (A.functor.obj s)) (d.coord (F.obj (d.base s))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base s))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base s)).trans
        (congrArg A.functor.obj (d.p_base s)))
    rw [hFs] at key
    exact d.act_free _ _ _ key
  -- `k₁`, `k₂` are globally constant since `S` is connected.
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have k₁c : ∀ s, d.coord (F₁.obj (d.base s)) = d.coord (F₁.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₁.obj (d.base s)))
      (fun _ _ u => kconst F₁ pc₁.covers pc₁ u) s s₀
  have k₂c : ∀ s, d.coord (F₂.obj (d.base s)) = d.coord (F₂.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₂.obj (d.base s)))
      (fun _ _ u => kconst F₂ pc₂.covers pc₂ u) s s₀
  have hcovΛ : ∀ g, (F₁ ⋙ Λ d g) ⋙ p = p ⋙ A.functor := by
    intro g
    rw [Functor.assoc, Λ_comp_p]; exact pc₁.covers
  refine ⟨d.coord (F₂.obj (d.base s₀)) * (d.coord (F₁.obj (d.base s₀)))⁻¹, ?_, ?_⟩
  · -- F₂ = F₁ ⋙ Λ d g
    refine funct_ext d (fun x => ?_) ?_
    · -- objects
      rw [Fobj F₂ h₂ pc₂.covers x]
      show _ = (Λ d _).obj (F₁.obj x)
      rw [Fobj F₁ h₁ pc₁.covers x]
      simp only [Λ, d.p_act, d.p_base, d.coord_base]
      rw [k₂c (p.obj x), k₁c (p.obj x)]
      congr 1
      group
    · rw [pc₂.covers]; exact (hcovΛ _).symm
  · -- uniqueness:  any `g'` with `F₂ = F₁ ⋙ Λ d g'` equals `g` (evaluate at `b_{s₀}`)
    intro g' hg'
    have hev := congrArg (fun (F : O ⥤ O) => d.coord (F.obj (d.base s₀))) hg'
    simp only [Functor.comp_obj, Λ, d.coord_base] at hev
    -- hev : coord (F₂ b_{s₀}) = g' * coord (F₁ b_{s₀})
    rw [hev]; group

/-- `𝟭 O` is `G`-equivariant.
@isnad1 id=isgequiv.0h5v.s5.5d13a064fcd8 from=translated src=- shape=3bc2011f vocab=be4dc360
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.id_isGEquivariant (d : OEData G p) : IsGEquivariant d (𝟭 O) := fun _ _ => rfl

/-- `𝟭 O` preserves the chosen cleavage (over `id_S`).
@isnad1 id=preserve.0h5v.s5.4d7727cd54da from=translated src=- shape=986640aa vocab=aac95e02
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.id_preservesCleavage (d : OEData G p) :
    PreservesCleavage d (𝟭 O) (𝟭 S) where
  covers := by rw [Functor.id_comp, Functor.comp_id]
  src _ _ _ := rfl

/-- `Λ d g` is `G`-equivariant.
@isnad1 id=isgequiv.0h6v.s5.0d8add415838 from=translated src=- shape=69b9f106 vocab=6e22a262
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_isGEquivariant (d : OEData G p) (g : G) : IsGEquivariant d (Λ d g) := by
  intro x h
  show d.act (d.base (p.obj (d.act x h))) (g * d.coord (d.act x h))
     = d.act (d.act (d.base (p.obj x)) (g * d.coord x)) h
  rw [d.p_act, d.coord_act, d.act_mul, mul_assoc]

/-- `Λ d g` preserves the chosen cleavage (over `id_S`), hence lies in `ker Φ`.
@isnad1 id=preserve.0h6v.s5.bab1c6ff59a3 from=translated src=- shape=1b29b0e0 vocab=10193d05
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_preservesCleavage (d : OEData G p) (g : G) :
    PreservesCleavage d (Λ d g) (𝟭 S) where
  covers := by rw [Λ_comp_p, Functor.comp_id]
  src u y hy := by
    simp only [Λ, d.reind_eq, d.coord_base, d.p_act, d.p_base, Functor.id_obj]

/-- Unbundled lift classification (paper `thm:strict`), functor-level form.

    First conjunct: unbundled existence of lifts.  Every equivalence `A : S ≌ S` has a
    `G`-equivariant functor `F : O ⥤ O` preserving the cleavage over `A.functor`.  This `F` is a
    bare functor with no strict inverse, so the conjunct is NOT a statement about the group
    `Aut□_G(O/p)`.  Second conjunct: kernel characterization.  A `G`-equivariant functor
    preserves the cleavage over `𝟭 S` iff it is a normalized fiber translation `Λ d g`.
    The group-level short exact sequence  1 → G → Aut□_G(O/p) → Aut(S) → 1  is the separate
    package `Φ_surjective` / `ΛHom_injective` / `ker_Φ_eq_range_Λ`.
@isnad1 id=and.0h5v.s7.5473528b2f37 from=translated src=- shape=0bde4317 vocab=737ebaae
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.unbundled_lift_classification (d : OEData G p) [IsConnected S] :
    (∀ A : S ≌ S, ∃ F : O ⥤ O, IsGEquivariant d F ∧ PreservesCleavage d F A.functor) ∧
    (∀ F : O ⥤ O, IsGEquivariant d F →
        (PreservesCleavage d F (𝟭 S) ↔ ∃ g : G, F = Λ d g)) := by
  refine ⟨fun A => lift_exists d A, ?_⟩
  intro F hF
  constructor
  · -- F ∈ ker Φ ⇒ F = Λ d g, via `rigidity` with F₁ = 𝟭 O, A = refl.
    intro hpc
    obtain ⟨g, hg, _⟩ := rigidity d (CategoryTheory.Equivalence.refl) (𝟭 O) F
      (id_isGEquivariant d) hF (id_preservesCleavage d) hpc
    exact ⟨g, by simpa only [Functor.id_comp] using hg⟩
  · -- Λ d g is cleavage-preserving over `id_S`, hence ∈ ker Φ.
    rintro ⟨g, rfl⟩
    exact Λ_preservesCleavage d g

/-- Alias of `unbundled_lift_classification`.  The group-theoretic short exact sequence is the
    separate `Φ_surjective` / `ΛHom_injective` / `ker_Φ_eq_range_Λ` package.
@isnad1 id=and.0h5v.s7.5473528b2f37 from=translated src=- shape=0bde4317 vocab=737ebaae
-/
alias Tengoku.ObserverEquivarianceLean.exact_sequence := unbundled_lift_classification

/-! ## 5. Non-degeneracy witness

  A concrete `OEData G (pWit G)` for an ARBITRARY group `G`.  It shows the structure is
  instantiable and — crucially — that `p_faithful` (thin fibers) coexists with `|G| > 1`,
  so thin fibers do not force `G` to be trivial.  `indiscrete ≠ discrete`:

  The fiber is the PAIR (codiscrete) groupoid on `G` — objects are the `|G|` group elements,
  with exactly ONE morphism between any two.  It is thin (⇒ `p` faithful) and connected, and it
  is NON-discrete: between distinct objects the hom-set is `PUnit`, not `∅`.  That non-empty
  hom is exactly what dodges the collapse (discrete fibers + flat section + connected `O`
  ⇒ `G` trivial).  Taking `G = Multiplicative (ZMod 2)` gives `|G| = 2` (see `witness₂`). -/

/-- The pair groupoid on a type `X` (the paper's `Pair(X)`; also called the codiscrete or
    indiscrete groupoid): exactly one morphism between any two objects.-/
structure _root_.Tengoku.ObserverEquivarianceLean.Pair (X : Type*) where pt : X

instance (X : Type*) : Groupoid (Pair X) where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl
  inv _ := ⟨⟩
  inv_comp _ := rfl
  comp_inv _ := rfl

/--
@isnad1 id=subsingl.0h3v.s4.bb5dc8656ff4 from=translated src=- shape=8e8062c2 vocab=9156a554
-/
instance Tengoku.ObserverEquivarianceLean.Pair.homSubsingleton {X : Type*} (a b : Pair X) : Subsingleton (a ⟶ b) :=
  ⟨fun _ _ => rfl⟩

/-- Witness projection: forget everything down to the one-object base `Pair PUnit`.-/
def _root_.Tengoku.ObserverEquivarianceLean.pWit (G : Type*) : Pair G ⥤ Pair PUnit where
  obj _ := ⟨PUnit.unit⟩
  map _ := ⟨⟩

/-- `OEData` is instantiable for EVERY group `G`, with thin fibers of size `|G|`.  Hence
    `p_faithful` is consistent with nontrivial `G`: no discrete-fiber degeneracy.-/
def _root_.Tengoku.ObserverEquivarianceLean.witness (G : Type*) [Group G] : OEData G (pWit G) where
  act x g := ⟨x.pt * g⟩
  act_one x := by simp
  act_mul x g h := by simp [mul_assoc]
  p_act _ _ := rfl
  act_free x g h e := mul_left_cancel (congrArg Pair.pt e)
  actHom _ _ := ⟨⟩
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  actHom_one _ := rfl
  actHom_mul _ _ _ := rfl
  p_actHom _ _ := rfl
  base _ := ⟨1⟩
  p_base _ := rfl
  coord x := x.pt
  base_coord x := by simp
  coord_base _ g := by simp
  reind _ y _ := y
  p_reind _ _ _ := rfl
  chi _ _ _ := ⟨⟩
  p_chi _ _ _ := rfl
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act _ _ _ _ := rfl
  ltrans _ _ := ⟨⟩
  p_ltrans _ _ := rfl
  reind_id _ _ := rfl
  chi_id _ _ := rfl
  reind_comp _ _ _ _ := rfl
  chi_comp _ _ _ _ := rfl
  p_faithful := ⟨fun _ => rfl⟩

/-- A concrete instantiation with a NONTRIVIAL structure group (`|G| = 2`): the witness
    is genuinely non-degenerate, with a 2-object connected (codiscrete) fiber.-/
def _root_.Tengoku.ObserverEquivarianceLean.witness₂ : OEData (Multiplicative (ZMod 2)) (pWit (Multiplicative (ZMod 2))) :=
  witness _

/-! ## 6. The exact sequence as a group statement (paper `thm:strict`)

  We package the result as genuine group theory.  The base symmetries `Aut(S)` and the
  bundle automorphisms `Aut□_G(O/p)` must be STRICT (on-the-nose) automorphisms: with
  `CategoryTheory.Equivalence` (`≌`, up-to-iso) there is no strict inverse, and `Λ_g ≅ 𝟭`
  would collapse the kernel.  This matches the paper's `Aut(S)` = the group of strict
  automorphisms (functors with a strict two-sided inverse).  No new `OEData` assumption is used. -/

/-- A strict automorphism of a category `C`: a functor with a strict two-sided inverse
    (an isomorphism in `Cat`).  These form the group `Aut(C)` of strict autoequivalences.-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.StrictAut (C : Type*) [Category C] where
  hom : C ⥤ C
  inv : C ⥤ C
  hom_inv_id : hom ⋙ inv = 𝟭 C
  inv_hom_id : inv ⋙ hom = 𝟭 C

namespace Tengoku.ObserverEquivarianceLean.StrictAut
variable {C : Type*} [Category C]

/-- Group of strict automorphisms.  Multiplication is composition `e₁ * e₂ = e₁ ∘ e₂`
    (apply `e₂` then `e₁`), so `(·).hom` / `(·).inv` are (anti)homomorphisms.-/
instance : Group (StrictAut C) where
  mul e₁ e₂ := ⟨e₂.hom ⋙ e₁.hom, e₁.inv ⋙ e₂.inv, by
      show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 C
      rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id], by
      show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 C
      rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]⟩
  one := ⟨𝟭 C, 𝟭 C, rfl, rfl⟩
  inv e := ⟨e.inv, e.hom, e.inv_hom_id, e.hom_inv_id⟩
  mul_assoc a b c := by ext <;> rfl
  one_mul a := by ext <;> rfl
  mul_one a := by ext <;> rfl
  inv_mul_cancel a := by ext <;> exact a.hom_inv_id

/--
@isnad1 id=eq.0h1v.s5.f6d1e3872338 from=translated src=- shape=462cbb7c vocab=919e78da
-/
@[simp] lemma one_hom : (1 : StrictAut C).hom = 𝟭 C := rfl
/--
@isnad1 id=eq.0h1v.s5.6dd1cf58fe02 from=translated src=- shape=462cbb7c vocab=9b46d230
-/
@[simp] lemma one_inv : (1 : StrictAut C).inv = 𝟭 C := rfl
/--
@isnad1 id=eq.0h3v.s6.ff27fb68df7c from=translated src=- shape=d61733c0 vocab=4063bf98
-/
@[simp] lemma mul_hom (e₁ e₂ : StrictAut C) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl

end Tengoku.ObserverEquivarianceLean.StrictAut

/-! ### Closure of the bundle-automorphism conditions under `⋙` and inverse -/

variable (d : OEData G p)

/-- `G`-equivariance is closed under composition.
@isnad1 id=isgequiv.2h7v.s6.62124b45e585 from=translated src=- shape=54328d23 vocab=27caf3b4
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isGEquivariant_comp {F F' : O ⥤ O}
    (h : IsGEquivariant d F) (h' : IsGEquivariant d F') : IsGEquivariant d (F ⋙ F') :=
  fun x g => by
    show F'.obj (F.obj (d.act x g)) = d.act (F'.obj (F.obj x)) g
    rw [h x g, h' (F.obj x) g]

/-- `G`-equivariance transfers to a strict inverse.
@isnad1 id=isgequiv.3h7v.s6.82acfc950003 from=translated src=- shape=2f4eda1a vocab=6e32147c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isGEquivariant_inv {F Finv : O ⥤ O} (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O)
    (h : IsGEquivariant d F) : IsGEquivariant d Finv := by
  have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
    have := Functor.congr_obj ih z; simpa using this
  have hinj : Function.Injective F.obj := fun a b hab => by
    have := congrArg Finv.obj hab
    have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
      have := Functor.congr_obj hi z; simpa using this
    rw [e, e] at this; exact this
  intro x g
  apply hinj
  rw [h (Finv.obj x) g, hFcancel, hFcancel]

/-- Cleavage preservation is closed under composition.
@isnad1 id=preserve.2h9v.s6.87a78c346452 from=translated src=- shape=0631142c vocab=26ce36ec
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.preservesCleavage_comp {F F' : O ⥤ O} {A A' : S ⥤ S}
    (pc : PreservesCleavage d F A) (pc' : PreservesCleavage d F' A') :
    PreservesCleavage d (F ⋙ F') (A ⋙ A') where
  covers := by rw [Functor.assoc, pc'.covers, ← Functor.assoc, pc.covers, Functor.assoc]
  src u y hy := by
    simp only [Functor.comp_obj, Functor.comp_map]
    rw [pc.src u y hy, pc'.src]

/-- Cleavage preservation transfers to a strict inverse (with the inverse base).
@isnad1 id=preserve.3h8v.s6.e8dac385024f from=translated src=- shape=b0070b36 vocab=aa91393c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.preservesCleavage_inv {F Finv : O ⥤ O} {B : StrictAut S}
    (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O)
    (pc : PreservesCleavage d F B.hom) : PreservesCleavage d Finv B.inv where
  covers := by
    have h1 : (Finv ⋙ p) ⋙ B.hom = p := by
      rw [Functor.assoc, ← pc.covers, ← Functor.assoc, ih, Functor.id_comp]
    calc Finv ⋙ p
        = (Finv ⋙ p) ⋙ B.hom ⋙ B.inv := by rw [B.hom_inv_id, Functor.comp_id]
      _ = ((Finv ⋙ p) ⋙ B.hom) ⋙ B.inv := rfl
      _ = p ⋙ B.inv := by rw [h1]
  src u y hy := by
    have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
      have := Functor.congr_obj ih z; simpa using this
    have hinj : Function.Injective F.obj := fun a b hab => by
      have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
        have := Functor.congr_obj hi z; simpa using this
      have := congrArg Finv.obj hab; rw [e, e] at this; exact this
    apply hinj
    rw [hFcancel, pc.src (B.inv.map u) (Finv.obj y)]
    simp only [d.reind_eq, hFcancel]
    congr 1
    exact congrArg d.base (Functor.congr_obj B.inv_hom_id _).symm

/-- `Λ` is trivial at the identity:  `Λ d 1 = 𝟭 O`.
@isnad1 id=eq.0h5v.s5.3698d952d957 from=translated src=- shape=9ecb265a vocab=61201780
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_one : Λ d (1 : G) = 𝟭 O :=
  funct_ext d (fun x => by
    show d.act (d.base (p.obj x)) (1 * d.coord x) = x
    rw [one_mul, d.base_coord]) (by rw [Λ_comp_p, Functor.id_comp])

/-- `Λ` is an (anti)homomorphism:  `Λ d g ⋙ Λ d h = Λ d (h * g)`.
@isnad1 id=eq.0h7v.s6.d8e8ed85a339 from=translated src=- shape=1796e47f vocab=0aa580a5
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_comp (g h : G) : Λ d g ⋙ Λ d h = Λ d (h * g) :=
  funct_ext d (fun x => by
    simp only [Functor.comp_obj, Λ, d.p_act, d.p_base, d.coord_base, mul_assoc])
    (by rw [Functor.assoc, Λ_comp_p, Λ_comp_p, Λ_comp_p])

/-! ### Translation by an object function  `ΛFun d γ`

  The fiber translation with a multiplier `γ : S → G` that may vary with the base object
  (paper `lem:local`, `prop:components`): `x ↦ b_{p x} · (γ(p x) · coord x)`, transported on
  morphisms along the vertical isomorphisms `ltrans`.  `Λ d g` is the constant case
  (`ΛFun_const`); `ΛFun d γ` preserves the chosen cleavage iff `γ` is constant along every base
  arrow (`ΛFun_preservesCleavage_iff`). -/

/-- Fiber translation by an object function `γ : S → G` (paper `lem:local`):
    `x ↦ b_{p x} · (γ(p x) · coord x)`, `f ↦ (ltrans_{γ(p x)} x)⁻¹ ≫ f ≫ ltrans_{γ(p y)} y`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛFun (d : OEData G p) (γ : S → G) : O ⥤ O where
  obj x := d.act (d.base (p.obj x)) (γ (p.obj x) * d.coord x)
  map {x y} f := inv (d.ltrans (γ (p.obj x)) x) ≫ f ≫ d.ltrans (γ (p.obj y)) y
  map_id x := by simp
  map_comp {x y z} f h := by simp

/-- `ΛFun d γ` covers the identity on `S`:  `ΛFun d γ ⋙ p = p` (paper `lem:local`).
@isnad1 id=eq.0h6v.s5.c5f8427ab5ae from=translated src=- shape=93b31550 vocab=9885dc8c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_comp_p (d : OEData G p) (γ : S → G) : ΛFun d γ ⋙ p = p := by
  have hobj : ∀ x, (ΛFun d γ ⋙ p).obj x = p.obj x := fun x =>
    (d.p_act (d.base (p.obj x)) (γ (p.obj x) * d.coord x)).trans (d.p_base (p.obj x))
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  show p.map (inv (d.ltrans (γ (p.obj x)) x) ≫ f ≫ d.ltrans (γ (p.obj y)) y) = _
  rw [p.map_comp, p.map_comp, d.p_map_inv_ltrans, d.p_ltrans]
  rfl

/-- A constant object function gives the ordinary fiber translation:
    `ΛFun d (fun _ => g) = Λ d g` (paper `lem:local`).
@isnad1 id=eq.0h6v.s5.94ad2b4ef3ae from=translated src=- shape=900c73e7 vocab=90b50342
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_const (d : OEData G p) (g : G) : ΛFun d (fun _ => g) = Λ d g := rfl

/-- The trivial object function gives the identity:  `ΛFun d 1 = 𝟭 O` (paper `lem:local`).
@isnad1 id=eq.0h5v.s6.e5e6a6324d22 from=translated src=- shape=2171154c vocab=e4ba4395
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_one (d : OEData G p) : ΛFun d 1 = 𝟭 O :=
  funct_ext d (fun x => by
    show d.act (d.base (p.obj x)) ((1 : S → G) (p.obj x) * d.coord x) = x
    rw [Pi.one_apply, one_mul, d.base_coord]) (by rw [ΛFun_comp_p, Functor.id_comp])

/-- Composition of object-function translations multiplies the multipliers pointwise, in the
    same (anti) order as `Λ_comp`:  `ΛFun d γ ⋙ ΛFun d δ = ΛFun d (δ * γ)`
    (paper `lem:local`).
@isnad1 id=eq.0h7v.s6.a69e59493a8f from=translated src=- shape=735071c2 vocab=008a6d70
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_comp (d : OEData G p) (γ δ : S → G) : ΛFun d γ ⋙ ΛFun d δ = ΛFun d (δ * γ) :=
  funct_ext d (fun x => by
    simp only [Functor.comp_obj, ΛFun, d.p_act, d.p_base, d.coord_base, Pi.mul_apply, mul_assoc])
    (by rw [Functor.assoc, ΛFun_comp_p, ΛFun_comp_p, ΛFun_comp_p])

/-- `ΛFun d γ` is `G`-equivariant (paper `lem:local`).
@isnad1 id=isgequiv.0h6v.s5.ea4510d8ae42 from=translated src=- shape=fd16ceba vocab=1a75599e
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_isGEquivariant (d : OEData G p) (γ : S → G) : IsGEquivariant d (ΛFun d γ) := by
  intro x h
  show d.act (d.base (p.obj (d.act x h))) (γ (p.obj (d.act x h)) * d.coord (d.act x h))
     = d.act (d.act (d.base (p.obj x)) (γ (p.obj x) * d.coord x)) h
  rw [d.p_act, d.coord_act, d.act_mul, mul_assoc]

/-- `ΛFun d γ` preserves the chosen cleavage (over `id_S`) iff its multiplier is constant along
    every base arrow (paper `lem:local`, `prop:components`).
@isnad1 id=iff.0h6v.s6.868e28afaa11 from=translated src=- shape=1c2e48a2 vocab=71a7c55c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛFun_preservesCleavage_iff (d : OEData G p) (γ : S → G) :
    PreservesCleavage d (ΛFun d γ) (𝟭 S) ↔ ∀ {s t : S} (_ : s ⟶ t), γ s = γ t := by
  constructor
  · intro pc s t u
    have key := pc.src u (d.base t) (d.p_base t)
    simp only [ΛFun, d.reind_eq, d.coord_base, d.p_act, d.p_base, Functor.id_obj,
      Functor.id_map] at key
    have hc : d.coord (d.base t) = 1 := by
      have h1 := d.coord_base t 1; rwa [d.act_one] at h1
    have hf := d.act_free _ _ _ key
    simpa only [hc, mul_one] using hf
  · intro hγ
    refine ⟨by rw [ΛFun_comp_p, Functor.comp_id], ?_⟩
    intro s t u y hy
    subst hy
    simp only [ΛFun, d.reind_eq, d.coord_base, d.p_act, d.p_base, Functor.id_obj,
      Functor.id_map]
    rw [hγ u]

/-- A bundle automorphism: a strict autoequivalence `hom` of `O` that is `G`-equivariant and
    preserves the cleavage over the strict base automorphism `base`.  Forms `Aut□_G(O/p)`.-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.AutBoxG (d : OEData G p) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : StrictAut S
  equiv : IsGEquivariant d hom
  pres : PreservesCleavage d hom base.hom

namespace Tengoku.ObserverEquivarianceLean.AutBoxG

instance : Group (AutBoxG d) where
  mul e₁ e₂ :=
    { hom := e₂.hom ⋙ e₁.hom
      inv := e₁.inv ⋙ e₂.inv
      hom_inv_id := by
        show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 O
        rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id]
      inv_hom_id := by
        show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 O
        rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]
      base := e₁.base * e₂.base
      equiv := isGEquivariant_comp d e₂.equiv e₁.equiv
      pres := preservesCleavage_comp d e₂.pres e₁.pres }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, id_isGEquivariant d, id_preservesCleavage d⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := isGEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      pres := preservesCleavage_inv d e.hom_inv_id e.inv_hom_id e.pres }
  mul_assoc a b c := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutBoxG.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutBoxG.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

/--
@isnad1 id=eq.0h7v.s7.948cd0053bd9 from=translated src=- shape=4aa5c957 vocab=53b540e5
-/
@[simp] lemma mul_hom (e₁ e₂ : AutBoxG d) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
/--
@isnad1 id=eq.0h7v.s7.1fd24db15616 from=translated src=- shape=f25a88cb vocab=be0c30a2
-/
@[simp] lemma mul_base (e₁ e₂ : AutBoxG d) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
/--
@isnad1 id=eq.0h5v.s6.c1a2f2a8610d from=translated src=- shape=3c977eb5 vocab=cb102685
-/
@[simp] lemma one_hom : (1 : AutBoxG d).hom = 𝟭 O := rfl
/--
@isnad1 id=eq.0h5v.s7.19746d4210d8 from=translated src=- shape=d9b421de vocab=3bdcd00c
-/
@[simp] lemma one_base : (1 : AutBoxG d).base = 1 := rfl

end Tengoku.ObserverEquivarianceLean.AutBoxG

/-- The lift is a strict homomorphism:  `liftFunctor A ⋙ liftFunctor B = liftFunctor (A ⋙ B)`.
@isnad1 id=eq.0h7v.s6.e7bb00df5a22 from=translated src=- shape=28584f1d vocab=2dead7c9
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.lift_comp (d : OEData G p) (A B : S ⥤ S) :
    liftFunctor d A ⋙ liftFunctor d B = liftFunctor d (A ⋙ B) :=
  funct_ext d
    (fun x => by simp only [Functor.comp_obj, liftFunctor, d.p_act, d.p_base, d.coord_base])
    (by rw [Functor.assoc, (lift_preservesCleavage d B).covers, ← Functor.assoc,
        (lift_preservesCleavage d A).covers, Functor.assoc, (lift_preservesCleavage d (A ⋙ B)).covers])

/-- The lift of the identity is the identity.
@isnad1 id=eq.0h5v.s5.df1d58b55758 from=translated src=- shape=9cb99d8e vocab=4b218394
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.lift_id (d : OEData G p) : liftFunctor d (𝟭 S) = 𝟭 O :=
  funct_ext d
    (fun x => by
      show d.act (d.base ((𝟭 S).obj (p.obj x))) (d.coord x) = x
      rw [Functor.id_obj, d.base_coord])
    (by rw [(lift_preservesCleavage d (𝟭 S)).covers, Functor.comp_id, Functor.id_comp])

/-- `Φ : Aut□_G(O/p) →* Aut(S)`:  the projection sending a bundle automorphism to the base
    symmetry it covers.  (This is the `Φ` of the short exact sequence.)-/
def _root_.Tengoku.ObserverEquivarianceLean.Φ (d : OEData G p) : AutBoxG d →* StrictAut S where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `Λ : G →* Aut□_G(O/p)`:  the normalized fiber-translation embedding.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛHom (d : OEData G p) : G →* AutBoxG d where
  toFun g :=
    { hom := Λ d g
      inv := Λ d g⁻¹
      hom_inv_id := by rw [Λ_comp, inv_mul_cancel, Λ_one]
      inv_hom_id := by rw [Λ_comp, mul_inv_cancel, Λ_one]
      base := 1
      equiv := Λ_isGEquivariant d g
      pres := Λ_preservesCleavage d g }
  map_one' := by
    refine AutBoxG.ext ?_ ?_ ?_
    · exact Λ_one d
    · show Λ d (1 : G)⁻¹ = 𝟭 O; rw [inv_one, Λ_one]
    · rfl
  map_mul' g h := by
    refine AutBoxG.ext ?_ ?_ ?_
    · show Λ d (g * h) = Λ d h ⋙ Λ d g; rw [Λ_comp]
    · show Λ d (g * h)⁻¹ = Λ d g⁻¹ ⋙ Λ d h⁻¹; rw [Λ_comp, mul_inv_rev]
    · rfl

/--
@isnad1 id=eq.0h6v.s7.92290a11b9bc from=translated src=- shape=b28e34c7 vocab=97a1c567
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHom_base (d : OEData G p) (g : G) : (ΛHom d g).base = 1 := rfl

/-- The canonical strict lift of a base automorphism, bundled as an element of `AutBoxG`
    (paper `sec:symmetries`, `thm:strict`).  `hom`/`inv` are `liftFunctor` of `A.hom`/`A.inv`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftAut (d : OEData G p) (A : StrictAut S) : AutBoxG d where
  hom := liftFunctor d A.hom
  inv := liftFunctor d A.inv
  hom_inv_id := by rw [lift_comp, A.hom_inv_id, lift_id]
  inv_hom_id := by rw [lift_comp, A.inv_hom_id, lift_id]
  base := A
  equiv := lift_isGEquivariant d A.hom
  pres := lift_preservesCleavage d A.hom

/--
@isnad1 id=eq.0h6v.s6.32349ab7c414 from=translated src=- shape=0e7fdefc vocab=b5b32892
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftAut_hom (d : OEData G p) (A : StrictAut S) :
    (liftAut d A).hom = liftFunctor d A.hom := rfl
/--
@isnad1 id=eq.0h6v.s6.d81e7e06872d from=translated src=- shape=0e7fdefc vocab=2f884fd4
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftAut_inv (d : OEData G p) (A : StrictAut S) :
    (liftAut d A).inv = liftFunctor d A.inv := rfl
/--
@isnad1 id=eq.0h6v.s5.c1bbfa168a23 from=translated src=- shape=2ac2150a vocab=5b10ff3f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftAut_base (d : OEData G p) (A : StrictAut S) :
    (liftAut d A).base = A := rfl

/--
@isnad1 id=eq.0h6v.s7.e9e195c41fd8 from=translated src=- shape=9ca8b5dd vocab=1a6ea30b
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.Φ_liftAut (d : OEData G p) (A : StrictAut S) :
    Φ d (liftAut d A) = A := rfl

/-- The canonical section homomorphism `StrictAut S →* AutBoxG d`, `A ↦ liftAut d A`.
    A genuine group hom because `liftFunctor` respects composition (`lift_comp`) and identity
    (`lift_id`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftHom (d : OEData G p) : StrictAut S →* AutBoxG d where
  toFun := liftAut d
  map_one' := by
    refine AutBoxG.ext ?_ ?_ ?_
    · show liftFunctor d (1 : StrictAut S).hom = 𝟭 O
      rw [StrictAut.one_hom]; exact lift_id d
    · show liftFunctor d (1 : StrictAut S).inv = 𝟭 O
      rw [StrictAut.one_inv]; exact lift_id d
    · rfl
  map_mul' A B := by
    refine AutBoxG.ext ?_ ?_ ?_
    · show liftFunctor d (A * B).hom = liftFunctor d B.hom ⋙ liftFunctor d A.hom
      rw [StrictAut.mul_hom, lift_comp]
    · show liftFunctor d (A.inv ⋙ B.inv) = liftFunctor d A.inv ⋙ liftFunctor d B.inv
      exact (lift_comp d A.inv B.inv).symm
    · rfl

/-- `Φ` is surjective:  every strict base automorphism is covered by the canonical lift
    (`⇒` surjectivity of the exact sequence).
@isnad1 id=surjecti.0h5v.s7.e3c1c95ff08d from=translated src=- shape=c3cd218f vocab=8ae4b355
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Φ_surjective (d : OEData G p) : Function.Surjective (Φ d) :=
  fun A => ⟨liftAut d A, rfl⟩

/-- `Λ` is injective (needs a basepoint; freeness of the action does the rest).
@isnad1 id=injectiv.0h5v.s7.11a026878c87 from=translated src=- shape=8c99219b vocab=3fcd35e8
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHom_injective (d : OEData G p) [Nonempty S] : Function.Injective (ΛHom d) := by
  intro g h hgh
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hev : (Λ d g).obj (d.base s₀) = (Λ d h).obj (d.base s₀) :=
    congrArg (·.obj (d.base s₀)) (congrArg AutBoxG.hom hgh)
  have hc : d.coord (d.base s₀) = 1 := by
    have h1 := d.coord_base s₀ 1; rwa [d.act_one] at h1
  simp only [Λ, d.p_base, hc, mul_one] at hev
  exact d.act_free _ _ _ hev

/-- The kernel of `Φ` is exactly the image of `Λ`:  `ker Φ = range Λ`.  This is exactness of
    `1 → G →[Λ] Aut□_G(O/p) →[Φ] Aut(S) → 1` at the middle term.
@isnad1 id=eq.0h5v.s7.a9cd8d760c89 from=translated src=- shape=27c43b63 vocab=8a84b230
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ker_Φ_eq_range_Λ (d : OEData G p) [IsConnected S] : (Φ d).ker = (ΛHom d).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have hb : e.base = 1 := he
    have hpc : PreservesCleavage d e.hom (𝟭 S) := by
      have hp := e.pres; rw [hb] at hp; exact hp
    obtain ⟨g, hg⟩ := ((unbundled_lift_classification d).2 e.hom e.equiv).1 hpc
    refine ⟨g, AutBoxG.ext hg.symm ?_ hb.symm⟩
    show Λ d g⁻¹ = e.inv
    have key : e.hom ⋙ Λ d g⁻¹ = 𝟭 O := by rw [hg, Λ_comp, inv_mul_cancel, Λ_one]
    calc Λ d g⁻¹ = (e.inv ⋙ e.hom) ⋙ Λ d g⁻¹ := by rw [e.inv_hom_id, Functor.id_comp]
      _ = e.inv ⋙ e.hom ⋙ Λ d g⁻¹ := rfl
      _ = e.inv := by rw [key, Functor.comp_id]
  · rintro ⟨g, rfl⟩
    rfl

/-! ## 7. Twisted (θ-equivariant / semidirect) generalization (paper `thm:twisted`,
       ambient-group analogue; the paper states it for a chosen subgroup `H`, see file §14)

  The strict theorem of §§1–6 realizes only DIRECT products `G × Aut(S)`: the conjugation
  `(liftFunctor A)⁻¹ ⋙ Λ d g ⋙ liftFunctor A = Λ d g` (Lean diagrammatic order, i.e.
  `Ã Λ_g Ã⁻¹ = Λ_g` in operator order) is trivial, because strict
  `G`-equivariance commutes on the nose with the right action.  Genuine semidirect symmetry
  groups require *twisted* equivariance: the lift `F` of a base symmetry `A` acts on the fiber
  through a group automorphism `θ ∈ MulAut G`,

        `F (x · g) = F x · (θ g)`,

  so that `(liftFunctorθ A θ)⁻¹ ⋙ Λ d g ⋙ liftFunctorθ A θ = Λ d (θ g)` (Lean order; operator
  order `Ã Λ_g Ã⁻¹ = Λ_{θ g}`; `Λ_comp_liftθ`) and the kernel `G`
  carries the nontrivial action — the semidirect structure on `Aut□^θ_G`, packaged in §9 as an
  explicit isomorphism `Aut□^θ_G ≃* G ⋊_θ Aut(S)` (`autBoxGθMulEquivSemidirect`).
  Setting `θ = 1` recovers §§1–6.  The paper's `sec:scope` mentions `V ⋊ O(1,3)` only as an
  abstract shape of this kind; nothing Lorentzian is formalized here.  §8/§15 give a fully
  closed nontrivial-`θ` witness with `G = Multiplicative (ZMod 3)` (a different witness from the
  paper's `ex:twist`).

  This section proves the twisted analogues of `lift_exists` and `rigidity`, the conjugation
  relation `Λ_comp_liftθ`, and the group-level exact sequence `1 → G → Aut□^θ_G(O/p) → Aut(S) → 1`
  (`Φθ_surjective`, `ΛHomθ_injective`, `ker_Φθ_eq_range_Λθ`).  The twist threads through because
  the lift's fiber coordinate transforms by `coord_act`, on which `θ` (a homomorphism) distributes,
  and it cancels in `rigidityθ` since both lifts carry the same `θ`. -/

/-- `θ`-twisted `G`-equivariance: `F (x · g) = F x · (θ g)` for a fiber-twist `θ ∈ MulAut G`.
    `θ = 1` is ordinary (strict) `G`-equivariance.-/
def _root_.Tengoku.ObserverEquivarianceLean.IsTwistedEquivariant (d : OEData G p) (θ : MulAut G) (F : O ⥤ O) : Prop :=
  ∀ (x : O) (g : G), F.obj (d.act x g) = d.act (F.obj x) (θ g)

/-- At `θ = 1`, twisted equivariance is exactly `IsGEquivariant`.
@isnad1 id=iff.0h6v.s7.5897db8e9cbd from=translated src=- shape=c3ab0767 vocab=4f0fdb1e
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isTwistedEquivariant_one (d : OEData G p) (F : O ⥤ O) :
    IsTwistedEquivariant d (1 : MulAut G) F ↔ IsGEquivariant d F := Iff.rfl

namespace Tengoku.ObserverEquivarianceLean.OEData
/-- Projection of a twisted lift on objects (for ANY fiber element):  `p(b_{A s} · g') = A s`.
@isnad1 id=eq.0h8v.s6.d2b2a3b73ec9 from=translated src=- shape=4f70dd52 vocab=e3d85ad5
-/
theorem p_liftObjθ (d : OEData G p) (A : S ⥤ S) (x : O) (g' : G) :
    p.obj (d.act (d.base (A.obj (p.obj x))) g') = A.obj (p.obj x) :=
  (d.p_act _ _).trans (d.p_base _)
end Tengoku.ObserverEquivarianceLean.OEData

/-- The `θ`-twisted lift of a base functor `A`.  On objects `x ↦ b_{A(p x)} · θ(coord x)`;
    on morphisms the unique lift of `A(p f)` (faithfulness), exactly as `liftFunctor`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) : O ⥤ O :=
  haveI := d.isFull
  haveI := d.p_faithful
  { obj := fun x => d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))
    map := fun {x y} f =>
      p.preimage (eqToHom (d.p_liftObjθ A x (θ (d.coord x)))
        ≫ A.map (p.map f) ≫ eqToHom (d.p_liftObjθ A y (θ (d.coord y))).symm)
    map_id := fun x => by
      refine p.map_injective ?_
      simp [eqToHom_trans]
    map_comp := fun {x y z} f g => by
      refine p.map_injective ?_
      simp [p.map_preimage, p.map_comp, Category.assoc] }

/-- The twisted lift is `θ`-twisted `G`-equivariant (analogue of `lift_isGEquivariant`).
@isnad1 id=istwiste.0h7v.s6.7afa21ea2495 from=translated src=- shape=caeeec3b vocab=8f3eff6f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftθ_isTwistedEquivariant (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    IsTwistedEquivariant d θ (liftFunctorθ d A θ) := by
  intro x g
  show d.act (d.base (A.obj (p.obj (d.act x g)))) (θ (d.coord (d.act x g)))
     = d.act (d.act (d.base (A.obj (p.obj x))) (θ (d.coord x))) (θ g)
  rw [d.p_act, d.coord_act, map_mul, d.act_mul]

/-- The twisted lift covers `A`:  `liftFunctorθ d A θ ⋙ p = p ⋙ A`.
@isnad1 id=eq.0h7v.s6.7f1d0ab152d3 from=translated src=- shape=0da94113 vocab=8811aa85
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftθ_covers (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    liftFunctorθ d A θ ⋙ p = p ⋙ A := by
  have hobj : ∀ x, (liftFunctorθ d A θ ⋙ p).obj x = (p ⋙ A).obj x :=
    fun x => d.p_liftObjθ A x (θ (d.coord x))
  refine CategoryTheory.Functor.ext hobj (fun x y f => ?_)
  haveI := d.isFull
  haveI := d.p_faithful
  show p.map (p.preimage (eqToHom (d.p_liftObjθ A x (θ (d.coord x))) ≫ A.map (p.map f)
      ≫ eqToHom (d.p_liftObjθ A y (θ (d.coord y))).symm)) = _
  rw [p.map_preimage]
  rfl

/-- Twisted lift at `θ = 1` is the strict lift.
@isnad1 id=eq.0h6v.s7.cabe01128d0f from=translated src=- shape=bd10a7e2 vocab=a574534f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftFunctorθ_one (d : OEData G p) (A : S ⥤ S) :
    liftFunctorθ d A (1 : MulAut G) = liftFunctor d A := rfl

/-- The twisted lift preserves the chosen cleavage (same `PreservesCleavage` predicate —
    the twist does not affect the source-identity, since `coord (Ã y) = θ (coord y)`).
@isnad1 id=preserve.0h7v.s6.0915a3a319e8 from=translated src=- shape=8c451b0c vocab=d6169b92
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftθ_preservesCleavage (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) :
    PreservesCleavage d (liftFunctorθ d A θ) A where
  covers := liftθ_covers d A θ
  src u y hy := by
    simp only [liftFunctorθ, d.reind_eq, d.coord_base, d.p_act, d.p_base]

/-- Twisted lift existence (analogue of `lift_exists`):  every base autoequivalence admits a
    `θ`-twisted equivariant cleavage-preserving lift covering it.  As with `lift_exists`, this is
    the ∃-witness of the predicates, not a bundled `AutBoxGθ` element.
@isnad1 id=ex.0h7v.s6.641b4c79ba45 from=translated src=- shape=0022892e vocab=b37ed8b6
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.twisted_lift_exists (d : OEData G p) (A : S ≌ S) (θ : MulAut G) :
    ∃ F : O ⥤ O, IsTwistedEquivariant d θ F ∧ PreservesCleavage d F A.functor :=
  ⟨liftFunctorθ d A.functor θ, liftθ_isTwistedEquivariant d A.functor θ,
    liftθ_preservesCleavage d A.functor θ⟩

/-- Alias of `twisted_lift_exists`.
@isnad1 id=ex.0h7v.s6.641b4c79ba45 from=translated src=- shape=0022892e vocab=b37ed8b6
-/
alias Tengoku.ObserverEquivarianceLean.strict_liftθ := twisted_lift_exists

/-- Twisted rigidity (analogue of `rigidity`).  Two `θ`-twisted equivariant cleavage-preserving
    lifts of the same base autoequivalence (the SAME twist `θ`) differ by a unique normalized
    fiber translation `Λ d g`.  The twist cancels — both carry it — so the difference is the
    untwisted `Λ d g`.  (`[IsConnected S]`; `p` faithful for the morphism step.)
@isnad1 id=existsun.4h9v.s7.9a07044fe3fb from=translated src=- shape=8219d595 vocab=3f296c61
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.rigidityθ (d : OEData G p) (A : S ≌ S) (θ : MulAut G) [IsConnected S] (F₁ F₂ : O ⥤ O)
    (h₁ : IsTwistedEquivariant d θ F₁) (h₂ : IsTwistedEquivariant d θ F₂)
    (pc₁ : PreservesCleavage d F₁ A.functor) (pc₂ : PreservesCleavage d F₂ A.functor) :
    ∃! g : G, F₂ = F₁ ⋙ Λ d g := by
  haveI := d.p_faithful
  -- Object form of a `θ`-twisted lift:  F x = b_{A(p x)} · (k(p x) · θ(coord x)).
  have Fobj : ∀ (F : O ⥤ O), IsTwistedEquivariant d θ F → F ⋙ p = p ⋙ A.functor → ∀ x,
      F.obj x = d.act (d.base (A.functor.obj (p.obj x)))
                  (d.coord (F.obj (d.base (p.obj x))) * θ (d.coord x)) := by
    intro F hF hc x
    have e1 : F.obj x = d.act (F.obj (d.base (p.obj x))) (θ (d.coord x)) := by
      conv_lhs => rw [← d.base_coord x]
      exact hF _ _
    have e2 : F.obj (d.base (p.obj x))
        = d.act (d.base (A.functor.obj (p.obj x))) (d.coord (F.obj (d.base (p.obj x)))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base (p.obj x)))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base (p.obj x))).trans
        (congrArg A.functor.obj (d.p_base (p.obj x))))
    rw [e1, ← d.act_mul, ← e2]
  -- Local constancy of `k` from cleavage preservation (twist-free: evaluated at basepoints).
  have kconst : ∀ (F : O ⥤ O), F ⋙ p = p ⋙ A.functor → PreservesCleavage d F A.functor →
      ∀ {s t : S}, (s ⟶ t) → d.coord (F.obj (d.base s)) = d.coord (F.obj (d.base t)) := by
    intro F hc pc s t u
    have key := pc.src u (d.base t) (d.p_base t)
    rw [d.reind_base, d.reind_eq] at key
    have hFs : F.obj (d.base s)
        = d.act (d.base (A.functor.obj s)) (d.coord (F.obj (d.base s))) := by
      conv_lhs => rw [← d.base_coord (F.obj (d.base s))]
      congr 1
      exact congrArg d.base ((Functor.congr_obj hc (d.base s)).trans
        (congrArg A.functor.obj (d.p_base s)))
    rw [hFs] at key
    exact d.act_free _ _ _ key
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have k₁c : ∀ s, d.coord (F₁.obj (d.base s)) = d.coord (F₁.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₁.obj (d.base s)))
      (fun _ _ u => kconst F₁ pc₁.covers pc₁ u) s s₀
  have k₂c : ∀ s, d.coord (F₂.obj (d.base s)) = d.coord (F₂.obj (d.base s₀)) := fun s =>
    constant_of_preserves_morphisms (fun s => d.coord (F₂.obj (d.base s)))
      (fun _ _ u => kconst F₂ pc₂.covers pc₂ u) s s₀
  have hcovΛ : ∀ g, (F₁ ⋙ Λ d g) ⋙ p = p ⋙ A.functor := by
    intro g
    rw [Functor.assoc, Λ_comp_p]; exact pc₁.covers
  refine ⟨d.coord (F₂.obj (d.base s₀)) * (d.coord (F₁.obj (d.base s₀)))⁻¹, ?_, ?_⟩
  · refine funct_ext d (fun x => ?_) ?_
    · rw [Fobj F₂ h₂ pc₂.covers x]
      show _ = (Λ d _).obj (F₁.obj x)
      rw [Fobj F₁ h₁ pc₁.covers x]
      simp only [Λ, d.p_act, d.p_base, d.coord_base]
      rw [k₂c (p.obj x), k₁c (p.obj x)]
      congr 1
      group
    · rw [pc₂.covers]; exact (hcovΛ _).symm
  · intro g' hg'
    have hev := congrArg (fun (F : O ⥤ O) => d.coord (F.obj (d.base s₀))) hg'
    simp only [Functor.comp_obj, Λ, d.coord_base] at hev
    rw [hev]; group

/-- The SEMIDIRECT relation.  The fiber translation `Λ d g` commutes past the twisted lift
    `Ã = liftFunctorθ d A θ` up to twisting `g` by `θ`:
        `Λ d g ⋙ Ã = Ã ⋙ Λ d (θ g)`,   i.e.   `Ã ∘ Λ d g ∘ Ã⁻¹ = Λ d (θ g)`.
    This is trivial (`Ã Λ_g Ã⁻¹ = Λ_g`) exactly when `θ = 1` — recovering the direct product
    `G × Aut(S)` of the strict theorem — and nontrivial otherwise, making the extension semidirect
    rather than direct (the kernel `G` is acted on by `θ`; paper `thm:twisted`).
@isnad1 id=eq.0h8v.s7.11b3452067d9 from=translated src=- shape=6caf49de vocab=d138be44
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_comp_liftθ (d : OEData G p) (A : S ⥤ S) (θ : MulAut G) (g : G) :
    Λ d g ⋙ liftFunctorθ d A θ = liftFunctorθ d A θ ⋙ Λ d (θ g) := by
  have hL : (Λ d g ⋙ liftFunctorθ d A θ) ⋙ p = p ⋙ A := by
    rw [Functor.assoc, liftθ_covers, ← Functor.assoc, Λ_comp_p]
  have hR : (liftFunctorθ d A θ ⋙ Λ d (θ g)) ⋙ p = p ⋙ A := by
    rw [Functor.assoc, Λ_comp_p, liftθ_covers]
  refine funct_ext d (fun x => ?_) (hL.trans hR.symm)
  simp only [Functor.comp_obj, Λ, liftFunctorθ, d.p_act, d.p_base, d.coord_base, map_mul]

/-- At `θ = 1` the semidirect relation degenerates to commutation `Λ d g ⋙ Ã = Ã ⋙ Λ d g`
    (the direct-product case): conjugation by a strict lift fixes every `Λ d g`.
@isnad1 id=eq.0h7v.s6.0685cbc1d48d from=translated src=- shape=3ae09c77 vocab=7bf5b14b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Λ_comp_lift_one (d : OEData G p) (A : S ⥤ S) (g : G) :
    Λ d g ⋙ liftFunctor d A = liftFunctor d A ⋙ Λ d g := by
  have := Λ_comp_liftθ d A (1 : MulAut G) g
  rwa [liftFunctorθ_one] at this

/-- Composition of twisted lifts:  `liftθ A θ ⋙ liftθ B φ = liftθ (A ⋙ B) (φ * θ)`.  The
    twists multiply in `MulAut G` (contravariantly, matching the lift's action on coordinates).
@isnad1 id=eq.0h9v.s8.05649db89b11 from=translated src=- shape=5199f85a vocab=14edf793
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftθ_comp (d : OEData G p) (A B : S ⥤ S) (θ φ : MulAut G) :
    liftFunctorθ d A θ ⋙ liftFunctorθ d B φ = liftFunctorθ d (A ⋙ B) (φ * θ) := by
  have hcov : (liftFunctorθ d A θ ⋙ liftFunctorθ d B φ) ⋙ p = p ⋙ (A ⋙ B) := by
    rw [Functor.assoc, liftθ_covers, ← Functor.assoc, liftθ_covers, Functor.assoc]
  refine funct_ext d (fun x => ?_) (hcov.trans (liftθ_covers d (A ⋙ B) (φ * θ)).symm)
  simp only [Functor.comp_obj, liftFunctorθ, d.p_act, d.p_base, d.coord_base, MulAut.mul_apply]

/-- The twisted lift of the identity at the trivial twist is the identity.
@isnad1 id=eq.0h5v.s7.568c28132e0e from=translated src=- shape=5d9cd1b1 vocab=3afcc10a
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftθ_id (d : OEData G p) : liftFunctorθ d (𝟭 S) (1 : MulAut G) = 𝟭 O := by
  rw [liftFunctorθ_one]; exact lift_id d

/-- Twisted equivariance is closed under composition; the twists multiply in `MulAut G`.
@isnad1 id=istwiste.2h9v.s7.365147d2cbb4 from=translated src=- shape=718eae17 vocab=1483697e
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isTwistedEquivariant_comp {F F' : O ⥤ O} {θ θ' : MulAut G}
    (h : IsTwistedEquivariant d θ F) (h' : IsTwistedEquivariant d θ' F') :
    IsTwistedEquivariant d (θ' * θ) (F ⋙ F') := fun x g => by
  show F'.obj (F.obj (d.act x g)) = d.act (F'.obj (F.obj x)) ((θ' * θ) g)
  rw [h x g, h' (F.obj x) (θ g), MulAut.mul_apply]

/-- Twisted equivariance transfers to a strict inverse, inverting the twist.
@isnad1 id=istwiste.3h8v.s7.9722ce5f7369 from=translated src=- shape=afe31da7 vocab=4221e542
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isTwistedEquivariant_inv {F Finv : O ⥤ O} {θ : MulAut G}
    (hi : F ⋙ Finv = 𝟭 O) (ih : Finv ⋙ F = 𝟭 O) (h : IsTwistedEquivariant d θ F) :
    IsTwistedEquivariant d θ⁻¹ Finv := by
  have hθ : ∀ g, θ (θ⁻¹ g) = g := fun g => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hFcancel : ∀ z, F.obj (Finv.obj z) = z := fun z => by
    have := Functor.congr_obj ih z; simpa using this
  have hinj : Function.Injective F.obj := fun a b hab => by
    have e : ∀ z, Finv.obj (F.obj z) = z := fun z => by
      have := Functor.congr_obj hi z; simpa using this
    have := congrArg Finv.obj hab; rw [e, e] at this; exact this
  intro x g
  apply hinj
  rw [h (Finv.obj x) (θ⁻¹ g), hFcancel, hFcancel, hθ]

/-! ### The semidirect bundle-automorphism group  `Aut□^θ_G(O/p)`  and its exact sequence

  Fix a *functorial twist* `θ : StrictAut S →* MulAut G` — the physical action of base symmetries
  on the structure group (paper `thm:twisted`, ambient-group analogue).  A
  `θ`-twisted bundle automorphism covers a base symmetry `A` and is `θ A`-twisted equivariant.
  These assemble into a group `AutBoxGθ d θ`, and `Φθ`/`ΛHomθ` give the short exact sequence

        `1 → G → Aut□^θ_G(O/p) → Aut(S) → 1`.

  By `Λ_comp_liftθ` the conjugation action of this group on the kernel `G` is `θ`, so the extension
  is semidirect rather than direct — `G ⋊_θ Aut(S)` — realized as an
  explicit `≃*` in §9 (`autBoxGθMulEquivSemidirect`); at `θ = 1` it is the direct product of §6.
  No new `OEData` assumption is used beyond §§1–6. -/

variable (θ : StrictAut S →* MulAut G)

/-- A `θ`-twisted bundle automorphism:  a strict autoequivalence `hom` of `O` that is
    `θ(base)`-twisted `G`-equivariant and cleavage-preserving over the strict base
    automorphism `base`.  Forms `Aut□^θ_G(O/p)`.-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.AutBoxGθ (d : OEData G p) (θ : StrictAut S →* MulAut G) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : StrictAut S
  equiv : IsTwistedEquivariant d (θ base) hom
  pres : PreservesCleavage d hom base.hom

namespace Tengoku.ObserverEquivarianceLean.AutBoxGθ

instance : Group (AutBoxGθ d θ) where
  mul e₁ e₂ :=
    { hom := e₂.hom ⋙ e₁.hom
      inv := e₁.inv ⋙ e₂.inv
      hom_inv_id := by
        show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 O
        rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id]
      inv_hom_id := by
        show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 O
        rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]
      base := e₁.base * e₂.base
      equiv := by
        rw [map_mul]; exact isTwistedEquivariant_comp d e₂.equiv e₁.equiv
      pres := preservesCleavage_comp d e₂.pres e₁.pres }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, by rw [map_one]; exact id_isGEquivariant d,
    id_preservesCleavage d⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := by
        rw [map_inv]; exact isTwistedEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      pres := preservesCleavage_inv d e.hom_inv_id e.inv_hom_id e.pres }
  mul_assoc a b c := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutBoxGθ.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutBoxGθ.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

/--
@isnad1 id=eq.0h8v.s8.16e5f5344684 from=translated src=- shape=28e1b332 vocab=c104ed98
-/
@[simp] lemma mul_hom (e₁ e₂ : AutBoxGθ d θ) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
/--
@isnad1 id=eq.0h8v.s8.cb9fa53c97e2 from=translated src=- shape=e0718a5c vocab=b5f2df39
-/
@[simp] lemma mul_base (e₁ e₂ : AutBoxGθ d θ) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
/--
@isnad1 id=eq.0h6v.s7.9f8ba59c7429 from=translated src=- shape=4858acd0 vocab=429a16ea
-/
@[simp] lemma one_hom : (1 : AutBoxGθ d θ).hom = 𝟭 O := rfl
/--
@isnad1 id=eq.0h6v.s7.df6d19f293e7 from=translated src=- shape=7c1a9a9f vocab=e8a46556
-/
@[simp] lemma one_base : (1 : AutBoxGθ d θ).base = 1 := rfl

end Tengoku.ObserverEquivarianceLean.AutBoxGθ

/-- `Φθ : Aut□^θ_G(O/p) →* Aut(S)`:  the base symmetry covered by a twisted bundle automorphism.-/
def _root_.Tengoku.ObserverEquivarianceLean.Φθ (d : OEData G p) (θ : StrictAut S →* MulAut G) : AutBoxGθ d θ →* StrictAut S where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `Λθ : G →* Aut□^θ_G(O/p)`:  the normalized fiber-translation embedding (base `1`, twist `1`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛHomθ (d : OEData G p) (θ : StrictAut S →* MulAut G) : G →* AutBoxGθ d θ where
  toFun g :=
    { hom := Λ d g
      inv := Λ d g⁻¹
      hom_inv_id := by rw [Λ_comp, inv_mul_cancel, Λ_one]
      inv_hom_id := by rw [Λ_comp, mul_inv_cancel, Λ_one]
      base := 1
      equiv := by rw [map_one]; exact Λ_isGEquivariant d g
      pres := Λ_preservesCleavage d g }
  map_one' := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · exact Λ_one d
    · show Λ d (1 : G)⁻¹ = 𝟭 O; rw [inv_one, Λ_one]
    · rfl
  map_mul' g h := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show Λ d (g * h) = Λ d h ⋙ Λ d g; rw [Λ_comp]
    · show Λ d (g * h)⁻¹ = Λ d g⁻¹ ⋙ Λ d h⁻¹; rw [Λ_comp, mul_inv_rev]
    · rfl

/-- The canonical `θ`-twisted strict lift of a base automorphism, bundled as an element of
    `AutBoxGθ` (twisted analogue of `liftAut`).  `hom`/`inv` are `liftFunctorθ` of
    `A.hom`/`A.inv` with twists `θ A` / `(θ A)⁻¹`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftAutθ (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    AutBoxGθ d θ where
  hom := liftFunctorθ d A.hom (θ A)
  inv := liftFunctorθ d A.inv (θ A)⁻¹
  hom_inv_id := by rw [liftθ_comp, inv_mul_cancel, A.hom_inv_id, liftθ_id]
  inv_hom_id := by rw [liftθ_comp, mul_inv_cancel, A.inv_hom_id, liftθ_id]
  base := A
  equiv := liftθ_isTwistedEquivariant d A.hom (θ A)
  pres := liftθ_preservesCleavage d A.hom (θ A)

/--
@isnad1 id=eq.0h7v.s8.8847a5f10b26 from=translated src=- shape=a0eb3dc3 vocab=d3ec41ac
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftAutθ_hom (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (liftAutθ d θ A).hom = liftFunctorθ d A.hom (θ A) := rfl
/--
@isnad1 id=eq.0h7v.s7.128e20b96e0b from=translated src=- shape=1b9e32b6 vocab=19e01e57
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftAutθ_base (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (liftAutθ d θ A).base = A := rfl
/--
@isnad1 id=eq.0h7v.s8.71fad4d4571d from=translated src=- shape=c3efe137 vocab=cb659386
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.Φθ_liftAutθ (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    Φθ d θ (liftAutθ d θ A) = A := rfl

/-- `Φθ` is surjective:  every base symmetry is covered by its `θ`-twisted strict lift.
@isnad1 id=surjecti.0h6v.s8.772f2950a52c from=translated src=- shape=84363120 vocab=8138c17b
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.Φθ_surjective (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    Function.Surjective (Φθ d θ) := fun A => ⟨liftAutθ d θ A, rfl⟩

/-- `Λθ` is injective (needs a basepoint; freeness of the action does the rest).
@isnad1 id=injectiv.0h6v.s8.cfd73d499467 from=translated src=- shape=04248bb6 vocab=a099134f
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomθ_injective (d : OEData G p) (θ : StrictAut S →* MulAut G) [Nonempty S] :
    Function.Injective (ΛHomθ d θ) := by
  intro g h hgh
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hev : (Λ d g).obj (d.base s₀) = (Λ d h).obj (d.base s₀) :=
    congrArg (·.obj (d.base s₀)) (congrArg AutBoxGθ.hom hgh)
  have hc : d.coord (d.base s₀) = 1 := by
    have h1 := d.coord_base s₀ 1; rwa [d.act_one] at h1
  simp only [Λ, d.p_base, hc, mul_one] at hev
  exact d.act_free _ _ _ hev

/-- Exactness at the middle:  `ker Φθ = range Λθ`.  A twisted bundle automorphism covers `id_S`
    (twist `θ 1 = 1`, so it is strictly equivariant) iff it is a normalized fiber translation.
    With `Φθ_surjective` and `ΛHomθ_injective` this is the SEMIDIRECT exact sequence
    `1 → G →[Λθ] Aut□^θ_G(O/p) →[Φθ] Aut(S) → 1`.
@isnad1 id=eq.0h6v.s7.5fc153f806c6 from=translated src=- shape=982223f1 vocab=c0ff78b7
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ker_Φθ_eq_range_Λθ (d : OEData G p) (θ : StrictAut S →* MulAut G) [IsConnected S] :
    (Φθ d θ).ker = (ΛHomθ d θ).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have hb : e.base = 1 := he
    have hgeq : IsGEquivariant d e.hom := by
      have h := e.equiv; rw [hb, map_one] at h; exact h
    have hpc : PreservesCleavage d e.hom (𝟭 S) := by
      have hp := e.pres; rw [hb] at hp; exact hp
    obtain ⟨g, hg⟩ := ((unbundled_lift_classification d).2 e.hom hgeq).1 hpc
    refine ⟨g, AutBoxGθ.ext hg.symm ?_ hb.symm⟩
    show Λ d g⁻¹ = e.inv
    have key : e.hom ⋙ Λ d g⁻¹ = 𝟭 O := by rw [hg, Λ_comp, inv_mul_cancel, Λ_one]
    calc Λ d g⁻¹ = (e.inv ⋙ e.hom) ⋙ Λ d g⁻¹ := by rw [e.inv_hom_id, Functor.id_comp]
      _ = e.inv ⋙ e.hom ⋙ Λ d g⁻¹ := rfl
      _ = e.inv := by rw [key, Functor.comp_id]
  · rintro ⟨g, rfl⟩
    rfl

/-! ## 8. A non-vacuous NONTRIVIAL-twist witness  (§7 is not vacuous for `θ ≠ 1`)

  We exhibit a concrete `OEData G p` together with a NONTRIVIAL functorial twist
  `θ : StrictAut S →* MulAut G`, so the semidirect theory of §7 is non-vacuous beyond `θ = 1`.

  The base is `S = SingleObj Q`, whose strict autoequivalences are `MulAut Q` (so taking
  `Q = G` gives the twist `θ : StrictAut S ≅ MulAut G`, the identity — nontrivial whenever `G`
  has a nontrivial automorphism, e.g. `Multiplicative (ZMod 3)`).

  The total groupoid is the `Q`-LABELLED codiscrete groupoid on `G` (`Lab G Q`): objects are
  `G`, every hom-set is `Q`, and `p` reads off the label.  Crucially the label is INDEPENDENT of
  the endpoints, so the structure-group action can leave it fixed (`actHom f g = f`) and the
  chosen vertical translation `ltrans` can be labelled `1` — genuinely vertical, as the current
  `OEData` requires.  (The naive `Pair G` with `p(a⟶b) = b·a⁻¹` would force `ltrans` to project
  to a nonidentity, violating `p_ltrans`.) -/

/-- The `Q`-labelled codiscrete groupoid on objects `B`: `Hom x y := Q`, composing by flipped
    multiplication (matching `SingleObj Q`), so `pLab` below is a functor.-/
@[ext] structure _root_.Tengoku.ObserverEquivarianceLean.Lab (B Q : Type*) where pt : B

instance (B Q : Type*) [Group Q] : Groupoid (Lab B Q) where
  Hom _ _ := Q
  id _ := 1
  comp f g := g * f
  id_comp _ := mul_one _
  comp_id _ := one_mul _
  assoc f g h := (mul_assoc h g f).symm
  inv f := f⁻¹
  inv_comp _ := mul_inv_cancel _
  comp_inv _ := inv_mul_cancel _

/-- The projection `Lab B Q ⥤ SingleObj Q` reading off the `Q`-label (faithful and full).-/
def _root_.Tengoku.ObserverEquivarianceLean.pLab (B Q : Type*) [Group Q] : Lab B Q ⥤ SingleObj Q where
  obj _ := SingleObj.star Q
  map f := f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The non-vacuous twist witness as an `OEData`: structure group `G` acts on objects by right
    multiplication, leaving the `Q`-label fixed; basepoint `⟨1⟩`, `coord = pt`; the chosen
    cleavage is the identity reindexing with `chi` the label `u`, and `ltrans` the label `1`
    (vertical).-/
def _root_.Tengoku.ObserverEquivarianceLean.labData (G Q : Type*) [Group G] [Group Q] : OEData G (pLab G Q) where
  act x g := ⟨x.pt * g⟩
  act_one x := by simp
  act_mul x g h := by simp [mul_assoc]
  p_act _ _ := rfl
  act_free x g h e := mul_left_cancel (congrArg Lab.pt e)
  actHom f _ := f
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  actHom_one f := by
    have e : ∀ {a b : Lab G Q} (hh : a = b), (eqToHom hh : a ⟶ b) = (1 : Q) := by
      rintro a b rfl; rfl
    rw [e, e]; simp [CategoryStruct.comp]
  actHom_mul f g h := by
    have e : ∀ {a b : Lab G Q} (hh : a = b), (eqToHom hh : a ⟶ b) = (1 : Q) := by
      rintro a b rfl; rfl
    rw [e, e]; simp [CategoryStruct.comp]
  p_actHom _ _ := by simp [pLab]
  base _ := ⟨1⟩
  p_base _ := rfl
  coord x := x.pt
  base_coord x := by simp
  coord_base _ g := by simp
  reind _ y _ := y
  p_reind _ _ _ := rfl
  chi u _ _ := u
  p_chi := fun {s t} u y hy => by
    obtain rfl : s = SingleObj.star Q := rfl
    obtain rfl : t = SingleObj.star Q := rfl
    simp [pLab]
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act _ _ _ _ := by simp
  ltrans _ _ := 1
  p_ltrans _ _ := by aesop_cat
  reind_id _ _ := rfl
  chi_id _ _ := by aesop_cat
  reind_comp _ _ _ _ := rfl
  chi_comp _ _ _ _ := by aesop_cat
  p_faithful := ⟨fun h => h⟩

/-- Reading a strict autoequivalence of `SingleObj G` as a group automorphism of `G` (its
    underlying monoid hom, via `SingleObj.mapHom`).  This realizes `StrictAut (SingleObj G) ≅
    MulAut G`.-/
def _root_.Tengoku.ObserverEquivarianceLean.toMulAutSingleObj (G : Type*) [Group G] (e : StrictAut (SingleObj G)) : MulAut G where
  toFun := (SingleObj.mapHom G G).symm e.hom
  invFun := (SingleObj.mapHom G G).symm e.inv
  left_inv g := by
    have h : ((SingleObj.mapHom G G).symm e.inv).comp ((SingleObj.mapHom G G).symm e.hom)
        = MonoidHom.id G := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e.hom_inv_id,
          SingleObj.mapHom_id]
    exact DFunLike.congr_fun h g
  right_inv g := by
    have h : ((SingleObj.mapHom G G).symm e.hom).comp ((SingleObj.mapHom G G).symm e.inv)
        = MonoidHom.id G := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply, e.inv_hom_id,
          SingleObj.mapHom_id]
    exact DFunLike.congr_fun h g
  map_mul' := ((SingleObj.mapHom G G).symm e.hom).map_mul

/-- The functorial twist `θ : StrictAut (SingleObj G) →* MulAut G`, the identity under the
    equivalence `StrictAut (SingleObj G) ≅ MulAut G`.-/
def _root_.Tengoku.ObserverEquivarianceLean.θSingleObj (G : Type*) [Group G] : StrictAut (SingleObj G) →* MulAut G where
  toFun := toMulAutSingleObj G
  map_one' := by
    ext g
    show ((SingleObj.mapHom G G).symm (𝟭 (SingleObj G))) g = g
    rw [← SingleObj.mapHom_id, Equiv.symm_apply_apply]; rfl
  map_mul' e₁ e₂ := by
    have key : (SingleObj.mapHom G G).symm (e₂.hom ⋙ e₁.hom)
        = ((SingleObj.mapHom G G).symm e₁.hom).comp ((SingleObj.mapHom G G).symm e₂.hom) := by
      apply (SingleObj.mapHom G G).injective
      rw [SingleObj.mapHom_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
    ext g
    show ((SingleObj.mapHom G G).symm (e₂.hom ⋙ e₁.hom)) g = _
    rw [key]; rfl

/-- `θSingleObj` is surjective:  every group automorphism of `G` is realized by a strict
    autoequivalence of `SingleObj G` (so `θSingleObj` is the iso `StrictAut (SingleObj G) ≅
    MulAut G`).
@isnad1 id=surjecti.0h1v.s8.2c7164beb642 from=translated src=- shape=70052d6d vocab=435fd547
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.θSingleObj_surjective (G : Type*) [Group G] : Function.Surjective (θSingleObj G) := by
  intro φ
  have hi : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext g; exact φ.symm_apply_apply g
  have hi' : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G := by
    ext g; exact φ.apply_symm_apply g
  refine ⟨{ hom := SingleObj.mapHom G G φ.toMonoidHom
            inv := SingleObj.mapHom G G φ.symm.toMonoidHom
            hom_inv_id := by rw [← SingleObj.mapHom_comp, hi, SingleObj.mapHom_id]
            inv_hom_id := by rw [← SingleObj.mapHom_comp, hi', SingleObj.mapHom_id] }, ?_⟩
  ext g
  show ((SingleObj.mapHom G G).symm (SingleObj.mapHom G G φ.toMonoidHom)) g = φ g
  rw [Equiv.symm_apply_apply]; rfl

/-! ## 9. The bundle-automorphism group as an explicit semidirect product

  Upgrades the §7 exact sequence to a literal group isomorphism

      `Aut□^θ_G(O/p)  ≃*  G ⋊[θ] Aut(S)`   (mathlib's `SemidirectProduct`).

  The map `G ⋊[θ] Aut(S) → Aut□^θ_G` is `SemidirectProduct.lift` of the fiber-translation
  embedding `Λθ` and the twisted-lift section `liftHomθ`, whose compatibility is exactly the
  conjugation law `Λ_comp_liftθ`.  Bijectivity is the exactness `ker_Φθ_eq_range_Λθ` together with
  `ΛHomθ_injective`.  Needs `[IsConnected S]`. -/

/-- The twisted-lift section as a group homomorphism `Aut(S) →* Aut□^θ_G(O/p)`:
    `A ↦ liftAutθ d θ A`, the canonical `θ_A`-twisted cleavage-preserving lift.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftHomθ (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    StrictAut S →* AutBoxGθ d θ where
  toFun := liftAutθ d θ
  map_one' := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show liftFunctorθ d (𝟭 S) (θ 1) = 𝟭 O
      rw [map_one]; exact liftθ_id d
    · show liftFunctorθ d (𝟭 S) (θ 1)⁻¹ = 𝟭 O
      rw [map_one, inv_one]; exact liftθ_id d
    · rfl
  map_mul' A B := by
    refine AutBoxGθ.ext ?_ ?_ ?_
    · show liftFunctorθ d (B.hom ⋙ A.hom) (θ (A * B))
          = liftFunctorθ d B.hom (θ B) ⋙ liftFunctorθ d A.hom (θ A)
      rw [liftθ_comp, map_mul]
    · show liftFunctorθ d (A.inv ⋙ B.inv) (θ (A * B))⁻¹
          = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ liftFunctorθ d B.inv (θ B)⁻¹
      rw [liftθ_comp, map_mul, mul_inv_rev]
    · rfl

/--
@isnad1 id=eq.0h7v.s8.d95d8f14ad7d from=translated src=- shape=d45b3686 vocab=ba3e102d
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftHomθ_base (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (liftHomθ d θ A).base = A := rfl

/--
@isnad1 id=eq.0h7v.s8.2737f1cad1c3 from=translated src=- shape=1533a7ad vocab=ad0bbc9e
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.Φθ_apply (d : OEData G p) (θ : StrictAut S →* MulAut G) (e : AutBoxGθ d θ) :
    Φθ d θ e = e.base := rfl

/--
@isnad1 id=eq.0h7v.s8.1b158423cb04 from=translated src=- shape=d3021a07 vocab=5ee7ad7a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomθ_base (d : OEData G p) (θ : StrictAut S →* MulAut G) (g : G) :
    (ΛHomθ d θ g).base = 1 := rfl

/--
@isnad1 id=eq.0h7v.s8.be283dc1ff1a from=translated src=- shape=337ac277 vocab=8d7f15a9
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.AutBoxGθ_inv_base (d : OEData G p) (θ : StrictAut S →* MulAut G)
    (e : AutBoxGθ d θ) : (e⁻¹).base = e.base⁻¹ := rfl

/-- The compatibility condition for `SemidirectProduct.lift`:  conjugating `Λθ g` by the lift of
    `A` twists `g` by `θ A` (this is `Λ_comp_liftθ` at the group level).
@isnad1 id=eq.0h7v.s11.269fb04d6502 from=translated src=- shape=3fa98e50 vocab=5a23bf80
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftHomθ_conj (d : OEData G p) (θ : StrictAut S →* MulAut G) (A : StrictAut S) :
    (ΛHomθ d θ).comp (θ A).toMonoidHom
      = (MulAut.conj (liftHomθ d θ A)).toMonoidHom.comp (ΛHomθ d θ) := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine AutBoxGθ.ext ?_ ?_ ?_
  · show Λ d ((θ A) g)
        = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ Λ d g ⋙ liftFunctorθ d A.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp]
  · show Λ d ((θ A) g)⁻¹
        = liftFunctorθ d A.inv (θ A)⁻¹ ⋙ Λ d g⁻¹ ⋙ liftFunctorθ d A.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp, map_inv]
  · simp

/-- `G ⋊[θ] Aut(S) →* Aut□^θ_G(O/p)`:  `inl g ↦ Λθ g`, `inr A ↦ liftHomθ A`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθ (d : OEData G p) (θ : StrictAut S →* MulAut G) :
    SemidirectProduct G (StrictAut S) θ →* AutBoxGθ d θ :=
  SemidirectProduct.lift (ΛHomθ d θ) (liftHomθ d θ) (liftHomθ_conj d θ)

/--
@isnad1 id=eq.0h7v.s9.b539b64de133 from=translated src=- shape=7790ab6a vocab=98c10de7
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθ_inl (d : OEData G p) (θ : StrictAut S →* MulAut G) (g : G) :
    semidirectToAutBoxGθ d θ (SemidirectProduct.inl g) = ΛHomθ d θ g :=
  SemidirectProduct.lift_inl _ _ _ g

/--
@isnad1 id=eq.0h7v.s9.9a5c1c287be8 from=translated src=- shape=ad0fc0ff vocab=587b6705
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθ_inr (d : OEData G p) (θ : StrictAut S →* MulAut G)
    (A : StrictAut S) :
    semidirectToAutBoxGθ d θ (SemidirectProduct.inr A) = liftHomθ d θ A :=
  SemidirectProduct.lift_inr _ _ _ A

/-- The §7 semidirect exact sequence, packaged as an explicit group isomorphism
    `Aut□^θ_G(O/p) ≃* G ⋊[θ] Aut(S)`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.autBoxGθMulEquivSemidirect (d : OEData G p) (θ : StrictAut S →* MulAut G)
    [IsConnected S] : AutBoxGθ d θ ≃* SemidirectProduct G (StrictAut S) θ := by
  have hinj : Function.Injective (semidirectToAutBoxGθ d θ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul,
      semidirectToAutBoxGθ_inl, semidirectToAutBoxGθ_inr] at hx
    have hright : x.right = 1 := by
      have h2 := congrArg (Φθ d θ) hx
      rw [map_mul, map_one] at h2
      simpa using h2
    rw [hright, map_one, mul_one] at hx
    have hleft : x.left = 1 := ΛHomθ_injective d θ (by rw [hx, map_one])
    exact SemidirectProduct.ext hleft hright
  have hsurj : Function.Surjective (semidirectToAutBoxGθ d θ) := by
    intro e
    have hker : e * (liftHomθ d θ e.base)⁻¹ ∈ (Φθ d θ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp
    rw [ker_Φθ_eq_range_Λθ, MonoidHom.mem_range] at hker
    obtain ⟨g, hg⟩ := hker
    refine ⟨SemidirectProduct.inl g * SemidirectProduct.inr e.base, ?_⟩
    rw [map_mul, semidirectToAutBoxGθ_inl, semidirectToAutBoxGθ_inr, hg, inv_mul_cancel_right]
  exact (MulEquiv.ofBijective (semidirectToAutBoxGθ d θ) ⟨hinj, hsurj⟩).symm

/-- The inverse of `autBoxGθMulEquivSemidirect` is the canonical map
    `G ⋊[θ] Aut(S) → Aut□^θ_G(O/p)`, `(a, A) ↦ Λ_a Ã_θ` (paper `thm:twisted`, ambient-group
    analogue).
@isnad1 id=eq.0h7v.s9.540e5430f71b from=translated src=- shape=a3fe865c vocab=4708610f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθMulEquivSemidirect_symm_apply (d : OEData G p)
    (θ : StrictAut S →* MulAut G) [IsConnected S] (x : SemidirectProduct G (StrictAut S) θ) :
    (autBoxGθMulEquivSemidirect d θ).symm x = semidirectToAutBoxGθ d θ x := rfl

/-- Projection: the right part of `autBoxGθMulEquivSemidirect` is `Φθ`
    (paper `thm:twisted`, ambient-group analogue).
@isnad1 id=eq.0h7v.s9.f990f7a1184c from=translated src=- shape=39eff35e vocab=761f372a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθMulEquivSemidirect_apply_right (d : OEData G p)
    (θ : StrictAut S →* MulAut G) [IsConnected S] (e : AutBoxGθ d θ) :
    (autBoxGθMulEquivSemidirect d θ e).right = Φθ d θ e := by
  conv_rhs => rw [← (autBoxGθMulEquivSemidirect d θ).symm_apply_apply e]
  rw [autBoxGθMulEquivSemidirect_symm_apply,
    ← SemidirectProduct.inl_left_mul_inr_right (autBoxGθMulEquivSemidirect d θ e),
    map_mul, semidirectToAutBoxGθ_inl, semidirectToAutBoxGθ_inr, map_mul]
  simp

/-! ## 10. The untwisted classification as an explicit DIRECT product  (paper `thm:strict`)

  For the whole ambient group `StrictAut S` (and, in §13, any subgroup `H`) the strict theorem
  realizes a genuine DIRECT product `AutBoxG d ≃* G × StrictAut S`.  The commutation is at the
  level of the CANONICAL normalized section `liftHom` (an arbitrary lift may carry a left
  translation `Λ h` and then conjugate `Λ` nontrivially when `G` is nonabelian). -/

/-- The canonical normalized lifts commute with `Λ` at the group level (from `Λ_comp_lift_one`).
    Only the canonical section `liftHom` centralizes the kernel — not an arbitrary lift.
@isnad1 id=eq.0h7v.s9.375db2576b34 from=translated src=- shape=1825ea65 vocab=91adab55
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHom_comm_liftHom (d : OEData G p) (g : G) (A : StrictAut S) :
    ΛHom d g * liftHom d A = liftHom d A * ΛHom d g := by
  refine AutBoxG.ext ?_ ?_ ?_
  · show liftFunctor d A.hom ⋙ Λ d g = Λ d g ⋙ liftFunctor d A.hom
    exact (Λ_comp_lift_one d A.hom g).symm
  · show Λ d g⁻¹ ⋙ liftFunctor d A.inv = liftFunctor d A.inv ⋙ Λ d g⁻¹
    exact Λ_comp_lift_one d A.inv g⁻¹
  · simp

/-- The direct-product embedding `G × StrictAut S →* AutBoxG d`, `(g, A) ↦ Λ_g · liftAut A`.
    A homomorphism because canonical lifts commute with `Λ` (`ΛHom_comm_liftHom`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.prodToAutBoxG (d : OEData G p) : G × StrictAut S →* AutBoxG d where
  toFun := fun x => ΛHom d x.1 * liftHom d x.2
  map_one' := by
    show ΛHom d (1 : G) * liftHom d (1 : StrictAut S) = 1
    simp
  map_mul' x y := by
    obtain ⟨g₁, A₁⟩ := x
    obtain ⟨g₂, A₂⟩ := y
    show ΛHom d (g₁ * g₂) * liftHom d (A₁ * A₂)
       = (ΛHom d g₁ * liftHom d A₁) * (ΛHom d g₂ * liftHom d A₂)
    rw [map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (ΛHom d g₂), ΛHom_comm_liftHom, mul_assoc]

/--
@isnad1 id=eq.0h7v.s9.3d719fb7632c from=translated src=- shape=c68ddacd vocab=7f0531a8
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.prodToAutBoxG_apply (d : OEData G p) (g : G) (A : StrictAut S) :
    prodToAutBoxG d (g, A) = ΛHom d g * liftHom d A := rfl

/-- The strict classification as an explicit group isomorphism
    `AutBoxG d ≃* G × StrictAut S`  (needs `[IsConnected S]`).  This is the untwisted
    counterpart of `autBoxGθMulEquivSemidirect`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.autBoxGMulEquivProd (d : OEData G p) [IsConnected S] :
    AutBoxG d ≃* G × StrictAut S := by
  have hinj : Function.Injective (prodToAutBoxG d) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, A⟩ := x
    rw [prodToAutBoxG_apply] at hx
    have hA : A = 1 := by
      have h2 := congrArg (Φ d) hx
      rw [map_mul, map_one] at h2
      rwa [show Φ d (ΛHom d g) = 1 from rfl, show Φ d (liftHom d A) = A from rfl,
        one_mul] at h2
    rw [hA, map_one, mul_one] at hx
    have hg : g = 1 := ΛHom_injective d (by rw [hx, map_one])
    exact Prod.ext hg hA
  have hsurj : Function.Surjective (prodToAutBoxG d) := by
    intro e
    have hker : e * (liftHom d e.base)⁻¹ ∈ (Φ d).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv,
        show Φ d (liftHom d e.base) = e.base from rfl,
        show Φ d e = e.base from rfl, mul_inv_cancel]
    rw [ker_Φ_eq_range_Λ, MonoidHom.mem_range] at hker
    obtain ⟨g, hg⟩ := hker
    exact ⟨(g, e.base), by rw [prodToAutBoxG_apply, hg, inv_mul_cancel_right]⟩
  exact (MulEquiv.ofBijective (prodToAutBoxG d) ⟨hinj, hsurj⟩).symm

/-- The inverse of `autBoxGMulEquivProd` is the paper's map `(a, A) ↦ Λ_a Ã`
    (paper `thm:strict`, ambient group `H = Aut(S)`).
@isnad1 id=eq.0h6v.s9.4b9939b10ff1 from=translated src=- shape=9ba3dc45 vocab=5d7249fa
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGMulEquivProd_symm_apply (d : OEData G p) [IsConnected S]
    (x : G × StrictAut S) :
    (autBoxGMulEquivProd d).symm x = ΛHom d x.1 * liftHom d x.2 := rfl

/-- Projection: the second component of `autBoxGMulEquivProd` is `Φ`
    (paper `thm:strict`, ambient group).
@isnad1 id=eq.0h6v.s9.28c485d5bf13 from=translated src=- shape=68f5d382 vocab=d16545ee
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGMulEquivProd_apply_snd (d : OEData G p) [IsConnected S] (e : AutBoxG d) :
    (autBoxGMulEquivProd d e).2 = Φ d e := by
  conv_rhs => rw [← (autBoxGMulEquivProd d).symm_apply_apply e]
  rw [autBoxGMulEquivProd_symm_apply, map_mul]; exact (one_mul _).symm

/-! ## 12. The product normal form  `O ≌ S × Pair G`  (WEAK equivalence form of paper
       `thm:normalform`; the paper's strict isomorphism of categories is
       `normalFormTo_comp_normalFormFrom` / `normalFormFrom_comp_normalFormTo` in
       `ObserverEquivariance/NormalForm.lean`)

  The normalization data trivialize the presentation on the nose: the comparison functor
  `x ↦ (p x, ⟨coord x⟩)` is fully faithful (from `isFull` + `p_faithful`) and essentially
  surjective, hence an equivalence.  Since `Pair G` is categorically contractible, `p` itself is an
  equivalence, and the nontrivial `G`-kernel lives only in the chosen strict presentation. -/

/-- The comparison functor `O ⥤ S × Pair G`,  `x ↦ (p x, ⟨coord x⟩)`,  `f ↦ (p f, ⟨⟩)`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.normalFormTo (d : OEData G p) : O ⥤ S × Pair G where
  obj x := (p.obj x, ⟨d.coord x⟩)
  map f := (p.map f, ⟨⟩)
  map_id x := Prod.ext (p.map_id x) (Subsingleton.elim _ _)
  map_comp f g := Prod.ext (p.map_comp f g) (Subsingleton.elim _ _)

/--
@isnad1 id=eq.0h6v.s6.8ecb89311430 from=translated src=- shape=11de3b68 vocab=d7a5fa7a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_obj (d : OEData G p) (x : O) :
    (normalFormTo d).obj x = (p.obj x, ⟨d.coord x⟩) := rfl

/--
@isnad1 id=eq.0h8v.s8.f91457edfef5 from=translated src=- shape=8464122e vocab=f1c853d4
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_map (d : OEData G p) {x y : O} (f : x ⟶ y) :
    (normalFormTo d).map f = (p.map f, ⟨⟩) := rfl

/-- The first product projection recovers `p`:  `normalFormTo d ⋙ fst = p`.
@isnad1 id=eq.0h5v.s6.ee6031b4172c from=translated src=- shape=ab250e59 vocab=39b04c9c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalFormTo_fst (d : OEData G p) :
    normalFormTo d ⋙ CategoryTheory.Prod.fst S (Pair G) = p := rfl

/-- On objects the comparison intertwines the right `G`-action with right multiplication in
    the `Pair G` coordinate.
@isnad1 id=eq.0h7v.s7.38a011cc04af from=translated src=- shape=efc037a6 vocab=3401f5cb
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalForm_coord_act (d : OEData G p) (x : O) (g : G) :
    (normalFormTo d).obj (d.act x g) = (p.obj x, ⟨d.coord x * g⟩) := by
  simp only [normalFormTo_obj, d.p_act, d.coord_act]

/-- The basepoint section goes to the unit coordinate:  `base s ↦ (s, ⟨1⟩)`.
@isnad1 id=eq.0h6v.s6.787eaf9af8a3 from=translated src=- shape=91e34174 vocab=64ccfe1d
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalForm_base (d : OEData G p) (s : S) :
    (normalFormTo d).obj (d.base s) = (s, (⟨1⟩ : Pair G)) := by
  have hc : d.coord (d.base s) = 1 := by have := d.coord_base s 1; rwa [d.act_one] at this
  show (p.obj (d.base s), (⟨d.coord (d.base s)⟩ : Pair G)) = (s, ⟨1⟩)
  rw [d.p_base, hc]

/-- Reindexing preserves the `Pair G` coordinate:  `u*y ↦ (s, ⟨coord y⟩)`.
@isnad1 id=eq.1h9v.s7.e4bafbfd045b from=translated src=- shape=ad617d07 vocab=fe6f8f09
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalForm_reind (d : OEData G p) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t) :
    (normalFormTo d).obj (d.reind u y hy) = (s, (⟨d.coord y⟩ : Pair G)) := by
  show (p.obj (d.reind u y hy), (⟨d.coord (d.reind u y hy)⟩ : Pair G)) = (s, ⟨d.coord y⟩)
  rw [d.p_reind, d.coord_reind]

/-- The product normal form as an equivalence `O ≌ S × Pair G`, with comparison functor
    `normalFormTo d`.  This is only the weak (equivalence) form of paper `thm:normalform`.
    The paper's strict isomorphism of categories is
    `normalFormTo_comp_normalFormFrom` / `normalFormFrom_comp_normalFormTo` (NormalForm.lean).
    Fully faithful from `isFull` + `p_faithful`; essentially surjective since `(s, ⟨g⟩)` is
    hit on the nose by `base s · g`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.productNormalForm (d : OEData G p) : O ≌ S × Pair G := by
  haveI : (normalFormTo d).Faithful := by
    haveI := d.p_faithful
    exact ⟨fun {x y} {f g} h => p.map_injective (congrArg Prod.fst h)⟩
  haveI : (normalFormTo d).Full := by
    haveI := d.isFull
    exact ⟨fun {x y} fg =>
      ⟨p.preimage fg.1, Prod.ext (p.map_preimage fg.1) (Subsingleton.elim _ _)⟩⟩
  haveI : (normalFormTo d).EssSurj := by
    refine ⟨fun Y => ?_⟩
    obtain ⟨s, gc⟩ := Y
    obtain ⟨g⟩ := gc
    refine ⟨d.act (d.base s) g, ⟨eqToIso ?_⟩⟩
    show (p.obj (d.act (d.base s) g), (⟨d.coord (d.act (d.base s) g)⟩ : Pair G)) = (s, ⟨g⟩)
    rw [d.p_act, d.p_base, d.coord_base]
  haveI : (normalFormTo d).IsEquivalence := {}
  exact (normalFormTo d).asEquivalence

/--
@isnad1 id=eq.0h5v.s6.b50e91e95dad from=translated src=- shape=8feaea2c vocab=acdc7966
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productNormalForm_functor (d : OEData G p) :
    (productNormalForm d).functor = normalFormTo d := rfl

/-- Since `Pair G` is categorically contractible, the projection `p` is itself an
    equivalence `O ≌ S`.  The nontrivial `G`-kernel therefore belongs to the chosen strict
    presentation, not to `S`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.projectionEquivalence (d : OEData G p) : O ≌ S := by
  haveI := d.isFull
  haveI := d.p_faithful
  haveI : p.EssSurj := ⟨fun s => ⟨d.base s, ⟨eqToIso (d.p_base s)⟩⟩⟩
  haveI : p.IsEquivalence := {}
  exact p.asEquivalence

/--
@isnad1 id=eq.0h5v.s5.8dc345ac178e from=translated src=- shape=8cecaab4 vocab=ddf8c988
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.projectionEquivalence_functor (d : OEData G p) :
    (projectionEquivalence d).functor = p := rfl

/-- The right `G`-action transported to the normal form:  `(s, ⟨h⟩) ↦ (s, ⟨h * g⟩)`, identity
    on the base component.  This is the product-side action intertwined by `normalFormTo`.-/
def _root_.Tengoku.ObserverEquivarianceLean.normalFormProductAction (g : G) : S × Pair G ⥤ S × Pair G where
  obj x := (x.1, ⟨x.2.pt * g⟩)
  map f := (f.1, ⟨⟩)
  map_id x := Prod.ext (by simp) (Subsingleton.elim _ _)
  map_comp f h := Prod.ext (by simp) (Subsingleton.elim _ _)

/-- Functorial `G`-equivariance of the comparison functor:  the upstairs action `actFunctor g`
    intertwines with the product action `normalFormProductAction g` through `normalFormTo`.
    Uses `p_actHom` (the morphism part of the right `G`-action).
@isnad1 id=eq.0h6v.s7.f1e176f95f86 from=translated src=- shape=c0064105 vocab=15a8dfe6
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.normalForm_equivariant (d : OEData G p) (g : G) :
    d.actFunctor g ⋙ normalFormTo d = normalFormTo d ⋙ normalFormProductAction g := by
  have hfst : ∀ {a b : S × Pair G} (m : a ⟶ b),
      m.1 = (CategoryTheory.Prod.fst S (Pair G)).map m := fun _ => rfl
  refine CategoryTheory.Functor.ext
    (fun x => Prod.ext (d.p_act x g) (congrArg (fun c => (⟨c⟩ : Pair G)) (d.coord_act x g)))
    (fun x y f => ?_)
  refine Prod.ext ?_ (Subsingleton.elim _ _)
  show p.map (d.actHom f g) = _
  rw [d.p_actHom, hfst, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  rfl

/-- Groupoid specialization, first half (paper `rem:groupoid`).  IF every arrow of `O` is
    invertible (hypothesis `hO`, i.e. `O` is a groupoid), then every base morphism
    `u : s ⟶ t` in `S` is invertible:  lift by `isFull`, invert in `O`, and reflect the iso
    back along the fully faithful projection.
    `O` is an arbitrary category, so the groupoid property is the explicit extra hypothesis
    `hO` of `rem:groupoid`; no general result depends on this theorem.
    Stated as a theorem, not a global `Groupoid S` instance.
@isnad1 id=isiso.1h8v.s6.7c34fe451415 from=translated src=- shape=d09a3c60 vocab=2e933a68
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.base_hom_isIso (d : OEData G p) (hO : ∀ {x y : O} (f : x ⟶ y), IsIso f)
    {s t : S} (u : s ⟶ t) : IsIso u := by
  haveI := d.isFull
  haveI := d.p_faithful
  haveI : p.EssSurj := ⟨fun s => ⟨d.base s, ⟨eqToIso (d.p_base s)⟩⟩⟩
  haveI : p.IsEquivalence := {}
  haveI : IsIso (p.inv.map u) := hO _
  exact isIso_of_reflects_iso u p.inv

/-- Groupoid specialization, converse half (paper `rem:groupoid`).  IF every arrow of `S` is
    invertible (hypothesis `hS`, i.e. `S` is a groupoid), then every arrow of `O` is
    invertible:  `p.map f` is an iso by `hS`, and the fully faithful `p` (`isFull` +
    `p_faithful`) reflects isomorphisms.
@isnad1 id=isiso.1h8v.s6.9539c9e43c90 from=translated src=- shape=6f396791 vocab=2e933a68
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.hom_isIso_of_base_isIso (d : OEData G p) (hS : ∀ {s t : S} (u : s ⟶ t), IsIso u)
    {x y : O} (f : x ⟶ y) : IsIso f := by
  haveI := d.isFull
  haveI := d.p_faithful
  haveI : IsIso (p.map f) := hS _
  exact isIso_of_reflects_iso f p

/-! ## 13. Restriction to a chosen symmetry subgroup (paper `thm:strict`,
       which is stated for a selected `H ≤ Aut(S)`; `def:law`)

  The strict classification `AutBoxG d ≃* G × StrictAut S` restricts to any subgroup
  `H ≤ StrictAut S` of "admissible" base symmetries: the bundle automorphisms covering an
  element of `H` are exactly `Φ⁻¹(H) = comap (Φ d) H`, and this preimage group is the direct
  product `G × H` (`autBoxGOverMulEquivProd`).  The physically relevant specialization takes
  `H = strictLawStabilizer L`, the strict automorphisms fixing a chosen "law" functor
  `L : S ⥤ C` on the nose:  not every strict category automorphism is a physical symmetry —
  only those preserving the law.  (Everything here is `θ = 1`; the twisted subgroup version is
  file §14 below.) -/

/-- The strict stabilizer of a "law" `L : S ⥤ C`:  the subgroup of `StrictAut S` whose
    underlying functor fixes `L` on the nose, `A.hom ⋙ L = L`.  Preservation only *up to*
    natural isomorphism would be a different, higher-categorical construction; this is the
    strict (on-the-nose) stabilizer.-/
def _root_.Tengoku.ObserverEquivarianceLean.strictLawStabilizer {C : Type*} [Category C] (L : S ⥤ C) : Subgroup (StrictAut S) where
  carrier := {A | A.hom ⋙ L = L}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [StrictAut.mul_hom, Functor.assoc, ha, hb]
  one_mem' := by
    simp only [Set.mem_ofPred_eq, StrictAut.one_hom, Functor.id_comp]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at ha ⊢
    show a.inv ⋙ L = L
    conv_lhs => rw [← ha]
    rw [← Functor.assoc, a.inv_hom_id, Functor.id_comp]

/-- The bundle automorphisms covering a base symmetry in `H`:  the preimage `Φ⁻¹(H)`.  These
    form a subgroup of `AutBoxG d`, hence a group in their own right.-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.AutBoxGOver (d : OEData G p) (H : Subgroup (StrictAut S)) :=
  ↥(Subgroup.comap (Φ d) H)

/-- `ΦOver : AutBoxGOver d H →* H`:  the base-symmetry projection, restricted to the preimage
    group and corestricted to `H`.-/
def _root_.Tengoku.ObserverEquivarianceLean.ΦOver (d : OEData G p) (H : Subgroup (StrictAut S)) : AutBoxGOver d H →* H where
  toFun x := ⟨Φ d x.1, x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `ΛHomOver : G →* AutBoxGOver d H`:  the fiber-translation embedding lands in `Φ⁻¹(H)`
    because every `Λ d g` covers the identity `1 ∈ H`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛHomOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    G →* AutBoxGOver d H where
  toFun g := ⟨ΛHom d g, H.one_mem⟩
  map_one' := Subtype.ext (ΛHom d).map_one
  map_mul' g h := Subtype.ext ((ΛHom d).map_mul g h)

/-- `liftHomOver : H →* AutBoxGOver d H`:  the canonical section, restricted to `H`.  The lift
    of `A ∈ H` covers `A ∈ H`, so it lands in `Φ⁻¹(H)`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftHomOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    H →* AutBoxGOver d H where
  toFun A := ⟨liftHom d A.1, A.2⟩
  map_one' := Subtype.ext (liftHom d).map_one
  map_mul' A B := Subtype.ext ((liftHom d).map_mul A.1 B.1)

/-- `ΛHomOver` is injective (needs a basepoint).
@isnad1 id=injectiv.0h6v.s8.394286fcf644 from=translated src=- shape=60605533 vocab=25707b67
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomOver_injective (d : OEData G p) (H : Subgroup (StrictAut S)) [Nonempty S] :
    Function.Injective (ΛHomOver d H) := fun _ _ hgh =>
  ΛHom_injective d (Subtype.ext_iff.mp hgh)

/-- Exactness at the middle for the restricted sequence:  `ker ΦOver = range ΛHomOver`.
    A bundle automorphism over `H` covers `id_S` iff it is a fiber translation.
@isnad1 id=eq.0h6v.s8.65dcc8aa98da from=translated src=- shape=26530290 vocab=74702c56
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ker_ΦOver_eq_range_ΛOver (d : OEData G p) (H : Subgroup (StrictAut S)) [IsConnected S] :
    (ΦOver d H).ker = (ΛHomOver d H).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have he1 : Φ d e.1 = 1 := Subtype.ext_iff.mp he
    have hmem : e.1 ∈ (Φ d).ker := he1
    rw [ker_Φ_eq_range_Λ, MonoidHom.mem_range] at hmem
    obtain ⟨g, hg⟩ := hmem
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, rfl⟩
    rfl

/-- The canonical restricted lifts commute with `Λ` at the group level.
@isnad1 id=eq.0h8v.s11.ee1f3e9828ce from=translated src=- shape=e98191a4 vocab=cf222c9a
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomOver_comm_liftHomOver (d : OEData G p) (H : Subgroup (StrictAut S))
    (g : G) (A : H) : ΛHomOver d H g * liftHomOver d H A = liftHomOver d H A * ΛHomOver d H g :=
  Subtype.ext (ΛHom_comm_liftHom d g A.1)

/-- The direct-product embedding `G × H →* AutBoxGOver d H`, `(g, A) ↦ Λ_g · liftHomOver A`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.prodToAutBoxGOver (d : OEData G p) (H : Subgroup (StrictAut S)) :
    G × H →* AutBoxGOver d H where
  toFun x := ΛHomOver d H x.1 * liftHomOver d H x.2
  map_one' := by simp
  map_mul' x y := by
    obtain ⟨g₁, A₁⟩ := x
    obtain ⟨g₂, A₂⟩ := y
    show ΛHomOver d H (g₁ * g₂) * liftHomOver d H (A₁ * A₂)
       = (ΛHomOver d H g₁ * liftHomOver d H A₁) * (ΛHomOver d H g₂ * liftHomOver d H A₂)
    rw [map_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (ΛHomOver d H g₂), ΛHomOver_comm_liftHomOver, mul_assoc]

/--
@isnad1 id=eq.0h8v.s11.4cc5088fc1df from=translated src=- shape=cfe6e2f8 vocab=a0420820
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.prodToAutBoxGOver_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    (g : G) (A : H) : prodToAutBoxGOver d H (g, A) = ΛHomOver d H g * liftHomOver d H A := rfl

/-- The restricted strict classification as an explicit group isomorphism
    `AutBoxGOver d H ≃* G × H`  (needs `[IsConnected S]`):  the formal statement that the
    admissible bundle automorphisms `Φ⁻¹(H)` are exactly the direct product `G × H`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.autBoxGOverMulEquivProd (d : OEData G p) (H : Subgroup (StrictAut S))
    [IsConnected S] : AutBoxGOver d H ≃* G × H := by
  have hinj : Function.Injective (prodToAutBoxGOver d H) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, A⟩ := x
    rw [prodToAutBoxGOver_apply] at hx
    have hA : A = 1 := by
      have h2 := congrArg (ΦOver d H) hx
      rw [map_mul, map_one] at h2
      rwa [show ΦOver d H (ΛHomOver d H g) = 1 from rfl,
        show ΦOver d H (liftHomOver d H A) = A from rfl, one_mul] at h2
    rw [hA, map_one, mul_one] at hx
    have hg : g = 1 := ΛHomOver_injective d H (by rw [hx, map_one])
    exact Prod.ext hg hA
  have hsurj : Function.Surjective (prodToAutBoxGOver d H) := by
    intro e
    have hker : e * (liftHomOver d H (ΦOver d H e))⁻¹ ∈ (ΦOver d H).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv,
        show ΦOver d H (liftHomOver d H (ΦOver d H e)) = ΦOver d H e from rfl, mul_inv_cancel]
    rw [ker_ΦOver_eq_range_ΛOver, MonoidHom.mem_range] at hker
    obtain ⟨g, hg⟩ := hker
    exact ⟨(g, ΦOver d H e), by
      rw [prodToAutBoxGOver_apply, hg, inv_mul_cancel_right]⟩
  exact (MulEquiv.ofBijective (prodToAutBoxGOver d H) ⟨hinj, hsurj⟩).symm

/-- The inverse of `autBoxGOverMulEquivProd` is the paper's map `G × H → Sym_H(p)`,
    `(a, A) ↦ Λ_a Ã` (paper `thm:strict`).
@isnad1 id=eq.0h7v.s11.325e4d22f899 from=translated src=- shape=37699414 vocab=8de97013
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGOverMulEquivProd_symm_apply (d : OEData G p) (H : Subgroup (StrictAut S))
    [IsConnected S] (x : G × H) :
    (autBoxGOverMulEquivProd d H).symm x = ΛHomOver d H x.1 * liftHomOver d H x.2 := rfl

/-- Projection: the second component of `autBoxGOverMulEquivProd` is `ΦOver`
    (paper `thm:strict`).
@isnad1 id=eq.0h7v.s10.867115543683 from=translated src=- shape=926cb401 vocab=4c8a366e
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGOverMulEquivProd_apply_snd (d : OEData G p) (H : Subgroup (StrictAut S))
    [IsConnected S] (e : AutBoxGOver d H) :
    (autBoxGOverMulEquivProd d H e).2 = ΦOver d H e := by
  conv_rhs => rw [← (autBoxGOverMulEquivProd d H).symm_apply_apply e]
  rw [autBoxGOverMulEquivProd_symm_apply, map_mul]; exact (one_mul _).symm

/-- The physically relevant specialization:  the law-preserving bundle automorphisms — those
    covering a strict symmetry that fixes the law `L` — are `AutBoxGOver d (strictLawStabilizer L)`.-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.LawPreservingAutBox (d : OEData G p) {C : Type*} [Category C] (L : S ⥤ C) :=
  AutBoxGOver d (strictLawStabilizer L)

/-- The law-preserving classification:  `LawPreservingAutBox d L ≃* G × strictLawStabilizer L`.
    The formal counterpart of the paper's physically relevant statement — the shared-law
    symmetries are the structure group `G` times the strict law stabilizer.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.lawPreservingAutBoxMulEquiv (d : OEData G p) {C : Type*} [Category C]
    (L : S ⥤ C) [IsConnected S] :
    LawPreservingAutBox d L ≃* G × strictLawStabilizer L :=
  autBoxGOverMulEquivProd d (strictLawStabilizer L)

/-- The stabilizer of a state (paper, discussion after `def:law`): given a specified action of
    `H_L = strictLawStabilizer L` on a space of states `X` and a state `σ : X`, the subgroup
    `H_{L,σ} = {A ∈ H_L | A · σ = σ}` of `StrictAut S`, i.e. the image of
    `MulAction.stabilizer H_L σ` under the inclusion `H_L ≤ StrictAut S`.-/
def _root_.Tengoku.ObserverEquivarianceLean.stateStabilizer {C : Type*} [Category C] (L : S ⥤ C) {X : Type*}
    [MulAction (strictLawStabilizer L) X] (σ : X) : Subgroup (StrictAut S) :=
  (MulAction.stabilizer (strictLawStabilizer L) σ).map (strictLawStabilizer L).subtype

/-- The lift classification restricted to the stabilizer of a state (paper, discussion after
    `def:law`: "the lift classification restricts to this subgroup as well"):
    `Sym_{H_{L,σ}}(p) ≃* G × H_{L,σ}` for connected `S`, the instance
    `H = stateStabilizer L σ` of `autBoxGOverMulEquivProd`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.stateStabilizerAutBoxMulEquiv (d : OEData G p) {C : Type*} [Category C]
    (L : S ⥤ C) {X : Type*} [MulAction (strictLawStabilizer L) X] (σ : X) [IsConnected S] :
    AutBoxGOver d (stateStabilizer L σ) ≃* G × stateStabilizer L σ :=
  autBoxGOverMulEquivProd d (stateStabilizer L σ)

/-! ## 14. Twist defined only on the chosen subgroup (paper `thm:twisted`)

  Paper `thm:twisted` takes the twist `θ : H → Aut(G)` on the chosen subgroup `H ≤ Aut(S)`,
  not on all of `StrictAut S`.  We thus package the twisted theory for a homomorphism
  `θ : H →* MulAut G`.  The bundle automorphisms
  over `H` with `θ`-twisted fibers form `AutBoxGθOver d H θ`, and the same exactness argument
  identifies them with the semidirect product `G ⋊[θ] H` (`autBoxGθOverMulEquivSemidirect`).
  The full-group `AutBoxGθ d θ` of §7 is the ANALOGUE of the case `H = ⊤`, not formally
  identified with it: its twist has type `StrictAut S →* MulAut G`, not `↥⊤ →* MulAut G`.
  The trivial twist `θ = 1` is identified with the untwisted group by
  `autBoxGθOverOneMulEquiv`. -/

/-- A `θ`-twisted bundle automorphism over the subgroup `H`:  a strict autoequivalence `hom` of
    `O`, `θ(base)`-twisted equivariant and cleavage-preserving over `base ∈ H`.-/
@[ext]
structure _root_.Tengoku.ObserverEquivarianceLean.AutBoxGθOver (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) where
  hom : O ⥤ O
  inv : O ⥤ O
  hom_inv_id : hom ⋙ inv = 𝟭 O
  inv_hom_id : inv ⋙ hom = 𝟭 O
  base : H
  equiv : IsTwistedEquivariant d (θ base) hom
  pres : PreservesCleavage d hom base.1.hom

namespace Tengoku.ObserverEquivarianceLean.AutBoxGθOver

variable {d : OEData G p} {H : Subgroup (StrictAut S)} {θ : H →* MulAut G}

instance : Group (AutBoxGθOver d H θ) where
  mul e₁ e₂ :=
    { hom := e₂.hom ⋙ e₁.hom
      inv := e₁.inv ⋙ e₂.inv
      hom_inv_id := by
        show e₂.hom ⋙ (e₁.hom ⋙ e₁.inv) ⋙ e₂.inv = 𝟭 O
        rw [e₁.hom_inv_id, Functor.id_comp, e₂.hom_inv_id]
      inv_hom_id := by
        show e₁.inv ⋙ (e₂.inv ⋙ e₂.hom) ⋙ e₁.hom = 𝟭 O
        rw [e₂.inv_hom_id, Functor.id_comp, e₁.inv_hom_id]
      base := e₁.base * e₂.base
      equiv := by
        rw [map_mul]; exact isTwistedEquivariant_comp d e₂.equiv e₁.equiv
      pres := preservesCleavage_comp d e₂.pres e₁.pres }
  one := ⟨𝟭 O, 𝟭 O, rfl, rfl, 1, by rw [map_one]; exact id_isGEquivariant d,
    id_preservesCleavage d⟩
  inv e :=
    { hom := e.inv
      inv := e.hom
      hom_inv_id := e.inv_hom_id
      inv_hom_id := e.hom_inv_id
      base := e.base⁻¹
      equiv := by
        rw [map_inv]; exact isTwistedEquivariant_inv d e.hom_inv_id e.inv_hom_id e.equiv
      pres := preservesCleavage_inv d e.hom_inv_id e.inv_hom_id e.pres }
  mul_assoc a b c := by refine AutBoxGθOver.ext ?_ ?_ ?_ <;> rfl
  one_mul a := by refine AutBoxGθOver.ext ?_ ?_ ?_ <;> rfl
  mul_one a := by refine AutBoxGθOver.ext ?_ ?_ ?_ <;> rfl
  inv_mul_cancel a := by
    refine AutBoxGθOver.ext ?_ ?_ ?_ <;> first | exact a.hom_inv_id | exact inv_mul_cancel _

/--
@isnad1 id=eq.0h9v.s9.fd622b09f4be from=translated src=- shape=2be9c059 vocab=fac51ad8
-/
@[simp] lemma mul_hom (e₁ e₂ : AutBoxGθOver d H θ) : (e₁ * e₂).hom = e₂.hom ⋙ e₁.hom := rfl
/--
@isnad1 id=eq.0h9v.s9.21f3ca267cf5 from=translated src=- shape=b8ccc1f2 vocab=183688b9
-/
@[simp] lemma mul_base (e₁ e₂ : AutBoxGθOver d H θ) : (e₁ * e₂).base = e₁.base * e₂.base := rfl
/--
@isnad1 id=eq.0h7v.s8.236209803d7e from=translated src=- shape=3d96c950 vocab=ac6ee827
-/
@[simp] lemma one_hom : (1 : AutBoxGθOver d H θ).hom = 𝟭 O := rfl
/--
@isnad1 id=eq.0h7v.s9.13b71ee49960 from=translated src=- shape=6e89a401 vocab=2296bbe8
-/
@[simp] lemma one_base : (1 : AutBoxGθOver d H θ).base = 1 := rfl
/--
@isnad1 id=eq.0h8v.s9.df9bf978f41c from=translated src=- shape=87cd4202 vocab=e274cbb6
-/
@[simp] lemma inv_base (e : AutBoxGθOver d H θ) : (e⁻¹).base = e.base⁻¹ := rfl

end Tengoku.ObserverEquivarianceLean.AutBoxGθOver

/-- `ΦθOver : AutBoxGθOver d H θ →* H`:  the base-symmetry projection into `H`.-/
def _root_.Tengoku.ObserverEquivarianceLean.ΦθOver (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) :
    AutBoxGθOver d H θ →* H where
  toFun e := e.base
  map_one' := rfl
  map_mul' _ _ := rfl

/--
@isnad1 id=eq.0h8v.s10.805e4be5464e from=translated src=- shape=42a01ca6 vocab=d7f88511
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.ΦθOver_apply (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)
    (e : AutBoxGθOver d H θ) : ΦθOver d H θ e = e.base := rfl

/-- `ΛHomθOver : G →* AutBoxGθOver d H θ`:  the fiber-translation embedding (base `1`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.ΛHomθOver (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) :
    G →* AutBoxGθOver d H θ where
  toFun g :=
    { hom := Λ d g
      inv := Λ d g⁻¹
      hom_inv_id := by rw [Λ_comp, inv_mul_cancel, Λ_one]
      inv_hom_id := by rw [Λ_comp, mul_inv_cancel, Λ_one]
      base := 1
      equiv := by rw [map_one]; exact Λ_isGEquivariant d g
      pres := Λ_preservesCleavage d g }
  map_one' := by
    refine AutBoxGθOver.ext ?_ ?_ ?_
    · exact Λ_one d
    · show Λ d (1 : G)⁻¹ = 𝟭 O; rw [inv_one, Λ_one]
    · rfl
  map_mul' g h := by
    refine AutBoxGθOver.ext ?_ ?_ ?_
    · show Λ d (g * h) = Λ d h ⋙ Λ d g; rw [Λ_comp]
    · show Λ d (g * h)⁻¹ = Λ d g⁻¹ ⋙ Λ d h⁻¹; rw [Λ_comp, mul_inv_rev]
    · rfl

/--
@isnad1 id=eq.0h8v.s9.b31a990ca2e6 from=translated src=- shape=183d91e5 vocab=3bad2a0a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomθOver_base (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)
    (g : G) : (ΛHomθOver d H θ g).base = 1 := rfl

/-- The twisted-lift section `liftHomθOver : H →* AutBoxGθOver d H θ`,
    `A ↦ liftFunctorθ d A.hom (θ A)`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.liftHomθOver (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) :
    H →* AutBoxGθOver d H θ where
  toFun A :=
    { hom := liftFunctorθ d A.1.hom (θ A)
      inv := liftFunctorθ d A.1.inv (θ A)⁻¹
      hom_inv_id := by rw [liftθ_comp, inv_mul_cancel, A.1.hom_inv_id, liftθ_id]
      inv_hom_id := by rw [liftθ_comp, mul_inv_cancel, A.1.inv_hom_id, liftθ_id]
      base := A
      equiv := liftθ_isTwistedEquivariant d A.1.hom (θ A)
      pres := liftθ_preservesCleavage d A.1.hom (θ A) }
  map_one' := by
    refine AutBoxGθOver.ext ?_ ?_ ?_
    · show liftFunctorθ d (𝟭 S) (θ 1) = 𝟭 O
      rw [map_one]; exact liftθ_id d
    · show liftFunctorθ d (𝟭 S) (θ 1)⁻¹ = 𝟭 O
      rw [map_one, inv_one]; exact liftθ_id d
    · rfl
  map_mul' A B := by
    refine AutBoxGθOver.ext ?_ ?_ ?_
    · show liftFunctorθ d (B.1.hom ⋙ A.1.hom) (θ (A * B))
          = liftFunctorθ d B.1.hom (θ B) ⋙ liftFunctorθ d A.1.hom (θ A)
      rw [liftθ_comp, map_mul]
    · show liftFunctorθ d (A.1.inv ⋙ B.1.inv) (θ (A * B))⁻¹
          = liftFunctorθ d A.1.inv (θ A)⁻¹ ⋙ liftFunctorθ d B.1.inv (θ B)⁻¹
      rw [liftθ_comp, map_mul, mul_inv_rev]
    · rfl

/--
@isnad1 id=eq.0h8v.s10.543bfbb1eefb from=translated src=- shape=2886ea21 vocab=ea5dbec5
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.liftHomθOver_base (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (A : H) : (liftHomθOver d H θ A).base = A := rfl

/-- `ΛHomθOver` is injective (needs a basepoint).
@isnad1 id=injectiv.0h7v.s9.d38ce35e0301 from=translated src=- shape=bada19a4 vocab=e4884ea6
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ΛHomθOver_injective (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)
    [Nonempty S] : Function.Injective (ΛHomθOver d H θ) := by
  intro g h hgh
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hev : (Λ d g).obj (d.base s₀) = (Λ d h).obj (d.base s₀) :=
    congrArg (·.obj (d.base s₀)) (congrArg AutBoxGθOver.hom hgh)
  have hc : d.coord (d.base s₀) = 1 := by
    have h1 := d.coord_base s₀ 1; rwa [d.act_one] at h1
  simp only [Λ, d.p_base, hc, mul_one] at hev
  exact d.act_free _ _ _ hev

/-- Exactness at the middle for the restricted twisted sequence:  `ker ΦθOver = range ΛHomθOver`.
@isnad1 id=eq.0h7v.s9.f99287695efe from=translated src=- shape=089c9741 vocab=b91b4199
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.ker_ΦθOver_eq_range_ΛθOver (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) [IsConnected S] :
    (ΦθOver d H θ).ker = (ΛHomθOver d H θ).range := by
  ext e
  simp only [MonoidHom.mem_ker, MonoidHom.mem_range]
  constructor
  · intro he
    have hb : e.base = 1 := he
    have hgeq : IsGEquivariant d e.hom := by
      have h := e.equiv; rw [hb, map_one] at h; exact h
    have hpc : PreservesCleavage d e.hom (𝟭 S) := by
      have hp := e.pres; rw [hb] at hp; exact hp
    obtain ⟨g, hg⟩ := ((unbundled_lift_classification d).2 e.hom hgeq).1 hpc
    refine ⟨g, AutBoxGθOver.ext hg.symm ?_ hb.symm⟩
    show Λ d g⁻¹ = e.inv
    have key : e.hom ⋙ Λ d g⁻¹ = 𝟭 O := by rw [hg, Λ_comp, inv_mul_cancel, Λ_one]
    calc Λ d g⁻¹ = (e.inv ⋙ e.hom) ⋙ Λ d g⁻¹ := by rw [e.inv_hom_id, Functor.id_comp]
      _ = e.inv ⋙ e.hom ⋙ Λ d g⁻¹ := rfl
      _ = e.inv := by rw [key, Functor.comp_id]
  · rintro ⟨g, rfl⟩
    rfl

/-- The `SemidirectProduct.lift` compatibility for the restricted twist:  conjugating `Λθ g` by
    the lift of `A ∈ H` twists `g` by `θ A`.
@isnad1 id=eq.0h8v.s11.bfe5fd4b275e from=translated src=- shape=d8820881 vocab=ab80ebf7
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.liftHomθOver_conj (d : OEData G p) (H : Subgroup (StrictAut S)) (θ : H →* MulAut G)
    (A : H) :
    (ΛHomθOver d H θ).comp (θ A).toMonoidHom
      = (MulAut.conj (liftHomθOver d H θ A)).toMonoidHom.comp (ΛHomθOver d H θ) := by
  refine MonoidHom.ext fun g => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine AutBoxGθOver.ext ?_ ?_ ?_
  · show Λ d ((θ A) g)
        = liftFunctorθ d A.1.inv (θ A)⁻¹ ⋙ Λ d g ⋙ liftFunctorθ d A.1.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.1.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp]
  · show Λ d ((θ A) g)⁻¹
        = liftFunctorθ d A.1.inv (θ A)⁻¹ ⋙ Λ d g⁻¹ ⋙ liftFunctorθ d A.1.hom (θ A)
    rw [Λ_comp_liftθ, ← Functor.assoc, liftθ_comp, A.1.inv_hom_id, mul_inv_cancel, liftθ_id,
      Functor.id_comp, map_inv]
  · simp

/-- `G ⋊[θ] H →* AutBoxGθOver d H θ`:  `inl g ↦ Λθ g`, `inr A ↦ liftHomθOver A`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθOver (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) : SemidirectProduct G H θ →* AutBoxGθOver d H θ :=
  SemidirectProduct.lift (ΛHomθOver d H θ) (liftHomθOver d H θ) (liftHomθOver_conj d H θ)

/--
@isnad1 id=eq.0h8v.s11.70350f6854a9 from=translated src=- shape=1d9265d3 vocab=799bb1ce
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθOver_inl (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (g : G) :
    semidirectToAutBoxGθOver d H θ (SemidirectProduct.inl g) = ΛHomθOver d H θ g :=
  SemidirectProduct.lift_inl _ _ _ g

/--
@isnad1 id=eq.0h8v.s11.21b8c105c93c from=translated src=- shape=7e8ae66a vocab=d553292f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.semidirectToAutBoxGθOver_inr (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) (A : H) :
    semidirectToAutBoxGθOver d H θ (SemidirectProduct.inr A) = liftHomθOver d H θ A :=
  SemidirectProduct.lift_inr _ _ _ A

/-- The restricted twisted classification as an explicit group isomorphism
    `AutBoxGθOver d H θ ≃* G ⋊[θ] H`  (needs `[IsConnected S]`).  This is the subgroup version
    of `autBoxGθMulEquivSemidirect` (paper `thm:twisted`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverMulEquivSemidirect (d : OEData G p) (H : Subgroup (StrictAut S))
    (θ : H →* MulAut G) [IsConnected S] :
    AutBoxGθOver d H θ ≃* SemidirectProduct G H θ := by
  have hinj : Function.Injective (semidirectToAutBoxGθOver d H θ) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul,
      semidirectToAutBoxGθOver_inl, semidirectToAutBoxGθOver_inr] at hx
    have hright : x.right = 1 := by
      have h2 := congrArg (ΦθOver d H θ) hx
      rw [map_mul, map_one] at h2
      simpa using h2
    rw [hright, map_one, mul_one] at hx
    have hleft : x.left = 1 := ΛHomθOver_injective d H θ (by rw [hx, map_one])
    exact SemidirectProduct.ext hleft hright
  have hsurj : Function.Surjective (semidirectToAutBoxGθOver d H θ) := by
    intro e
    have hker : e * (liftHomθOver d H θ e.base)⁻¹ ∈ (ΦθOver d H θ).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      simp
    rw [ker_ΦθOver_eq_range_ΛθOver, MonoidHom.mem_range] at hker
    obtain ⟨g, hg⟩ := hker
    refine ⟨SemidirectProduct.inl g * SemidirectProduct.inr e.base, ?_⟩
    rw [map_mul, semidirectToAutBoxGθOver_inl, semidirectToAutBoxGθOver_inr, hg,
      inv_mul_cancel_right]
  exact (MulEquiv.ofBijective (semidirectToAutBoxGθOver d H θ) ⟨hinj, hsurj⟩).symm

/-- The inverse of `autBoxGθOverMulEquivSemidirect` is the canonical map
    `G ⋊[θ] H → Sym^θ_H(p)`, `(a, A) ↦ Λ_a Ã_θ` (paper `thm:twisted`).
@isnad1 id=eq.0h8v.s11.a2e656fef01d from=translated src=- shape=3956a161 vocab=0a72e2a3
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverMulEquivSemidirect_symm_apply (d : OEData G p)
    (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) [IsConnected S]
    (x : SemidirectProduct G H θ) :
    (autBoxGθOverMulEquivSemidirect d H θ).symm x = semidirectToAutBoxGθOver d H θ x := rfl

/-- Projection: the right part of `autBoxGθOverMulEquivSemidirect` is `ΦθOver`
    (paper `thm:twisted`).
@isnad1 id=eq.0h8v.s10.9a2be6e3d3a5 from=translated src=- shape=60eda63a vocab=30693e47
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverMulEquivSemidirect_apply_right (d : OEData G p)
    (H : Subgroup (StrictAut S)) (θ : H →* MulAut G) [IsConnected S] (e : AutBoxGθOver d H θ) :
    (autBoxGθOverMulEquivSemidirect d H θ e).right = ΦθOver d H θ e := by
  conv_rhs => rw [← (autBoxGθOverMulEquivSemidirect d H θ).symm_apply_apply e]
  rw [autBoxGθOverMulEquivSemidirect_symm_apply,
    ← SemidirectProduct.inl_left_mul_inr_right (autBoxGθOverMulEquivSemidirect d H θ e),
    map_mul, semidirectToAutBoxGθOver_inl, semidirectToAutBoxGθOver_inr, map_mul]
  simp

/-- The untwisted theorem is the special case of trivial `θ` (paper, remark after
    `thm:twisted`), at group level: for `θ = 1` the twisted group `Sym^1_H(p)` is
    `Sym_H(p)`.  The map is the identity on `hom`, `inv` and the base symmetry; twisted
    equivariance at `θ = 1` is `IsGEquivariant` (`isTwistedEquivariant_one`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverOneMulEquiv (d : OEData G p) (H : Subgroup (StrictAut S)) :
    AutBoxGθOver d H 1 ≃* AutBoxGOver d H where
  toFun e := ⟨{ hom := e.hom
                inv := e.inv
                hom_inv_id := e.hom_inv_id
                inv_hom_id := e.inv_hom_id
                base := e.base.1
                equiv := by
                  have h := e.equiv
                  rw [MonoidHom.one_apply] at h
                  exact (isTwistedEquivariant_one d e.hom).1 h
                pres := e.pres }, e.base.2⟩
  invFun e :=
    { hom := e.1.hom
      inv := e.1.inv
      hom_inv_id := e.1.hom_inv_id
      inv_hom_id := e.1.inv_hom_id
      base := ⟨e.1.base, e.2⟩
      equiv := by
        rw [MonoidHom.one_apply]
        exact (isTwistedEquivariant_one d e.1.hom).2 e.1.equiv
      pres := e.1.pres }
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- `autBoxGθOverOneMulEquiv` is the identity on the total functor (paper, remark after
    `thm:twisted`).
@isnad1 id=eq.0h7v.s14.57be5b11adb7 from=translated src=- shape=b20e06fd vocab=c5d78a91
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverOneMulEquiv_apply_hom (d : OEData G p) (H : Subgroup (StrictAut S))
    (e : AutBoxGθOver d H 1) : (autBoxGθOverOneMulEquiv d H e).1.hom = e.hom := rfl

/-- `autBoxGθOverOneMulEquiv` is the identity on the covered base symmetry (paper, remark after
    `thm:twisted`).
@isnad1 id=eq.0h7v.s14.169e7fdb1717 from=translated src=- shape=9b3b7a3a vocab=15180b7a
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.autBoxGθOverOneMulEquiv_apply_base (d : OEData G p)
    (H : Subgroup (StrictAut S)) (e : AutBoxGθOver d H 1) :
    (autBoxGθOverOneMulEquiv d H e).1.base = e.base.1 := rfl

/-! ## 15. A fully closed concrete nontrivial twist:  `G = Multiplicative (ZMod 3)`

  The general `θSingleObj_ne_one` is conditional on `[Nontrivial (MulAut G)]`.  Here we discharge
  that hypothesis with a fully closed witness:  inversion on `Multiplicative (ZMod 3)` (i.e.
  negation on `ZMod 3`) is a nontrivial group automorphism, so `θSingleObj (Multiplicative (ZMod 3))`
  is a genuinely nontrivial twist, and the semidirect identification applies to it. -/

/-- The concrete structure group `G = Multiplicative (ZMod 3)`, which has a nontrivial
    automorphism (negation), hence a nontrivial twist.-/
abbrev _root_.Tengoku.ObserverEquivarianceLean.G3 := Multiplicative (ZMod 3)

/-- Inversion on `G3 = Multiplicative (ZMod 3)` — equivalently negation on `ZMod 3` — as a group
    automorphism (a homomorphism because `G3` is commutative).-/
def _root_.Tengoku.ObserverEquivarianceLean.zmod3NegMulAut : MulAut G3 where
  toFun := Inv.inv
  invFun := Inv.inv
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' a b := mul_inv a b

/-- The negation automorphism is nontrivial:  it sends `ofAdd 1` to `ofAdd (-1) = ofAdd 2 ≠ ofAdd 1`.
@isnad1 id=ne.0h0v.s8.97cabc788bf2 from=translated src=- shape=2d527563 vocab=ae7769b7
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.zmod3NegMulAut_ne_one : zmod3NegMulAut ≠ 1 := by
  intro h
  have hval : (Multiplicative.ofAdd (1 : ZMod 3))⁻¹ = Multiplicative.ofAdd (1 : ZMod 3) :=
    DFunLike.congr_fun h (Multiplicative.ofAdd (1 : ZMod 3))
  have e : Multiplicative.ofAdd (-1 : ZMod 3) = Multiplicative.ofAdd (1 : ZMod 3) := by
    rw [ofAdd_neg]; exact hval
  have hz : (-1 : ZMod 3) = 1 := Multiplicative.ofAdd.injective e
  exact absurd hz (by decide)

/-- A fully closed semidirect-product identification with a nontrivial twist:
    `Aut□^θ_G3(O/pLab) ≃* G3 ⋊[θSingleObj] Aut(SingleObj G3)` — an instance of paper
    `thm:twisted` with a concrete `θ ≠ 1` (a different witness from the paper's `ex:twist`).-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.zmod3SemidirectWitness :
    AutBoxGθ (labData G3 G3) (θSingleObj G3)
      ≃* SemidirectProduct G3 (StrictAut (SingleObj G3)) (θSingleObj G3) :=
  autBoxGθMulEquivSemidirect (labData G3 G3) (θSingleObj G3)

/-! ## 11. Additional helper lemmas the article uses

  A strict autoequivalence is determined by its `hom` functor (`StrictAut.ext_hom`); the
  packaging of `θSingleObj` as a genuine `MulEquiv` (`θSingleObjEquiv`); the full MORPHISM
  forms of the object-level predicates (`PreservesCleavage.map_chi`,
  `isGEquivariant_map_actHom`); and base-symmetry uniqueness (`OEData.base_unique`) with the
  resulting `hom`-only extensionality (`AutBoxG.ext_hom`).  The last three formalize the
  reasoning the paper's `def:lifts` states in prose: because `p` is faithful, the object-level
  equations force the corresponding morphism-level ones, and the covered base symmetry is
  determined strictly by the total functor.

  PROOF TECHNIQUE NOTE.  The `eqToHom` casts produced by `Functor.congr_hom`/`congr_obj` on
  composite functors carry `(F ⋙ p).obj`-shaped endpoints that are only *definitionally* equal
  to the `p.obj (F.obj _)` forms the rest of the file uses; goals mixing the two are ill-typed
  at instance transparency, which silently disables `simp`/`rw`/`aesop_cat`.  The fix used
  throughout this section: state every intermediate cast with syntactically clean endpoints in
  a `have`, justify it by a defeq `exact`, and only then rewrite. -/

/-- A strict autoequivalence is determined by its `hom` functor (its strict inverse is unique).
@isnad1 id=eq.1h3v.s5.1318b4c8616e from=translated src=- shape=1a8ef8bc vocab=cca69aa9
-/
theorem Tengoku.ObserverEquivarianceLean.StrictAut.ext_hom {C : Type*} [Category C] {A B : StrictAut C} (h : A.hom = B.hom) :
    A = B := by
  refine StrictAut.ext h ?_
  calc A.inv = A.inv ⋙ (B.hom ⋙ B.inv) := by rw [B.hom_inv_id, Functor.comp_id]
    _ = A.inv ⋙ (A.hom ⋙ B.inv) := by rw [h]
    _ = (A.inv ⋙ A.hom) ⋙ B.inv := rfl
    _ = B.inv := by rw [A.inv_hom_id, Functor.id_comp]

/-- `θSingleObj` is injective, hence (with `θSingleObj_surjective`) a genuine group isomorphism.
@isnad1 id=injectiv.0h1v.s8.7fdef4355da6 from=translated src=- shape=70052d6d vocab=bf0eead7
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.θSingleObj_injective (G : Type*) [Group G] : Function.Injective (θSingleObj G) := by
  intro A B hAB
  have hfun : ∀ g, ((SingleObj.mapHom G G).symm A.hom) g = ((SingleObj.mapHom G G).symm B.hom) g :=
    fun g => DFunLike.congr_fun hAB g
  have hhom : A.hom = B.hom := (SingleObj.mapHom G G).symm.injective (MonoidHom.ext hfun)
  exact StrictAut.ext_hom hhom

/-- The functorial twist `θSingleObj` packaged as a genuine group isomorphism
    `StrictAut (SingleObj G) ≃* MulAut G`.-/
noncomputable def _root_.Tengoku.ObserverEquivarianceLean.θSingleObjEquiv (G : Type*) [Group G] :
    StrictAut (SingleObj G) ≃* MulAut G :=
  MulEquiv.ofBijective (θSingleObj G) ⟨θSingleObj_injective G, θSingleObj_surjective G⟩

/--
@isnad1 id=eq.0h2v.s9.9fca65cce5d5 from=translated src=- shape=73f305fe vocab=a4b8c6a8
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.θSingleObjEquiv_apply (G : Type*) [Group G] (A : StrictAut (SingleObj G)) :
    θSingleObjEquiv G A = θSingleObj G A := rfl

/-- The full MORPHISM form of cleavage preservation (the article's `def:lifts` remark):
    `pc.src`, the covering equation and `p_faithful` force the morphism equality
    `F(χ_{u,y}) = χ_{A u, F y}` up to the `eqToHom` cast supplied by `pc.src`.  So the
    object-level `PreservesCleavage` really is the full "chosen cartesian arrows to chosen
    cartesian arrows" condition.
@isnad1 id=eq.4h11v.s8.95bbc917b617 from=translated src=- shape=b9a17e28 vocab=b581c40d
-/
theorem Tengoku.ObserverEquivarianceLean.PreservesCleavage.map_chi (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (pc : PreservesCleavage d F A) {s t : S} (u : s ⟶ t) (y : O) (hy : p.obj y = t)
    {hy' : p.obj (F.obj y) = A.obj t}
    (hsrc : F.obj (d.reind u y hy) = d.reind (A.map u) (F.obj y) hy') :
    F.map (d.chi u y hy) = eqToHom hsrc ≫ d.chi (A.map u) (F.obj y) hy' := by
  haveI := d.p_faithful
  -- All intermediate statements are phrased with syntactically clean endpoints
  -- (`p.obj (F.obj _)`, `A.obj (p.obj _)`), then justified by defeq `exact`s: the raw
  -- `Functor.congr_hom pc.covers` casts carry `(F ⋙ p).obj`-shaped endpoints that are only
  -- definitionally equal, which blocks every simp/rw at instance transparency.
  have h₁ : p.obj (F.obj (d.reind u y hy)) = A.obj (p.obj (d.reind u y hy)) :=
    Functor.congr_obj pc.covers _
  have h₂ : p.obj (F.obj y) = A.obj (p.obj y) := Functor.congr_obj pc.covers y
  have hcovχ : p.map (F.map (d.chi u y hy))
      = eqToHom h₁ ≫ A.map (p.map (d.chi u y hy)) ≫ eqToHom h₂.symm :=
    Functor.congr_hom pc.covers _
  apply p.map_injective
  rw [hcovχ, d.p_chi, p.map_comp, eqToHom_map, d.p_chi]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- Morphism-level `G`-equivariance is DERIVED (the article's `def:lifts`
    remark):  an object-equivariant `F` covering a base functor is automatically equivariant on
    morphisms, up to the `eqToHom` casts supplied by object equivariance.
@isnad1 id=eq.2h11v.s9.c0828267fd51 from=translated src=- shape=c1482740 vocab=3508ee45
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.isGEquivariant_map_actHom (d : OEData G p) {F : O ⥤ O} {A : S ⥤ S}
    (hF : IsGEquivariant d F) (hc : F ⋙ p = p ⋙ A) {x y : O} (f : x ⟶ y) (g : G) :
    F.map (d.actHom f g)
      = eqToHom (hF x g) ≫ d.actHom (F.map f) g ≫ eqToHom (hF y g).symm := by
  haveI := d.p_faithful
  -- Clean-endpoint restatements of the covering equation (see `PreservesCleavage.map_chi`).
  have h₁ : p.obj (F.obj (d.act x g)) = A.obj (p.obj (d.act x g)) := Functor.congr_obj hc _
  have h₂ : p.obj (F.obj (d.act y g)) = A.obj (p.obj (d.act y g)) := Functor.congr_obj hc _
  have h₃ : p.obj (F.obj x) = A.obj (p.obj x) := Functor.congr_obj hc x
  have h₄ : p.obj (F.obj y) = A.obj (p.obj y) := Functor.congr_obj hc y
  have hcov₁ : p.map (F.map (d.actHom f g))
      = eqToHom h₁ ≫ A.map (p.map (d.actHom f g)) ≫ eqToHom h₂.symm :=
    Functor.congr_hom hc _
  have hcov₂ : p.map (F.map f) = eqToHom h₃ ≫ A.map (p.map f) ≫ eqToHom h₄.symm :=
    Functor.congr_hom hc f
  apply p.map_injective
  rw [hcov₁, d.p_actHom, p.map_comp, p.map_comp, eqToHom_map, eqToHom_map, d.p_actHom, hcov₂]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc]

/-- Uniqueness of the covered base functor (the article's `def:lifts`: the base functor `A` is
    determined by `F`):  since every base object is
    `p.obj (base s)` and every base arrow lifts through derived fullness, precomposition with
    `p` is injective on functors:  `p ⋙ A = p ⋙ B → A = B`.  Hence the `base` field of a
    bundle automorphism is determined by its `hom` field.
@isnad1 id=eq.1h7v.s6.08c401a99c5c from=translated src=- shape=b728fd8c vocab=59b01e11
-/
theorem Tengoku.ObserverEquivarianceLean.OEData.base_unique (d : OEData G p) {A B : S ⥤ S} (hAB : p ⋙ A = p ⋙ B) : A = B := by
  haveI := d.isFull
  haveI := d.p_faithful
  have hobj : ∀ s, A.obj s = B.obj s := fun s => by
    have h : A.obj (p.obj (d.base s)) = B.obj (p.obj (d.base s)) :=
      Functor.congr_obj hAB (d.base s)
    rwa [d.p_base] at h
  refine CategoryTheory.Functor.ext hobj (fun s t u => ?_)
  -- Lift `u` through `p` (up to the basepoint casts) and transport `hAB` along the lift,
  -- with all cast endpoints phrased cleanly (see `PreservesCleavage.map_chi`).
  have hw : p.map (p.preimage (eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm))
      = eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm := p.map_preimage _
  have hA : A.obj (p.obj (d.base s)) = B.obj (p.obj (d.base s)) := Functor.congr_obj hAB _
  have hB : A.obj (p.obj (d.base t)) = B.obj (p.obj (d.base t)) := Functor.congr_obj hAB _
  have key : A.map (p.map (p.preimage (eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm)))
      = eqToHom hA
          ≫ B.map (p.map (p.preimage (eqToHom (d.p_base s) ≫ u ≫ eqToHom (d.p_base t).symm)))
          ≫ eqToHom hB.symm :=
    Functor.congr_hom hAB _
  rw [hw] at key
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans,
    eqToHom_trans_assoc] at key
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at key
  simpa only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Category.comp_id] using key

/-- `AutBoxG` extensionality by `hom` alone:  equal `hom` functors force
    equal `base` (`base_unique` + `StrictAut.ext_hom`) and equal `inv` (a strict inverse is
    unique), so the same total functor cannot cover two different base symmetries.
@isnad1 id=eq.1h7v.s6.917f3000e37f from=translated src=- shape=7244f288 vocab=870c179d
-/
theorem Tengoku.ObserverEquivarianceLean.AutBoxG.ext_hom (d : OEData G p) {e₁ e₂ : AutBoxG d} (h : e₁.hom = e₂.hom) :
    e₁ = e₂ := by
  have hbase : e₁.base = e₂.base := by
    refine StrictAut.ext_hom (d.base_unique ?_)
    rw [← e₁.pres.covers, h, e₂.pres.covers]
  have hinv : e₁.inv = e₂.inv := by
    calc e₁.inv = e₁.inv ⋙ (e₂.hom ⋙ e₂.inv) := by rw [e₂.hom_inv_id, Functor.comp_id]
      _ = e₁.inv ⋙ (e₁.hom ⋙ e₂.inv) := by rw [h]
      _ = (e₁.inv ⋙ e₁.hom) ⋙ e₂.inv := rfl
      _ = e₂.inv := by rw [e₁.inv_hom_id, Functor.id_comp]
  exact AutBoxG.ext h hinv hbase
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
