import Tengoku.Seed.Topology.Connected.PathConnected
import Tengoku.Seed.Topology.Connected.TotallyDisconnected
import Tengoku.Seed.Topology.Homeomorph.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The path-component Reeb quotient

For a continuous map `f : C(X, Y)` into an arbitrary topological space `Y`, two points are
Reeb-related when some path joins them along which `f` is constant (`ReebRel`); equivalently,
they have equal value and lie in the same path component of that fibre. The Reeb quotient
`ReebQuotient f` is `X` modulo this equivalence with the quotient topology, with projection
`ReebQuotient.mk f` and the descended map `ReebQuotient.height f`, the height when `Y = ℝ`.
Every continuous map constant on Reeb classes descends uniquely (`ReebQuotient.existsUnique_lift`).

The acceptance cases are an empty domain, an injective map (the quotient is homeomorphic to `X`)
and a constant map (the quotient is homeomorphic to `ZerothHomotopy X`). Nothing here claims
that the projection is open or that the quotient is Hausdorff.

Source: de Silva, Munch and Patel, *Categorified Reeb Graphs*, §2.4: the object-level
construction of Proposition 2.10, not its functor; see `docs/math/reeb-quotient.md`.
-/

open Topology

universe u v w

namespace TDA.Reeb

variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-! ## Constant-value path relation -/

/-- `x ~_f x'`: some path from `x` to `x'` stays at the value `f x`.-/
def ReebRel (f : C(X, Y)) (x x' : X) : Prop :=
  ∃ γ : Path x x', ∀ t, f (γ t) = f x

/-- The relation is literally `JoinedIn` the fibre `f ⁻¹' {f x}` of the source point.
@isnad1 id=iff.0h5v.s6.b7edbf13cabc from=translated src=- shape=fc5f88e4 vocab=cdc5be24
-/
theorem reebRel_iff_joinedIn (f : C(X, Y)) (x x' : X) :
    ReebRel f x x' ↔ JoinedIn (f ⁻¹' {f x}) x x' := Iff.rfl

/--
@isnad1 id=eq.1h5v.s6.3e0fc2e7865a from=translated src=- shape=aee8a1e6 vocab=a206a1d4
-/
theorem ReebRel.apply_eq {f : C(X, Y)} {x x' : X} (h : ReebRel f x x') : f x' = f x := by
  obtain ⟨γ, hγ⟩ := h
  simpa using hγ 1

/-- Contract form: equal value and the same path component of that fibre subtype.
@isnad1 id=iff.0h5v.s8.ed52413d65b5 from=translated src=- shape=a98b9588 vocab=3f78c033
-/
theorem reebRel_iff_joined_fiber (f : C(X, Y)) (x x' : X) :
    ReebRel f x x' ↔
      ∃ h : f x' = f x,
        Joined (⟨x, rfl⟩ : f ⁻¹' {f x}) (⟨x', h⟩ : f ⁻¹' {f x}) := by
  constructor
  · intro hr
    exact ⟨hr.apply_eq, (joinedIn_iff_joined (F := f ⁻¹' {f x}) rfl hr.apply_eq).1 hr⟩
  · rintro ⟨h, hj⟩
    exact (joinedIn_iff_joined (F := f ⁻¹' {f x}) rfl h).2 hj

/-! ## Setoid -/

/--
@isnad1 id=reebrel.0h4v.s4.ede7581819bf from=translated src=- shape=29347264 vocab=5bd7a094
-/
theorem ReebRel.refl (f : C(X, Y)) (x : X) : ReebRel f x x :=
  ⟨Path.refl x, fun _ => rfl⟩

/--
@isnad1 id=reebrel.1h5v.s5.1b9ad87909d9 from=translated src=- shape=1b526085 vocab=5bd7a094
-/
theorem ReebRel.symm {f : C(X, Y)} {x x' : X} (h : ReebRel f x x') : ReebRel f x' x := by
  obtain ⟨γ, hγ⟩ := h
  refine ⟨γ.symm, fun t => ?_⟩
  show f (γ (unitInterval.symm t)) = f x'
  rw [hγ]
  simpa using (hγ 1).symm

/--
@isnad1 id=reebrel.2h6v.s5.0342f751a615 from=translated src=- shape=3708c587 vocab=5bd7a094
-/
theorem ReebRel.trans {f : C(X, Y)} {x x' x'' : X} (h₁ : ReebRel f x x')
    (h₂ : ReebRel f x' x'') : ReebRel f x x'' := by
  have e := h₁.apply_eq
  obtain ⟨γ, hγ⟩ := h₁
  obtain ⟨δ, hδ⟩ := h₂
  refine ⟨γ.trans δ, fun t => ?_⟩
  rw [Path.trans_apply]
  split_ifs
  · exact hγ _
  · rw [hδ, e]

/-- The Reeb equivalence of `f` as a setoid on `X`.-/
def reebSetoid (f : C(X, Y)) : Setoid X where
  r := ReebRel f
  iseqv := ⟨ReebRel.refl f, ReebRel.symm, ReebRel.trans⟩

/--
@isnad1 id=iff.0h5v.s5.05f261113d47 from=translated src=- shape=2ea79652 vocab=6dabebd8
-/
theorem reebSetoid_r (f : C(X, Y)) (x x' : X) : reebSetoid f x x' ↔ ReebRel f x x' := Iff.rfl

/-! ## Quotient with the quotient topology -/

/-- The Reeb quotient `Q_f = X / ~_f`.-/
def ReebQuotient (f : C(X, Y)) : Type u := Quotient (reebSetoid f)

instance (f : C(X, Y)) : TopologicalSpace (ReebQuotient f) :=
  inferInstanceAs (TopologicalSpace (Quotient (reebSetoid f)))

namespace ReebQuotient

variable (f : C(X, Y))

/-- The projection `q_f : X → Q_f`.-/
def mk (x : X) : ReebQuotient f := Quotient.mk (reebSetoid f) x

/--
@isnad1 id=surjecti.0h3v.s4.7d5f4f83419b from=translated src=- shape=e224cbca vocab=fb2aefc5
-/
theorem mk_surjective : Function.Surjective (mk f) := Quotient.mk_surjective

/--
@isnad1 id=isquotie.0h3v.s5.960f4056461f from=translated src=- shape=e224cbca vocab=80d03a0f
-/
theorem isQuotientMap_mk : IsQuotientMap (mk f) := isQuotientMap_quotient_mk'

/--
@isnad1 id=continuo.0h3v.s5.9e6e2b19bb79 from=translated src=- shape=e224cbca vocab=871f9280
-/
@[continuity, fun_prop]
theorem continuous_mk : Continuous (mk f) := (isQuotientMap_mk f).continuous

/-- `q_f` as a bundled continuous map.-/
def proj : C(X, ReebQuotient f) := ⟨mk f, continuous_mk f⟩

/--
@isnad1 id=eq.0h4v.s6.cca410205b97 from=translated src=- shape=1885642b vocab=36e7afc9
-/
@[simp] theorem proj_apply (x : X) : proj f x = mk f x := rfl

/--
@isnad1 id=iff.0h5v.s5.28fc27fc0991 from=translated src=- shape=012a237f vocab=e7299e53
-/
theorem mk_eq_mk_iff {x x' : X} : mk f x = mk f x' ↔ ReebRel f x x' := Quotient.eq

/--
@isnad1 id=eq.1h6v.s6.504e68e90da1 from=translated src=- shape=40c5ffee vocab=fb3499ea
-/
theorem mk_eq_mk_of_path {x x' : X} (γ : Path x x') (hγ : ∀ t, f (γ t) = f x) :
    mk f x = mk f x' := (mk_eq_mk_iff f).2 ⟨γ, hγ⟩

/--
@isnad1 id=var.0h6v.s5.37451a36488e from=translated src=- shape=e4fe8223 vocab=dffbb84b
-/
@[elab_as_elim]
theorem ind {motive : ReebQuotient f → Prop} (h : ∀ x, motive (mk f x)) (q : ReebQuotient f) :
    motive q := Quotient.ind h q

/-! ## Universal property and the descended map -/

variable {f}

/-- Descent of a continuous map constant on `~_f` classes (any target `Z`).-/
def lift (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    C(ReebQuotient f, Z) :=
  ⟨Quotient.lift k hk, k.continuous.quotient_lift hk⟩

/--
@isnad1 id=eq.1h6v.s7.a79317b61f0c from=translated src=- shape=620e4431 vocab=317ac515
-/
@[simp] theorem lift_mk (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') (x : X) :
    lift k hk (mk f x) = k x := rfl

/--
@isnad1 id=eq.1h5v.s6.bb7df0bcaea9 from=translated src=- shape=c1f87785 vocab=5a122eef
-/
theorem lift_comp_proj (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    (lift k hk).comp (proj f) = k := rfl

/-- Uniqueness via surjectivity of `q_f`.
@isnad1 id=eq.2h6v.s7.2d4cee8f6f7d from=translated src=- shape=e56d828b vocab=317ac515
-/
theorem lift_unique (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x')
    (g : C(ReebQuotient f, Z)) (hg : ∀ x, g (mk f x) = k x) : g = lift k hk := by
  ext q
  induction q using ind with
  | h x => exact hg x

/--
@isnad1 id=eq.1h6v.s7.4dbc969f16ea from=translated src=- shape=725b4594 vocab=7e3dd62c
-/
theorem hom_ext {g g' : C(ReebQuotient f, Z)} (h : ∀ x, g (mk f x) = g' (mk f x)) : g = g' := by
  ext q
  induction q using ind with
  | h x => exact h x

/--
@isnad1 id=existsun.1h5v.s7.d501c7e43039 from=translated src=- shape=36911e39 vocab=1d52ada0
-/
theorem existsUnique_lift (k : C(X, Z)) (hk : ∀ x x', ReebRel f x x' → k x = k x') :
    ∃! g : C(ReebQuotient f, Z), g.comp (proj f) = k :=
  ⟨lift k hk, rfl, fun g hg =>
    lift_unique k hk g fun x => by simpa using congrArg (· x) hg⟩

/-- Any continuous map that factors through `q_f` is constant on classes (converse).
@isnad1 id=eq.1h7v.s7.8575eb185569 from=translated src=- shape=6f17a311 vocab=d7c6c19a
-/
theorem apply_eq_of_reebRel (g : C(ReebQuotient f, Z)) {x x' : X} (h : ReebRel f x x') :
    g (mk f x) = g (mk f x') := by rw [(mk_eq_mk_iff f).2 h]

variable (f)

/-- `f̄ : Q_f → Y`, the descended map; the height when `Y = ℝ`.-/
def height : C(ReebQuotient f, Y) :=
  lift f fun _ _ h => h.apply_eq.symm

/--
@isnad1 id=eq.0h4v.s6.c819e3866ab8 from=translated src=- shape=a5438134 vocab=e932dd9c
-/
@[simp] theorem height_mk (x : X) : height f (mk f x) = f x := rfl

/--
@isnad1 id=eq.0h3v.s5.10ce4bf9d066 from=translated src=- shape=12a8542f vocab=5a651cc2
-/
theorem height_comp_proj : (height f).comp (proj f) = f := rfl

/-! ## Acceptance theorems (any target `Y`) -/

/-- Empty domain: the quotient is empty.
@isnad1 id=isempty.0h3v.s4.2015e8008fa9 from=translated src=- shape=cbcc3c3e vocab=b2b04c19
-/
instance instIsEmpty [IsEmpty X] : IsEmpty (ReebQuotient f) :=
  ⟨fun q => by induction q using ReebQuotient.ind with | h x => exact isEmptyElim x⟩

end ReebQuotient

/--
@isnad1 id=iff.1h5v.s5.28f523d796ba from=translated src=- shape=e3b27275 vocab=4b42d760
-/
theorem reebRel_iff_eq_of_injective {f : C(X, Y)} (hf : Function.Injective f) (x x' : X) :
    ReebRel f x x' ↔ x = x' := by
  constructor
  · rintro ⟨γ, hγ⟩
    simpa using (hf (hγ 1)).symm
  · rintro rfl; exact ReebRel.refl f x

/--
@isnad1 id=iff.0h5v.s5.5604c77c72ce from=translated src=- shape=9a8fd420 vocab=0e4d4bf7
-/
theorem reebRel_const_iff (c : Y) (x x' : X) :
    ReebRel (ContinuousMap.const X c) x x' ↔ Joined x x' :=
  ⟨fun ⟨γ, _⟩ => ⟨γ⟩, fun ⟨γ⟩ => ⟨γ, fun _ => rfl⟩⟩

namespace ReebQuotient

/-- Injective `f`: the quotient is canonically homeomorphic to `X`.-/
def homeomorphOfInjective {f : C(X, Y)} (hf : Function.Injective f) : ReebQuotient f ≃ₜ X :=
  (Homeomorph.Quotient.congrRight (r := reebSetoid f) (r' := ⊥) fun x x' => by
      rw [Setoid.bot_def, reebSetoid_r, reebRel_iff_eq_of_injective hf]).trans
    Homeomorph.quotientBot

/--
@isnad1 id=eq.1h4v.s6.52215bf986f9 from=translated src=- shape=7dff142d vocab=599bbadb
-/
@[simp] theorem homeomorphOfInjective_mk {f : C(X, Y)} (hf : Function.Injective f) (x : X) :
    homeomorphOfInjective hf (mk f x) = x := rfl

/-- Constant `f`: the quotient is homeomorphic to the existing path-component quotient
`ZerothHomotopy X` with its quotient topology.-/
def homeomorphZerothHomotopy (c : Y) :
    ReebQuotient (ContinuousMap.const X c) ≃ₜ ZerothHomotopy X :=
  Homeomorph.Quotient.congrRight (r := reebSetoid (ContinuousMap.const X c))
    (r' := pathSetoid X) fun x x' => reebRel_const_iff c x x'

/--
@isnad1 id=eq.0h4v.s7.97bc609f4f47 from=translated src=- shape=8a5d3ef5 vocab=7ebe31f9
-/
@[simp] theorem homeomorphZerothHomotopy_mk (c : Y) (x : X) :
    homeomorphZerothHomotopy c (mk (ContinuousMap.const X c) x) = ZerothHomotopy.mk x := rfl

end ReebQuotient

/-! ## Fixtures (`Y := ℝ` and one non-real target) -/

namespace Examples

open ReebQuotient

/-- Discrete two-point domain, constant real height: the two classes are distinct.
@isnad1 id=ne.0h0v.s6.af0eaac58dfd from=translated src=- shape=6e4b0340 vocab=17d0711a
-/
theorem boolConst_mk_false_ne_true :
    mk (ContinuousMap.const Bool (0 : ℝ)) false ≠ mk (ContinuousMap.const Bool (0 : ℝ)) true := by
  intro h
  obtain ⟨γ, -⟩ := (mk_eq_mk_iff _).1 h
  have := PreconnectedSpace.constant inferInstance γ.continuous (x := 0) (y := 1)
  simp at this

/-- Every class of that quotient is one of the two.
@isnad1 id=or.0h1v.s7.28fef5f24c22 from=translated src=- shape=965b2fc3 vocab=17d0711a
-/
theorem boolConst_eq_mk_false_or_mk_true (q : ReebQuotient (ContinuousMap.const Bool (0 : ℝ))) :
    q = mk _ false ∨ q = mk _ true := by
  induction q using ReebQuotient.ind with
  | h b => cases b <;> simp

/-- Identity height on `ℝ`: `Q_id ≃ₜ ℝ`.-/
def realIdHomeomorph : ReebQuotient (ContinuousMap.id ℝ) ≃ₜ ℝ :=
  homeomorphOfInjective (f := ContinuousMap.id ℝ) Function.injective_id

end Examples

end TDA.Reeb
