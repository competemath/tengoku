import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku.Seed.AlgebraicGeometry.ResidueField
import Tengoku.Seed.AlgebraicGeometry.Morphisms.QuasiCompact
import Tengoku.Seed.AlgebraicGeometry.Morphisms.ClosedImmersion
import Tengoku.Seed.AlgebraicGeometry.Over
import Tengoku.Seed.Topology.LocallyFinsupp.Pushforward
import Tengoku.Seed.Algebra.FreeAbelianGroup.Finsupp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic cycles on a scheme, graded by codimension

This file defines the group of algebraic cycles on an arbitrary scheme `X` —
functions `X → ℤ` with locally finite support, following the carrier design
Mathlib itself adopts for (ungraded) algebraic cycles — together with:

* `HodgePilot.Scheme.Cycle`: the carrier, `Function.locallyFinsupp X R`;
* `HodgePilot.Scheme.codim` / `HodgePilot.Scheme.dimClosure`: codimension
  (`Order.coheight`) and dimension of the closure (`Order.height`) of a
  point — the two gradings; the generic point of an integral scheme has
  codimension `0`;
* `HodgePilot.Scheme.cyclesOfCodim X p` / `cyclesOfDim X d`: the subgroup
  `Z^p(X)` (resp. `Z_d(X)`) of cycles supported on points of codimension `p`
  (resp. on points whose closure has dimension `d`);
* `HodgePilot.Scheme.Cycle.toFinsupp`: on a quasi-compact (e.g. Noetherian)
  scheme every cycle has finite support: `Cycle X ℤ ≃+ (X →₀ ℤ)`;
* `HodgePilot.Scheme.cyclesOfCodimEquivFreeAbelian`: **the free abelian group
  theorem** — on a quasi-compact scheme, `Z^p(X)` is the free abelian group
  on the codimension-`p` points of `X` (equivalently, on the integral closed
  subschemes of codimension `p`: points of a scheme correspond to irreducible
  closed subsets, `irreducibleSetEquivPoints`);
* `HodgePilot.Scheme.Cycle.map`: pushforward along a quasi-compact morphism,
  weighted by the residue-field degree; along a closed immersion it is
  coefficient-preserving (`HodgePilot.Scheme.Cycle.map_single`);
* `HodgePilot.Scheme.Cycle.weightedDegree` / `degree`: the degree of a cycle
  on a scheme over a field `k`, weighting each point by `[κ(x) : k]`.

## Attribution and provenance

The carrier layer (`Function.locallyFinsupp` with its lattice/group API, and
the weighted pushforward `Function.locallyFinsupp.map`) together with the
order-of-vanishing infrastructure the follow-up stages consume
(`Ring.ord`/`Ring.ordFrac`) are due to **Raphael Douglas Giles** (with Stefan
Kebekus for `locallyFinsupp` itself) and are already in Mathlib at our pin;
this file deliberately builds the graded layer on exactly his carrier shape.
The carrier and weighted pushforward were merged as Mathlib PRs **#26304**
(merged 2026-06-05) and **#37901** (merged 2026-06-25, adding
`Mathlib/AlgebraicGeometry/AlgebraicCycle/Basic.lean`, commit `d31b5731`); the
order-of-vanishing infrastructure was merged as **#29774** (merged 2026-07-02).

Two declarations (`Scheme.Hom.residueDegree` and the shape of `Cycle.map`)
are **vendored** from Raphael Douglas Giles's `AlgebraicGeometry.AlgebraicCycle`
work; `Scheme.Hom.residueDegree` is on Mathlib master now
(`Mathlib/AlgebraicGeometry/ResidueField.lean:147`), in Mathlib master since
2026-06 (PR #37901 chain); DELETE at the first bump past manifest
fabf563a's successor, replacing the vendored copies with the upstream names.

## Design notes

* Points are the subvarieties: a codimension-`p` "integral closed subscheme"
  is represented by its generic point (schemes are sober); no reduced-induced
  subscheme structure is ever constructed.
* Both gradings (dimension and codimension) are provided; no conversion
  between them is claimed — that would require catenary hypotheses absent
  from Mathlib.
* Coefficients are `ℤ` where the group structure matters, generalized to a
  `Zero`-type where it costs nothing.
* `DecidableEq` on scheme points is always discharged by `Classical.decEq`
  (a local instance in this file); no public signature carries it.
-/

open AlgebraicGeometry CategoryTheory Order TopologicalSpace

noncomputable section

namespace HodgePilot

universe u v

attribute [local instance] Classical.decEq

namespace Scheme

variable {X Y : Scheme.{u}} {R : Type v}

/-!
## The carrier: cycles as functions with locally finite support
-/

/-- An **algebraic cycle** on a scheme `X` with coefficients in `R` is a
function `X → R` with locally finite support: the point `x` is thought of as
the integral closed subscheme `closure {x}` (schemes are sober, so this is a
bijective dictionary), and the value at `x` as its multiplicity.

This is exactly the carrier Mathlib itself adopts for algebraic cycles
(`AlgebraicGeometry.AlgebraicCycle`, ≥ 4.32, Raphael Douglas Giles); we keep
it as an `abbrev` so that the entire `Function.locallyFinsupp` API applies
verbatim.-/
abbrev Cycle (X : Scheme.{u}) (R : Type v) [Zero R] :=
  Function.locallyFinsupp X R

namespace Cycle

/-- The **prime cycle** `r · [x]`: the cycle supported at the single point
`x`, with coefficient `r`. (Decidability of equality on points is discharged
classically; no `DecidableEq` hypothesis is exposed.)-/
abbrev single (x : X) (r : R) [Zero R] : Cycle X R :=
  Function.locallyFinsuppWithin.single x r

@[simp]
lemma single_apply [Zero R] (x : X) (r : R) (y : X) :
    single x r y = if y = x then r else 0 :=
  Function.locallyFinsuppWithin.single_apply

lemma support_single_subset [Zero R] (x : X) (r : R) :
    Function.support ⇑(single x r) ⊆ {x} := by
  rw [Function.locallyFinsuppWithin.coe_single]
  exact Pi.support_single_subset

end Cycle

/-!
## Codimension and dimension of points

On the points of a scheme, the specialization preorder (`x ≤ y ↔ y ⤳ x`,
generic points at the top) is the global `Preorder` instance. The
codimension of the subvariety `closure {x}` is `Order.coheight x`, and its
dimension is `Order.height x`. Downstream files should use only these two
named abbreviations, never raw `coheight`/`height` (getting the order
direction wrong typechecks and proves garbage).
-/

/-- The **codimension** of the point `x` — i.e. of the integral closed
subscheme `closure {x}` — as the coheight of `x` in the specialization
order. Equals the Krull dimension of the stalk at `x`
(`codim_eq_ringKrullDim_stalk`, Stacks 02IZ).-/
abbrev codim {X : Scheme.{u}} (x : X) : ℕ∞ :=
  Order.coheight x

/-- The **dimension of the closure** of the point `x` — i.e. of the integral
closed subscheme `closure {x}` — as the height of `x` in the specialization
order.-/
abbrev dimClosure {X : Scheme.{u}} (x : X) : ℕ∞ :=
  Order.height x

/-- The codimension of a point is the Krull dimension of the local ring at
that point (Stacks 02IZ).-/
lemma codim_eq_ringKrullDim_stalk {X : Scheme.{u}} (x : X) :
    (codim x : WithBot ℕ∞) = ringKrullDim (X.presheaf.stalk x) :=
  (ringKrullDim_stalk_eq_coheight x).symm

/-- On an integral scheme, the generic point has codimension zero.-/
@[simp]
lemma codim_genericPoint (X : Scheme.{u}) [IsIntegral X] :
    codim (genericPoint X) = 0 :=
  Order.coheight_eq_zero.mpr fun b _ =>
    AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes b)

/-!
## The graded cycle groups `Z^p(X)` and `Z_d(X)`

Homogeneous cycle groups are subgroups of the one ambient group `Cycle X ℤ`,
not a type-indexed family.
-/

/-- `Z^p(X)`: the subgroup of cycles all of whose support points have
codimension `p`.-/
def cyclesOfCodim (X : Scheme.{u}) (p : ℕ∞) : AddSubgroup (Cycle X ℤ) where
  carrier := {c | ∀ x ∈ Function.support ⇑c, codim x = p}
  zero_mem' := by intro x hx; simp at hx
  add_mem' {a b} ha hb := by
    intro x hx
    have : x ∈ Function.support ⇑a ∪ Function.support ⇑b := by
      have h := Function.support_add (f := ⇑a) (g := ⇑b)
      exact h (by simpa using hx)
    rcases this with h | h
    · exact ha x h
    · exact hb x h
  neg_mem' {a} ha := by intro x hx; exact ha x (by simpa using hx)

/-- `Z_d(X)`: the subgroup of cycles all of whose support points have closure
of dimension `d`.-/
def cyclesOfDim (X : Scheme.{u}) (d : ℕ∞) : AddSubgroup (Cycle X ℤ) where
  carrier := {c | ∀ x ∈ Function.support ⇑c, dimClosure x = d}
  zero_mem' := by intro x hx; simp at hx
  add_mem' {a b} ha hb := by
    intro x hx
    have : x ∈ Function.support ⇑a ∪ Function.support ⇑b := by
      have h := Function.support_add (f := ⇑a) (g := ⇑b)
      exact h (by simpa using hx)
    rcases this with h | h
    · exact ha x h
    · exact hb x h
  neg_mem' {a} ha := by intro x hx; exact ha x (by simpa using hx)

lemma mem_cyclesOfCodim_iff {X : Scheme.{u}} {p : ℕ∞} {c : Cycle X ℤ} :
    c ∈ cyclesOfCodim X p ↔ ∀ x ∈ Function.support ⇑c, codim x = p :=
  Iff.rfl

lemma mem_cyclesOfDim_iff {X : Scheme.{u}} {d : ℕ∞} {c : Cycle X ℤ} :
    c ∈ cyclesOfDim X d ↔ ∀ x ∈ Function.support ⇑c, dimClosure x = d :=
  Iff.rfl

/-- The prime cycle at a codimension-`p` point lies in `Z^p(X)`.-/
lemma single_mem_cyclesOfCodim {X : Scheme.{u}} {x : X} {p : ℕ∞}
    (h : codim x = p) (n : ℤ) :
    Cycle.single x n ∈ cyclesOfCodim X p := by
  intro y hy
  obtain rfl : y = x := Set.eq_of_mem_singleton (Cycle.support_single_subset x n hy)
  exact h

/-- The prime cycle at a point of closure-dimension `d` lies in `Z_d(X)`.-/
lemma single_mem_cyclesOfDim {X : Scheme.{u}} {x : X} {d : ℕ∞}
    (h : dimClosure x = d) (n : ℤ) :
    Cycle.single x n ∈ cyclesOfDim X d := by
  intro y hy
  obtain rfl : y = x := Set.eq_of_mem_singleton (Cycle.support_single_subset x n hy)
  exact h

/-!
## Finiteness of supports on quasi-compact schemes
-/

namespace Cycle

/-- On a quasi-compact scheme, every cycle has finite support.-/
lemma finite_support {X : Scheme.{u}} [CompactSpace X] [Zero R] (c : Cycle X R) :
    (Function.support ⇑c).Finite := by
  have h := c.locallyFiniteSupport.finite_inter_support_of_isCompact
    (W := Set.univ) CompactSpace.isCompact_univ
  simpa using h

/-- On a Noetherian scheme, every cycle has finite support.-/
lemma finite_support_of_isNoetherian {X : Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] [Zero R] (c : Cycle X R) :
    (Function.support ⇑c).Finite :=
  finite_support c

/-!
## Cycles on a quasi-compact scheme are finitely supported functions
-/

section Finsupp

variable {X : Scheme.{u}} [CompactSpace X]

/-- On a quasi-compact (e.g. Noetherian) scheme, cycles are exactly the
finitely supported `ℤ`-valued functions on points: the additive equivalence
`Cycle X ℤ ≃+ (X →₀ ℤ)`.-/
def toFinsupp : Scheme.Cycle X ℤ ≃+ (X →₀ ℤ) where
  toFun c := Finsupp.onFinset (finite_support c).toFinset ⇑c
    (fun _ ha => (finite_support c).mem_toFinset.mpr ha)
  invFun F :=
    { toFun := ⇑F
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ =>
        ⟨Set.univ, Filter.univ_mem,
          (F.fun_support_eq.symm ▸ F.support.finite_toSet).inter_of_right _⟩ }
  left_inv c := by
    ext x
    simp
  right_inv F := by
    ext x
    simp
  map_add' c₁ c₂ := by
    ext x
    simp [Finsupp.onFinset_apply]

@[simp]
lemma toFinsupp_apply (c : Scheme.Cycle X ℤ) (x : X) :
    toFinsupp c x = c x :=
  rfl

@[simp]
lemma toFinsupp_symm_apply (F : X →₀ ℤ) (x : X) :
    toFinsupp.symm F x = F x :=
  rfl

@[simp]
lemma toFinsupp_single (x : X) (n : ℤ) :
    toFinsupp (single x n) = Finsupp.single x n := by
  ext y
  rw [toFinsupp_apply, single_apply, Finsupp.single_apply]
  by_cases h : y = x
  · subst h
    rw [ite_eq_left rfl]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

end Finsupp

end Cycle

/-!
## The free abelian group theorem for `Z^p(X)`
-/

section Graded

variable {X : Scheme.{u}}

private lemma finite_support_subtype [CompactSpace X] (c : Scheme.Cycle X ℤ)
    (p : ℕ∞) :
    (Function.support fun x : {x : X // codim x = p} => c x.val).Finite := by
  refine Set.Finite.subset
    ((Cycle.finite_support c).preimage Subtype.val_injective.injOn) ?_
  intro y hy
  exact hy

/-- Implementation detail of `cyclesOfCodimEquiv`: extend a finitely
supported function on the codimension-`p` points by zero.-/
private def extendSubtype (p : ℕ∞) (F : {x : X // codim x = p} →₀ ℤ) :
    Scheme.Cycle X ℤ where
  toFun x := if h : codim x = p then F ⟨x, h⟩ else 0
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem, by
      apply Set.Finite.inter_of_right
      apply Set.Finite.subset ((F.support.finite_toSet).image Subtype.val)
      intro x hx
      simp only [Function.mem_support] at hx
      by_cases h : codim x = p
      · refine ⟨⟨x, h⟩, ?_, rfl⟩
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        rw [dite_eq_left h] at hx
        exact hx
      · exact absurd (dite_eq_right h) hx⟩

private lemma extendSubtype_apply (p : ℕ∞) (F : {x : X // codim x = p} →₀ ℤ)
    (x : X) :
    extendSubtype p F x = if h : codim x = p then F ⟨x, h⟩ else 0 :=
  rfl

private lemma extendSubtype_mem (p : ℕ∞) (F : {x : X // codim x = p} →₀ ℤ) :
    extendSubtype p F ∈ cyclesOfCodim X p := by
  intro x hx
  by_cases h : codim x = p
  · exact h
  · refine absurd ?_ hx
    show extendSubtype p F x = 0
    rw [extendSubtype_apply, dite_eq_right h]

/-- On a quasi-compact scheme, `Z^p(X)` is (additively) the group of
finitely supported `ℤ`-valued functions on the codimension-`p` points.-/
def cyclesOfCodimEquiv (X : Scheme.{u}) [CompactSpace X] (p : ℕ∞) :
    cyclesOfCodim X p ≃+ ({x : X // codim x = p} →₀ ℤ) where
  toFun c := Finsupp.onFinset (finite_support_subtype c.1 p).toFinset
    (fun x => c.1 x.1)
    (fun _ ha => (finite_support_subtype c.1 p).mem_toFinset.mpr ha)
  invFun F := ⟨extendSubtype p F, extendSubtype_mem p F⟩
  left_inv c := by
    apply Subtype.ext
    ext x
    rw [extendSubtype_apply]
    split_ifs with h
    · rfl
    · by_contra hne
      exact h (c.2 x (Function.mem_support.mpr fun h0 => hne h0.symm))
  right_inv F := by
    ext a
    rw [Finsupp.onFinset_apply, extendSubtype_apply, dite_eq_left a.2]
  map_add' c₁ c₂ := by
    ext a
    simp [Finsupp.onFinset_apply]

/-- **The free abelian group theorem**: on a quasi-compact (e.g. Noetherian)
scheme, the group `Z^p(X)` of codimension-`p` cycles is the free abelian
group on the codimension-`p` points of `X` — equivalently (schemes being
sober, `irreducibleSetEquivPoints`), on the integral closed subschemes of
codimension `p`.-/
def cyclesOfCodimEquivFreeAbelian (X : Scheme.{u}) [CompactSpace X] (p : ℕ∞) :
    cyclesOfCodim X p ≃+ FreeAbelianGroup {x : X // codim x = p} :=
  (cyclesOfCodimEquiv X p).trans (FreeAbelianGroup.equivFinsupp _).symm

end Graded

end Scheme

/-!
## Vendored upstream declarations

The next two declarations are vendored (verbatim up to namespace) from
Raphael Douglas Giles's `Mathlib.AlgebraicGeometry.ResidueField` additions in
Mathlib ≥ 4.32.  DELETE both after the ≥ 4.32 bump and use the upstream
`AlgebraicGeometry.Scheme.Hom.residueDegree` instead.
-/

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- Degree of `f` at a point `x`: the degree of the residue field extension
`κ(x)/κ(f x)`. Junk value `0` when this degree is infinite.

(Vendored from Mathlib ≥ 4.32, author Raphael Douglas Giles; DELETE at the
bump.)-/
def residueDegree (f : X ⟶ Y) (x : X) : ℕ :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

@[simp]
lemma residueDegree_id (x : X) : residueDegree (𝟙 X) x = 1 := by
  dsimp [residueDegree]
  rw [AlgebraicGeometry.Scheme.residueFieldMap_id]
  exact CommSemiring.finrank_self _

end Scheme.Hom

namespace Scheme.Cycle

variable {X Y : Scheme.{u}}

/-!
## Pushforward
-/

/-- The **pushforward** of a cycle along a quasi-compact morphism, weighting
each point by the degree of the residue field extension: at `z : Y`,

`(map f c) z = ∑ᶠ x ∈ f ⁻¹' {z}, c x * [κ(x) : κ(z)]`.

This is the constant-weight specialization of Mathlib's (≥ 4.32) weighted
pushforward of algebraic cycles; it is the geometrically correct pushforward
for closed immersions and, more generally, finite morphisms. (Fulton's
dimension test for killing positive-dimensional fibers enters only with the
fully weighted map — a later stage.)-/
def map (f : X ⟶ Y) [QuasiCompact f] (c : Scheme.Cycle X ℤ) : Scheme.Cycle Y ℤ :=
  Function.locallyFinsupp.map f (fun x => (Scheme.Hom.residueDegree f x : ℤ))
    f.isSpectralMap c

@[simp]
lemma map_apply (f : X ⟶ Y) [QuasiCompact f] (c : Scheme.Cycle X ℤ) (z : Y) :
    map f c z = ∑ᶠ x ∈ f ⁻¹' {z}, c x * (Scheme.Hom.residueDegree f x : ℤ) :=
  rfl

@[simp]
lemma map_id (c : Scheme.Cycle X ℤ) : map (𝟙 X) c = c := by
  apply Function.locallyFinsupp.map_id
  intro z
  simp

/-- The pushforward is additive. (The content is that the two supports meet
each fiber in a finite set: the fiber sits inside the preimage of a compact
open neighbourhood, which is compact because the morphism is spectral.)-/
lemma map_add (f : X ⟶ Y) [QuasiCompact f] (c₁ c₂ : Scheme.Cycle X ℤ) :
    map f (c₁ + c₂) = map f c₁ + map f c₂ := by
  ext z
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (Set.mem_univ z) isOpen_univ
  have key : ∀ c : Scheme.Cycle X ℤ,
      ((f ⁻¹' {z} : Set X) ∩
        Function.support fun x => c x * (Scheme.Hom.residueDegree f x : ℤ)).Finite := by
    intro c
    apply Set.Finite.subset
      (c.locallyFiniteSupport.finite_inter_support_of_isCompact
        (f.isSpectralMap.2 hU.1.1 hU.1.2))
    rintro y ⟨hy1, hy2⟩
    refine ⟨?_, ?_⟩
    · show f y ∈ U
      have hyz : f y = z := hy1
      rw [hyz]
      exact hU.2.1
    · exact fun h0 => hy2 (mul_eq_zero_of_left h0 _)
  simp only [map_apply, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
  exact finsum_mem_add_distrib' (key c₁) (key c₂)

end Scheme.Cycle

/-!
## Closed immersions: the pushforward is coefficient-preserving
-/

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The residue field map of a closed immersion is surjective.-/
lemma residueFieldMap_surjective (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Function.Surjective (f.residueFieldMap x) := by
  intro y
  obtain ⟨a, ha⟩ := X.residue_surjective x y
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h2 := congrArg CommRingCat.Hom.hom
    (AlgebraicGeometry.Scheme.residue_residueFieldMap (f := f) (x := x))
  rw [CommRingCat.hom_comp, CommRingCat.hom_comp] at h2
  have h3 := RingHom.congr_fun h2 b
  simp only [RingHom.coe_comp, Function.comp_apply] at h3
  rw [← ha, ← hb]
  exact h3

/-- The residue field map of a closed immersion is bijective: it is a
surjective homomorphism of fields.-/
lemma residueFieldMap_bijective (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    Function.Bijective (f.residueFieldMap x) :=
  ⟨(f.residueFieldMap x).hom.injective, residueFieldMap_surjective f x⟩

/-- Along a closed immersion, the residue degree is `1`: the residue field
extension is an isomorphism.-/
@[simp]
lemma residueDegree_eq_one_of_isClosedImmersion (f : X ⟶ Y) [IsClosedImmersion f]
    (x : X) :
    residueDegree f x = 1 := by
  letI := (f.residueFieldMap x).hom.toAlgebra
  have e : Y.residueField (f x) ≃ₗ[Y.residueField (f x)] X.residueField x :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) (residueFieldMap_bijective f x)
  show Module.finrank (Y.residueField (f x)) (X.residueField x) = 1
  rw [← e.finrank_eq]
  exact CommSemiring.finrank_self _

end Scheme.Hom

namespace Scheme

variable {X Y : Scheme.{u}}

/-- A closed immersion preserves the dimension of point-closures
(`Order.height` in the specialization order): the specialization order of `X`
embeds into that of `Y` as a downward-closed suborder.-/
lemma dimClosure_map (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    dimClosure (f x) = dimClosure x := by
  have hle : ∀ a b : X, f a ≤ f b ↔ a ≤ b := by
    intro a b
    rw [AlgebraicGeometry.Scheme.le_iff_specializes,
      AlgebraicGeometry.Scheme.le_iff_specializes]
    exact f.isClosedEmbedding.toIsEmbedding.toIsInducing.specializes_iff
  refine (Order.height_eq_of_strictMono f ?_ ?_ x).symm
  · intro a b hab
    rw [lt_iff_le_not_ge] at hab ⊢
    exact ⟨(hle a b).mpr hab.1, fun h => hab.2 ((hle b a).mp h)⟩
  · intro a b hb
    have hba : b ∈ closure ({f a} : Set Y) :=
      specializes_iff_mem_closure.mp
        (AlgebraicGeometry.Scheme.le_iff_specializes.mp hb.le)
    rw [← Set.image_singleton, f.isClosedEmbedding.closure_image_eq] at hba
    obtain ⟨a', ha', rfl⟩ := hba
    refine ⟨a', ?_, rfl⟩
    rw [lt_iff_le_not_ge]
    refine ⟨AlgebraicGeometry.Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr ha'), fun h => ?_⟩
    exact hb.not_ge ((hle a a').mpr h)

/-- The degree `[κ(x) : k]` of the residue field of a point of a scheme over
a field `k` (with the `k`-algebra structure on `κ(x)` induced by the
structure morphism to `Spec k`). Junk value `0` when the extension is
infinite.-/
def residueFieldDegreeOver (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ Spec (CommRingCat.of k)).appTop ≫ X.Γevaluation x).hom.toAlgebra
  Module.finrank k (X.residueField x)

end Scheme

namespace Scheme.Cycle

variable {X Y : Scheme.{u}}

/-- Pushforward along a closed immersion is coefficient-preserving on prime
cycles: `f_*(n · [x]) = n · [f x]`.-/
@[simp]
lemma map_single (f : X ⟶ Y) [IsClosedImmersion f] (x : X) (n : ℤ) :
    map f (single x n) = single (f x) n := by
  ext z
  rw [map_apply]
  by_cases hz : z = f x
  · subst hz
    have hfib : (f ⁻¹' {f x} : Set X) = {x} := by
      apply Set.eq_singleton_iff_unique_mem.mpr
      exact ⟨rfl, fun y hy => f.isClosedEmbedding.injective hy⟩
    rw [hfib, finsum_mem_singleton]
    simp
  · refine Eq.trans (finsum_mem_of_eqOn_zero fun y hy => ?_) ?_
    · have hyz : f y = z := hy
      have hyx : y ≠ x := by
        rintro rfl
        exact hz hyz.symm
      show single x n y * (Scheme.Hom.residueDegree f y : ℤ) = 0
      rw [single_apply, ite_eq_right hyx, zero_mul]
    · rw [single_apply, ite_eq_right hz]

/-- The pushforward along a closed immersion respects the grading by
dimension of point-closures. (No such statement holds for the codimension
grading without catenary hypotheses.)-/
lemma map_mem_cyclesOfDim (f : X ⟶ Y) [IsClosedImmersion f] {d : ℕ∞}
    {c : Scheme.Cycle X ℤ} (hc : c ∈ cyclesOfDim X d) :
    map f c ∈ cyclesOfDim Y d := by
  intro y hy
  have hsub : Function.support ⇑(map f c) ⊆ ⇑f '' Function.support ⇑c :=
    Function.locallyFinsupp.support_map_subset_of_forall_mem f.isSpectralMap
      (fun x => (Scheme.Hom.residueDegree f x : ℤ)) c (Function.support ⇑c)
      (⇑f '' Function.support ⇑c) subset_rfl
      (fun x hx _ => Set.mem_image_of_mem _ hx)
  obtain ⟨x, hx, rfl⟩ := hsub hy
  rw [dimClosure_map f x]
  exact hc x hx

/-!
## Degree of cycles
-/

/-- The degree of a cycle with respect to an arbitrary weight `w` on points,
`deg_w(c) = ∑_x c(x) · w(x)`, as an additive homomorphism (the scheme is
assumed quasi-compact so that the sum is finite).-/
def weightedDegree {X : Scheme.{u}} [CompactSpace X] (w : X → ℤ) :
    Scheme.Cycle X ℤ →+ ℤ where
  toFun c := (toFinsupp c).sum fun x n => n * w x
  map_zero' := by simp
  map_add' c₁ c₂ := by
    rw [_root_.map_add]
    exact Finsupp.sum_add_index' (fun a => zero_mul _) fun a b₁ b₂ => add_mul _ _ _

@[simp]
lemma weightedDegree_single {X : Scheme.{u}} [CompactSpace X] (w : X → ℤ)
    (x : X) (n : ℤ) :
    weightedDegree w (single x n) = n * w x := by
  show (toFinsupp (single x n)).sum (fun x n => n * w x) = n * w x
  rw [toFinsupp_single]
  exact Finsupp.sum_single_index (zero_mul _)

/-- The **degree** of a cycle on a quasi-compact scheme over a field `k`:
`deg(c) = ∑_x c(x) · [κ(x) : k]`, as an additive homomorphism. Points with
infinite residue degree weigh `0` (`Module.finrank`'s junk value);
finiteness/positivity of the weights at closed points of finite-type schemes
is a deliberately deferred theorem.-/
def degree (k : Type u) [Field k] {X : Scheme.{u}} [CompactSpace X]
    [X.Over (Spec (CommRingCat.of k))] : Scheme.Cycle X ℤ →+ ℤ :=
  weightedDegree fun x => (residueFieldDegreeOver k x : ℤ)

@[simp]
lemma degree_single (k : Type u) [Field k] {X : Scheme.{u}} [CompactSpace X]
    [X.Over (Spec (CommRingCat.of k))] (x : X) (n : ℤ) :
    degree k (single x n) = n * (residueFieldDegreeOver k x : ℤ) :=
  weightedDegree_single _ x n

end Scheme.Cycle

end HodgePilot
