module

public import Tengoku.Seed.Logic.Equiv.Fintype
public import Tengoku.Seed.Data.Sym.Card
public import Tengoku.Seed.Data.Fintype.Powerset
public import Tengoku.Seed.Combinatorics.SimpleGraph.Basic
public import Tengoku.Seed.GroupTheory.Perm.Basic
public import Tengoku.Seed.SetTheory.Cardinal.Finite
public import Tengoku.Seed.Data.Rat.Cast.Order
public import Tengoku.Seed.Tactic.NormNum.Pow

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Invariance under relabelling the index type

The symmetric group `Equiv.Perm X` acts on everything built over `X`. This
module collects what that action forces, for two kinds of object, with no
commitment to what `X` is for.

## Functions `X → Y`

`permOrbit f` is the set of relabellings of `f`, and `ClosedUnderPermutation F`
says `F` is a union of orbits — the condition variously called *anonymity*,
*exchangeability*, or *order-blindness* depending on the field.

`spectrum f : Sym Y |X|` is the multiset of values `f` takes, and it is the
**complete invariant** of the orbit: `spectrum_eq_iff_mem_permOrbit`. So a
property of functions that cannot see which point is which factors through
`spectrum`, and `closedUnderPermutationEquivSet` turns that into a bijection —
**relabelling-invariant families of functions are exactly families of
multisets**, with nothing lost either way. The counts follow from Mathlib's
tally of `Sym`.

## Relations on `X`

`forall_rel_of_permInvariant`: a relation invariant under every permutation is
constant off the diagonal, and `rel_diag_iff_of_permInvariant` says it is
constant on the diagonal too — independently. Neither symmetry nor
irreflexivity is used, so `exists_perm_rel_not_iff` reaches relations no graph
can be instantiated at. The `SimpleGraph` corollaries are the form a reader
looking for graph automorphisms would search for: such a graph is complete or
empty.

## Consumers

`AISafetyAtlas.Learning.Sharp` uses all of it — closure under permutation is
exactly the condition under which No Free Lunch holds, the counts say almost no
prior meets it, and the relation results say no structured search space does.
That is one application. Nothing here mentions search, learning, or objectives.

Two more places do this kind of reasoning and do not yet route through here, so
the relationship is worth stating rather than assuming.
`AISafetyAtlas.Compositional.Hyperproperties.toBatch_perm` proves that
reordering a tuple does not change the traces it mentions; that is the image of
`spectrum` under `Multiset.toFinset`, so it follows from `spectrum` being
orbit-invariant, but **only in one direction** — `toBatch` is a `Finset` and
forgets multiplicity, so it cannot be strengthened to the `iff` that
`spectrum_eq_iff_mem_permOrbit` gives. And `AISafetyAtlas.Upstream` relabels
voters and alternatives by hand, which is anonymity and neutrality; that module
is vendored and is deliberately left alone.
-/

namespace AISafetyAtlas.Combinatorics

open Function

variable {X : Type*} {Y : Type*}

/-! ## Orbits of functions under relabelling of the domain -/

/--
**Schumacher–Vose–Whitley's set form.** A set of objectives closed under
permutation of the domain has a permutation-invariant indicator weight, so NFL
holds over it. `ClosedUnderPermutation` is their condition verbatim.-/
@[expose] public def ClosedUnderPermutation (F : Set (X → Y)) : Prop :=
  ∀ (π : Equiv.Perm X) (f : X → Y), f ∈ F → f ∘ π ∈ F

/--
**The permutation orbit of an objective**: everything obtainable from `f` by
relabelling the search domain. That this coincides with Igel–Toussaint's *basis
class* is their Lemma 1(2), proved as `basisClass_histogram_eq_permOrbit` — not
assumed here.-/
@[expose] public def permOrbit (f : X → Y) : Set (X → Y) :=
  {g | ∃ π : Equiv.Perm X, g = f ∘ (π : X → X)}

/--
**Igel–Toussaint's histogram.** How many points of the domain each cost value
receives. Their `h_f(y) = |f⁻¹(y)|`.-/
@[expose] public noncomputable def histogram [Fintype X] [DecidableEq Y]
    (f : X → Y) : Y → ℕ :=
  fun y => (Finset.univ.filter fun x : X => f x = y).card

/-- Their **basis class** `B_h`: all objectives with a given histogram.-/
@[expose] public noncomputable def basisClass [Fintype X] [DecidableEq Y]
    (h : Y → ℕ) : Set (X → Y) :=
  {f | histogram f = h}

/--
**Igel–Toussaint's Lemma 1(2)**: the basis class of `f`'s histogram *is* `f`'s
permutation orbit.

This is the half of their Lemma 1 with content — histograms and orbits are
defined independently, and the lemma says they cut the objectives the same way.
The atlas states `PermInvariant` in terms of orbits and the source states
Theorem 5's hypothesis in terms of histograms, so without this the two are not
known to be the same condition.

Both inclusions are counting. A relabelling permutes the fibres of `f` without
resizing them, so an orbit member has `f`'s histogram; conversely two objectives
with the same histogram have equinumerous fibres, and any family of bijections
between corresponding fibres assembles into a permutation carrying one to the
other.-/
public theorem basisClass_histogram_eq_permOrbit [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) : basisClass (histogram f) = permOrbit f := by
  classical
  apply Set.eq_of_subset_of_subset
  · rintro g (hg : histogram g = histogram f)
    -- equal histograms give a bijection of each fibre, hence a permutation
    have hcard : ∀ y : Y, (Finset.univ.filter fun x : X => g x = y).card
        = (Finset.univ.filter fun x : X => f x = y).card := fun y => congrFun hg y
    have hbij : ∀ y : Y, Nonempty ({x : X // g x = y} ≃ {x : X // f x = y}) := by
      intro y
      refine ⟨Fintype.equivOfCardEq ?_⟩
      simpa [Fintype.card_subtype] using hcard y
    have e : ∀ y : Y, ({x : X // g x = y} ≃ {x : X // f x = y}) :=
      fun y => Classical.choice (hbij y)
    -- `Equiv.ofFiberEquiv` assembles the fibrewise bijections into a permutation
    refine ⟨Equiv.ofFiberEquiv e, funext fun x => ?_⟩
    exact (Equiv.ofFiberEquiv_map e x).symm

  · rintro g ⟨π, rfl⟩
    show histogram (f ∘ (π : X → X)) = histogram f
    funext y
    refine Finset.card_bij (fun x _ => π x) (fun x hx => ?_) (fun a _ b _ h => π.injective h)
      (fun b hb => ⟨π.symm b, ?_, by simp⟩)
    · simpa [histogram] using hx
    · simpa [histogram] using hb

/--
**The multiset of values a function takes on a finite domain** — its image with
multiplicity, as an element of `Sym Y |X|`.

This is the complete invariant of a function under relabelling its domain:
`spectrum_eq_iff_mem_permOrbit` says two functions have the same spectrum
exactly when one is the other precomposed with a permutation. So anything
definable on `X → Y` that cannot see which point is which — an anonymous or
exchangeable property — factors through `spectrum`, and questions about such
properties become questions about subsets of `Sym Y |X|`, where Mathlib's count
of symmetric powers applies.

Here it is Igel and Toussaint's histogram of cost values, but nothing in the
definition is about search.-/
@[expose] public noncomputable def spectrum [Fintype X] (f : X → Y) :
    Sym Y (Fintype.card X) :=
  ⟨Multiset.map f Finset.univ.val, by simp [Finset.card_univ]⟩

/-- `spectrum` and `histogram` carry the same information: the multiset's
multiplicity at `y` is the number of domain points `f` sends to `y`.-/
public theorem spectrum_eq_iff_histogram_eq [Fintype X] [DecidableEq Y]
    (f g : X → Y) : spectrum f = spectrum g ↔ histogram f = histogram g := by
  -- `Sym.coe_inj` has to fire before `spectrum` unfolds: once the goal is an
  -- equality of anonymous constructors the `Sym` type is gone and it cannot.
  rw [← Sym.coe_inj]
  simp only [spectrum, Sym.coe_mk, Multiset.ext, Multiset.count_map, histogram,
    funext_iff, Finset.card, Finset.filter, eq_comm]

/-- **Lemma 1, in the form the count needs.** Two objectives have the same
spectrum exactly when one is a relabelling of the other.-/
public theorem spectrum_eq_iff_mem_permOrbit [Fintype X] [DecidableEq X]
    [DecidableEq Y] (f g : X → Y) :
    spectrum f = spectrum g ↔ g ∈ permOrbit f := by
  rw [spectrum_eq_iff_histogram_eq, ← basisClass_histogram_eq_permOrbit f]
  simp [basisClass, eq_comm]

/-- Every multiset of `|X|` cost values is the spectrum of some objective, so
the orbits are exactly the elements of `Sym Y |X|` and none is missed.-/
public theorem surjective_spectrum [Fintype X] :
    Function.Surjective (spectrum (X := X) (Y := Y)) := by
  classical
  intro s
  have hlen : s.val.toList.length = Fintype.card X := by
    rw [Multiset.length_toList, s.2]
  let e : X ≃ Fin s.val.toList.length :=
    (Fintype.equivFin X).trans (finCongr hlen.symm)
  refine ⟨fun x => s.val.toList.get (e x), Subtype.ext ?_⟩
  show Multiset.map (fun x => s.val.toList.get (e x)) Finset.univ.val = s.val
  rw [show (fun x => s.val.toList.get (e x)) = s.val.toList.get ∘ e from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv e, Fin.univ_val_map,
    List.ofFn_get]
  exact Multiset.coe_toList s.val

/-- A permutation-closed set is recovered from its set of spectra: membership
depends on nothing but the multiset of cost values.-/
public theorem preimage_image_spectrum [Fintype X] [DecidableEq X] [DecidableEq Y]
    {F : Set (X → Y)} (hF : ClosedUnderPermutation F) :
    spectrum ⁻¹' (spectrum '' F) = F := by
  apply Set.Subset.antisymm
  · rintro g ⟨f, hf, hfg⟩
    obtain ⟨π, rfl⟩ := (spectrum_eq_iff_mem_permOrbit f g).1 hfg
    exact hF π f hf
  · exact fun f hf => ⟨f, hf, rfl⟩

/--
**Relabelling-invariant families of functions are exactly families of
multisets.** The subsets of `X → Y` closed under precomposition by permutations
of a finite `X` biject with the subsets of `Sym Y |X|`, by taking each family to
its set of spectra.

The orbit space itself is `Sym Y |X|` — `surjective_spectrum` and
`spectrum_eq_iff_mem_permOrbit` are what identify it. This equiv is the
statement one level up, about invariant *subsets*, and it is the general form of
what "depends on the values but
not on which point carries them" means: an anonymous, exchangeable, or
order-blind family of functions *is* a family of multisets, with no information
lost either way.

Here it turns Igel–Toussaint's count into Mathlib's tally of `Sym`, but the
bijection is not about search or about counting.-/
@[expose] public noncomputable def closedUnderPermutationEquivSet [Fintype X]
    [DecidableEq X] [DecidableEq Y] :
    {F : Set (X → Y) // ClosedUnderPermutation F} ≃ Set (Sym Y (Fintype.card X)) where
  toFun F := spectrum '' F.1
  invFun S := ⟨spectrum ⁻¹' S, by
    rintro π f hf
    have : spectrum (f ∘ (π : X → X)) = spectrum f :=
      ((spectrum_eq_iff_mem_permOrbit f (f ∘ (π : X → X))).2 ⟨π, rfl⟩).symm
    simpa [Set.mem_preimage, this] using hf⟩
  left_inv := by
    rintro ⟨F, hF⟩
    exact Subtype.ext (preimage_image_spectrum hF)
  right_inv S := Set.image_preimage_eq S surjective_spectrum

/--
The bijection above, restricted to the non-empty sets on both sides.-/
@[expose] public noncomputable def closedUnderPermutationNonemptyEquivSet [Fintype X]
    [DecidableEq X] [DecidableEq Y] :
    {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty}
      ≃ {S : Set (Sym Y (Fintype.card X)) // S.Nonempty} where
  toFun F := ⟨spectrum '' F.1, F.2.2.image _⟩
  invFun S :=
    ⟨spectrum ⁻¹' S.1,
      (closedUnderPermutationEquivSet.symm S.1).2,
      by
        obtain ⟨t, ht⟩ := S.2
        obtain ⟨f, hf⟩ := surjective_spectrum (X := X) (Y := Y) t
        exact ⟨f, by simpa [Set.mem_preimage, hf] using ht⟩⟩
  left_inv := by
    rintro ⟨F, hF, -⟩
    exact Subtype.ext (preimage_image_spectrum hF)
  right_inv S := Subtype.ext (Set.image_preimage_eq S.1 surjective_spectrum)

/-! ## Relations invariant under relabelling -/

end AISafetyAtlas.Combinatorics
