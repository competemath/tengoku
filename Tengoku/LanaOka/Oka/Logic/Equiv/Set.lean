/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Logic.Equiv.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fibre of a composite, as a sigma of the fibres of the first map

Material for `Mathlib/Logic/Equiv/Set.lean`; see `README.md` on the mirror tree. There is no
complex-analytic content here.

`Set.preimageCompEquivSigma` splits the fibre of `g ∘ f` over a point of the target into the
fibres of `f` over the points of the fibre of `g`, **as an equivalence and not as a count**: it
assumes nothing at all — no finiteness, no decidability, no hypothesis relating the two maps.

## Why the destination is this file and not the one this statement was written in

It was declared in `Oka/SetTheory/Cardinal/Finite.lean`, beside
`Nat.card_preimage_singleton_comp`, which is its only consumer in this repository. **That file
claims `Mathlib/SetTheory/Cardinal/Finite.lean` as its destination and this statement could not
go there**: it mentions no `Nat.card` and no `Cardinal`. `README.md`'s mirror-tree section asks
that a mirror file's declarations all be placeable where its docstring says, on the ground that a
file mixing destinations tells a Mathlib reviewer something untrue.

**`Mathlib/Logic/Equiv/Set.lean` is where the nearest Mathlib statement lives**, and it is
`Equiv.sigmaPreimageEquiv` — `(Σ b, f ⁻¹' {b}) ≃ α`, the total space split into the preimages of
points, in the same preimage-of-a-singleton spelling as the statement below. Mathlib's own
`Equiv.sigmaFiberEquiv`, which is the subtype spelling of the same fact and which
`Oka/SetTheory/Cardinal/Finite.lean` used to name as the neighbour, carries a comment pointing at
`Equiv.sigmaPreimageEquiv` for exactly this reason.

**Both directions of the import were measured with `scripts/import_cost.py`, at the Mathlib
revision `lakefile.toml` pins, rather than guessed.** `Mathlib/SetTheory/Cardinal/Finite.lean`
already has `Mathlib/Logic/Equiv/Set.lean` in its transitive closure, so a consumer importing
this file pays **0**; and
`Mathlib/Logic/Equiv/Set.lean` needs nothing added to host the statement below, so the
destination claim costs **0** in that direction too. Neither figure holds for the other Mathlib
file this statement is near: hosting it in `Mathlib/Logic/Equiv/Sum.lean`, where
`Equiv.sigmaFiberEquiv` is, would cost that file **6** modules for `Mathlib.Data.Set.Operations`
and **46** for `Mathlib.Data.Set.Basic`.

**What that file cannot reach is `Set.preimage` and the coercion that reads a `Set` as a type,
and not `Set` itself.** This paragraph used to give the reason as *"it has no `Set` theory at
all"*, and
`python3 scripts/import_cost.py --target Mathlib.Logic.Equiv.Sum Mathlib.Data.Set.Defs` refutes
that in one line — *1 already in that closure -> cost 0*. `Mathlib/Data/Set/Defs.lean` declares
`Set`, `setOf`, membership, `Set.univ` and `Set.image`, and is inside that closure of 90 already;
under `import Mathlib.Logic.Equiv.Sum` alone `#check @Set.image`, `#check @setOf` and
`#check @Set.univ` all elaborate, while `#check @Set.preimage` reports an unknown constant. So
part of what the **6** buys is `Set.preimage` together with its `f ⁻¹' s` notation, which
`Mathlib/Data/Set/Operations.lean` declares — and lacking the notation
`Set.preimageCompEquivSigma` does not fail to typecheck, it fails to lex, since the apostrophe
opens a character literal.

**That is the failure a reader meets first and it is not the only one behind it.** Running
`python3 scripts/import_cost.py --target Mathlib.Logic.Equiv.Sum Mathlib.Data.Set.Operations`
prints `Mathlib.Data.Set.CoeSort` on that same list, and, at the Mathlib revision `lakefile.toml`
pins, `Mathlib/Data/Set/CoeSort.lean:40` is `instance : CoeSort (Set α) (Type u) := ⟨Elem⟩` — the
coercion that reads a `Set` as the subtype of its members. `Set.preimageCompEquivSigma` is an
equivalence between two sets read that way, so it needs that instance as much as it needs the
preimage, and **the two obstructions have separate causes, which an added import shows in one
direction and no added import could show in the other**. With `import Mathlib.Data.Set.CoeSort`
beside it the coercion is repaired and the lexing is not: `(f ⁻¹' {z} : Set α)` still reports
*missing end of character literal*. The other direction takes the notation out of the expression
rather than putting an import in — under `import Mathlib.Logic.Equiv.Sum` alone
`example (s t : Set Nat) : Type := s ≃ t`, which carries no `⁻¹'` at all, reports *Application type
mismatch … has type `Set Nat` but is expected to have type `Prop`*, a typecheck failure with the
lexing out of the picture — **and no import stands in for that deletion**, because the notation is
declared at `Mathlib/Data/Set/Operations.lean:127` and that file's ninth line is
`public import Mathlib.Data.Set.CoeSort`, so whatever reaches the notation reaches the instance.
`import Mathlib.Data.Set.Operations` therefore clears both at once; the **6** is the price under
either account, and `Mathlib/Logic/Equiv/Sum.lean` is the wrong host for
`Set.preimageCompEquivSigma` on two counts rather than one. **Both costs were measured and the
reason offered under them was not.**

## Deriving it from Mathlib, and the measurement that was on record was wrong

`Oka/SetTheory/Cardinal/Finite.lean` used to say that getting this statement out of
`Equiv.sigmaFiberEquiv` — by restricting along the inclusion of `(g ∘ f) ⁻¹' {z}` and then
reconciling a subtype of a subtype at each point — **is *longer than writing the equivalence
out*. It is not: at `a8c2f63` the two spellings were the same length**, ten non-blank lines each,
counting the shared two-line signature into both. **That figure is a record of a measurement at
a named commit rather than a count of `Set.preimageCompEquivSigma`'s proof as it stands today**:
an edit to that proof moves the count and leaves this sentence true, as it does any figure pinned
to a commit. Striking the numeral and keeping the comparison would have gone the wrong way — the
comparison is the part that rots, and the figure is what a reader can check it against.

What the derivation does not do is avoid building an equivalence by hand: the
subtype-of-a-subtype step is itself a four-field `Equiv` passed to `Equiv.sigmaCongrRight`. So
citing the Mathlib statement relocates the hand construction rather than removing it, and **that,
rather than a line count, is why the statement is written out below**.
-/

/-- **The fibre of a composite over a point, as a sigma of the fibres of the first map.**

`(g ∘ f) ⁻¹' {z}` is the set of points `x` with `g (f x) = z`; sending such an `x` to the pair
consisting of `f x` — which lies in `g ⁻¹' {z}` — and of `x` itself — which lies in the fibre of
`f` over `f x` — is a bijection, and its inverse forgets the first component.

**Nothing is assumed**: the types are arbitrary, the maps are arbitrary, and no finiteness and no
decidability enters. `Nat.card_preimage_singleton_comp`
(`Oka/SetTheory/Cardinal/Finite.lean`) is the count this makes available once the fibres are
finite, and is this repository's only consumer of it.

**Membership in a singleton preimage is definitionally the equation**, which is what makes
`toFun` and `left_inv` proofs by `rfl`: `x.2` has type `(g ∘ f) x = z` and is accepted where
`f x ∈ g ⁻¹' {z}` is expected. Only `right_inv` has content, and it is a `subst` of the equation
the second component carries followed by proof irrelevance. -/
def Set.preimageCompEquivSigma {α β γ : Type*} (f : α → β) (g : β → γ) (z : γ) :
    ((g ∘ f) ⁻¹' {z} : Set α) ≃ Σ y : (g ⁻¹' {z} : Set β), (f ⁻¹' {(y : β)} : Set α) where
  toFun x := ⟨⟨f x.1, x.2⟩, ⟨x.1, rfl⟩⟩
  invFun p := ⟨p.2.1, show g (f p.2.1) = z by rw [show f p.2.1 = p.1.1 from p.2.2]; exact p.1.2⟩
  left_inv _ := rfl
  right_inv p := by
    obtain ⟨⟨y, hy⟩, ⟨a, ha⟩⟩ := p
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha
    subst ha
    rfl
