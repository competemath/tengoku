/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.LanaOka.Oka.Logic.Equiv.Set

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fibres of a map, counted

Material for `Mathlib/SetTheory/Cardinal/Finite.lean`; see `README.md` on the mirror tree. There
is no complex-analytic content here.

**The title of this file used to be *Bijectivity read off the sizes of the fibres*, which is what
`Function.bijective_iff_forall_card_preimage_eq_one` is about and is no longer what the file is
about.** `Nat.card_preimage_singleton_comp` below is about the fibres of a *composite* and does
not mention bijectivity; the widened title is the repair, and the paragraphs each declaration is
described by are kept apart under their own headings rather than merged.

**The widened title was written when the equivalence under that count was declared here too, and
it is now in `Oka/Logic/Equiv/Set.lean`.** `Set.preimageCompEquivSigma` mentions no `Nat.card`
and no `Cardinal`, so it could not go to this file's stated destination; that file's docstring
gives the measured import costs that decided where it went instead. **What is left names
`Nat.card` in its own statement, which is what the destination above claims**, and that is what
the move was for.

## Bijectivity read off the sizes of the fibres

**Mathlib already reads bijectivity off the fibres one at a time**, as
`Function.bijective_iff_existsUnique` — `Bijective f ↔ ∀ b, ∃! a, f a = b`. What it does not have
is that statement in the `Nat.card` spelling, and it relates `Nat.card` to `Function.Bijective`
only in the *counting* direction: a map between types of equal finite cardinality is bijective as
soon as it is injective (`Nat.bijective_iff_injective_and_card`). So the gap is a translation and
not a theorem, which is why the proof below is a `simp only` between the two spellings followed by
a transposition of `∃!` against `Subsingleton`-and-inhabited.

The `Nat.card` spelling is the one a covering-space argument produces: the number of sheets is
`Nat.card (f ⁻¹' {b})` for each `b` separately, and `1` is the value at which the covering is
trivial.

**The `1` on the right is doing both halves of the work at once.** `Nat.card_eq_one_iff_unique`
splits it as `Subsingleton` and `Nonempty`, and those are exactly injectivity and surjectivity at
the point `b`. Neither type is assumed finite anywhere: `Nat.card` of an infinite type is `0`, so
the hypothesis `Nat.card (f ⁻¹' {b}) = 1` already rules out an infinite fibre by itself, which is
why this is an honest `↔` and not the usual junk-value trap.

## The fibres of a composite

**The equivalence this count rests on is not here.** `Set.preimageCompEquivSigma`
(`Oka/Logic/Equiv/Set.lean`) splits the fibre of `g ∘ f` over a point of the target into the
fibres of `f` over the points of the fibre of `g`, assuming nothing at all, and this file is its
only consumer; **it is filed with its Mathlib neighbour rather than with that consumer**, and the
paragraph arguing that destination against a measured import cost is in its own file rather than
restated here.

`Nat.card_preimage_singleton_comp` is the count that follows: **if every fibre of `f` has `d`
points then the fibre of `g ∘ f` over `z` has `Nat.card (g ⁻¹' {z}) * d`.** The uniform `d` is a
hypothesis and not a conclusion; nothing here says why the fibres of a map would all have the same
size, and in the covering-space setting that is a theorem about a preconnected base rather than
anything a counting lemma can supply.

**The finiteness hypotheses are `Finite` instances and are genuinely needed as instances, not as
`Fintype`s.** `Nat.card_sigma` asks for a `Fintype` on the index type and `Finite` on the fibres;
the `Fintype` is produced by `Fintype.ofFinite` inside the proof, under `classical`, so that no
caller has to carry a decidable equality it does not have. **Whether the hypotheses can be dropped
outright is not settled here** — `Nat.card` of an infinite type is `0`, so both sides degenerate
together in the cases one would check first, but that is an argument and not a proof, and the
statement is used only where the fibres are finite for a structural reason.

## No declaration here is advertised, because this file advertises nothing

There is no `## Main results` heading here and none is added: this file has never had one, so
`Function.bijective_iff_forall_card_preimage_eq_one` and `Nat.card_preimage_singleton_comp` are
unadvertised for that reason. **This heading read *Neither declaration is advertised* while the
file held three declarations**, which is a count of the file written where no count is wanted;
it is rewritten so that nothing here has to be recounted when a declaration is added or, as now,
taken away.
-/

/-- **A map is bijective exactly when every fibre has exactly one point.**

The `Nat.card` spelling of `Function.bijective_iff_existsUnique`, which is what the proof reduces
to: `Nat.card_eq_one_iff_unique` turns `Nat.card (f ⁻¹' {b}) = 1` into `Subsingleton` and
`Nonempty` of the fibre, `Set.subsingleton_coe` and `Set.preimage_singleton_nonempty` read those
as `(f ⁻¹' {b}).Subsingleton` and `b ∈ Set.range f` — injectivity of `f` on that fibre and `b`
being in the range — and what is left is `∃!` against those two.

No finiteness hypothesis is needed on either type, and none is hidden in `Nat.card`: an infinite
fibre has `Nat.card` equal to `0`, not to `1`. -/
theorem Function.bijective_iff_forall_card_preimage_eq_one {α β : Type*} (f : α → β) :
    Function.Bijective f ↔ ∀ b, Nat.card (f ⁻¹' {b}) = 1 := by
  simp only [Function.bijective_iff_existsUnique, Nat.card_eq_one_iff_unique,
    Set.subsingleton_coe, Set.nonempty_coe_sort, Set.preimage_singleton_nonempty]
  refine forall_congr' fun b ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, ha, hu⟩ := h
    exact ⟨fun x hx y hy ↦ (hu x hx).trans (hu y hy).symm, a, ha⟩
  · obtain ⟨hs, a, ha⟩ := h
    exact ⟨a, ha, fun y hy ↦ hs hy ha⟩

/-- **A map all of whose fibres have `d` points multiplies the size of a fibre by `d`.**

`Set.preimageCompEquivSigma` (`Oka/Logic/Equiv/Set.lean`) transports the fibre of `g ∘ f` over
`z` to a sigma type, `Nat.card` of a sigma over a finite index type is the sum of the
cardinalities, and the hypothesis makes every summand `d`.

**The uniform `d` is a hypothesis about every point of `β` and not only about the points of
`g ⁻¹' {z}`**, which is more than the proof uses and is what every caller has: it is the form
`Function.bijective_iff_forall_card_preimage_eq_one` above is stated in, and the form a constant
fibre count over a connected base arrives in.

**The `Fintype` is manufactured inside the proof.** `Nat.card_sigma` asks for one on the index
type; `Fintype.ofFinite` under `classical` supplies it from the `Finite` instance, so the
statement asks for no decidable equality on `β`. -/
theorem Nat.card_preimage_singleton_comp {α β γ : Type*} (f : α → β) (g : β → γ) (z : γ)
    [Finite ((g ⁻¹' {z}) : Set β)] [∀ y : β, Finite ((f ⁻¹' {y}) : Set α)] {d : ℕ}
    (hf : ∀ y : β, Nat.card ((f ⁻¹' {y}) : Set α) = d) :
    Nat.card (((g ∘ f) ⁻¹' {z}) : Set α) = Nat.card ((g ⁻¹' {z}) : Set β) * d := by
  classical
  letI : Fintype ((g ⁻¹' {z}) : Set β) := Fintype.ofFinite _
  rw [Nat.card_congr (Set.preimageCompEquivSigma f g z), Nat.card_sigma]
  simp [hf, Nat.card_eq_fintype_card, mul_comm]
