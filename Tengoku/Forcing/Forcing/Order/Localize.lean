/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Order.Filter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localization: globalizing a test that is dense only below a condition

Atomic forcing naturally produces sets that are dense only *below* a condition `p`, while
genericity meets visible **global** dense-open tests. `localizeBelow` is the bridge: pad the
downward closure of the local test with everything incompatible with `p`. The result is
globally dense open whenever the original is dense below `p` (`isDenseOpen_localizeBelow`),
and for a filter containing `p` the padding is invisible — meeting the localized test is
*equivalent* to meeting the original (`meets_localizeBelow_iff`), because a filter through
`p` can never contain anything incompatible with `p`.

The truth lemma's visibility hypotheses will name these localized tests explicitly; this
file keeps the bridge in the order layer, independent of names.

## Main definitions

* `Forcing.localizeBelow`: the globalization of a test local to a condition.

## Main results

* `Forcing.isDenseOpen_localizeBelow`: locally dense tests globalize to dense-open ones.
* `Forcing.meets_localizeBelow_iff`: through `p`, meeting the localization is meeting the
  original.
-/

namespace Forcing

open Order

variable {P : Type*} [Preorder P] {D : Set P} {p q : P} {G : PFilter P}

/-- Globalize a test that is only dense below `p`: its downward closure, padded with
everything incompatible with `p`.-/
def localizeBelow (D : Set P) (p : P) : Set P :=
  ↑(lowerClosure D) ∪ {q | Incompatible q p}

/--
@isnad1 id=mem.1h4v.s5.1b835a5ef129 from=translated src=- shape=2600d9e9 vocab=8e17453d
-/
theorem mem_localizeBelow_of_mem (h : q ∈ D) : q ∈ localizeBelow D p :=
  Or.inl (subset_lowerClosure h)

/-- A locally dense test globalizes to a dense-open one: below anything compatible with `p`,
strengthen into the test through a common strengthening; anything incompatible with `p` is
already in the padding.
@isnad1 id=isdenseo.1h3v.s4.b3839770e215 from=translated src=- shape=05107f25 vocab=6fe79234
-/
theorem isDenseOpen_localizeBelow (h : IsDenseBelow D p) :
    IsDenseOpen (localizeBelow D p) := by
  constructor
  · intro r
    by_cases hrp : Compatible r p
    · obtain ⟨s, hsr, hsp⟩ := hrp
      obtain ⟨d, hdD, hds⟩ := h (Set.mem_Iic.2 hsp)
      exact ⟨d, Or.inl (subset_lowerClosure hdD), hds.trans hsr⟩
    · exact ⟨r, Or.inr hrp, le_rfl⟩
  · refine IsLowerSet.union (lowerClosure D).lower fun a b hba ha hb ↦ ?_
    obtain ⟨s, hsb, hsp⟩ := hb
    exact ha ⟨s, hsb.trans hba, hsp⟩

/-- **Through `p`, the padding is invisible**: a filter containing `p` meets the localized
test exactly when it meets the original. The forward direction uses upward closure (through
the lower closure) and directedness (a filter through `p` contains nothing incompatible with
`p`); the reverse is inclusion.
@isnad1 id=iff.1h4v.s5.c543bfc6d9f1 from=translated src=- shape=1013ec78 vocab=315426d3
-/
theorem meets_localizeBelow_iff (hp : p ∈ G) :
    Meets G (localizeBelow D p) ↔ Meets G D := by
  constructor
  · rintro ⟨q, hqG, hq | hq⟩
    · exact meets_lowerClosure.1 ⟨q, hqG, hq⟩
    · obtain ⟨s, hsG, hsq, hsp⟩ := exists_mem_le_le hqG hp
      exact absurd ⟨s, hsq, hsp⟩ hq
  · exact fun h ↦ h.mono fun q hq ↦ mem_localizeBelow_of_mem hq

/-!
### Sanity example

A globally dense-open test localizes to a superset of itself, so localization never loses a
test that was already global.
-/

end Forcing
