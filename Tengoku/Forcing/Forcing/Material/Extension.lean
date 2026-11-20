/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Material.Names

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The material extension

The indexed material set of the values of the ground's internal names along a condition
oracle, packaged as a `MaterialCarrier`. The dependency structure is deliberate and minimal:

* `extensionSet` and `extensionCarrier` require **only the small enumeration and subname
  closure** — no order, no top, no filter, no genericity. The construction works for any
  condition oracle `S : Set P`; nothing about it is generic.
* The indexed membership law (`mem_extensionSet_iff`) comes first; the identification with
  the external semantics (`toSet_extensionSet`, equality with `valuationImage`) is derived
  from it; transitivity (`isTransitive_extensionSet`) is proved solely through
  `mem_zval_iff` and subname closure.
* The **canonical-names section is where the library first speaks of `M[G]`**: under
  `[Top P]` and `⊤ ∈ S`, `HasCanonicalNames` gives ground inclusion and generic-code
  membership. Filter corollaries pay via `[OrderTop P]`.

Smallness is the point of the design: the enumeration is kept, so the extension is a genuine
`ZFSet` by construction, rather than an extensional image whose smallness would have to be
recovered later. Dependency note: `code`/`code_mem` play no part in the carrier or its
transitivity — the material valuation carrier needs only a small subname-closed enumeration;
the internal-code side first matters for internal definability, later.

No visibility, no `GenericOver`: composing the extension with genericity is the business of
the Cohen material adapter. And no minimality claim: the eventual `M[G] = M[c_G]` must
compare against an independently characterized extension, never one made true by definition.

## Main definitions

* `Forcing.InternalNamePresentation.extensionSet`: the indexed material set of values.
* `Forcing.InternalNamePresentation.extensionCarrier`: its `MaterialCarrier` packaging.

## Main results

* `Forcing.InternalNamePresentation.mem_extensionSet_iff`: the indexed membership law.
* `Forcing.InternalNamePresentation.toSet_extensionSet`: agreement with the external
  `valuationImage`.
* `Forcing.InternalNamePresentation.isTransitive_extensionSet`: transitivity, from subname
  closure alone.
* `Forcing.InternalNamePresentation.HasCanonicalNames.mem_extensionCarrier_of_mem`,
  `Forcing.InternalNamePresentation.HasCanonicalNames.zval_genName_mem_extensionCarrier`:
  the `M[G]` contract — ground inclusion and generic-code membership.
-/

universe u

namespace Forcing

namespace InternalNamePresentation

open PName

variable {M : MaterialCarrier.{u}} {P : Type u}
variable (N : InternalNamePresentation M P)

/-- The extension set along a condition oracle: the indexed material set of the values of
all internal names. Only the enumeration is used — no order, top, filter, or genericity.-/
def extensionSet (S : Set P) : ZFSet.{u} :=
  ZFSet.mk <| PSet.mk N.Code fun i ↦ (N.decode i).val S

/-- **The indexed membership law**: the members of the extension set are exactly the values
of the decoded names.
@isnad1 id=iff.0h5v.s5.53d43249b839 from=translated src=- shape=b72fa908 vocab=0893b662
-/
theorem mem_extensionSet_iff {S : Set P} {y : ZFSet.{u}} :
    y ∈ N.extensionSet S ↔ ∃ i, y = zval S (N.decode i) := by
  induction y using Quotient.inductionOn with
  | h z =>
    exact ⟨fun ⟨i, h⟩ ↦ ⟨i, ZFSet.sound h⟩, fun ⟨i, h⟩ ↦ ⟨i, ZFSet.exact h⟩⟩

/-- Agreement with the external semantics: as a set of sets, the extension is exactly the
valuation image of the internal name family. The extensional `valuationImage` stays the
external API; this indexed construction is what makes it material.
@isnad1 id=eq.0h4v.s4.f529f53811bd from=translated src=- shape=aedfe9f2 vocab=54c597e7
-/
theorem toSet_extensionSet (S : Set P) :
    (N.extensionSet S).toSet = valuationImage N.names S := by
  ext y
  change y ∈ N.extensionSet S ↔ _
  rw [mem_extensionSet_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact mem_valuationImage (N.decode_mem_names i)
  · rintro ⟨τ, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- **Transitivity, from subname closure alone**: an element of a value is the value of a
subname, and subnames are decoded. Proved through `mem_zval_iff` and `subname_closed`;
nothing else of the presentation participates.
@isnad1 id=istransi.0h4v.s4.6c2237996210 from=translated src=- shape=ed36f83f vocab=1b9cedb5
-/
theorem isTransitive_extensionSet (S : Set P) : (N.extensionSet S).IsTransitive := by
  intro y hy z hz
  rw [mem_extensionSet_iff] at hy
  obtain ⟨i, rfl⟩ := hy
  obtain ⟨j, -, hzj⟩ := mem_zval_iff.1 hz
  obtain ⟨k, hk⟩ := N.subname_closed i j
  exact N.mem_extensionSet_iff.2 ⟨k, by rw [hzj, hk]⟩

/-- **The material extension carrier**: the indexed set with its transitivity.-/
def extensionCarrier (S : Set P) : MaterialCarrier.{u} :=
  ⟨N.extensionSet S, N.isTransitive_extensionSet S⟩

/--
@isnad1 id=iff.0h5v.s5.49c983a033d0 from=translated src=- shape=c039586e vocab=ee03bce3
-/
@[simp] theorem mem_extensionCarrier_iff {S : Set P} {y : ZFSet.{u}} :
    y ∈ N.extensionCarrier S ↔ ∃ i, y = zval S (N.decode i) :=
  N.mem_extensionSet_iff

/-- The indexed analog of `mem_valuationImage_of_mem_of_zval_eq`: membership via a semantic
representative in the family.
@isnad1 id=mem.2h6v.s5.c4a9d86a505a from=translated src=- shape=582e3058 vocab=48f0ed80
-/
theorem mem_extensionCarrier_of_mem_of_zval_eq {S : Set P} {τ : PName P} (hτ : τ ∈ N.names)
    {x : ZFSet.{u}} (h : zval S τ = x) : x ∈ N.extensionCarrier S := by
  obtain ⟨i, rfl⟩ := hτ
  exact N.mem_extensionCarrier_iff.2 ⟨i, h.symm⟩

/-!
### The `M[G]` contract

Only from here on does the library speak of `M[G]`: with canonical names available, the
extension carrier along any condition set containing `⊤` contains the ground and the
generic's code. The construction above is oracle-relative and genericity-free; these
theorems are what earns the extension reading.
-/

section Canonical

variable [Preorder P] [Top P] {Pres : InternalForcingPresentation M P}
variable {N : InternalNamePresentation M P} {S : Set P}

/-- **Ground inclusion** — the first half of the `M[G]` contract: every carrier element
belongs to the extension carrier, along any condition set containing `⊤`. The external
layer's explicit hypothesis is discharged by the semantic check-name representative.
@isnad1 id=mem.3h6v.s6.6412bed2bb94 from=translated src=- shape=f151c511 vocab=f2279726
-/
theorem HasCanonicalNames.mem_extensionCarrier_of_mem (h : HasCanonicalNames Pres N)
    {x : ZFSet.{u}} (hx : x ∈ M) (hS : (⊤ : P) ∈ S) : x ∈ N.extensionCarrier S := by
  obtain ⟨τ, hτ, hval⟩ := h.check_represented x hx
  exact N.mem_extensionCarrier_of_mem_of_zval_eq hτ (hval S hS)

/-- **Generic-code membership** — the second half of the `M[G]` contract: the value of the
generic's name for the presentation's condition code belongs to the extension carrier.
@isnad1 id=mem.2h5v.s6.5dccfc4f2152 from=translated src=- shape=d511d880 vocab=79e48df2
-/
theorem HasCanonicalNames.zval_genName_mem_extensionCarrier (h : HasCanonicalNames Pres N)
    (hS : (⊤ : P) ∈ S) :
    zval S (genName Pres.conditionCode) ∈ N.extensionCarrier S := by
  obtain ⟨τ, hτ, hval⟩ := h.genName_represented
  exact N.mem_extensionCarrier_of_mem_of_zval_eq hτ (hval S hS)

end Canonical

/-- The filter corollary of ground inclusion, via `Order.PFilter.top_mem`.
@isnad1 id=mem.2h6v.s6.dd5d861002aa from=translated src=- shape=b08aa064 vocab=4c3cce65
-/
theorem HasCanonicalNames.mem_extensionCarrier_of_mem_pfilter [Preorder P] [OrderTop P]
    {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
    (h : HasCanonicalNames Pres N) {x : ZFSet.{u}} (hx : x ∈ M) (G : Order.PFilter P) :
    x ∈ N.extensionCarrier (G : Set P) :=
  h.mem_extensionCarrier_of_mem hx G.top_mem

/-- The filter corollary of generic-code membership.
@isnad1 id=mem.1h5v.s6.fcb741611b1c from=translated src=- shape=a09a6999 vocab=dc5a11c7
-/
theorem HasCanonicalNames.zval_genName_mem_extensionCarrier_pfilter [Preorder P] [OrderTop P]
    {Pres : InternalForcingPresentation M P} {N : InternalNamePresentation M P}
    (h : HasCanonicalNames Pres N) (G : Order.PFilter P) :
    zval (G : Set P) (genName Pres.conditionCode) ∈ N.extensionCarrier (G : Set P) :=
  h.zval_genName_mem_extensionCarrier G.top_mem

end InternalNamePresentation

end Forcing
