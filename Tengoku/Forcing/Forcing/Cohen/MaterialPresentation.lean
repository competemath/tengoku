/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Forcing.Forcing.Material.DerivedVisibility
import Tengoku.Forcing.Forcing.Cohen.Visibility
import Tengoku.Forcing.Forcing.Cohen.RealName

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Cohen material presentation: visibility derived, never stored

The material data from which Cohen visibility is **derived**: an internal forcing
presentation tied explicitly to `cohenConditionCode` (so no second, unrelated coding can be
certified), internal coordinate-test codes, and internal diagonal-test codes for every
materially coded real — each an internal subset with its externalization law.

Everything the visibility layer wants is then a *theorem or definition over this data*, never
a field: the visibility context (`derivedContext`) has visible sets exactly the
externalizations of internal subsets and designated reals exactly the materially coded reals
`{c | realCode c ∈ M}` — so M3's avoidance conclusion `c ∉ designatedReals` *is* the material
`realCode c ∉ M`, with no separate bridge. `Sees` is proved from the membership laws of the
carried test codes (`sees_derivedContext`); a bare transitive carrier could not supply those
sets, which is exactly why the presentation carries them. Countability of the visible family
follows from external countability of the carrier, in two stages
(`countable_visible_derivedContext`, `countable_visibleDenseOpen_derivedContext`) — external
countability stays an existence-side hypothesis, as everywhere since M2.

The dependency boundary is deliberate: this file needs the forcing presentation, the Cohen
visibility layer, and the real code — and does **not** import the material names or the
extension. Names and `extensionCarrier` contribute to material membership, not to
visibility; the two halves meet only in the final composition.

## Main definitions

* `Forcing.Cohen.CohenMaterialPresentation`: the carried internal test codes.
* `Forcing.Cohen.CohenMaterialPresentation.derivedContext`: the derived visibility context.

## Main results

* `Forcing.Cohen.CohenMaterialPresentation.sees_derivedContext`: `Sees`, proved rather than
  assumed.
* `Forcing.Cohen.CohenMaterialPresentation.countable_visibleDenseOpen_derivedContext`:
  external countability of the carrier bounds the visible dense-open family.
-/

namespace Forcing.Cohen

open FinitePartialFunction InternalForcingPresentation

variable {M : MaterialCarrier.{0}}

/-- The Cohen material presentation: an internal forcing presentation **tied to
`cohenConditionCode`**, with internal coordinate-test codes and internal diagonal-test codes
for every materially coded real. Visibility data is derived from this structure, never stored
in it — and it carries no names.-/
structure CohenMaterialPresentation (M : MaterialCarrier.{0}) where
  /-- The internal presentation of the Cohen forcing notion.-/
  forcing : InternalForcingPresentation M Cond
  /-- The presentation codes conditions by the structural Cohen code — no second coding.-/
  conditionCode_eq : forcing.conditionCode = cohenConditionCode
  /-- The internal coordinate-test codes.-/
  coordCode : ℕ → forcing.InternalSubset
  /-- Each coordinate-test code externalizes to the coordinate requirement's support.-/
  coord_externalize : ∀ n, (coordCode n).externalize = (coordReq n).support
  /-- The internal diagonal-test codes, one per materially coded real.-/
  diagCode : {c : ℕ → Bool // realCode c ∈ M} → forcing.InternalSubset
  /-- Each diagonal-test code externalizes to the diagonal requirement's support.-/
  diag_externalize : ∀ c, (diagCode c).externalize = (diagReq c.1).support

namespace CohenMaterialPresentation

variable (C : CohenMaterialPresentation M)

/-- **The derived visibility context**: visible sets are exactly the externalizations of
internal subsets; designated reals are exactly the materially coded reals. Derived, not
stored — the observer vocabularies as projections of one material presentation.-/
def derivedContext : CohenVisibilityContext where
  toVisibilityContext := C.forcing.derivedContext
  designatedReals := {c | realCode c ∈ M}

/-- The underlying context **is** the presentation's general derived context — one derived
context in the library, not two extensionally identical ones.
@isnad1 id=eq.0h2v.s5.fdd8babe0e33 from=translated src=- shape=146666fe vocab=ad29bc00
-/
theorem derivedContext_toVisibilityContext :
    C.derivedContext.toVisibilityContext = C.forcing.derivedContext :=
  rfl

/-- Visibility in the derived context is exactly internal-subset externalization.
@isnad1 id=iff.0h3v.s5.03e3566aab1e from=translated src=- shape=8dc6679c vocab=95c1d2ed
-/
theorem visible_derivedContext_iff {D : Set Cond} :
    C.derivedContext.Visible D ↔ ∃ d : C.forcing.InternalSubset, d.externalize = D :=
  Iff.rfl

/-- The derived designated reals are the materially coded reals, definitionally.
@isnad1 id=iff.0h3v.s5.5faf09a660b1 from=translated src=- shape=0e363d31 vocab=0fec6eb2
-/
@[simp] theorem mem_designatedReals_derivedContext {c : ℕ → Bool} :
    c ∈ C.derivedContext.designatedReals ↔ realCode c ∈ M :=
  Iff.rfl

/-- M3's avoidance conclusion, read through the derived context, **is** the material
nonmembership — no separate bridge.
@isnad1 id=iff.0h3v.s5.a13f198cd163 from=translated src=- shape=c06e2760 vocab=0fec6eb2
-/
theorem not_mem_designatedReals_iff {c : ℕ → Bool} :
    c ∉ C.derivedContext.designatedReals ↔ realCode c ∉ M :=
  Iff.rfl

/-- **`Sees`, proved rather than assumed**: the carried internal test codes witness the
visibility obligations through their externalization laws.
@isnad1 id=sees.0h2v.s3.99edab38e34a from=translated src=- shape=1f8e965c vocab=95c71553
-/
theorem sees_derivedContext : C.derivedContext.Sees :=
  ⟨fun n ↦ ⟨C.coordCode n, C.coord_externalize n⟩,
    fun _ hc ↦ ⟨C.diagCode ⟨_, hc⟩, C.diag_externalize _⟩⟩

/-- Stage one of countability: a countable carrier admits only countably many visible sets,
since every visible set is the externalization of a carrier element.
@isnad1 id=countabl.1h2v.s4.6d2fe8c37bce from=translated src=- shape=d21e55b4 vocab=ab813563
-/
theorem countable_visible_derivedContext (hM : (M : Set ZFSet.{0}).Countable) :
    C.derivedContext.visible.Countable :=
  C.forcing.countable_visible_derivedContext hM

/-- Stage two: the visible dense-open family is countable — the hypothesis Rasiowa–Sikorski
existence consumes, from external countability of the carrier alone.
@isnad1 id=countabl.1h2v.s4.13c11cc8474f from=translated src=- shape=08ba93ec vocab=1c454df2
-/
theorem countable_visibleDenseOpen_derivedContext (hM : (M : Set ZFSet.{0}).Countable) :
    C.derivedContext.visibleDenseOpen.Countable :=
  C.forcing.countable_visibleDenseOpen_derivedContext hM

/-!
### Sanity example

The condition code is fixed, not free; both derived projections read off definitionally. The
composition with the M3 avoidance theorem lives downstream, in the final composition module —
this file deliberately does not import the adequacy layer.
-/

end CohenMaterialPresentation

end Forcing.Cohen
