/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Tengoku.Seed.Order.Antisymmetrization
import Tengoku.Forcing.Forcing.Order.Filter

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The separative modification and quotient

Distinct conditions of a forcing notion can carry the same information: in any linear order, for
instance, all conditions are pairwise compatible, so no condition excludes any other. The
*separative preorder* `SepLE p q` — every strengthening of `p` is compatible with `q` — captures
"q carries no information beyond p", and quotienting by mutual `SepLE` identifies conditions
with identical forcing content. This is the bridge between raw forcing notions and (at M6) their
Boolean completions.

Design, per the decision recorded in issue #8:

* `SepLE` lives on a **type synonym** `SepMod P` (the separative modification), whose preorder
  is `SepLE`.
* The quotient is mathlib's antisymmetrization of `SepMod P`, giving a partial order for free.
* The canonical map `sepQuotient : P → SepQuotient P` is **not** a `DenseOrderEmbedding` — it is
  generally noninjective and does not reflect the original `≤` (quotient order reflection gives
  only `SepLE p q`). Transport of compatibility, dense sets, filters, and genericity is proved
  **directly**; no weaker morphism abstraction is introduced.

## Main definitions

* `Forcing.SepLE p q`: every strengthening of `p` is compatible with `q`.
* `Forcing.SepMod P`: the separative modification — `P` reordered by `SepLE`.
* `Forcing.SepQuotient P`: the separative quotient, a partial order.
* `Forcing.sepQuotient`: the canonical map `P → SepQuotient P`.
* `Forcing.IsSeparative P`: `SepLE` implies `≤`.

## Main results

* `Forcing.isSeparative_sepQuotient`: the quotient is separative.
* `Forcing.compatible_sepQuotient_iff`: the canonical map preserves and reflects compatibility.
* `Forcing.IsDense.image_sepQuotient`, `Forcing.IsDenseOpen.preimage_sepQuotient`,
  `Forcing.meets_sepQuotientPFilter_iff`, `Forcing.genericFor_sepQuotientPFilter`: direct
  transport of density, meeting, and genericity along the canonical map.
-/

namespace Forcing

variable {P : Type*} [Preorder P] {p q r : P} {D : Set P}

/-- The separative preorder: `SepLE p q` iff every strengthening of `p` is compatible with `q`,
that is, `q` carries no information beyond `p`.-/
def SepLE (p q : P) : Prop :=
  ∀ r ≤ p, Compatible r q

/--
@isnad1 id=seple.0h2v.s3.45a05019572d from=translated src=- shape=e6608552 vocab=865b8b2e
-/
theorem SepLE.refl (p : P) : SepLE p p :=
  fun _ hr ↦ .of_le hr

/-- `SepLE` extends the forcing order.
@isnad1 id=seple.1h3v.s4.7e708cf10286 from=translated src=- shape=4ab508a5 vocab=b00390c2
-/
theorem SepLE.of_le (h : p ≤ q) : SepLE p q :=
  fun _ hr ↦ .of_le (hr.trans h)

/--
@isnad1 id=seple.2h4v.s4.adb8319c4a67 from=translated src=- shape=ed0e08c7 vocab=865b8b2e
-/
theorem SepLE.trans (h1 : SepLE p q) (h2 : SepLE q r) : SepLE p r := by
  intro s hs
  obtain ⟨t, hts, htq⟩ := h1 s hs
  obtain ⟨u, hut, hur⟩ := h2 t htq
  exact ⟨u, hut.trans hts, hur⟩

/--
@isnad1 id=compatib.1h3v.s4.d887560c84d4 from=translated src=- shape=4ab508a5 vocab=e02bd211
-/
theorem SepLE.compatible (h : SepLE p q) : Compatible p q :=
  h p le_rfl

/-- Conditions with a common `SepLE`-strengthening are compatible.
@isnad1 id=compatib.2h4v.s4.fcd908a210b2 from=translated src=- shape=f8061e47 vocab=e02bd211
-/
theorem Compatible.of_sepLE_of_sepLE (h1 : SepLE r p) (h2 : SepLE r q) : Compatible p q := by
  obtain ⟨t, htr, htp⟩ := h1 r le_rfl
  obtain ⟨u, hut, huq⟩ := h2 t htr
  exact ⟨u, hut.trans htp, huq⟩

/-- The separative equivalence: mutual `SepLE`.-/
def SepEquiv (p q : P) : Prop :=
  SepLE p q ∧ SepLE q p

/-- `SepEquiv` is an equivalence relation.
@isnad1 id=equivale.0h1v.s3.16051da40fdf from=translated src=- shape=84bfdc15 vocab=fdb934b0
-/
theorem sepEquiv_equivalence : Equivalence (@SepEquiv P _) where
  refl p := ⟨.refl p, .refl p⟩
  symm h := ⟨h.2, h.1⟩
  trans h1 h2 := ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

/-- A preorder is *separative* if the separative preorder implies the forcing order.-/
def IsSeparative (P : Type*) [Preorder P] : Prop :=
  ∀ ⦃p q : P⦄, SepLE p q → p ≤ q

/-- The *separative modification*: a type synonym for `P` carrying `SepLE` as its order.-/
def SepMod (P : Type*) : Type _ :=
  P

/-- Interpret a condition in the separative modification.-/
def toSepMod : P → SepMod P :=
  id

/-- Interpret an element of the separative modification as a condition.-/
def ofSepMod : SepMod P → P :=
  id

omit [Preorder P] in
/--
@isnad1 id=eq.0h2v.s3.57b46562cd54 from=translated src=- shape=9290c416 vocab=885d706a
-/
@[simp] theorem ofSepMod_toSepMod (p : P) : ofSepMod (toSepMod p) = p :=
  rfl

omit [Preorder P] in
/--
@isnad1 id=eq.0h2v.s3.b03e486b2e24 from=translated src=- shape=efbf31f7 vocab=f67183f7
-/
@[simp] theorem toSepMod_ofSepMod (p : SepMod P) : toSepMod (ofSepMod p) = p :=
  rfl

instance : Preorder (SepMod P) where
  le p q := SepLE (ofSepMod p) (ofSepMod q)
  le_refl p := SepLE.refl _
  le_trans _ _ _ := SepLE.trans

/--
@isnad1 id=iff.0h3v.s4.ebd6b2fc6cb5 from=translated src=- shape=5d6b553c vocab=7091ca5a
-/
@[simp] theorem toSepMod_le_toSepMod : toSepMod p ≤ toSepMod q ↔ SepLE p q :=
  .rfl

/-- The *separative quotient*: the antisymmetrization of the separative modification. A partial
order by mathlib's `instPartialOrderAntisymmetrization`.-/
abbrev SepQuotient (P : Type*) [Preorder P] :=
  Antisymmetrization (SepMod P) (· ≤ ·)

/-- The canonical map onto the separative quotient.-/
def sepQuotient (p : P) : SepQuotient P :=
  toAntisymmetrization (· ≤ ·) (toSepMod p)

/--
@isnad1 id=surjecti.0h1v.s3.cc2da2cbee22 from=translated src=- shape=a638af76 vocab=c4675706
-/
theorem sepQuotient_surjective : Function.Surjective (sepQuotient : P → SepQuotient P) :=
  fun x ↦ Quotient.inductionOn' x fun p ↦ ⟨ofSepMod p, rfl⟩

/--
@isnad1 id=iff.0h3v.s5.aa2cefdb1e33 from=translated src=- shape=5d6b553c vocab=3ffb41cc
-/
@[simp] theorem sepQuotient_le_sepQuotient : sepQuotient p ≤ sepQuotient q ↔ SepLE p q :=
  toAntisymmetrization_le_toAntisymmetrization_iff

/--
@isnad1 id=monotone.0h1v.s4.e47066d4ef01 from=translated src=- shape=a638af76 vocab=4d546e48
-/
theorem sepQuotient_monotone : Monotone (sepQuotient : P → SepQuotient P) :=
  fun _ _ h ↦ sepQuotient_le_sepQuotient.2 (.of_le h)

/--
@isnad1 id=iff.0h3v.s4.3a2525626af9 from=translated src=- shape=5d6b553c vocab=4e233cd0
-/
@[simp] theorem sepQuotient_eq_sepQuotient : sepQuotient p = sepQuotient q ↔ SepEquiv p q := by
  rw [le_antisymm_iff, sepQuotient_le_sepQuotient, sepQuotient_le_sepQuotient]
  exact .rfl

/-- The canonical map preserves and reflects compatibility.
@isnad1 id=iff.0h3v.s5.4ea4c9a7c46a from=translated src=- shape=89f3a64e vocab=9312a396
-/
@[simp] theorem compatible_sepQuotient_iff :
    Compatible (sepQuotient p) (sepQuotient q) ↔ Compatible p q := by
  constructor
  · rintro ⟨x, hx1, hx2⟩
    obtain ⟨r, rfl⟩ := sepQuotient_surjective x
    exact .of_sepLE_of_sepLE (sepQuotient_le_sepQuotient.1 hx1)
      (sepQuotient_le_sepQuotient.1 hx2)
  · rintro ⟨r, h1, h2⟩
    exact ⟨sepQuotient r, sepQuotient_monotone h1, sepQuotient_monotone h2⟩

/-- The separative quotient is separative.
@isnad1 id=issepara.0h1v.s4.65ef8aa6e189 from=translated src=- shape=1666ae32 vocab=cd1b3df8
-/
theorem isSeparative_sepQuotient : IsSeparative (SepQuotient P) := by
  intro x y hxy
  obtain ⟨p, rfl⟩ := sepQuotient_surjective x
  obtain ⟨q, rfl⟩ := sepQuotient_surjective y
  rw [sepQuotient_le_sepQuotient]
  intro r hrp
  exact compatible_sepQuotient_iff.1
    (hxy _ (sepQuotient_le_sepQuotient.2 (.of_le hrp)))

/-- The image of a dense set under the canonical map is dense.
@isnad1 id=isdense.1h2v.s5.44b4e92d1e2a from=translated src=- shape=4ea057af vocab=9a83ec98
-/
theorem IsDense.image_sepQuotient (hD : IsDense D) :
    IsDense (sepQuotient '' D : Set (SepQuotient P)) := by
  intro x
  obtain ⟨p, rfl⟩ := sepQuotient_surjective x
  obtain ⟨q, hqD, hqp⟩ := hD p
  exact ⟨sepQuotient q, ⟨q, hqD, rfl⟩, sepQuotient_monotone hqp⟩

/-- The preimage of a dense open set under the canonical map is dense open. Openness (downward
closure) is essential: a plain dense set in the quotient has a dense preimage only after passing
to its downward closure, since order reflection along the map gives only `SepLE`.
@isnad1 id=isdenseo.1h2v.s5.6c008f9d3c7d from=translated src=- shape=45886b6c vocab=c8d8b3d0
-/
theorem IsDenseOpen.preimage_sepQuotient {D' : Set (SepQuotient P)} (h : IsDenseOpen D') :
    IsDenseOpen (sepQuotient ⁻¹' D') := by
  constructor
  · intro p
    obtain ⟨y, hyD, hyp⟩ := h.1 (sepQuotient p)
    obtain ⟨q, rfl⟩ := sepQuotient_surjective y
    obtain ⟨r, hrq, hrp⟩ := (sepQuotient_le_sepQuotient.1 hyp).compatible
    exact ⟨r, h.2 (sepQuotient_monotone hrq) hyD, hrp⟩
  · exact fun a b hba ha ↦ h.2 (sepQuotient_monotone hba) ha

/-- The filter on the separative quotient generated by the image of a filter on `P`.-/
def sepQuotientPFilter (G : Order.PFilter P) : Order.PFilter (SepQuotient P) :=
  (Order.IsPFilter.of_def (F := {y | ∃ p ∈ G, sepQuotient p ≤ y})
    (by
      obtain ⟨p, hp⟩ := G.nonempty
      exact ⟨sepQuotient p, p, hp, le_rfl⟩)
    (by
      rintro y₁ ⟨p₁, hp₁, h₁⟩ y₂ ⟨p₂, hp₂, h₂⟩
      obtain ⟨r, hrG, hr₁, hr₂⟩ := exists_mem_le_le hp₁ hp₂
      exact ⟨sepQuotient r, ⟨r, hrG, le_rfl⟩, (sepQuotient_monotone hr₁).trans h₁,
        (sepQuotient_monotone hr₂).trans h₂⟩)
    (fun hxy ⟨p, hp, hple⟩ ↦ ⟨p, hp, hple.trans hxy⟩)).toPFilter

/--
@isnad1 id=iff.0h3v.s6.5aea2400b843 from=translated src=- shape=dc30db13 vocab=cab74fa9
-/
@[simp] theorem mem_sepQuotientPFilter {G : Order.PFilter P} {y : SepQuotient P} :
    y ∈ sepQuotientPFilter G ↔ ∃ p ∈ G, sepQuotient p ≤ y :=
  .rfl

/-- Meeting transports along the canonical map: for downward-closed targets, the generated
filter meets `D'` iff `G` meets its preimage.
@isnad1 id=iff.1h3v.s6.4aa162351aee from=translated src=- shape=d51ae933 vocab=4ef47e81
-/
theorem meets_sepQuotientPFilter_iff {G : Order.PFilter P} {D' : Set (SepQuotient P)}
    (hD' : IsLowerSet D') :
    Meets (sepQuotientPFilter G) D' ↔ Meets G (sepQuotient ⁻¹' D') := by
  constructor
  · rintro ⟨y, ⟨p, hpG, hpy⟩, hyD⟩
    exact ⟨p, hpG, hD' hpy hyD⟩
  · rintro ⟨p, hpG, hpD⟩
    exact ⟨sepQuotient p, ⟨p, hpG, le_rfl⟩, hpD⟩

/-- Genericity transports along the canonical map: generic for the preimage family, generated
filter generic for the original family.
@isnad1 id=genericf.1h3v.s5.1372e820c5da from=translated src=- shape=cb42e77b vocab=8aa6ec61
-/
theorem genericFor_sepQuotientPFilter {G : Order.PFilter P} {𝒟' : Set (Set (SepQuotient P))}
    (h : GenericFor ((sepQuotient ⁻¹' ·) '' 𝒟') G) :
    GenericFor 𝒟' (sepQuotientPFilter G) := by
  intro D' hD'
  obtain ⟨p, hpG, hpD⟩ := h _ (Set.mem_image_of_mem _ hD')
  exact ⟨sepQuotient p, ⟨p, hpG, le_rfl⟩, hpD⟩

/-- For families of downward-closed sets, genericity transport is an equivalence.
@isnad1 id=iff.1h3v.s6.4f262382bf2f from=translated src=- shape=a6b84f17 vocab=a1ca30b2
-/
theorem genericFor_sepQuotientPFilter_iff {G : Order.PFilter P}
    {𝒟' : Set (Set (SepQuotient P))} (h𝒟' : ∀ D' ∈ 𝒟', IsLowerSet D') :
    GenericFor 𝒟' (sepQuotientPFilter G) ↔ GenericFor ((sepQuotient ⁻¹' ·) '' 𝒟') G := by
  constructor
  · rintro h E ⟨D', hD', rfl⟩
    exact (meets_sepQuotientPFilter_iff (h𝒟' D' hD')).1 (h D' hD')
  · exact genericFor_sepQuotientPFilter

/-!
### Sanity examples

Linear orders are the canonical non-separative forcing notions: all conditions are compatible,
so `SepLE` holds everywhere and the quotient collapses — distinct conditions carry the same
(empty) forcing information.
-/

end Forcing
