/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Tengoku.Seed.Algebra.Category.Ring.Limits
import Tengoku.Seed.Analysis.Analytic.Within
import Tengoku.Seed.Topology.Sheaves.LocalPredicate
import Tengoku.LanaOka.Oka.OkaRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The structure sheaf of `ℂ^ι`

We assemble the rings `OkaRing U` of holomorphic functions on the opens `U` of `ℂ^ι` into a
sheaf of rings `okaSheaf ι` on the site of opens of `ℂ^ι`.

## Main definitions

- `okaPresheaf`: the presheaf of rings `U ↦ OkaRing U`.
- `okaSheaf`: the structure sheaf of `ℂ^ι`, i.e. `okaPresheaf` together with the sheaf condition.
- `OkaRing.evalHom`: evaluation of a holomorphic function at a point of its domain.
- `OkaRing.congr`: the isomorphism of rings of holomorphic functions induced by a `ℂ`-linear
  change of coordinates `ℂ^ι ≃ ℂ^κ`.
-/
namespace Tengoku.LanaOka end Tengoku.LanaOka open Tengoku.LanaOka
open CategoryTheory TopologicalSpace Opposite

universe u

variable {ι : Type u} [Fintype ι]

namespace Tengoku.LanaOka.OkaRing

/--
@isnad1 id=eq.1h4v.s7.8a9d72cd4567 from=translated src=- shape=212e1839 vocab=33c3411d
-/
@[ext]
lemma ext {U : Opens (ι → ℂ)} {f g : OkaRing U} (h : f.toFun = g.toFun) : f = g :=
  Subtype.ext h

/--
@isnad1 id=eq.1h4v.s9.f1bd568da2e9 from=translated src=- shape=0aa0c51e vocab=c34f36cb
-/
@[simp]
lemma restrict_toFun {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : OkaRing V) :
    (OkaRing.restrict h f).toFun = f.toFun ∘ Opens.inclusion h :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.f792a7f647a1 from=translated src=- shape=933ad603 vocab=68cb27ac
-/
@[simp]
lemma restrict_self {U : Opens (ι → ℂ)} (f : OkaRing U) :
    OkaRing.restrict le_rfl f = f :=
  rfl

/--
@isnad1 id=eq.2h5v.s9.52fb84825236 from=translated src=- shape=492c4c1d vocab=5f84625b
-/
@[simp]
lemma restrict_restrict {U V W : Opens (ι → ℂ)} (h : U ≤ V) (h' : V ≤ W) (f : OkaRing W) :
    OkaRing.restrict h (OkaRing.restrict h' f) = OkaRing.restrict (h.trans h') f :=
  rfl

/-- Evaluation of a holomorphic function at a point of its domain, as a ring homomorphism. -/
def evalHom {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) : OkaRing U →+* ℂ where
  toFun f := f.toFun _ ⟨x, hx⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/--
@isnad1 id=eq.1h4v.s8.6cf59fd77aac from=translated src=- shape=88601603 vocab=2b03d36a
-/
@[simp]
lemma evalHom_apply {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) (f : OkaRing U) :
    OkaRing.evalHom hx f = f.toFun _ ⟨x, hx⟩ :=
  rfl

/--
@isnad1 id=eq.2h5v.s9.99d0119a4cdd from=translated src=- shape=a6162dcc vocab=ade768f3
-/
@[simp]
lemma evalHom_restrict {U V : Opens (ι → ℂ)} (h : V ≤ U) {x : ι → ℂ} (hx : x ∈ V)
    (f : OkaRing U) :
    OkaRing.evalHom hx (OkaRing.restrict h f) = OkaRing.evalHom (h hx) f :=
  rfl

-- Not `@[simp]`: `evalHom_apply` is `@[simp]` and unfolds `evalHom` to `toFun`, so the
-- left-hand side here is never in normal form. `toFun_algebraMap` below is the form `simp`
-- actually meets.
/--
@isnad1 id=eq.1h4v.s8.e7f0094cea23 from=translated src=- shape=ac547455 vocab=ca338c87
-/
lemma evalHom_algebraMap {U : Opens (ι → ℂ)} {x : ι → ℂ} (hx : x ∈ U) (c : ℂ) :
    OkaRing.evalHom hx (algebraMap ℂ (OkaRing U) c) = c :=
  rfl

/-- `evalHom_algebraMap` in `simp` normal form: a constant function has that constant as its
value at every point.
@isnad1 id=eq.0h4v.s7.e0fb86b4ee49 from=translated src=- shape=15b3e68f vocab=81233076
-/
@[simp]
lemma toFun_algebraMap {U : Opens (ι → ℂ)} (c : ℂ) (p : U) :
    OkaRing.toFun U (algebraMap ℂ (OkaRing U) c) p = c :=
  rfl

end Tengoku.LanaOka.OkaRing

section Analytic

/-- Being holomorphic is a pointwise condition: since `U` is open, `OkaAnalytic f` holds if and
only if the extension of `f` by zero is analytic at every point of `U`.
@isnad1 id=iff.0h3v.s8.ea5b955bfa3b from=translated src=- shape=f0ea5ed0 vocab=a63096fa
-/
lemma _root_.Tengoku.LanaOka.okaAnalytic_iff {U : Opens (ι → ℂ)} (f : U → ℂ) :
    OkaAnalytic f ↔ ∀ x ∈ U, AnalyticAt ℂ (Function.extend Subtype.val f 0) x :=
  U.isOpen.analyticOn_iff_analyticOnNhd

omit [Fintype ι] in
/-- Extending by zero commutes with restriction, up to functions agreeing near a point of the
smaller open set.
@isnad1 id=eventual.2h5v.s9.ea79027b867c from=translated src=- shape=8a8cf666 vocab=81316d68
-/
lemma _root_.Tengoku.LanaOka.extend_eventuallyEq_extend {U V : Opens (ι → ℂ)} (h : U ≤ V) (f : V → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 =ᶠ[nhds x]
      Function.extend Subtype.val f 0 := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  have h₁ : Function.extend Subtype.val (f ∘ Opens.inclusion h) 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩
  have h₂ : Function.extend Subtype.val f 0 y = f ⟨y, h hy⟩ :=
    Subtype.val_injective.extend_apply (f := (Subtype.val : V → ι → ℂ)) _ _ ⟨y, h hy⟩
  rw [h₁, h₂]

omit [Fintype ι] in
/-- Near a point of `U`, the extension by zero of the restriction of a globally defined
function agrees with the function itself.
@isnad1 id=eventual.1h4v.s9.f133235e84b5 from=translated src=- shape=c5afe854 vocab=3cf4e621
-/
lemma _root_.Tengoku.LanaOka.extend_restrict_eventuallyEq {U : Opens (ι → ℂ)} (g : (ι → ℂ) → ℂ)
    {x : ι → ℂ} (hx : x ∈ U) :
    Function.extend Subtype.val (fun y : U ↦ g y) 0 =ᶠ[nhds x] g := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨y, hy⟩

/-- A function which is holomorphic at every point of `U` restricts to an element of the ring
of holomorphic functions on `U`.
@isnad1 id=okaanaly.1h3v.s8.14105a6abf07 from=translated src=- shape=8747e3a1 vocab=dca5a273
-/
lemma _root_.Tengoku.LanaOka.okaAnalytic_restrict {U : Opens (ι → ℂ)} {g : (ι → ℂ) → ℂ}
    (hg : ∀ x ∈ U, AnalyticAt ℂ g x) :
    OkaAnalytic (fun y : U ↦ g y) := by
  rw [okaAnalytic_iff]
  exact fun x hx ↦ (hg x hx).congr (extend_restrict_eventuallyEq g hx).symm

/-- The extension by zero of `f : OkaRing U` agrees with `f` on `U`.
@isnad1 id=eq.1h4v.s7.981865fa0d62 from=translated src=- shape=ee8b8e5a vocab=78d23567
-/
lemma Tengoku.LanaOka.OkaRing.toGlobalFun_apply {U : Opens (ι → ℂ)} (f : OkaRing U) {x : ι → ℂ} (hx : x ∈ U) :
    f.toGlobalFun _ x = f.toFun _ ⟨x, hx⟩ :=
  Subtype.val_injective.extend_apply (f := (Subtype.val : U → ι → ℂ)) _ _ ⟨x, hx⟩

/-- **A holomorphic function is continuous on its domain.**
@isnad1 id=continuo.0h3v.s7.6a27842fc684 from=translated src=- shape=0ea8d827 vocab=c1bc6656
-/
lemma Tengoku.LanaOka.OkaRing.continuousOn_toGlobalFun {U : Opens (ι → ℂ)} (f : OkaRing U) :
    ContinuousOn (f.toGlobalFun _) U :=
  fun x hx ↦ ((okaAnalytic_iff _).1 f.2 x hx).continuousAt.continuousWithinAt

/-- **The value of a holomorphic function depends continuously on the point.**

This is `OkaRing.continuousOn_toGlobalFun` read through `OkaRing.evalHom`, and it is the form
in which the value map of a complex analytic space is shown to be continuous.
@isnad1 id=continuo.0h3v.s8.9435c4b103d7 from=translated src=- shape=a99e384e vocab=5488e26c
-/
lemma Tengoku.LanaOka.OkaRing.continuous_evalHom {U : Opens (ι → ℂ)} (f : OkaRing U) :
    Continuous fun x : U ↦ OkaRing.evalHom x.2 f := by
  refine (continuousOn_iff_continuous_domRestrict.1 f.continuousOn_toGlobalFun).congr fun x ↦ ?_
  exact f.toGlobalFun_apply x.2

/-- Holomorphic functions restrict to holomorphic functions.
@isnad1 id=okaanaly.2h4v.s8.31cc7ad9f931 from=translated src=- shape=bcd22967 vocab=377a7034
-/
lemma Tengoku.LanaOka.OkaAnalytic.restrict {U V : Opens (ι → ℂ)} (h : U ≤ V) {f : V → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (f ∘ Opens.inclusion h) := by
  rw [okaAnalytic_iff] at hf ⊢
  exact fun x hx ↦ (hf x (h hx)).congr (extend_eventuallyEq_extend h f hx).symm

/-- Being holomorphic is a local condition.
@isnad1 id=okaanaly.1h3v.s10.d4527518e636 from=translated src=- shape=8538272a vocab=c2028db6
-/
lemma _root_.Tengoku.LanaOka.okaAnalytic_of_locally {U : Opens (ι → ℂ)} (f : U → ℂ)
    (hf : ∀ x : U, ∃ (V : Opens (ι → ℂ)) (_ : x.1 ∈ V) (h : V ≤ U),
      OkaAnalytic (f ∘ Opens.inclusion h)) :
    OkaAnalytic f := by
  rw [okaAnalytic_iff]
  intro x hx
  obtain ⟨V, hxV, h, hV⟩ := hf ⟨x, hx⟩
  rw [okaAnalytic_iff] at hV
  exact (hV x hxV).congr (extend_eventuallyEq_extend h f hxV)

end Analytic

section Reindex

/-- A continuous linear equivalence induces an order isomorphism on open sets. -/
abbrev ContinuousLinearEquiv.opensCongr {R E F : Type*} [Semiring R]
    [AddCommMonoid E] [AddCommMonoid F] [Module R E] [Module R F]
    [TopologicalSpace E] [TopologicalSpace F] (φ : E ≃L[R] F) :
    Opens E ≃o Opens F :=
  φ.toHomeomorph.opensCongr

variable {κ : Type*} [Fintype κ] (φ : (ι → ℂ) ≃L[ℂ] (κ → ℂ))

/-- Precomposing a holomorphic function on `U` with a continuous linear map mapping `V` into `U`
gives a holomorphic function on `V`.
@isnad1 id=okaanaly.2h6v.s10.c7183bf6e29b from=translated src=- shape=1c248dc2 vocab=27b0676c
-/
lemma Tengoku.LanaOka.OkaAnalytic.comp_continuousLinearMap {U : Opens (ι → ℂ)} {V : Opens (κ → ℂ)}
    (ψ : (κ → ℂ) →L[ℂ] (ι → ℂ)) (h : ∀ y ∈ V, ψ y ∈ U) {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) := by
  have key : ∀ y ∈ V, AnalyticAt ℂ (Function.extend Subtype.val f 0 ∘ ψ) y := fun y hy ↦
    ((okaAnalytic_iff f).1 hf _ (h y hy)).comp (ψ.analyticAt y)
  refine (funext fun z ↦ ?_ : (fun y : V ↦ f ⟨ψ y, h y y.2⟩) =
    fun y : V ↦ (Function.extend Subtype.val f 0 ∘ ψ) y) ▸ okaAnalytic_restrict key
  exact (Subtype.val_injective.extend_apply _ _ ⟨ψ z, h z z.2⟩).symm

/-- A `ℂ`-linear change of coordinates `φ : ℂ^ι ≃ ℂ^κ` identifies the holomorphic functions on
`U` with the holomorphic functions on the image of `U`. -/
noncomputable def Tengoku.LanaOka.OkaRing.congr (U : Opens (ι → ℂ)) :
    OkaRing U ≃ₐ[ℂ] OkaRing (φ.opensCongr U) where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨φ.symm y, y.2⟩)
    (f.2.comp_continuousLinearMap (φ.symm : (κ → ℂ) →L[ℂ] (ι → ℂ)) fun _ hy ↦ hy)
  invFun g := OkaRing.mk (fun z ↦ g.toFun _ ⟨φ z, by simp [z.2]⟩)
    (g.2.comp_continuousLinearMap (φ : (ι → ℂ) →L[ℂ] (κ → ℂ)) fun _ hz ↦ by simp [hz])
  left_inv f := by
    ext z
    exact congrArg (f.toFun _) (Subtype.ext (φ.symm_apply_apply (z : ι → ℂ)))
  right_inv g := by
    ext z
    exact congrArg (g.toFun _) (Subtype.ext (φ.apply_symm_apply (z : κ → ℂ)))
  map_mul' f g := rfl
  map_add' f g := rfl
  commutes' c := rfl

/-- Changing coordinates commutes with restriction.
@isnad1 id=eq.1h6v.s14.e66073193bbb from=translated src=- shape=3ed88548 vocab=469c972e
-/
lemma Tengoku.LanaOka.OkaRing.congr_restrict {U V : Opens (ι → ℂ)} (h : V ≤ U) (f : OkaRing U) :
    OkaRing.congr φ V (OkaRing.restrict h f) =
      OkaRing.restrict (φ.opensCongr.monotone h) (OkaRing.congr φ U f) :=
  rfl

/-- Changing coordinates back commutes with restriction.
@isnad1 id=eq.1h6v.s15.8d757fa092ff from=translated src=- shape=f867a521 vocab=fa19be39
-/
lemma Tengoku.LanaOka.OkaRing.congr_symm_restrict {U V : Opens (ι → ℂ)}
    (h : φ.opensCongr V ≤ φ.opensCongr U) (g : OkaRing (φ.opensCongr U)) :
    (OkaRing.congr φ V).symm (OkaRing.restrict h g) =
      OkaRing.restrict (φ.opensCongr.le_iff_le.mp h) ((OkaRing.congr φ U).symm g) :=
  rfl

end Reindex

section Translate

/-- **Precomposing a holomorphic function on `U` with a map which is analytic only on `V` and
sends `V` into `U` gives a holomorphic function on `V`.**

`ψ` is a map defined on all of `κ → ℂ`, but analyticity is required only at the points of `V`,
which is all the conclusion can see. That is what makes this usable when `ψ` comes from a
holomorphic function on a *proper* open subset — extended by zero outside it, as
`OkaRing.toGlobalFun` does — where analyticity off `V` is false and irrelevant.
@isnad1 id=okaanaly.3h6v.s9.56d79be6eaf4 from=translated src=- shape=469c1508 vocab=88572fcd
-/
lemma Tengoku.LanaOka.OkaAnalytic.comp_analyticOn {κ : Type u} [Fintype κ] {U : Opens (ι → ℂ)}
    {V : Opens (κ → ℂ)} (ψ : (κ → ℂ) → (ι → ℂ)) (hψ : ∀ y ∈ V, AnalyticAt ℂ ψ y)
    (h : ∀ y ∈ V, ψ y ∈ U) {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) := by
  have key : ∀ y ∈ V, AnalyticAt ℂ (Function.extend Subtype.val f 0 ∘ ψ) y := fun y hy ↦
    ((okaAnalytic_iff f).1 hf _ (h y hy)).comp (hψ y hy)
  refine (funext fun z ↦ ?_ : (fun y : V ↦ f ⟨ψ y, h y y.2⟩) =
    fun y : V ↦ (Function.extend Subtype.val f 0 ∘ ψ) y) ▸ okaAnalytic_restrict key
  exact (Subtype.val_injective.extend_apply _ _ ⟨ψ z, h z z.2⟩).symm

/-- Precomposing a holomorphic function on `U` with an entire map sending `V` into `U` gives a
holomorphic function on `V`.
@isnad1 id=okaanaly.3h6v.s9.5afa3a7967ba from=translated src=- shape=8ac9abeb vocab=88572fcd
-/
lemma Tengoku.LanaOka.OkaAnalytic.comp_analytic {κ : Type u} [Fintype κ] {U : Opens (ι → ℂ)} {V : Opens (κ → ℂ)}
    (ψ : (κ → ℂ) → (ι → ℂ)) (hψ : ∀ y, AnalyticAt ℂ ψ y) (h : ∀ y ∈ V, ψ y ∈ U)
    {f : U → ℂ} (hf : OkaAnalytic f) :
    OkaAnalytic (fun y : V ↦ f ⟨ψ y, h y y.2⟩) :=
  hf.comp_analyticOn ψ (fun y _ ↦ hψ y) h

namespace TopologicalSpace.Opens

omit [Fintype ι]

variable (U : Opens (ι → ℂ)) (v : ι → ℂ)

/-- The translate of an open set `U` of `ℂ^ι` by `-v`, i.e. the preimage of `U` under the
translation `y ↦ y + v`. Its points are the `y` with `y + v ∈ U`. -/
def shift : Opens (ι → ℂ) :=
  ⟨(fun y ↦ y + v) ⁻¹' U, U.isOpen.preimage (continuous_id.add continuous_const)⟩

/--
@isnad1 id=iff.0h4v.s7.865f0dccbd30 from=translated src=- shape=ce24c515 vocab=35bb17d7
-/
@[simp]
lemma mem_shift {y : ι → ℂ} : y ∈ U.shift v ↔ y + v ∈ U :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s6.00380e0d4618 from=translated src=- shape=bd70a55b vocab=25776ce6
-/
@[simp]
lemma shift_zero : U.shift 0 = U := by
  ext y
  simp

variable {U v} in
/--
@isnad1 id=le.1h4v.s8.bf219aa087bc from=translated src=- shape=14926bc6 vocab=d7557300
-/
lemma shift_mono {V : Opens (ι → ℂ)} (h : U ≤ V) : U.shift v ≤ V.shift v :=
  fun _ hy ↦ h hy

/--
@isnad1 id=eq.0h4v.s6.3880907d3199 from=translated src=- shape=3095c101 vocab=29f50db0
-/
lemma shift_shift (w : ι → ℂ) : (U.shift v).shift w = U.shift (v + w) := by
  ext y
  simp [add_comm, add_left_comm]

/--
@isnad1 id=eq.0h3v.s6.816759bf07cb from=translated src=- shape=d227a9d5 vocab=9802ef2a
-/
@[simp]
lemma shift_shift_neg : (U.shift v).shift (-v) = U := by
  rw [shift_shift]
  simp

variable {U v} in
/--
@isnad1 id=iff.0h4v.s8.670ac04308db from=translated src=- shape=0b88a2bf vocab=d7557300
-/
lemma shift_le_shift_iff {V : Opens (ι → ℂ)} : U.shift v ≤ V.shift v ↔ U ≤ V := by
  refine ⟨fun h y hy ↦ ?_, fun h ↦ shift_mono h⟩
  have hy' : y - v ∈ U.shift v := by simpa using hy
  simpa using h hy'

end TopologicalSpace.Opens

variable (U : Opens (ι → ℂ)) (v : ι → ℂ)

/-- Translation by `v` identifies the holomorphic functions on `U` with the holomorphic
functions on the translate `U.shift v` of `U`. -/
noncomputable def Tengoku.LanaOka.OkaRing.shift : OkaRing U ≃ₐ[ℂ] OkaRing (U.shift v) where
  toFun f := OkaRing.mk (fun y ↦ f.toFun _ ⟨(y : ι → ℂ) + v, y.2⟩)
    (f.2.comp_analytic (fun y ↦ y + v) (fun _ ↦ analyticAt_id.add analyticAt_const) fun _ hy ↦ hy)
  invFun g := OkaRing.mk (fun z ↦ g.toFun _ ⟨(z : ι → ℂ) - v, by simp⟩)
    (g.2.comp_analytic (fun z ↦ z - v) (fun _ ↦ analyticAt_id.sub analyticAt_const)
      fun _ hz ↦ by simpa using hz)
  left_inv f := by
    ext z
    exact congrArg (f.toFun _) (Subtype.ext (by simp))
  right_inv g := by
    ext z
    exact congrArg (g.toFun _) (Subtype.ext (by simp))
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

variable {U v}

/-- Translating commutes with restriction.
@isnad1 id=eq.1h5v.s9.25b3d7e011d4 from=translated src=- shape=776fc556 vocab=78cd9a93
-/
lemma Tengoku.LanaOka.OkaRing.shift_restrict {V : Opens (ι → ℂ)} (h : V ≤ U) (f : OkaRing U) :
    OkaRing.shift V v (OkaRing.restrict h f) =
      OkaRing.restrict (Opens.shift_mono h) (OkaRing.shift U v f) :=
  rfl

/-- Translating back commutes with restriction.
@isnad1 id=eq.1h5v.s9.57d24fadf93a from=translated src=- shape=5540dc09 vocab=455509f7
-/
lemma Tengoku.LanaOka.OkaRing.shift_symm_restrict {V : Opens (ι → ℂ)} (h : V.shift v ≤ U.shift v)
    (g : OkaRing (U.shift v)) :
    (OkaRing.shift V v).symm (OkaRing.restrict h g) =
      OkaRing.restrict (Opens.shift_le_shift_iff.mp h) ((OkaRing.shift U v).symm g) :=
  rfl

end Translate

/-- The presheaf of rings of holomorphic functions on `ℂ^ι`. -/
noncomputable def _root_.Tengoku.LanaOka.okaPresheaf (ι : Type u) [Fintype ι] : (Opens (ι → ℂ))ᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (OkaRing U.unop)
  map f := RingCat.ofHom (OkaRing.restrict (leOfHom f.unop)).toRingHom
  map_id U := by ext f; rfl
  map_comp f g := by ext h; rfl

/-- Being holomorphic, as a local predicate on the sheaf of `ℂ`-valued functions. -/
def _root_.Tengoku.LanaOka.okaLocalPredicate (ι : Type u) [Fintype ι] :
    TopCat.LocalPredicate (X := TopCat.of (ι → ℂ)) (fun _ ↦ ℂ) where
  pred {_} f := OkaAnalytic f
  res i _ hf := hf.restrict (leOfHom i)
  locality _ hf := okaAnalytic_of_locally _ fun x ↦ by
    obtain ⟨V, hxV, i, hi⟩ := hf x
    exact ⟨V, hxV, leOfHom i, hi⟩

/-- The presheaf of holomorphic functions is, as a presheaf of types, the subpresheaf of the
sheaf of all `ℂ`-valued functions cut out by the local predicate `OkaAnalytic`. -/
noncomputable def _root_.Tengoku.LanaOka.okaPresheafIsoSubpresheaf (ι : Type u) [Fintype ι] :
    okaPresheaf ι ⋙ CategoryTheory.forget RingCat.{u} ≅
      TopCat.subpresheafToTypes (okaLocalPredicate ι).toPrelocalPredicate :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The presheaf of holomorphic functions on `ℂ^ι` is a sheaf.
@isnad1 id=issheaf.0h1v.s7.6f6ee86a00b2 from=translated src=- shape=9a66d125 vocab=bc275a79
-/
theorem _root_.Tengoku.LanaOka.okaPresheaf_isSheaf (ι : Type u) [Fintype ι] :
    Presheaf.IsSheaf (Opens.grothendieckTopology (ι → ℂ)) (okaPresheaf ι) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget RingCat.{u}),
    isSheaf_iff_isSheaf_of_type]
  have h := TopCat.subpresheafToTypes.isSheaf (okaLocalPredicate ι)
  rw [TopCat.Presheaf.IsSheaf, isSheaf_iff_isSheaf_of_type] at h
  exact Presieve.isSheaf_iso _ (okaPresheafIsoSubpresheaf ι).symm h

/-- The structure sheaf of `ℂ^ι`: the sheaf of rings of holomorphic functions. -/
noncomputable def _root_.Tengoku.LanaOka.okaSheaf (ι : Type u) [Fintype ι] :
    Sheaf (Opens.grothendieckTopology (ι → ℂ)) RingCat.{u} :=
  ⟨okaPresheaf ι, okaPresheaf_isSheaf ι⟩
-- Tengoku: root names of this library moved to Tengoku.LanaOka so they do not collide with other libraries (generated)
