import Tengoku.PshdLean.PshLines.Plurisubharmonic
import Tengoku.Seed.Analysis.Calculus.ContDiff.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local quasi-PSH potentials and additive singularity comparison

Source: `transcendental-nakamaye-revised-20260831:sec:qpsh`.
The local decomposition uses the existing extended-real PSH germs and a real
smooth summand. The raw criterion permits the identically negative-infinite
function, like `PlurisubharmonicAt`; `LocalQuasiPshPotentialOn` separately
excludes it on every open neighborhood. No current or global geometry is assumed.

`MoreSingularOn u v U` means `u ≤ v + C`, in the manuscript's direction.
Constants are always real, so these comparisons also make sense at poles.
-/

open Set Filter
open scoped Topology ContDiff

namespace PshLines

section LocalPotentials

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]

/-- Locally the sum of an actual PSH germ and a smooth real function.
This raw local criterion allows the identically negative-infinite germ.-/
def QuasiPlurisubharmonicAt (u : E → EReal) (x : E) : Prop :=
  ∃ (p : E → EReal) (h : E → ℝ), PlurisubharmonicAt p x ∧
    (∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) ∧
    u =ᶠ[𝓝 x] (fun y => p y + (h y : EReal))

/-- Ambient quasi-PSH germs at all points of a set.-/
def QuasiPlurisubharmonicOn (u : E → EReal) (U : Set E) : Prop :=
  ∀ x ∈ U, QuasiPlurisubharmonicAt u x

/-- A nondegenerate local quasi-PSH potential on an open domain: every
neighborhood of each domain point meets its finite locus. Thus no open
component is allowed to be identically negative infinity.-/
def LocalQuasiPshPotentialOn (u : E → EReal) (U : Set E) : Prop :=
  IsOpen U ∧ QuasiPlurisubharmonicOn u U ∧
    ∀ x ∈ U, ∀ V : Set E, IsOpen V → x ∈ V →
      ∃ y ∈ U ∩ V, u y ≠ ⊥

/--
@isnad1 id=quasiplu.1h3v.s5.65f8c4b6969c from=translated src=- shape=a25cc173 vocab=2b32e05b
-/
theorem PlurisubharmonicAt.quasiPlurisubharmonicAt {u : E → EReal} {x : E}
    (hu : PlurisubharmonicAt u x) : QuasiPlurisubharmonicAt u x := by
  exact ⟨u, fun _ => 0, hu, Filter.Eventually.of_forall (fun _ => contDiffAt_const), by simp⟩

/--
@isnad1 id=quasiplu.2h4v.s6.2daf19883ed6 from=translated src=- shape=cdd7449d vocab=b20dcbbe
-/
theorem QuasiPlurisubharmonicAt.congr {u v : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) (huv : u =ᶠ[𝓝 x] v) :
    QuasiPlurisubharmonicAt v x := by
  obtain ⟨p, h, hp, hh, heq⟩ := hu
  exact ⟨p, h, hp, hh, huv.symm.trans heq⟩

/--
@isnad1 id=ne.1h3v.s5.5d2ed5004512 from=translated src=- shape=f59f49dc vocab=6d6b5a6b
-/
theorem QuasiPlurisubharmonicAt.ne_top {u : E → EReal} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) : u x ≠ ⊤ := by
  obtain ⟨p, h, hp, _, heq⟩ := hu
  rw [heq.eq_of_nhds]
  exact EReal.add_ne_top hp.ne_top (EReal.coe_ne_top _)

/--
@isnad1 id=quasiplu.2h4v.s6.3c4ee3d75013 from=translated src=- shape=66be7017 vocab=ee83a75f
-/
theorem QuasiPlurisubharmonicAt.add_smooth {u : E → EReal} {h : E → ℝ} {x : E}
    (hu : QuasiPlurisubharmonicAt u x) (hh : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) :
    QuasiPlurisubharmonicAt (fun y => u y + (h y : EReal)) x := by
  obtain ⟨p, g, hp, hg, heq⟩ := hu
  refine ⟨p, fun y => g y + h y, hp, ?_, ?_⟩
  · filter_upwards [hg, hh] with y hgy hhy
    exact hgy.add hhy
  filter_upwards [heq] with y hy
  rw [hy, EReal.coe_add, add_assoc]

/--
@isnad1 id=quasiplu.2h4v.s5.8aa37fde57a7 from=translated src=- shape=ad507478 vocab=fe4d3f93
-/
theorem QuasiPlurisubharmonicOn.mono {u : E → EReal} {U V : Set E}
    (hu : QuasiPlurisubharmonicOn u U) (hVU : V ⊆ U) :
    QuasiPlurisubharmonicOn u V := fun x hx => hu x (hVU hx)

/--
@isnad1 id=quasiplu.2h4v.s6.6be4a84b33d4 from=translated src=- shape=02ebb940 vocab=d45fa956
-/
theorem QuasiPlurisubharmonicOn.add_smooth {u : E → EReal} {h : E → ℝ} {U : Set E}
    (hu : QuasiPlurisubharmonicOn u U)
    (hh : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ h y) :
    QuasiPlurisubharmonicOn (fun y => u y + (h y : EReal)) U :=
  fun x hx => (hu x hx).add_smooth (hh x hx)

/--
@isnad1 id=localqua.3h4v.s6.902f47cf7c85 from=translated src=- shape=75dc5fc9 vocab=aa7b5340
-/
theorem LocalQuasiPshPotentialOn.mono {u : E → EReal} {U V : Set E}
    (hu : LocalQuasiPshPotentialOn u U) (hV : IsOpen V) (hVU : V ⊆ U) :
    LocalQuasiPshPotentialOn u V := by
  refine ⟨hV, hu.2.1.mono hVU, ?_⟩
  intro x hx W hW hxW
  obtain ⟨y, hy, hfin⟩ := hu.2.2 x (hVU hx) (V ∩ W) (hV.inter hW) ⟨hx, hxW⟩
  exact ⟨y, hy.2, hfin⟩

/--
@isnad1 id=localqua.1h3v.s5.a291ea83f4e8 from=translated src=- shape=8e35346e vocab=c6b9e85b
-/
theorem localQuasiPshPotentialOn_const (c : ℝ) {U : Set E} (hU : IsOpen U) :
    LocalQuasiPshPotentialOn (fun _ : E => (c : EReal)) U := by
  refine ⟨hU, fun x _ => (plurisubharmonicAt_const c (EReal.coe_ne_top c) x).quasiPlurisubharmonicAt, ?_⟩
  exact fun x hx V _ hxV => ⟨x, ⟨hx, hxV⟩, EReal.coe_ne_bot c⟩

end LocalPotentials

section SingularityOrder

variable {X : Type*}

/-- `u` is more singular than `v` on `U`, with one finite additive constant.-/
def MoreSingularOn (u v : X → EReal) (U : Set X) : Prop :=
  ∃ C : ℝ, ∀ x ∈ U, u x ≤ v x + (C : EReal)

/-- Equality of singularity type means two additive comparisons, not equality
of values and not subtraction of potentially infinite values.-/
def SameSingularityTypeOn (u v : X → EReal) (U : Set X) : Prop :=
  MoreSingularOn u v U ∧ MoreSingularOn v u U

/--
@isnad1 id=moresing.1h4v.s5.ccd17cff0f3e from=translated src=- shape=ffd29c06 vocab=4882076a
-/
theorem MoreSingularOn.of_le {u v : X → EReal} {U : Set X}
    (h : ∀ x ∈ U, u x ≤ v x) : MoreSingularOn u v U :=
  ⟨0, by simpa using h⟩

/--
@isnad1 id=moresing.0h3v.s3.16359e854ce9 from=translated src=- shape=aa66c1fa vocab=6df43352
-/
theorem MoreSingularOn.refl (u : X → EReal) (U : Set X) : MoreSingularOn u u U :=
  .of_le (fun _ _ => le_rfl)

/--
@isnad1 id=moresing.2h5v.s5.ca9688fd31d6 from=translated src=- shape=630d3c74 vocab=6df43352
-/
theorem MoreSingularOn.trans {u v w : X → EReal} {U : Set X}
    (huv : MoreSingularOn u v U) (hvw : MoreSingularOn v w U) :
    MoreSingularOn u w U := by
  obtain ⟨C, hC⟩ := huv
  obtain ⟨D, hD⟩ := hvw
  refine ⟨D + C, fun x hx => ?_⟩
  calc
    u x ≤ v x + (C : EReal) := hC x hx
    _ ≤ (w x + (D : EReal)) + (C : EReal) := add_le_add (hD x hx) le_rfl
    _ = w x + ((D + C : ℝ) : EReal) := by rw [EReal.coe_add, add_assoc]

/--
@isnad1 id=moresing.2h5v.s5.89991ef5e795 from=translated src=- shape=f71ecf2f vocab=eeab96fe
-/
theorem MoreSingularOn.mono {u v : X → EReal} {U V : Set X}
    (h : MoreSingularOn u v U) (hVU : V ⊆ U) : MoreSingularOn u v V := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, fun x hx => hC x (hVU hx)⟩

/-- A pole of the less singular potential is necessarily a pole of the more
singular one. No subtraction or `toReal` operation is used.-/
theorem MoreSingularOn.eq_bot_of_eq_bot {u v : X → EReal} {U : Set X}
    (h : MoreSingularOn u v U) {x : X} (hx : x ∈ U) (hv : v x = ⊥) : u x = ⊥ := by
  obtain ⟨C, hC⟩ := h
  have h := hC x hx
  simpa [hv] using h

/--
@isnad1 id=samesing.0h3v.s3.d2da801bd3bb from=translated src=- shape=aa66c1fa vocab=c2dc4759
-/
theorem SameSingularityTypeOn.refl (u : X → EReal) (U : Set X) :
    SameSingularityTypeOn u u U := ⟨.refl u U, .refl u U⟩

/--
@isnad1 id=samesing.1h4v.s4.9dddf01d455f from=translated src=- shape=001343d5 vocab=c2dc4759
-/
theorem SameSingularityTypeOn.symm {u v : X → EReal} {U : Set X}
    (h : SameSingularityTypeOn u v U) : SameSingularityTypeOn v u U := ⟨h.2, h.1⟩

/--
@isnad1 id=samesing.2h5v.s5.255760153642 from=translated src=- shape=630d3c74 vocab=c2dc4759
-/
theorem SameSingularityTypeOn.trans {u v w : X → EReal} {U : Set X}
    (huv : SameSingularityTypeOn u v U) (hvw : SameSingularityTypeOn v w U) :
    SameSingularityTypeOn u w U := ⟨huv.1.trans hvw.1, hvw.2.trans huv.2⟩

/--
@isnad1 id=samesing.0h4v.s5.7b4e41bfe009 from=translated src=- shape=ec845514 vocab=1bc476c1
-/
theorem sameSingularityTypeOn_add_const (u : X → EReal) (U : Set X) (c : ℝ) :
    SameSingularityTypeOn (fun x => u x + (c : EReal)) u U := by
  refine ⟨⟨c, fun _ _ => le_rfl⟩, ⟨-c, fun x _ => ?_⟩⟩
  rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]

variable [TopologicalSpace X]

/-- Additive singularity comparison on some neighborhood, with one real constant.-/
def MoreSingularAt (u v : X → EReal) (x : X) : Prop :=
  ∃ C : ℝ, ∀ᶠ y in 𝓝 x, u y ≤ v y + (C : EReal)

/--
@isnad1 id=moresing.0h3v.s4.e0469735a94f from=translated src=- shape=b1d49a06 vocab=b03ea485
-/
theorem MoreSingularAt.refl (u : X → EReal) (x : X) : MoreSingularAt u u x :=
  ⟨0, Filter.Eventually.of_forall (fun _ => by simp)⟩

/--
@isnad1 id=moresing.2h5v.s5.75a7a4cba1bf from=translated src=- shape=d41b1df9 vocab=b03ea485
-/
theorem MoreSingularAt.trans {u v w : X → EReal} {x : X}
    (huv : MoreSingularAt u v x) (hvw : MoreSingularAt v w x) :
    MoreSingularAt u w x := by
  obtain ⟨C, hC⟩ := huv
  obtain ⟨D, hD⟩ := hvw
  refine ⟨D + C, ?_⟩
  filter_upwards [hC, hD] with y hyC hyD
  simpa [EReal.coe_add, add_assoc] using hyC.trans (add_le_add hyD (le_rfl : (C : EReal) ≤ C))

/--
@isnad1 id=moresing.2h5v.s5.1048a412702b from=translated src=- shape=3dbe9944 vocab=89d4ef0b
-/
theorem MoreSingularOn.moreSingularAt {u v : X → EReal} {U : Set X}
    (h : MoreSingularOn u v U) {x : X} (hU : U ∈ 𝓝 x) : MoreSingularAt u v x := by
  obtain ⟨C, hC⟩ := h
  exact ⟨C, Filter.eventually_of_mem hU (fun y hy => hC y hy)⟩

omit [TopologicalSpace X] in
/-- The global branch lies below its actual collar maximum.
@isnad1 id=moresing.0h5v.s4.0e632533c7f6 from=translated src=- shape=bf7cbcd3 vocab=86d0b2eb
-/
theorem moreSingularOn_gluedMax (U V : Set X) (u v : X → EReal) :
    MoreSingularOn v (gluedMax U u v) V := by
  apply MoreSingularOn.of_le
  intro x _
  classical
  by_cases hx : x ∈ U
  · rw [gluedMax_eq_max hx]
    exact le_max_right _ _
  · simp [gluedMax, hx]

end SingularityOrder

end PshLines
