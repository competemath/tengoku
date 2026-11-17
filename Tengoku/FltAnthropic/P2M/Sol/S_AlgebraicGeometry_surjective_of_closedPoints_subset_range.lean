import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_surjective_of_closedPoints_subset_range.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_surjective_of_closedPoints_subset_range

set_option autoImplicit false

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.AlgebraicGeometry open _root_.Topology

universe u

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Surjective Scheme.Hom Scheme.Hom.isLocallyConstructible_image QuasiCompact Scheme LocallyOfFinitePresentation)
namespace SurjClosedPoints
open _root_.AlgebraicGeometry

section TopLemmas

variable {X : Type*} [TopologicalSpace X]

def FinLC (s : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ z ∈ S, IsLocallyClosed z) ∧ s = ⋃₀ S

/--
@isnad1 id=finlc.1h2v.s4.e06e9cc20807 from=translated src=- shape=93e860ac vocab=13be6b2a
-/
theorem FinLC.of_isLocallyClosed {s : Set X} (hs : IsLocallyClosed s) : FinLC s :=
  ⟨{s}, Set.finite_singleton s, by simpa using hs, by simp⟩

/--
@isnad1 id=finlc.2h3v.s4.6147f2bf1aaa from=translated src=- shape=0540dca0 vocab=2802bdfc
-/
theorem FinLC.union {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∪ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨S ∪ T, hSf.union hTf, ?_, (Set.sUnion_union S T).symm⟩
  rintro z (hz | hz)
  exacts [hSl z hz, hTl z hz]

/--
@isnad1 id=finlc.2h3v.s4.e7fb3b6d1ac7 from=translated src=- shape=0540dca0 vocab=e1e77b2c
-/
theorem FinLC.inter {s t : Set X} (hs : FinLC s) (ht : FinLC t) : FinLC (s ∩ t) := by
  obtain ⟨S, hSf, hSl, rfl⟩ := hs
  obtain ⟨T, hTf, hTl, rfl⟩ := ht
  refine ⟨Set.image2 (· ∩ ·) S T, hSf.image2 _ hTf, ?_, ?_⟩
  · rintro z ⟨a, ha, b, hb, rfl⟩
    exact (hSl a ha).inter (hTl b hb)
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image2, exists_exists_and_exists_and_eq_and]
    constructor
    · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
      exact ⟨a, ha, b, hb, hxa, hxb⟩
    · rintro ⟨a, ha, b, hb, hxa, hxb⟩
      exact ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩

/--
@isnad1 id=and.1h2v.s4.11af9c947408 from=translated src=- shape=d664e1b8 vocab=aba5b826
-/
theorem finLC_and_compl_of_isConstructible {s : Set X} (hs : IsConstructible s) :
    FinLC s ∧ FinLC sᶜ := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    exact ⟨.of_isLocallyClosed hU.isLocallyClosed, .of_isLocallyClosed hU.isClosed_compl.isLocallyClosed⟩
  | union s _ t _ hs ht =>
    refine ⟨hs.1.union ht.1, ?_⟩
    rw [Set.compl_union]
    exact hs.2.inter ht.2
  | compl s _ hs =>
    rw [compl_compl]
    exact ⟨hs.2, hs.1⟩

/--
@isnad1 id=nonempty.2h2v.s5.270f77b53e84 from=translated src=- shape=81037f4a vocab=2bc9dec0
-/
theorem nonempty_inter_closedPoints_of_isConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨S, -, hSl, rfl⟩ := (finLC_and_compl_of_isConstructible hs).1
  obtain ⟨x, z, hz, hxz⟩ := hne
  obtain ⟨y, hyz, hyc⟩ := nonempty_inter_closedPoints ⟨x, hxz⟩ (hSl z hz)
  exact ⟨y, ⟨z, hz, hyz⟩, hyc⟩

/--
@isnad1 id=nonempty.2h2v.s5.ff3cedae0f37 from=translated src=- shape=81037f4a vocab=d479b18b
-/
theorem nonempty_inter_closedPoints_of_isLocallyConstructible [JacobsonSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  haveI : JacobsonSpace U := .of_isOpenEmbedding hUo.isOpenEmbedding_subtypeVal
  have hxU : x ∈ U := mem_of_mem_nhds hUx
  obtain ⟨y, hys, hyc⟩ :=
    nonempty_inter_closedPoints_of_isConstructible hUc ⟨⟨x, hxU⟩, show (⟨x, hxU⟩ : U).1 ∈ s from hx⟩
  refine ⟨y.1, hys, ?_⟩
  have := hUo.isOpenEmbedding_subtypeVal.preimage_closedPoints (X := U) (Y := X)
  rw [← this] at hyc
  exact hyc

end TopLemmas

/--
@isnad1 id=islocall.1h2v.s4.80ae02b0adc7 from=translated src=- shape=a3b738d9 vocab=118d1026
-/
theorem isLocallyConstructible_compl {X : Type*} [TopologicalSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) : IsLocallyConstructible sᶜ := by
  intro x
  obtain ⟨U, hUx, hUo, hUc⟩ := hs x
  refine ⟨U, hUx, hUo, ?_⟩
  have e : (Subtype.val ⁻¹' sᶜ : Set U) = (Subtype.val ⁻¹' s : Set U)ᶜ := by
    ext y; simp
  rw [e]
  exact hUc.compl

/--
@isnad1 id=surjecti.1h3v.s8.012091249d80 from=translated src=- shape=b65da572 vocab=25ab450f
-/
theorem surjective_of_closedPoints_subset_range {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hlc : IsLocallyConstructible (Set.range f.base) := by
    simpa [Set.image_univ] using f.isLocallyConstructible_image (s := Set.univ) (by simp)
  have hne : ((Set.range f.base)ᶜ).Nonempty := ⟨y, hy⟩
  obtain ⟨z, hz, hzc⟩ :=
    nonempty_inter_closedPoints_of_isLocallyConstructible (isLocallyConstructible_compl hlc) hne
  exact hz (h hzc)

end AlgebraicGeometry.SurjClosedPoints

open AlgebraicGeometry.SurjClosedPoints in
/--
@isnad1 id=surjecti.1h3v.s8.012091249d80 from=translated src=- shape=b65da572 vocab=25ab450f
-/
theorem solution {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [JacobsonSpace Y]
    (h : closedPoints Y ⊆ Set.range f.base) : Surjective f :=
  surjective_of_closedPoints_subset_range f h
