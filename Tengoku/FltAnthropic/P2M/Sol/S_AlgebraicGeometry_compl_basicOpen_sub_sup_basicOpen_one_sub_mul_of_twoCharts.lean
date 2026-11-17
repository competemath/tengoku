import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_compl_basicOpen_sub_sup_basicOpen_one_sub_mul_of_twoCharts

set_option autoImplicit false

universe u

open _root_.CategoryTheory open _root_.CategoryTheory.Limits open _root_.Opposite open _root_.TopologicalSpace open _root_.AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.mem_basicOpen RingedSpace.isUnit_res_basicOpen Scheme isAffineOpen_of_isAffineOpen_basicOpen Scheme.basicOpen_mul IsAffineOpen RingedSpace)
namespace TwoChartsJne
open _root_.AlgebraicGeometry

variable {X : Scheme.{u}}

abbrev res {U V : X.Opens} (h : V ≤ U) : Γ(X, U) →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE h).op).hom

/--
@isnad1 id=eq.2h5v.s13.4c3cc5840d74 from=translated src=- shape=17fbc4cf vocab=43c1ca28
-/
theorem res_res {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  change (X.presheaf.map (homOfLE h₁).op ≫ X.presheaf.map (homOfLE h₂).op).hom x = _
  rw [← Functor.map_comp]
  rfl

/--
@isnad1 id=eq.1h4v.s11.39bb34c4e720 from=translated src=- shape=b2f5f901 vocab=574ff941
-/
theorem basicOpen_res' {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    X.basicOpen (res h x) = V ⊓ X.basicOpen x :=
  X.basicOpen_res x (homOfLE h).op

section Main

variable (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hf : U ⊓ V = X.basicOpen f) (hg : U ⊓ V = X.basicOpen g)
    (hfg : res (inf_le_left : U ⊓ V ≤ U) f * res (inf_le_right : U ⊓ V ≤ V) g = 1)
    (hUV : U ⊔ V = ⊤)
    (s : Γ(X, ⊤))

include hfg in

/--
@isnad1 id=eq.1h6v.s15.2d6c928e9ab8 from=translated src=- shape=d95d277f vocab=08d763cb
-/
theorem res_one_sub_mul :
    res (inf_le_right : U ⊓ V ≤ V) (1 - res (le_top : V ≤ ⊤) s * g) =
      res (inf_le_left : U ⊓ V ≤ U) (f - res (le_top : U ≤ ⊤) s) * res (inf_le_right : U ⊓ V ≤ V) g := by
  rw [map_sub, map_one, map_mul, map_sub, sub_mul, hfg, res_res, res_res]

include hg hfg in

/--
@isnad1 id=eq.2h6v.s14.00c8c4ddd84a from=translated src=- shape=c244c465 vocab=e53e905a
-/
theorem inf_basicOpen_eq :
    (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) =
      (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
  calc (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g)
        = X.basicOpen (res (inf_le_right : U ⊓ V ≤ V) (1 - res (le_top : V ≤ ⊤) s * g)) :=
          (basicOpen_res' _ _).symm
    _ = X.basicOpen (res (inf_le_left : U ⊓ V ≤ U) (f - res (le_top : U ≤ ⊤) s)) ⊓
          X.basicOpen (res (inf_le_right : U ⊓ V ≤ V) g) := by
          rw [res_one_sub_mul U V f g hfg s, Scheme.basicOpen_mul]
    _ = ((U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s)) ⊓ ((U ⊓ V) ⊓ (U ⊓ V)) := by
          rw [basicOpen_res', basicOpen_res', ← hg]
    _ = (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
          rw [inf_idem]
          exact inf_eq_left.mpr inf_le_left

include hg hfg in

/--
@isnad1 id=eq.2h6v.s14.199771d0723e from=translated src=- shape=6e8c074e vocab=e53e905a
-/
theorem basicOpen_inf_basicOpen_eq :
    X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) =
      (U ⊓ V) ⊓ X.basicOpen (f - res (le_top : U ≤ ⊤) s) := by
  have key := inf_basicOpen_eq U V f g hg hfg s
  apply le_antisymm
  · refine le_inf (le_inf ?_ ?_) inf_le_left
    · exact inf_le_left.trans (X.basicOpen_le _)
    · exact inf_le_right.trans (X.basicOpen_le _)
  · refine le_inf inf_le_right ?_
    rw [← key]; exact inf_le_right

include hg in

/--
@isnad1 id=mem.3h6v.s12.1505a2fc19ce from=translated src=- shape=d82063cc vocab=3780577c
-/
theorem mem_basicOpen_one_sub_mul {x : X} (hxV : x ∈ V) (hxU : x ∉ U) :
    x ∈ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) := by
  rw [Scheme.mem_basicOpen _ _ _ hxV, map_sub, map_one, map_mul]
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  rw [← IsLocalRing.mem_maximalIdeal]
  apply Ideal.mul_mem_left
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← Scheme.mem_basicOpen _ _ _ hxV, ← hg]
  exact fun h => hxU h.1

include hg hfg hUV in

/--
@isnad1 id=eq.3h6v.s14.a6e74c3e2329 from=translated src=- shape=c16c88ae vocab=0ce06ad3
-/
theorem compl_sup_eq :
    ((X.basicOpen (f - res (le_top : U ≤ ⊤) s) ⊔ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) : X.Opens) : Set X)ᶜ =
      (U : Set X) ∩ (X.basicOpen (f - res (le_top : U ≤ ⊤) s) : Set X)ᶜ := by
  have hAB := basicOpen_inf_basicOpen_eq U V f g hg hfg s
  ext x
  simp only [Opens.coe_sup, Set.compl_union, Set.mem_inter_iff, Set.mem_compl_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hA, hB⟩
    refine ⟨?_, hA⟩
    by_contra hxU
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [← hUV] at hx
    rcases (show x ∈ (U : Set X) ∪ (V : Set X) by exact hx) with h | h
    · exact hxU h
    · exact hB (mem_basicOpen_one_sub_mul U V g hg s h hxU)
  · rintro ⟨hxU, hA⟩
    refine ⟨hA, fun hB => hA ?_⟩
    have key := inf_basicOpen_eq U V f g hg hfg s
    have : x ∈ (U ⊓ V) ⊓ X.basicOpen (1 - res (le_top : V ≤ ⊤) s * g) := ⟨⟨hxU, X.basicOpen_le _ hB⟩, hB⟩
    rw [key] at this
    exact this.2

end Main

end AlgebraicGeometry.TwoChartsJne

end

/--
@isnad1 id=eq.3h6v.s14.b8431006af26 from=translated src=- shape=9a7cb16a vocab=3a6278f5
-/
theorem solution
    {X : Scheme.{u}} (U V : X.Opens)
    (f : Γ(X, U)) (g : Γ(X, V))
    (hg : U ⊓ V = X.basicOpen g)
    (hfg : (X.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (X.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hUV : U ⊔ V = ⊤) (s : Γ(X, ⊤)) :
    ((X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) ⊔
        X.basicOpen (1 - (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s * g) : X.Opens) : Set X)ᶜ =
      (U : Set X) ∩ (X.basicOpen (f - (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom s) : Set X)ᶜ :=
  AlgebraicGeometry.TwoChartsJne.compl_sup_eq U V f g hg hfg hUV s
