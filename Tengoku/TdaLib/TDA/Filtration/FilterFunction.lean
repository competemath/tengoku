import Tengoku.TdaLib.TDA.Simplicial.Bridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Face-value sublevel filtrations

A `FilterFunction` assigns an ordered value to each nonempty face of a preabstract
simplicial complex. Its sublevel at `r` contains exactly the faces whose values are at most `r`;
the resulting complexes form a support-aware simplicial filtration.

## Source and convention digest

`TDA.Simplicial.TotalFace` is the existing subtype of faces from
`TDA/Simplicial/Bridge.lean` (blob `a811965673ef1d3da54efe0aef768bcbf3ae1d50`), with no
ambient vertex-order parameter. The filtration, its support, and singleton-face fixtures reuse
`TDA/Filtration/Basic.lean` (blob `77a63f98ba6e7c3cbfe6fc92f6a51014643ef32f`). Face closure and
the absence of an empty face follow mathlib's `PreAbstractSimplicialComplex` in
`Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`, pinned at
`0df444a360eaa60ab8c11dca51a86af692955474`. In particular, a subface is admitted only when it
is nonempty and is a subset of an existing face. The construction is a direct library extension;
it does not assert a translation of an external persistence theorem.
-/

universe u w

namespace TDA.Filtration

variable {V : Type u} {α : Type w}

/-- A monotone value assignment on the faces of a preabstract simplicial complex.-/
structure FilterFunction (K : PreAbstractSimplicialComplex V)
    (α : Type w) [LinearOrder α] where
  value : TDA.Simplicial.TotalFace K → α
  mono : ∀ {τ σ : TDA.Simplicial.TotalFace K},
    τ.val ⊆ σ.val → value τ ≤ value σ

namespace FilterFunction

variable [LinearOrder α] {K : PreAbstractSimplicialComplex V}

/-- The subcomplex of faces whose assigned value is at most `r`.-/
def sublevel (f : FilterFunction K α) (r : α) :
    PreAbstractSimplicialComplex V where
  faces := {s | ∃ hs : s ∈ K, f.value ⟨s, hs⟩ ≤ r}
  isRelLowerSet_faces := by
    intro s hs
    rcases hs with ⟨hs, hsr⟩
    constructor
    · exact (K.isRelLowerSet_faces hs).1
    · intro t hts ht
      have htK : t ∈ K := (K.isRelLowerSet_faces hs).2 hts ht
      refine ⟨htK, ?_⟩
      exact (f.mono (τ := ⟨t, htK⟩) (σ := ⟨s, hs⟩) hts).trans hsr

/-- Membership in a sublevel means being a face with value at most the threshold.
@isnad1 id=iff.0h6v.s6.1d128e442db8 from=translated src=- shape=99480994 vocab=9906307f
-/
theorem mem_sublevel_iff (f : FilterFunction K α) (r : α) (s : Finset V) :
    s ∈ f.sublevel r ↔ ∃ hs : s ∈ K, f.value ⟨s, hs⟩ ≤ r := Iff.rfl

/-- For a face, sublevel membership is equivalent to its value bound.
@isnad1 id=iff.0h6v.s6.4cabc0fb5ee4 from=translated src=- shape=a401c280 vocab=ce261d23
-/
theorem mem_sublevel_iff_of_mem (f : FilterFunction K α) (r : α)
    (s : TDA.Simplicial.TotalFace K) :
    s.val ∈ f.sublevel r ↔ f.value s ≤ r := by
  rw [mem_sublevel_iff]
  constructor
  · rintro ⟨hs, h⟩
    have he : (⟨s.val, hs⟩ : TDA.Simplicial.TotalFace K) = s := Subtype.ext rfl
    simpa only [he] using h
  · intro h
    exact ⟨s.property, h⟩

/-- Every sublevel is a subcomplex of the original complex.
@isnad1 id=le.0h5v.s4.eb25dcce8b5c from=translated src=- shape=4599dcba vocab=4e8659b6
-/
theorem sublevel_le (f : FilterFunction K α) (r : α) :
    f.sublevel r ≤ K := by
  intro s hs
  exact (mem_sublevel_iff f r s).mp hs |>.1

/-- Increasing the threshold can only add faces.
@isnad1 id=monotone.0h4v.s5.454b85fcb4ea from=translated src=- shape=99e16ea2 vocab=7b0dc5d1
-/
theorem sublevel_mono (f : FilterFunction K α) : Monotone f.sublevel := by
  intro r q hrq s hs
  rcases (mem_sublevel_iff f r s).mp hs with ⟨hsK, hsr⟩
  exact (mem_sublevel_iff f q s).mpr ⟨hsK, hsr.trans hrq⟩

/-- The sublevels, indexed by the ordered grade type, as a simplicial filtration.-/
def sublevelFiltration (f : FilterFunction K α) : SimplicialFiltration α V where
  toFun := f.sublevel
  monotone' := f.sublevel_mono

/-- Evaluation of the sublevel filtration at `r` is the sublevel at `r`.
@isnad1 id=eq.0h5v.s6.720c5693436b from=translated src=- shape=4de136f9 vocab=23e5514e
-/
theorem sublevelFiltration_apply (f : FilterFunction K α) (r : α) :
    f.sublevelFiltration r = f.sublevel r := rfl

/-- A vertex is supported at `r` exactly when its singleton is a face of value at most
`r`; an absent singleton is never inserted by the sublevel construction.
@isnad1 id=iff.0h6v.s7.a428ff705e68 from=translated src=- shape=4cd85128 vocab=562c049f
-/
theorem mem_support_sublevelFiltration_iff
    (f : FilterFunction K α) (r : α) (v : V) :
    v ∈ support f.sublevelFiltration r ↔
      ∃ hs : ({v} : Finset V) ∈ K, f.value ⟨{v}, hs⟩ ≤ r := by
  exact mem_sublevel_iff f r {v}

/-- If every face has value at most `r`, the sublevel is the original complex.
@isnad1 id=eq.1h5v.s5.f2a94b2d993a from=translated src=- shape=ace23e14 vocab=77cbf202
-/
theorem sublevel_eq_self_of_forall_le (f : FilterFunction K α) (r : α)
    (h : ∀ s : TDA.Simplicial.TotalFace K, f.value s ≤ r) :
    f.sublevel r = K := by
  apply le_antisymm (f.sublevel_le r)
  intro s hs
  exact (mem_sublevel_iff f r s).mpr ⟨hs, h ⟨s, hs⟩⟩

/-- If `r` is strictly below every face value, the sublevel is bottom.
@isnad1 id=eq.1h5v.s5.8ad66d959347 from=translated src=- shape=c8d3727f vocab=eb7dda82
-/
theorem sublevel_eq_bot_of_forall_lt (f : FilterFunction K α) (r : α)
    (h : ∀ s : TDA.Simplicial.TotalFace K, r < f.value s) :
    f.sublevel r = ⊥ := by
  apply le_antisymm
  · intro s hs
    rcases (mem_sublevel_iff f r s).mp hs with ⟨hsK, hsr⟩
    exact ((not_lt_of_ge hsr) (h ⟨s, hsK⟩)).elim
  · exact bot_le

/-- Every sublevel of the empty complex is bottom, without choosing a face value.
@isnad1 id=eq.0h4v.s5.52fb0da7dbcf from=translated src=- shape=b859934a vocab=a9381e1b
-/
theorem sublevel_bot (f : FilterFunction (⊥ : PreAbstractSimplicialComplex V) α)
    (r : α) : f.sublevel r = ⊥ := by
  apply le_antisymm
  · exact (f.sublevel_le r).trans le_rfl
  · exact bot_le

end FilterFunction
end TDA.Filtration
