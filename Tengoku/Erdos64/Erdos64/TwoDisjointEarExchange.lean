import Tengoku.Erdos64.Erdos64.DyadicPathEar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The simplicity part of fresh-ear rerouting needs no lower bound on the
length of either route. If both routes have length at most one, they coincide.
@isnad1 id=ispath.4h10v.s7.4c9a3afae464 from=translated src=- shape=1b1d2560 vocab=594048f1
-/
theorem terminal_path_reroute_isPath_of_fresh_ear
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y) :
    ((pre.append ear).append suffix).IsPath := by
  by_cases hlong : 1 < segment.length ∨ 1 < ear.length
  · exact (terminal_path_reroute_of_fresh_ear pre segment suffix ear
      horiginal hear hxy hfresh hlong).1
  · have heq : ear = segment :=
      SimpleGraph.Walk.eq_of_length_le_one (by omega) (by omega)
    simpa only [heq] using horiginal

/-- Two ordered, internally disjoint fresh ears can be exchanged simultaneously.
The middle walk may be nil, so the two replaced segments may share an endpoint.
The mutual-intersection hypothesis allows this shared attachment but excludes
shared ear interiors. No parity or extremality condition is imposed on the
intermediate path obtained after the first replacement.
@isnad1 id=and.8h15v.s8.464e2ceb02ee from=translated src=- shape=26f1633b vocab=5b4a79ad
-/
theorem terminal_path_reroute_of_two_disjoint_fresh_ears
    {V : Type u} {G : SimpleGraph V} {a b x₁ y₁ x₂ y₂ : V}
    (pre : G.Walk a x₁) (segment₁ : G.Walk x₁ y₁)
    (middle : G.Walk y₁ x₂) (segment₂ : G.Walk x₂ y₂)
    (suffix : G.Walk y₂ b)
    (ear₁ : G.Walk x₁ y₁) (ear₂ : G.Walk x₂ y₂)
    (horiginal :
      ((((pre.append segment₁).append middle).append segment₂).append suffix).IsPath)
    (hear₁ : ear₁.IsPath) (hear₂ : ear₂.IsPath)
    (hxy₁ : x₁ ≠ y₁) (hxy₂ : x₂ ≠ y₂)
    (hfresh₁ : ∀ z, z ∈ ear₁.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support →
      z = x₁ ∨ z = y₁)
    (hfresh₂ : ∀ z, z ∈ ear₂.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support →
      z = x₂ ∨ z = y₂)
    (hdisjoint : ∀ z, z ∈ ear₁.support → z ∈ ear₂.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support) :
    ((((pre.append ear₁).append middle).append ear₂).append suffix).IsPath ∧
      ((((pre.append ear₁).append middle).append ear₂).append suffix).length +
          (segment₁.length + segment₂.length) =
        ((((pre.append segment₁).append middle).append segment₂).append suffix).length +
          (ear₁.length + ear₂.length) := by
  have horiginal' :
      ((pre.append segment₁).append ((middle.append segment₂).append suffix)).IsPath := by
    simpa only [SimpleGraph.Walk.append_assoc] using horiginal
  have hfresh₁' : ∀ z, z ∈ ear₁.support →
      z ∈ ((pre.append segment₁).append ((middle.append segment₂).append suffix)).support →
      z = x₁ ∨ z = y₁ := by
    simpa only [SimpleGraph.Walk.append_assoc] using hfresh₁
  have hfirst :
      ((((pre.append ear₁).append middle).append segment₂).append suffix).IsPath := by
    simpa only [SimpleGraph.Walk.append_assoc] using
      terminal_path_reroute_isPath_of_fresh_ear pre segment₁
        ((middle.append segment₂).append suffix) ear₁ horiginal' hear₁ hxy₁ hfresh₁'
  have hfresh₂' : ∀ z, z ∈ ear₂.support →
      z ∈ ((((pre.append ear₁).append middle).append segment₂).append suffix).support →
      z = x₂ ∨ z = y₂ := by
    intro z hzear₂ hzfirst
    apply hfresh₂ z hzear₂
    simp only [SimpleGraph.Walk.mem_support_append_iff] at hzfirst ⊢
    rcases hzfirst with (((hzpre | hzear₁) | hzmiddle) | hzsegment₂) | hzsuffix
    · exact Or.inl (Or.inl (Or.inl (Or.inl hzpre)))
    · have hz := hdisjoint z hzear₁ hzear₂
      simpa only [SimpleGraph.Walk.mem_support_append_iff] using hz
    · exact Or.inl (Or.inl (Or.inr hzmiddle))
    · exact Or.inl (Or.inr hzsegment₂)
    · exact Or.inr hzsuffix
  refine ⟨terminal_path_reroute_isPath_of_fresh_ear
    ((pre.append ear₁).append middle) segment₂ suffix ear₂
    hfirst hear₂ hxy₂ hfresh₂', ?_⟩
  simp only [SimpleGraph.Walk.length_append]
  omega

/-- A balanced pair of disjoint ear replacements stays on the same path-length
level, even if either individual replacement changes length or parity. This
only consumes a specified pair of ears; it does not assert that one exists.
@isnad1 id=and.9h15v.s8.1376d69d4945 from=translated src=- shape=0556c34b vocab=5b4a79ad
-/
theorem terminal_path_equal_length_exchange_of_two_disjoint_fresh_ears
    {V : Type u} {G : SimpleGraph V} {a b x₁ y₁ x₂ y₂ : V}
    (pre : G.Walk a x₁) (segment₁ : G.Walk x₁ y₁)
    (middle : G.Walk y₁ x₂) (segment₂ : G.Walk x₂ y₂)
    (suffix : G.Walk y₂ b)
    (ear₁ : G.Walk x₁ y₁) (ear₂ : G.Walk x₂ y₂)
    (horiginal :
      ((((pre.append segment₁).append middle).append segment₂).append suffix).IsPath)
    (hear₁ : ear₁.IsPath) (hear₂ : ear₂.IsPath)
    (hxy₁ : x₁ ≠ y₁) (hxy₂ : x₂ ≠ y₂)
    (hfresh₁ : ∀ z, z ∈ ear₁.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support →
      z = x₁ ∨ z = y₁)
    (hfresh₂ : ∀ z, z ∈ ear₂.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support →
      z = x₂ ∨ z = y₂)
    (hdisjoint : ∀ z, z ∈ ear₁.support → z ∈ ear₂.support →
      z ∈ ((((pre.append segment₁).append middle).append segment₂).append suffix).support)
    (hbalance : ear₁.length + ear₂.length = segment₁.length + segment₂.length) :
    ((((pre.append ear₁).append middle).append ear₂).append suffix).IsPath ∧
      ((((pre.append ear₁).append middle).append ear₂).append suffix).length =
        ((((pre.append segment₁).append middle).append segment₂).append suffix).length := by
  obtain ⟨hpath, hlength⟩ := terminal_path_reroute_of_two_disjoint_fresh_ears
    pre segment₁ middle segment₂ suffix ear₁ ear₂ horiginal hear₁ hear₂
    hxy₁ hxy₂ hfresh₁ hfresh₂ hdisjoint
  exact ⟨hpath, by omega⟩

end Erdos64
