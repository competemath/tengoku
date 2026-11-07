/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Tnlean.TNLean.PEPS.TorusTranslation
import Tengoku.Tnlean.TNLean.PEPS.IsoTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Translation-invariant PEPS tensors on the torus

A PEPS on the discrete torus (`TNLean/PEPS/TorusLatticeGraph.lean`) is
**translation invariant** when it is fixed by transport along every translation
automorphism: `A.transport (translate a b) = A` for all coordinate offsets
`(a, b)`.  This is the faithful formalization of the source's setting, where one
tensor is repeated at every site of a lattice on which translation is a symmetry
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`).

Translation invariance has two consequences used by the source's gauge reduction.
First, the state coefficient is invariant under the precomposed translation of the
physical configuration (`stateCoeff_translationInvariant`).  Second, the bond
dimension at any edge equals the bond dimension at every translate of that edge
(`bondDim_translateEdge_of_translationInvariant`); since the translations act
transitively on each orientation class — every horizontal edge is the translate of
every other, and likewise for vertical edges — this is the constant-bond content
that makes the reduction to one horizontal and one vertical matrix well-defined.  The
transitivity is supported by the normal-form characterization
`isHorizontalTorusEdge_eq_rightEdge` writing each horizontal edge as the right edge
of its left endpoint; the full orientation-class constancy is `TorusUniformBondDim`
below, recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`, remaining
obligation 6.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- A PEPS tensor on the torus is **translation invariant** when it is fixed by
transport along every translation automorphism.  This is the faithful statement of
the source's setting: one tensor repeated at every site, with translation a
symmetry of the network.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1452 of
`Papers/1804.04964/paper_normal.tex`.-/
def IsTorusTranslationInvariant (A : Tensor (torusGraph width height) d) : Prop :=
  ∀ (a : ZMod width) (b : ZMod height), A.transport (translate a b) = A

/-- The edge action of the translation `(a, b)` coincides with the edge action of
the translation automorphism `translate a b`: both push the endpoints through the
translation and reorder them into the `Edge` convention.
@isnad1 id=eq.0h5v.s7.6971d9abba30 from=translated src=- shape=c9fdfc1c vocab=d10735c3
-/
theorem translateEdge_eq_map (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    translateEdge a b e = Edge.map (translate a b) e :=
  rfl

/-- The state coefficient of a translation-invariant tensor is invariant under the
translation of the physical configuration: shifting `σ` by a translation leaves the
coefficient unchanged.  This is the physical-level statement of translation
invariance, obtained from `stateCoeff_transport` and the defining fixed-point
equation.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h7v.s7.c3c0394bb7ac from=translated src=- shape=301a9c2e vocab=aa01c07f
-/
theorem stateCoeff_translationInvariant {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    (σ : TorusVertex width height → Fin d) :
    stateCoeff A (fun v => σ (translate a b v)) = stateCoeff A σ := by
  have h := hA a b
  calc stateCoeff A (fun v => σ (translate a b v))
      = stateCoeff (A.transport (translate a b)) σ := (stateCoeff_transport A _ σ).symm
    _ = stateCoeff A σ := by rw [h]

/-! ### Constant bond dimension on each orientation class

A translation-invariant tensor has the same bond dimension on all horizontal edges
and the same bond dimension on all vertical edges.  The translation moving one
horizontal edge to another carries the bond dimension across, so within each
orientation class the bond dimension is constant.  This is the constant-bond
consequence of translation invariance, recorded below as `TorusUniformBondDim`. -/

/-- The bond dimension of a translation-invariant tensor at the translate of an
edge equals the bond dimension at the original edge.  Transport invariance gives
`A.bondDim (translateEdge a b e) = A.bondDim e` after reindexing through the edge
action.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h7v.s7.bdfd864d0cf4 from=translated src=- shape=b0ec50ef vocab=d83bc5aa
-/
theorem bondDim_translateEdge_of_translationInvariant
    {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    (e : Edge (torusGraph width height)) :
    A.bondDim (translateEdge a b e) = A.bondDim e := by
  have h := hA a b
  have hb : (A.transport (translate a b)).bondDim (translateEdge a b e) =
      A.bondDim (translateEdge a b e) := by rw [h]
  rw [Tensor.transport_bondDim] at hb
  rw [← hb]
  congr 1
  -- Edge.map (translate a b).symm (translateEdge a b e) = e
  change Edge.map (translate a b).symm (Edge.map (translate a b) e) = e
  exact Edge.map_symm_map (translate a b) e

/-! ### Normal form of horizontal and vertical torus edges

Each horizontal edge is the right edge of a well-defined left endpoint `p`, the
edge with unordered endpoints `p` and `p + (1, 0)`.  The lexicographic order may
place either of these first (the coordinate value wraps around the torus), so the
left endpoint is read from whichever incidence carries the `+1` step.  This normal
form gives the transitivity of the translation action on the horizontal class:
translating the left endpoint of one horizontal edge to the left
endpoint of another carries the whole edge across. -/

/-- The horizontal torus edge with left endpoint `p`, i.e. the edge on the adjacent
pair `(p, p + (1, 0))`.-/
def torusRightEdge (p : TorusVertex width height) : Edge (torusGraph width height) :=
  Edge.ofAdj (torusGraph_adj_right p.1 p.2)

/-- The vertical torus edge with lower endpoint `p`, i.e. the edge on the adjacent
pair `(p, p + (0, 1))`.-/
def torusUpEdge (p : TorusVertex width height) : Edge (torusGraph width height) :=
  Edge.ofAdj (torusGraph_adj_up p.1 p.2)

/-- Every horizontal torus edge is the right edge of a left endpoint `p`: its
unordered endpoints are `p` and `p + (1, 0)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=ex.1h3v.s6.e95fbdff814f from=translated src=- shape=7eb7f725 vocab=4c1a9d43
-/
theorem isHorizontalTorusEdge_eq_rightEdge {e : Edge (torusGraph width height)}
    (he : IsHorizontalTorusEdge e) :
    ∃ p : TorusVertex width height, e = torusRightEdge p := by
  have hc : e.1.1.2 = e.1.2.2 := he.1
  rcases he.2 with h2 | h2
  · refine ⟨e.1.1, ?_⟩
    rw [torusRightEdge]
    symm
    apply Edge.ofAdj_eq_of_endpoints
    exact Or.inl ⟨rfl, Prod.ext (by exact h2) (by simpa using hc)⟩
  · refine ⟨e.1.2, ?_⟩
    rw [torusRightEdge]
    symm
    apply Edge.ofAdj_eq_of_endpoints
    exact Or.inr ⟨rfl, Prod.ext (by exact h2) (by simpa using hc.symm)⟩

/-- Every vertical torus edge is the up edge of a lower endpoint `p`: its unordered
endpoints are `p` and `p + (0, 1)`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=ex.1h3v.s6.be2024a782bb from=translated src=- shape=7eb7f725 vocab=49854ed1
-/
theorem isVerticalTorusEdge_eq_upEdge {e : Edge (torusGraph width height)}
    (he : IsVerticalTorusEdge e) :
    ∃ p : TorusVertex width height, e = torusUpEdge p := by
  have hc : e.1.1.1 = e.1.2.1 := he.1
  rcases he.2 with h2 | h2
  · refine ⟨e.1.1, ?_⟩
    rw [torusUpEdge]
    symm
    apply Edge.ofAdj_eq_of_endpoints
    exact Or.inl ⟨rfl, Prod.ext (by simpa using hc) (by exact h2)⟩
  · refine ⟨e.1.2, ?_⟩
    rw [torusUpEdge]
    symm
    apply Edge.ofAdj_eq_of_endpoints
    exact Or.inr ⟨rfl, Prod.ext (by simpa using hc.symm) (by exact h2)⟩

/-! ### Transitivity of translations on each orientation class

Translation carries the right edge of `p` to the right edge of the translated
point, and likewise for up edges.  Hence any two horizontal edges (any two
vertical edges) are related by a translation, so a translation-invariant tensor has
the same bond dimension throughout each orientation class. -/

/-- Translation carries the right edge of `p` to the right edge of `p + (a, b)`.
@isnad1 id=eq.0h5v.s7.abe94eef3ddc from=translated src=- shape=174406b1 vocab=f83cf873
-/
theorem translateEdge_torusRightEdge (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) :
    translateEdge a b (torusRightEdge p) = torusRightEdge (p.1 + a, p.2 + b) := by
  rw [torusRightEdge, torusRightEdge, translateEdge_eq_map, Edge.map]
  apply Edge.ofAdj_eq_ofAdj
  rcases Edge.ofAdj_endpoints (torusGraph_adj_right p.1 p.2) with ⟨o1, o2⟩ | ⟨o1, o2⟩
  · exact Or.inl ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply],
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]; ring⟩
  · exact Or.inr ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply]; ring,
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]⟩

/-- Translation carries the up edge of `p` to the up edge of `p + (a, b)`.
@isnad1 id=eq.0h5v.s7.03cd86bdd2b2 from=translated src=- shape=174406b1 vocab=dfe8bd10
-/
theorem translateEdge_torusUpEdge (a : ZMod width) (b : ZMod height)
    (p : TorusVertex width height) :
    translateEdge a b (torusUpEdge p) = torusUpEdge (p.1 + a, p.2 + b) := by
  rw [torusUpEdge, torusUpEdge, translateEdge_eq_map, Edge.map]
  apply Edge.ofAdj_eq_ofAdj
  rcases Edge.ofAdj_endpoints (torusGraph_adj_up p.1 p.2) with ⟨o1, o2⟩ | ⟨o1, o2⟩
  · exact Or.inl ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply],
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]; ring⟩
  · exact Or.inr ⟨by rw [o1]; apply Prod.ext <;> simp [translate_apply]; ring,
      by rw [o2]; apply Prod.ext <;> simp [translate_apply]⟩

/-- A bond-dimension function invariant under torus translations is constant
on the horizontal edges.

This is the geometric transitivity argument shared by tensor-level and
state-level translation invariance.

Source: arXiv:1804.04964, the horizontal bond-dimension conclusion at lines
1891--1894 of `Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h5v.s7.ca82a55e65ba from=translated src=- shape=9f095107 vocab=6fc4d000
-/
theorem bondDim_torusRightEdge_const_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e)
    (p p' : TorusVertex width height) :
    bondDim (torusRightEdge p') = bondDim (torusRightEdge p) := by
  have key :
      translateEdge (p'.1 - p.1) (p'.2 - p.2) (torusRightEdge p) =
        torusRightEdge p' := by
    rw [translateEdge_torusRightEdge]
    congr 1
    apply Prod.ext <;> simp
  rw [← key]
  exact htranslate _ _ (torusRightEdge p)

/-- A bond-dimension function invariant under torus translations is constant
on the vertical edges.

This is the geometric transitivity argument shared by tensor-level and
state-level translation invariance.

Source: arXiv:1804.04964, the vertical bond-dimension conclusion at lines
1891--1894 of `Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h5v.s7.65e2c0b3bf49 from=translated src=- shape=9f095107 vocab=afbb0cbf
-/
theorem bondDim_torusUpEdge_const_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e)
    (p p' : TorusVertex width height) :
    bondDim (torusUpEdge p') = bondDim (torusUpEdge p) := by
  have key :
      translateEdge (p'.1 - p.1) (p'.2 - p.2) (torusUpEdge p) =
        torusUpEdge p' := by
    rw [translateEdge_torusUpEdge]
    congr 1
    apply Prod.ext <;> simp
  rw [← key]
  exact htranslate _ _ (torusUpEdge p)

/-- A translation-invariant tensor has the same bond dimension on every
horizontal edge: the bond dimension of any right edge is independent of its
left endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h6v.s7.aff34e20236b from=translated src=- shape=032fdad5 vocab=a62045c1
-/
theorem bondDim_torusRightEdge_const {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (p p' : TorusVertex width height) :
    A.bondDim (torusRightEdge p') = A.bondDim (torusRightEdge p) :=
  bondDim_torusRightEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA) p p'

/-- A translation-invariant tensor has the same bond dimension on every vertical
edge: the bond dimension of any up edge is independent of its lower endpoint.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`.
@isnad1 id=eq.1h6v.s7.2a38cad824f7 from=translated src=- shape=032fdad5 vocab=81d124fa
-/
theorem bondDim_torusUpEdge_const {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (p p' : TorusVertex width height) :
    A.bondDim (torusUpEdge p') = A.bondDim (torusUpEdge p) :=
  bondDim_torusUpEdge_const_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA) p p'

/-! ### Constant bond dimension on each orientation class

The bond dimension of a translation-invariant tensor is `Dh` on every horizontal
edge and `Dv` on every vertical edge, where `Dh` and `Dv` are read off at a
reference edge of each class.  This is the constant-bond content that makes the
reduction to one horizontal and one vertical matrix well-defined.  The lattice has at
least one edge of each orientation, so the reference dimensions exist. -/

/-- The bond-dimension function of a tensor on the torus is **orientation uniform**
with horizontal dimension `Dh` and vertical dimension `Dv` when every horizontal
edge has bond dimension `Dh` and every vertical edge has bond dimension `Dv`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`.-/
def TorusUniformBondDim (bondDim : Edge (torusGraph width height) → ℕ) (Dh Dv : ℕ) : Prop :=
  (∀ e : Edge (torusGraph width height), IsHorizontalTorusEdge e → bondDim e = Dh) ∧
    (∀ e : Edge (torusGraph width height), IsVerticalTorusEdge e → bondDim e = Dv)

/-- A bond-dimension function invariant under torus translations is uniform
on each orientation class.

Source: arXiv:1804.04964, the orientation-wise bond-dimension conclusion at
lines 1891--1894 of `Papers/1804.04964/paper_normal.tex`.
@isnad1 id=torusuni.1h3v.s7.98484edad125 from=translated src=- shape=8ad86ecf vocab=5aae71f2
-/
theorem torusUniformBondDim_of_translate
    (bondDim : Edge (torusGraph width height) → ℕ)
    (htranslate : ∀ (a : ZMod width) (b : ZMod height) e,
      bondDim (translateEdge a b e) = bondDim e) :
    TorusUniformBondDim bondDim
      (bondDim (torusRightEdge 0)) (bondDim (torusUpEdge 0)) := by
  refine ⟨fun e he ↦ ?_, fun e he ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := isHorizontalTorusEdge_eq_rightEdge he
    exact bondDim_torusRightEdge_const_of_translate bondDim htranslate 0 p
  · obtain ⟨p, rfl⟩ := isVerticalTorusEdge_eq_upEdge he
    exact bondDim_torusUpEdge_const_of_translate bondDim htranslate 0 p

/-- **A translation-invariant tensor has orientation-uniform bond dimensions.**

Reading off the horizontal dimension `Dh` at the right edge of the origin and the
vertical dimension `Dv` at the up edge of the origin, every horizontal edge has
bond dimension `Dh` and every vertical edge has bond dimension `Dv`.  Each edge is
the right edge (respectively up edge) of its endpoint by the normal form, and the
class constancy carries the reference dimension across.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`, where translation invariance makes the gauge
"the same matrix on all horizontal (vertical) edges".
@isnad1 id=torusuni.1h4v.s8.b6b5f1f72724 from=translated src=- shape=72850780 vocab=4b26365a
-/
theorem torusUniformBondDim_of_translationInvariant {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) :
    TorusUniformBondDim A.bondDim
      (A.bondDim (torusRightEdge 0)) (A.bondDim (torusUpEdge 0)) :=
  torusUniformBondDim_of_translate A.bondDim
    (bondDim_translateEdge_of_translationInvariant hA)

end PEPS
end TNLean
