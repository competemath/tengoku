import Tengoku.TunnellTwoToOneMap.TunnellMap.ProjectiveKey
import Tengoku.TunnellTwoToOneMap.TunnellMap.ResidualBalance

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ranked residual-orbit graph

This file passes the representative-level midpoint key to antipodal residual
orbits.  The key is independent of both signs, and its incident values are
injective at each endpoint.  Consequently the complete residual bipartite
graph is a globally ranked instance and has a unique stable perfect matching
whenever the two orbit sets have equal cardinality.
-/

namespace TunnellMap

abbrev TripleLexKey := ℤ ×ₗ (ℤ ×ₗ ℤ)

def tripleLexKey (v : Triple) : TripleLexKey :=
  toLex (v.x, toLex (v.y, v.z))

/--
@isnad1 id=injectiv.0h0v.s2.59dded89989d from=translated src=- shape=54c8eceb vocab=30a29f56
-/
theorem tripleLexKey_injective : Function.Injective tripleLexKey := by
  intro v w h
  apply Triple.ext
  · exact congrArg (fun k : TripleLexKey => (ofLex k).1) h
  · exact congrArg (fun k : TripleLexKey => (ofLex (ofLex k).2).1) h
  · exact congrArg (fun k : TripleLexKey => (ofLex (ofLex k).2).2) h

def bResidualLexKey {n : ℤ} (s : BResidual n) : TripleLexKey :=
  tripleLexKey s.1.1

def aResidualLexKey {n : ℤ} (t : AResidual n) : TripleLexKey :=
  tripleLexKey t.1.1

/--
@isnad1 id=injectiv.0h1v.s3.1a12383f86e4 from=translated src=- shape=64d36d98 vocab=35a1edd2
-/
theorem bResidualLexKey_injective {n : ℤ} :
    Function.Injective (bResidualLexKey (n := n)) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  exact tripleLexKey_injective h

/--
@isnad1 id=injectiv.0h1v.s3.7a713390b68c from=translated src=- shape=64d36d98 vocab=762eb049
-/
theorem aResidualLexKey_injective {n : ℤ} :
    Function.Injective (aResidualLexKey (n := n)) := by
  intro s t h
  apply Subtype.ext
  apply Subtype.ext
  exact tripleLexKey_injective h

/-- The lexicographically smaller signed residual source representative used
in the manuscript.-/
def canonicalBResidualRepresentative {n : ℤ} :
    (bResidualInvolution n).Orbit → BResidual n :=
  (bResidualInvolution n).canonicalRepresentative bResidualLexKey
    bResidualLexKey_injective

/-- The lexicographically smaller signed residual target representative used
in the manuscript.-/
def canonicalAResidualRepresentative {n : ℤ} (hnpos : 0 < n) :
    (aResidualInvolution n hnpos).Orbit → AResidual n :=
  (aResidualInvolution n hnpos).canonicalRepresentative aResidualLexKey
    aResidualLexKey_injective

/-- The projective midpoint key of a pair of antipodal residual orbits.-/
noncomputable def orbitEdgeKey {n : ℤ} (hnpos : 0 < n)
    (s : (bResidualInvolution n).Orbit)
    (t : (aResidualInvolution n hnpos).Orbit) : DirectionKey :=
  representativeEdgeKey
    (canonicalBResidualRepresentative s)
    (canonicalAResidualRepresentative hnpos t)

/-- Computing the orbit key from any signed representatives gives the same
answer.  This is the representative-independence assertion in Lemma 4.1.
@isnad1 id=eq.1h3v.s5.b8961c1ffe9f from=translated src=- shape=d48989db vocab=db077c4f
-/
theorem representativeEdgeKey_eq_orbitEdgeKey {n : ℤ} (hnpos : 0 < n)
    (s : BResidual n) (t : AResidual n) :
    representativeEdgeKey s t =
      orbitEdgeKey hnpos ((bResidualInvolution n).orbit s)
        ((aResidualInvolution n hnpos).orbit t) := by
  let BI := bResidualInvolution n
  let AI := aResidualInvolution n hnpos
  let rs := canonicalBResidualRepresentative (BI.orbit s)
  let rt := canonicalAResidualRepresentative hnpos (AI.orbit t)
  have hsOrbit : BI.orbit rs = BI.orbit s := by
    exact BI.orbit_canonicalRepresentative bResidualLexKey
      bResidualLexKey_injective _
  have htOrbit : AI.orbit rt = AI.orbit t := by
    exact AI.orbit_canonicalRepresentative aResidualLexKey
      aResidualLexKey_injective _
  have hs : s = rs ∨ s = negBResidual rs := by
    change s = rs ∨ s = BI.neg rs
    exact BI.orbit_eq_iff.mp hsOrbit
  have ht : t = rt ∨ t = negAResidual rt := by
    change t = rt ∨ t = AI.neg rt
    exact AI.orbit_eq_iff.mp htOrbit
  change representativeEdgeKey s t = representativeEdgeKey rs rt
  rcases hs with hs | hs <;> rcases ht with ht | ht
  · rw [hs, ht]
  · rw [hs, ht]
    exact representativeEdgeKey_neg_target _ _
  · rw [hs, ht]
    exact representativeEdgeKey_neg_source _ _
  · rw [hs, ht, representativeEdgeKey_neg_source,
      representativeEdgeKey_neg_target]

/-- Proposition 4.2: the projective keys make the residual orbit graph a
globally ranked complete bipartite graph.-/
noncomputable def residualOrbitRanking {n : ℤ} (hnpos : 0 < n) :
    GloballyRanked DirectionKey (bResidualInvolution n).Orbit
      (aResidualInvolution n hnpos).Orbit where
  rank := orbitEdgeKey hnpos
  source_injective := by
    intro s t₁ t₂ hkey
    have horbit := representativeEdgeKey_source_orbit_injective hnpos
      (canonicalBResidualRepresentative s) hkey
    let AI := aResidualInvolution n hnpos
    calc
      t₁ = AI.orbit (canonicalAResidualRepresentative hnpos t₁) :=
        (AI.orbit_canonicalRepresentative aResidualLexKey
          aResidualLexKey_injective t₁).symm
      _ = AI.orbit (canonicalAResidualRepresentative hnpos t₂) := horbit
      _ = t₂ := AI.orbit_canonicalRepresentative aResidualLexKey
        aResidualLexKey_injective t₂
  target_injective := by
    intro t s₁ s₂ hkey
    have horbit := representativeEdgeKey_target_orbit_injective
      (canonicalAResidualRepresentative hnpos t) hkey
    let BI := bResidualInvolution n
    calc
      s₁ = BI.orbit (canonicalBResidualRepresentative s₁) :=
        (BI.orbit_canonicalRepresentative bResidualLexKey
          bResidualLexKey_injective s₁).symm
      _ = BI.orbit (canonicalBResidualRepresentative s₂) := horbit
      _ = s₂ := BI.orbit_canonicalRepresentative bResidualLexKey
        bResidualLexKey_injective s₂

section Finite

variable {n : ℤ} (hnpos : 0 < n)
  [Fintype (BOddRep n)] [Fintype (ARep n)]

/-- The paper's residual orbit matching, characterized as the unique stable
matching for the projective midpoint ranking.-/
noncomputable def residualOrbitMatching
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (bResidualInvolution n).Orbit ≃ (aResidualInvolution n hnpos).Orbit := by
  classical
  exact Classical.choose
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)

/--
@isnad1 id=stable.2h1v.s6.2ffbe2b5bbb4 from=translated src=- shape=338043ed vocab=00d8f2bb
-/
theorem residualOrbitMatching_stable
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit) :
    (residualOrbitRanking hnpos).Stable
      (residualOrbitMatching hnpos hcard) := by
  classical
  exact (Classical.choose_spec
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)).1

/--
@isnad1 id=eq.3h2v.s6.99d8a083454e from=translated src=- shape=700be2f9 vocab=7c86a923
-/
theorem residualOrbitMatching_unique
    (hcard : Fintype.card (bResidualInvolution n).Orbit =
      Fintype.card (aResidualInvolution n hnpos).Orbit)
    (M : (bResidualInvolution n).Orbit ≃
      (aResidualInvolution n hnpos).Orbit)
    (hM : (residualOrbitRanking hnpos).Stable M) :
    M = residualOrbitMatching hnpos hcard := by
  classical
  exact (Classical.choose_spec
    (GloballyRanked.exists_unique_stable (residualOrbitRanking hnpos) hcard)).2 M hM

end Finite

end TunnellMap
