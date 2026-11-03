import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Auslander--Reiten Euler counts and surplus

This file formalizes the first numerical reduction in the frozen manuscript.
For a finite Auslander--Reiten vertex type, the almost-split meshes are indexed
by the nonprojective vertices.  Hence

`mesh count = vertex count - projective count`.

If the projective count is the number of simple modules and magnitude is given
by the Auslander--Reiten Euler characteristic `vertices - arrows + meshes`, its
surplus over the number of simples is `2 * meshes - arrows`.
-/

set_option autoImplicit false

namespace MagnitudeConjecture.ARCount

universe u

variable {ι : Type u} [Fintype ι]

/-- Number of vertices, regarded as an integer for Euler calculations.-/
def vertexCount : ℤ := Fintype.card ι

/-- Total arrow multiplicity of a finite directed multigraph.-/
def arrowCount (arrowMultiplicity : ι → ι → ℕ) : ℤ :=
  ∑ source, ∑ target, (arrowMultiplicity source target : ℤ)

/-- Total incoming arrow multiplicity at one vertex.-/
def indegree (arrowMultiplicity : ι → ι → ℕ) (target : ι) : ℤ :=
  ∑ source, (arrowMultiplicity source target : ℤ)

/-- Number of projective vertices.  In the module-category specialization this
is the number of simple modules.-/
def projectiveCount (IsProjective : ι → Prop) [DecidablePred IsProjective] : ℤ :=
  Fintype.card {X : ι // IsProjective X}

/-- Number of almost-split meshes, indexed by nonprojective vertices.-/
def meshCount (IsProjective : ι → Prop) [DecidablePred IsProjective] : ℤ :=
  Fintype.card {X : ι // ¬ IsProjective X}

/-- The Auslander--Reiten Euler expression for magnitude.-/
def eulerMagnitude
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective] : ℤ :=
  vertexCount (ι := ι) - arrowCount arrowMultiplicity + meshCount IsProjective

/-- Magnitude minus the number of simple modules, represented here by the
number of projective vertices.-/
def surplus
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective] : ℤ :=
  eulerMagnitude arrowMultiplicity IsProjective - projectiveCount IsProjective

/-- Local density used in the finite-control covering argument: twice the
nonprojective indicator minus total incoming arrow multiplicity.-/
def localDensity
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective]
    (X : ι) : ℤ :=
  2 * (if IsProjective X then 0 else 1) - indegree arrowMultiplicity X

/-- Incoming multiplicities sum to the total arrow multiplicity.
@isnad1 id=eq.0h2v.s4.28fabd347c65 from=translated src=- shape=0d210eae vocab=d11dfb55
-/
theorem sum_indegree_eq_arrowCount
    (arrowMultiplicity : ι → ι → ℕ) :
    ∑ X, indegree arrowMultiplicity X = arrowCount arrowMultiplicity := by
  simp only [indegree, arrowCount]
  rw [Finset.sum_comm]

/-- The sum of nonprojective indicators is the number of meshes.
@isnad1 id=eq.0h2v.s5.03d8b6591e7f from=translated src=- shape=a3e81dc6 vocab=28129fa4
-/
theorem sum_nonprojectiveIndicator_eq_meshCount
    (IsProjective : ι → Prop) [DecidablePred IsProjective] :
    ∑ X : ι, (if IsProjective X then (0 : ℤ) else 1) =
      meshCount IsProjective := by
  classical
  simp_rw [show ∀ X : ι,
      (if IsProjective X then (0 : ℤ) else 1) =
        if ¬ IsProjective X then 1 else 0 by simp]
  change (∑ X ∈ Finset.univ, if ¬ IsProjective X then (1 : ℤ) else 0) = _
  rw [Finset.sum_boole]
  simp [meshCount, Fintype.card_subtype]

/-- The sum of projective indicators is the number of projective vertices.
@isnad1 id=eq.0h2v.s5.2867b858e4c4 from=translated src=- shape=a3e81dc6 vocab=dfbe8578
-/
theorem sum_projectiveIndicator_eq_projectiveCount
    (IsProjective : ι → Prop) [DecidablePred IsProjective] :
    ∑ X : ι, (if IsProjective X then (1 : ℤ) else 0) =
      projectiveCount IsProjective := by
  classical
  rw [Finset.sum_boole]
  simp [projectiveCount, Fintype.card_subtype]

/-- Projective and nonprojective vertices partition the finite AR vertex set.
@isnad1 id=eq.0h2v.s5.8b8d84322abe from=translated src=- shape=97694f58 vocab=fca68bc6
-/
theorem vertexCount_eq_projectiveCount_add_meshCount
    (IsProjective : ι → Prop) [DecidablePred IsProjective] :
    vertexCount (ι := ι) =
      projectiveCount IsProjective + meshCount IsProjective := by
  classical
  have hcompl := Fintype.card_subtype_compl IsProjective
  have hle := Fintype.card_subtype_le IsProjective
  have hnat :
      Fintype.card ι =
        Fintype.card {X : ι // IsProjective X} +
          Fintype.card {X : ι // ¬ IsProjective X} := by
    omega
  simpa [vertexCount, projectiveCount, meshCount] using
    congrArg (fun n : ℕ ↦ (n : ℤ)) hnat

/-- Frozen manuscript, equations (2.1)--(2.2): the magnitude surplus is twice
the number of meshes minus the total arrow multiplicity.
@isnad1 id=eq.0h3v.s5.1c408ca319a6 from=translated src=- shape=44a959fc vocab=e4a233bd
-/
theorem surplus_eq_two_mul_meshCount_sub_arrowCount
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective] :
    surplus arrowMultiplicity IsProjective =
      2 * meshCount IsProjective - arrowCount arrowMultiplicity := by
  rw [surplus, eulerMagnitude,
    vertexCount_eq_projectiveCount_add_meshCount IsProjective]
  ring

/-- Frozen manuscript, local-density formula: summing the vertexwise density
recovers the Auslander--Reiten surplus.
@isnad1 id=eq.0h3v.s5.d9f9fd320c14 from=translated src=- shape=d4751268 vocab=b1461fe3
-/
theorem sum_localDensity_eq_surplus
    (arrowMultiplicity : ι → ι → ℕ)
    (IsProjective : ι → Prop) [DecidablePred IsProjective] :
    ∑ X, localDensity arrowMultiplicity IsProjective X =
      surplus arrowMultiplicity IsProjective := by
  calc
    ∑ X, localDensity arrowMultiplicity IsProjective X =
        2 * (∑ X, if IsProjective X then (0 : ℤ) else 1) -
          ∑ X, indegree arrowMultiplicity X := by
      simp only [localDensity, Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * meshCount IsProjective - arrowCount arrowMultiplicity := by
      rw [sum_nonprojectiveIndicator_eq_meshCount,
        sum_indegree_eq_arrowCount]
    _ = surplus arrowMultiplicity IsProjective := by
      rw [surplus_eq_two_mul_meshCount_sub_arrowCount]

end MagnitudeConjecture.ARCount
