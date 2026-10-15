/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/
module

public import Tengoku

/-!
# The planar circular restricted three-body Hamiltonian

This file gives the exact definitions occurring in the Poincaré nonintegrability challenge and
establishes their elementary structural properties. It deliberately does not import the challenge
module: the solution and challenge environments must remain separately exportable for comparator.
-/

@[expose] public section

namespace LeanPool.PoincareThreeBody

open Set

/-- Planar canonical phase space, ordered as `(x, y, pₓ, pᵧ)`. -/
abbrev PhaseSpace := Fin 4 → ℝ

/-- Squared distance from the primary of mass `μ` at `(1 - μ, 0)`. -/
def firstPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 - 1 + μ) ^ 2 + (s 1) ^ 2

/-- Squared distance from the primary of mass `1 - μ` at `(-μ, 0)`. -/
def secondPrimaryDistanceSq (μ : ℝ) (s : PhaseSpace) : ℝ :=
  (s 0 + μ) ^ 2 + (s 1) ^ 2

/-- The collision-free joint mass-parameter/phase-space domain. -/
def collisionFree : Set (ℝ × PhaseSpace) :=
  {z | firstPrimaryDistanceSq z.1 z.2 ≠ 0 ∧ secondPrimaryDistanceSq z.1 z.2 ≠ 0}

/-- The collision-free domain with the mass parameter restricted to `|μ| < δ`. -/
def parameterDomain (δ : ℝ) : Set (ℝ × PhaseSpace) :=
  {z | |z.1| < δ ∧ z ∈ collisionFree}

/-- The Newtonian potential in the rotating frame. -/
noncomputable def potential (μ : ℝ) (s : PhaseSpace) : ℝ :=
  μ / Real.sqrt (firstPrimaryDistanceSq μ s) +
    (1 - μ) / Real.sqrt (secondPrimaryDistanceSq μ s)

/-- The planar circular restricted three-body Hamiltonian in rotating canonical coordinates. -/
noncomputable def hamiltonian (μ : ℝ) (s : PhaseSpace) : ℝ :=
  ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 - potential μ s

/-- The coordinate basis vector in the concrete phase space. -/
def coordinateVector (i : Fin 4) : PhaseSpace :=
  fun j ↦ if j = i then 1 else 0

/-- The canonical Poisson bracket in coordinates `(x, y, pₓ, pᵧ)`. -/
noncomputable def poissonBracket (F G : PhaseSpace → ℝ) (s : PhaseSpace) : ℝ :=
  let dF := fderiv ℝ F s
  let dG := fderiv ℝ G s
  dF (coordinateVector 0) * dG (coordinateVector 2) -
      dF (coordinateVector 2) * dG (coordinateVector 0) +
    (dF (coordinateVector 1) * dG (coordinateVector 3) -
      dF (coordinateVector 3) * dG (coordinateVector 1))

/-- Joint real analyticity in the mass parameter and phase variables. -/
def IsJointlyAnalytic (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  AnalyticOnNhd ℝ (Function.uncurry F) (parameterDomain δ)

/-- A first-integral family Poisson-commutes with the Hamiltonian throughout the domain. -/
noncomputable def IsFirstIntegralFamily (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∀ z ∈ parameterDomain δ, poissonBracket (F z.1) (hamiltonian z.1) z.2 = 0

/-- Functional independence of the phase differentials at some point. -/
noncomputable def IsIndependentSomewhere (δ : ℝ) (F : ℝ → PhaseSpace → ℝ) : Prop :=
  ∃ z ∈ parameterDomain δ,
    LinearIndependent ℝ
      ![fderiv ℝ (hamiltonian z.1) z.2, fderiv ℝ (F z.1) z.2]

/--
@isnad1 id=le.0h2v.s4.ae9a456c5bcd from=translated src=- shape=25b8bdde vocab=a05fa614
-/
lemma firstPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ firstPrimaryDistanceSq μ s := by
  simp only [firstPrimaryDistanceSq]
  positivity

/--
@isnad1 id=le.0h2v.s4.8b152f79fd51 from=translated src=- shape=25b8bdde vocab=017152cb
-/
lemma secondPrimaryDistanceSq_nonneg (μ : ℝ) (s : PhaseSpace) :
    0 ≤ secondPrimaryDistanceSq μ s := by
  simp only [secondPrimaryDistanceSq]
  positivity

/--
@isnad1 id=lt.1h2v.s4.e84be090e07c from=translated src=- shape=a2ca859b vocab=f5a7d3f3
-/
lemma firstPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : firstPrimaryDistanceSq μ s ≠ 0) : 0 < firstPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (firstPrimaryDistanceSq_nonneg μ s) (Ne.symm h)

/--
@isnad1 id=lt.1h2v.s4.ce291f069837 from=translated src=- shape=a2ca859b vocab=8040b2b2
-/
lemma secondPrimaryDistanceSq_pos {μ : ℝ} {s : PhaseSpace}
    (h : secondPrimaryDistanceSq μ s ≠ 0) : 0 < secondPrimaryDistanceSq μ s :=
  lt_of_le_of_ne (secondPrimaryDistanceSq_nonneg μ s) (Ne.symm h)

/--
@isnad1 id=iff.0h2v.s5.b6bcfb6ad53a from=translated src=- shape=87865d7c vocab=cde884c6
-/
lemma mem_collisionFree_iff {μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ collisionFree ↔
      firstPrimaryDistanceSq μ s ≠ 0 ∧ secondPrimaryDistanceSq μ s ≠ 0 :=
  Iff.rfl

/--
@isnad1 id=iff.0h3v.s5.3040d111dfd6 from=translated src=- shape=d80521ab vocab=1f05be0b
-/
lemma mem_parameterDomain_iff {δ μ : ℝ} {s : PhaseSpace} :
    (μ, s) ∈ parameterDomain δ ↔ |μ| < δ ∧ (μ, s) ∈ collisionFree :=
  Iff.rfl

/--
@isnad1 id=eq.0h1v.s4.e101e3bd3a61 from=translated src=- shape=6e4c2516 vocab=333140e3
-/
@[simp] lemma coordinateVector_same (i : Fin 4) : coordinateVector i i = 1 := by
  simp [coordinateVector]

/--
@isnad1 id=eq.1h2v.s5.5540e51bdd34 from=translated src=- shape=68592342 vocab=333140e3
-/
@[simp] lemma coordinateVector_apply {i j : Fin 4} (h : j ≠ i) : coordinateVector i j = 0 := by
  simp [coordinateVector, h]

/--
@isnad1 id=eq.0h2v.s4.221b2439e73b from=translated src=- shape=dbd4350f vocab=bce1ac6d
-/
lemma poissonBracket_self (F : PhaseSpace → ℝ) (s : PhaseSpace) :
    poissonBracket F F s = 0 := by
  simp only [poissonBracket]
  ring

/--
@isnad1 id=isfirsti.0h1v.s2.cd6f250520dc from=translated src=- shape=2d69f17f vocab=1201fbca
-/
lemma hamiltonian_isFirstIntegralFamily (δ : ℝ) :
    IsFirstIntegralFamily δ hamiltonian := by
  intro z hz
  exact poissonBracket_self (hamiltonian z.1) z.2

/--
@isnad1 id=eq.0h1v.s8.a6097b4af7ec from=translated src=- shape=57df12bb vocab=3128c90d
-/
lemma hamiltonian_zero (s : PhaseSpace) :
    hamiltonian 0 s =
      ((s 2) ^ 2 + (s 3) ^ 2) / 2 + s 2 * s 1 - s 3 * s 0 -
        1 / Real.sqrt ((s 0) ^ 2 + (s 1) ^ 2) := by
  simp [hamiltonian, potential, firstPrimaryDistanceSq, secondPrimaryDistanceSq]

/--
@isnad1 id=eq.3h3v.s6.43875c20d557 from=translated src=- shape=3ef046bd vocab=309beb49
-/
lemma IsFirstIntegralFamily.poissonBracket_zero_at_mass_zero {δ : ℝ}
    {F : ℝ → PhaseSpace → ℝ} (hδ : 0 < δ) (hF : IsFirstIntegralFamily δ F)
    {s : PhaseSpace} (hs : (0, s) ∈ collisionFree) :
    poissonBracket (F 0) (hamiltonian 0) s = 0 := by
  apply hF (0, s)
  exact ⟨by simpa using hδ, hs⟩

/--
@isnad1 id=not.0h1v.s2.4c6be754a087 from=translated src=- shape=69c56833 vocab=a403e87a
-/
lemma hamiltonian_not_independent (δ : ℝ) : ¬IsIndependentSomewhere δ hamiltonian := by
  rintro ⟨z, hz, hlinear⟩
  have hindex : (0 : Fin 2) = 1 := hlinear.injective (by simp)
  norm_num at hindex

end LeanPool.PoincareThreeBody
