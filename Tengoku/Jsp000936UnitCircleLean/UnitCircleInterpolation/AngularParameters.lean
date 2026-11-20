/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.CyclicAngles
import Tengoku.Seed.Data.Fin.Tuple.Basic
import Tengoku.Seed.Topology.Order.OrderClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An open chart for normalized cyclic angles

The free parameters are the `d` nonzero angles of a normalized configuration
with `d+1` nodes. The first angle stays literally zero. All domain constraints
are finite strict inequalities, so this parameter domain is open in `Fin d → ℝ`.
The constructions below are inverse to each other, including when `d = 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

variable {d : ℕ}

/-- The actual full angle family, with its normalizing angle fixed at zero.-/
def angularParameterAngles (u : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cons 0 u

/--
@isnad1 id=eq.0h2v.s5.07d221728785 from=translated src=- shape=b6a59515 vocab=a1650445
-/
@[simp] lemma angularParameterAngles_zero (u : Fin d → ℝ) :
    angularParameterAngles u 0 = 0 :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.3d82a60b9abc from=translated src=- shape=6d29024d vocab=e173a672
-/
@[simp] lemma angularParameterAngles_succ (u : Fin d → ℝ) (i : Fin d) :
    angularParameterAngles u i.succ = u i :=
  rfl

/-- Strictly ordered normalized angles, with every angle below the end of the period.-/
def angularParameterDomain (d : ℕ) : Set (Fin d → ℝ) :=
  {u | StrictMono (angularParameterAngles u) ∧ ∀ i, u i < 2 * Real.pi}

/--
@isnad1 id=continuo.0h2v.s5.a62d9d27fc2e from=translated src=- shape=528a39dc vocab=96f9d7b3
-/
lemma continuous_angularParameterAngle (i : Fin (d + 1)) :
    Continuous (fun u : Fin d → ℝ => angularParameterAngles u i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [angularParameterAngles_zero] using
      (continuous_const : Continuous (fun _ : Fin d → ℝ => (0 : ℝ)))
  · simpa only [angularParameterAngles_succ] using
      (continuous_apply j : Continuous (fun u : Fin d → ℝ => u j))

/--
@isnad1 id=continuo.0h1v.s6.6bba03815e04 from=translated src=- shape=fc826ba2 vocab=96f9d7b3
-/
lemma continuous_angularParameterAngles :
    Continuous (angularParameterAngles : (Fin d → ℝ) → Fin (d + 1) → ℝ) :=
  continuous_pi continuous_angularParameterAngle

/-- The normalized angular chart has no boundary equalities among its free parameters.
@isnad1 id=isopen.0h1v.s4.91883f104a79 from=translated src=- shape=fe6f4f64 vocab=82f7f651
-/
theorem isOpen_angularParameterDomain (d : ℕ) : IsOpen (angularParameterDomain d) := by
  have horder : IsOpen {u : Fin d → ℝ | StrictMono (angularParameterAngles u)} := by
    have heq : {u : Fin d → ℝ | StrictMono (angularParameterAngles u)} =
        ⋂ i : Fin (d + 1), ⋂ j : Fin (d + 1),
          {u : Fin d → ℝ | i < j → angularParameterAngles u i < angularParameterAngles u j} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      rfl
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    by_cases hij : i < j
    · simp only [hij, true_implies]
      exact isOpen_lt (continuous_angularParameterAngle i) (continuous_angularParameterAngle j)
    · simp only [hij, false_implies, Set.ofPred_true]
      exact isOpen_univ
  have hupper : IsOpen {u : Fin d → ℝ | ∀ i, u i < 2 * Real.pi} := by
    have heq : {u : Fin d → ℝ | ∀ i, u i < 2 * Real.pi} =
        ⋂ i : Fin d, {u : Fin d → ℝ | u i < 2 * Real.pi} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt (continuous_apply i) continuous_const)
  exact horder.inter hupper

/--
@isnad1 id=lt.1h3v.s5.bd8ee5036a00 from=translated src=- shape=1e3f7272 vocab=e76f1231
-/
lemma angularParameter_pos (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d)
    (i : Fin d) : 0 < u i := by
  have h := hu.1 (Fin.succ_pos i)
  simpa only [angularParameterAngles_zero, angularParameterAngles_succ] using h

/--
@isnad1 id=mem.1h3v.s6.bdb8f6f80448 from=translated src=- shape=36093cbe vocab=6d916675
-/
lemma angularParameterAngle_mem_Ico (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) (i : Fin (d + 1)) :
    angularParameterAngles u i ∈ Set.Ico 0 (2 * Real.pi) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [angularParameterAngles_zero, Set.mem_Ico, le_refl, true_and]
    positivity
  · simpa only [angularParameterAngles_succ, Set.mem_Ico] using
      And.intro (angularParameter_pos u hu j).le (hu.2 j)

/-- The admissible parameter gives an actual canonical angular configuration.-/
def cyclicAnglesOfParameters (u : Fin d → ℝ) (hu : u ∈ angularParameterDomain d) :
    CyclicAngles (d + 1) (Nat.succ_pos d) where
  angle := angularParameterAngles u
  strictMono := hu.1
  first_eq_zero := angularParameterAngles_zero u
  lt_two_pi i := (angularParameterAngle_mem_Ico u hu i).2

/--
@isnad1 id=eq.1h2v.s6.538327b5b464 from=translated src=- shape=94e124ea vocab=a5eb60d3
-/
@[simp] lemma cyclicAnglesOfParameters_angle (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) :
    (cyclicAnglesOfParameters u hu).angle = angularParameterAngles u :=
  rfl

/-- Extract precisely the free angles, without a rotation or permutation.-/
def CyclicAngles.interiorParameters (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) :
    Fin d → ℝ :=
  Fin.tail angles.angle

/--
@isnad1 id=eq.0h3v.s5.3ffc0b335c41 from=translated src=- shape=d856ea2b vocab=b2b8e453
-/
@[simp] lemma CyclicAngles.interiorParameters_apply
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) (i : Fin d) :
    angles.interiorParameters i = angles.angle i.succ :=
  rfl

/-- Reattaching the literal zero angle recovers the original full angle family.
@isnad1 id=eq.0h2v.s5.756e2b139412 from=translated src=- shape=d6a6be8e vocab=2992d751
-/
lemma angularParameterAngles_interiorParameters
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) :
    angularParameterAngles angles.interiorParameters = angles.angle := by
  change Fin.cons 0 (Fin.tail angles.angle) = angles.angle
  rw [← angles.first_eq_zero]
  exact Fin.cons_self_tail angles.angle

/--
@isnad1 id=mem.0h2v.s5.3cb8c08a7923 from=translated src=- shape=9e886b58 vocab=62a9eb74
-/
lemma CyclicAngles.interiorParameters_mem_domain
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) :
    angles.interiorParameters ∈ angularParameterDomain d := by
  constructor
  · rw [angularParameterAngles_interiorParameters]
    exact angles.strictMono
  · intro i
    exact angles.lt_two_pi i.succ

/--
@isnad1 id=eq.1h2v.s5.e92b96378926 from=translated src=- shape=92a7b600 vocab=3d85edb9
-/
@[simp] lemma CyclicAngles.interiorParameters_ofParameters (u : Fin d → ℝ)
    (hu : u ∈ angularParameterDomain d) :
    (cyclicAnglesOfParameters u hu).interiorParameters = u :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.3ac94f5bdd43 from=translated src=- shape=55ed04bc vocab=6ffd0522
-/
@[simp] lemma cyclicAnglesOfParameters_interiorParameters
    (angles : CyclicAngles (d + 1) (Nat.succ_pos d)) :
    cyclicAnglesOfParameters angles.interiorParameters angles.interiorParameters_mem_domain =
      angles := by
  have hangle := angularParameterAngles_interiorParameters angles
  cases angles
  unfold cyclicAnglesOfParameters
  congr 1

/-- The open parameter domain and actual canonical angle configurations are equivalent.-/
def angularParametersEquiv (d : ℕ) :
    angularParameterDomain d ≃ CyclicAngles (d + 1) (Nat.succ_pos d) where
  toFun u := cyclicAnglesOfParameters u.val u.property
  invFun angles := ⟨angles.interiorParameters, angles.interiorParameters_mem_domain⟩
  left_inv u := Subtype.ext (CyclicAngles.interiorParameters_ofParameters u.val u.property)
  right_inv := cyclicAnglesOfParameters_interiorParameters

end

end UnitCircleInterpolation
