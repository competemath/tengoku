/-
Copyright (c) 2026 wang060919.
Released under the MIT license; see LICENSE.
Public project author: wang060919. Developed with Codex assistance.
-/

import Tengoku.Jsp000936UnitCircleLean.UnitCircleInterpolation.Symmetry
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.Seed.Data.Finset.Sort
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical cyclic angles and an ordered representation of every node family

Every unit complex number has a unique angle in `[0, 2π)`. The finite set of
these angles is then ordered using `Finset.orderIsoOfFin`; its equivalence with
the original index set supplies the reindexing permutation. Thus the sorting
and normalization constraints below are proved for arbitrary admissible nodes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnitCircleInterpolation

noncomputable section

/-- The representative of a unit complex number in the half-open interval `[0, 2π)`.-/
def cyclicPhase (z : Circle) : ℝ :=
  if Complex.arg (z : ℂ) < 0 then Complex.arg (z : ℂ) + 2 * Real.pi
  else Complex.arg (z : ℂ)

/--
@isnad1 id=mem.0h1v.s5.5d873ede02bd from=translated src=- shape=4dc7b4fa vocab=fb5fd484
-/
lemma cyclicPhase_mem_Ico (z : Circle) : cyclicPhase z ∈ Set.Ico 0 (2 * Real.pi) := by
  obtain ⟨harg_lower, harg_upper⟩ := Complex.arg_mem_Ioc (z : ℂ)
  unfold cyclicPhase
  split_ifs with h
  · constructor <;> linarith [Real.pi_pos]
  · constructor <;> linarith [Real.pi_pos]

/--
@isnad1 id=eq.0h1v.s4.683a8b34986d from=translated src=- shape=8f2957ed vocab=54355ed3
-/
@[simp] lemma exp_cyclicPhase (z : Circle) : Circle.exp (cyclicPhase z) = z := by
  unfold cyclicPhase
  split_ifs with h
  · rw [Circle.exp_add, Circle.exp_arg, Circle.exp_two_pi, mul_one]
  · exact Circle.exp_arg z

/--
@isnad1 id=eq.0h0v.s4.ef4a7979ed55 from=translated src=- shape=1ac31801 vocab=26c5fa80
-/
@[simp] lemma cyclicPhase_one : cyclicPhase (1 : Circle) = 0 := by
  simp [cyclicPhase]

/--
@isnad1 id=injectiv.0h0v.s2.3501492ea777 from=translated src=- shape=54c8eceb vocab=f1cc284d
-/
lemma cyclicPhase_injective : Function.Injective cyclicPhase := by
  intro z w h
  calc
    z = Circle.exp (cyclicPhase z) := (exp_cyclicPhase z).symm
    _ = Circle.exp (cyclicPhase w) := congrArg Circle.exp h
    _ = w := exp_cyclicPhase w

/--
@isnad1 id=eq.1h1v.s6.b4baaead90ca from=translated src=- shape=ee588d2c vocab=915f3c0e
-/
lemma cyclicPhase_exp {t : ℝ} (ht : t ∈ Set.Ico 0 (2 * Real.pi)) :
    cyclicPhase (Circle.exp t) = t :=
  Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by simp)
    (cyclicPhase_mem_Ico _) ht (exp_cyclicPhase _)

/--
@isnad1 id=eq.0h0v.s5.d350cc7cbc81 from=translated src=- shape=5a20ef5a vocab=b6c3c38b
-/
lemma range_cyclicPhase : Set.range cyclicPhase = Set.Ico 0 (2 * Real.pi) := by
  ext t
  constructor
  · rintro ⟨z, rfl⟩
    exact cyclicPhase_mem_Ico z
  · intro ht
    exact ⟨Circle.exp t, cyclicPhase_exp ht⟩

/-- The entire circle is equivalent to the half-open interval of cyclic representatives.-/
def cyclicPhaseEquiv : Circle ≃ Set.Ico (0 : ℝ) (2 * Real.pi) where
  toFun z := ⟨cyclicPhase z, cyclicPhase_mem_Ico z⟩
  invFun t := Circle.exp t
  left_inv := exp_cyclicPhase
  right_inv t := Subtype.ext (cyclicPhase_exp t.property)

variable {n : ℕ}

/-- Rotate the original first node to `1`; no ordering assumptions are imposed on the input.-/
def anchoredNodes (nodes : NodeFamily n) (hn : 0 < n) : NodeFamily n :=
  nodes.rotate (nodes.point ⟨0, hn⟩)⁻¹

/--
@isnad1 id=eq.1h2v.s5.e444dbac47db from=translated src=- shape=b10dd508 vocab=48f6e7a2
-/
@[simp] lemma anchoredNodes_first (nodes : NodeFamily n) (hn : 0 < n) :
    (anchoredNodes nodes hn).point ⟨0, hn⟩ = 1 := by
  simp [anchoredNodes, NodeFamily.rotate]

/-- The finite set of all the family's canonical cyclic angles.-/
def NodeFamily.phaseSet (nodes : NodeFamily n) : Finset ℝ :=
  Finset.univ.image (fun i => cyclicPhase (nodes.point i))

/--
@isnad1 id=eq.0h2v.s3.1b847d8caa81 from=translated src=- shape=37d26c04 vocab=f6001121
-/
lemma NodeFamily.phaseSet_card (nodes : NodeFamily n) : nodes.phaseSet.card = n := by
  simpa only [NodeFamily.phaseSet, Function.comp_def, Finset.card_univ, Fintype.card_fin] using
    Finset.card_image_of_injective (Finset.univ : Finset (Fin n))
      (cyclicPhase_injective.comp nodes.injective)

def NodeFamily.phaseToSet (nodes : NodeFamily n) (i : Fin n) : nodes.phaseSet :=
  ⟨cyclicPhase (nodes.point i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩

/--
@isnad1 id=bijectiv.0h2v.s4.61440f55a01b from=translated src=- shape=7e57936d vocab=da1963c4
-/
lemma NodeFamily.phaseToSet_bijective (nodes : NodeFamily n) :
    Function.Bijective nodes.phaseToSet := by
  constructor
  · intro i j h
    exact nodes.injective (cyclicPhase_injective (congrArg Subtype.val h))
  · rintro ⟨t, ht⟩
    rcases Finset.mem_image.mp ht with ⟨i, hi, hit⟩
    exact ⟨i, Subtype.ext hit⟩

/-- This equivalence records the actual original index corresponding to each phase.-/
def NodeFamily.phaseSetEquiv (nodes : NodeFamily n) : Fin n ≃ nodes.phaseSet :=
  Equiv.ofBijective nodes.phaseToSet nodes.phaseToSet_bijective

/-- The increasing enumeration of the complete finite phase set.-/
def NodeFamily.sortedPhase (nodes : NodeFamily n) : Fin n → ℝ :=
  nodes.phaseSet.orderEmbOfFin nodes.phaseSet_card

/-- The permutation from sorted indices back to the original enumeration.-/
def NodeFamily.sortedPermutation (nodes : NodeFamily n) : Equiv.Perm (Fin n) :=
  (nodes.phaseSet.orderIsoOfFin nodes.phaseSet_card).toEquiv.trans nodes.phaseSetEquiv.symm

/--
@isnad1 id=strictmo.0h2v.s4.adf065ee4497 from=translated src=- shape=cc4c7d09 vocab=0e0fa751
-/
lemma NodeFamily.sortedPhase_strictMono (nodes : NodeFamily n) :
    StrictMono nodes.sortedPhase :=
  (nodes.phaseSet.orderEmbOfFin nodes.phaseSet_card).strictMono

/--
@isnad1 id=eq.0h3v.s5.93749fd9d6c1 from=translated src=- shape=bffe838d vocab=4272819c
-/
lemma NodeFamily.phase_sortedPermutation (nodes : NodeFamily n) (i : Fin n) :
    cyclicPhase (nodes.point (nodes.sortedPermutation i)) = nodes.sortedPhase i := by
  have h := nodes.phaseSetEquiv.apply_symm_apply
    (nodes.phaseSet.orderIsoOfFin nodes.phaseSet_card i)
  exact congrArg Subtype.val h

/--
@isnad1 id=mem.0h3v.s5.5c7835ae1017 from=translated src=- shape=24e03f2a vocab=ca45c6f8
-/
lemma NodeFamily.sortedPhase_mem_Ico (nodes : NodeFamily n) (i : Fin n) :
    nodes.sortedPhase i ∈ Set.Ico 0 (2 * Real.pi) := by
  rw [← nodes.phase_sortedPermutation i]
  exact cyclicPhase_mem_Ico _

/--
@isnad1 id=eq.0h3v.s6.b597060ead52 from=translated src=- shape=bb164dd6 vocab=baa8555f
-/
lemma NodeFamily.exp_sortedPhase (nodes : NodeFamily n) (i : Fin n) :
    Circle.exp (nodes.sortedPhase i) = nodes.point (nodes.sortedPermutation i) := by
  rw [← nodes.phase_sortedPermutation i, exp_cyclicPhase]

/--
@isnad1 id=eq.1h2v.s5.62f5886a0ceb from=translated src=- shape=b10dd508 vocab=a6aa9bcb
-/
lemma sortedPhase_anchored_zero (nodes : NodeFamily n) (hn : 0 < n) :
    (anchoredNodes nodes hn).sortedPhase ⟨0, hn⟩ = 0 := by
  let rotated := anchoredNodes nodes hn
  change rotated.phaseSet.orderEmbOfFin rotated.phaseSet_card ⟨0, hn⟩ = 0
  rw [Finset.orderEmbOfFin_zero rotated.phaseSet_card hn]
  apply (Finset.min'_eq_iff _ _ 0).mpr
  constructor
  · apply Finset.mem_image.mpr
    refine ⟨⟨0, hn⟩, Finset.mem_univ _, ?_⟩
    simp [rotated]
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨i, hi, hit⟩
    rw [← hit]
    exact (cyclicPhase_mem_Ico _).1

/-- An ordered, normalized angular configuration, with every constraint included as evidence.-/
structure CyclicAngles (n : ℕ) (hn : 0 < n) where
  angle : Fin n → ℝ
  strictMono : StrictMono angle
  first_eq_zero : angle ⟨0, hn⟩ = 0
  lt_two_pi : ∀ i, angle i < 2 * Real.pi

/-- The canonical angular configuration constructed from arbitrary admissible nodes.-/
def orderedAngles (nodes : NodeFamily n) (hn : 0 < n) : CyclicAngles n hn where
  angle := (anchoredNodes nodes hn).sortedPhase
  strictMono := (anchoredNodes nodes hn).sortedPhase_strictMono
  first_eq_zero := sortedPhase_anchored_zero nodes hn
  lt_two_pi i := ((anchoredNodes nodes hn).sortedPhase_mem_Ico i).2

/--
@isnad1 id=le.1h3v.s5.38d5c92f58a1 from=translated src=- shape=80fcade7 vocab=20ba5587
-/
lemma CyclicAngles.nonneg {hn : 0 < n} (angles : CyclicAngles n hn) (i : Fin n) :
    0 ≤ angles.angle i := by
  rw [← angles.first_eq_zero]
  exact angles.strictMono.monotone (show (⟨0, hn⟩ : Fin n) ≤ i from Nat.zero_le i.val)

/--
@isnad1 id=eq.1h3v.s6.ad46347288ca from=translated src=- shape=d46fb477 vocab=d3e0f669
-/
lemma orderedAngles_recovers (nodes : NodeFamily n) (hn : 0 < n) (i : Fin n) :
    nodes.point ((anchoredNodes nodes hn).sortedPermutation i) =
      nodes.point ⟨0, hn⟩ * Circle.exp ((orderedAngles nodes hn).angle i) := by
  rw [show (orderedAngles nodes hn).angle i = (anchoredNodes nodes hn).sortedPhase i from rfl,
    (anchoredNodes nodes hn).exp_sortedPhase]
  change nodes.point _ = nodes.point ⟨0, hn⟩ *
    ((nodes.point ⟨0, hn⟩)⁻¹ * nodes.point _)
  simp

/-- Every positive-size family admits an ordered angular representation, including its
normalizing rotation and an actual permutation of the original indices.
@isnad1 id=ex.1h2v.s6.e90be603230a from=translated src=- shape=49d07b44 vocab=6f88bc34
-/
theorem exists_orderedAngles (nodes : NodeFamily n) (hn : 0 < n) :
    ∃ rotation : Circle, ∃ permutation : Equiv.Perm (Fin n), ∃ angles : CyclicAngles n hn,
      ∀ i, nodes.point (permutation i) = rotation * Circle.exp (angles.angle i) := by
  exact ⟨nodes.point ⟨0, hn⟩, (anchoredNodes nodes hn).sortedPermutation,
    orderedAngles nodes hn, orderedAngles_recovers nodes hn⟩

end

end UnitCircleInterpolation
