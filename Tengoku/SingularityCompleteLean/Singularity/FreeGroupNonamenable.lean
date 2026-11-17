import Tengoku.SingularityCompleteLean.Singularity.InvariantMeanTransport
import Tengoku.Seed.GroupTheory.FreeGroup.Orbit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Nonamenability from a free subgroup

For each generator, its positive cone contains the translate of the complement
of its negative cone. An invariant mean would therefore give total mass at least
one to each of two disjoint pairs of cones, contradicting total mass one.
Subgroup heredity transfers this obstruction through an injective homomorphism.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

/-- A free group on at least two generators has no invariant mean.
@isnad1 id=not.0h1v.s3.8e8cb7ce23f0 from=translated src=- shape=fba248a8 vocab=58a19fa3
-/
theorem freeGroup_no_invariantMean (α : Type*) [Nontrivial α] :
    ¬HasInvariantMean (FreeGroup α) := by
  classical
  rintro ⟨m, hpos, hemp, huniv, hadd, hinv⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  have hpair (a : α) : 1 ≤ m (FreeGroup.startsWith (a, true)) +
      m (FreeGroup.startsWith (a, false)) := by
    have hsub : (fun x => FreeGroup.mk [(a, true)] * x) ''
        (FreeGroup.startsWith (a, false))ᶜ ⊆ FreeGroup.startsWith (a, true) := by
      rintro _ ⟨x, hx, rfl⟩
      exact FreeGroup.startsWith_mk_mul x hx
    have hle := invariantMean_mono m hpos hadd hsub
    rw [hinv] at hle
    have hsum := hadd (FreeGroup.startsWith (a, false))
      (FreeGroup.startsWith (a, false))ᶜ disjoint_compl_right
    rw [union_compl_self, huniv] at hsum
    linarith
  let A := FreeGroup.startsWith (a, true)
  let B := FreeGroup.startsWith (a, false)
  let C := FreeGroup.startsWith (b, true)
  let D := FreeGroup.startsWith (b, false)
  have hAB : Disjoint A B := by simp [A, B]
  have hCD : Disjoint C D := by simp [C, D]
  have hdisj : Disjoint (A ∪ B) (C ∪ D) := by
    simp [A, B, C, D, Set.disjoint_union_left, Set.disjoint_union_right, hab]
  have hle := invariantMean_mono m hpos hadd (Set.subset_univ ((A ∪ B) ∪ (C ∪ D)))
  rw [huniv, hadd _ _ hdisj, hadd _ _ hAB, hadd _ _ hCD] at hle
  have ha := hpair a
  have hb := hpair b
  change 1 ≤ m A + m B at ha
  change 1 ≤ m C + m D at hb
  linarith

/-- A group containing a free group on two generators is nonamenable.
@isnad1 id=not.1h2v.s6.8161ada2dc0b from=translated src=- shape=ad36415b vocab=6764ba4e
-/
theorem no_invariantMean_of_free_subgroup {G : Type*} [Group G]
    (j : FreeGroup Bool →* G) (hj : Function.Injective j) : ¬HasInvariantMean G :=
  fun hm => freeGroup_no_invariantMean Bool (hasInvariantMean_of_injective j hj hm)

end Singularity
