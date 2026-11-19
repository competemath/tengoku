/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.GradedFlagSequence
import Tengoku.Seed.SetTheory.Cardinal.Finite
import Tengoku.Seed.Order.Cover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interleaving graded maximal chains in a product

A shuffle path records, at every step, whether the left or right rank
increases.  Two saturated factor flags and such a path give a saturated flag
of the product.  The construction is injective: factor grades recover the
path, and surjectivity of both coordinate paths recovers the two flags.
-/

namespace HansenCograph

universe u v

/-- A monotone lattice path from `(0,0)` to `(n,m)`, with one coordinate
covering at each step.  Coordinate surjectivity is recorded explicitly for
use in recovering the two factor flags.-/
structure ShufflePath (n m : ℕ) where
  left : Fin (n + m + 1) → Fin (n + 1)
  right : Fin (n + m + 1) → Fin (m + 1)
  left_zero : left 0 = 0
  right_zero : right 0 = 0
  left_last : left (.last (n + m)) = .last n
  right_last : right (.last (n + m)) = .last m
  step : ∀ k : Fin (n + m),
    (left k.castSucc ⋖ left k.succ ∧ right k.castSucc = right k.succ) ∨
      (right k.castSucc ⋖ right k.succ ∧ left k.castSucc = left k.succ)
  left_surjective : Function.Surjective left
  right_surjective : Function.Surjective right

@[ext] theorem ShufflePath.ext {n m : ℕ} {s t : ShufflePath n m}
    (hleft : ∀ k, s.left k = t.left k)
    (hright : ∀ k, s.right k = t.right k) : s = t := by
  cases s
  cases t
  simp only [mk.injEq]
  exact ⟨funext hleft, funext hright⟩

noncomputable instance instFiniteShufflePath {n m : ℕ} :
    Finite (ShufflePath n m) :=
  Finite.of_injective (fun s ↦ (s.left, s.right)) (fun _ _ h ↦
    ShufflePath.ext (congrFun (congrArg Prod.fst h))
      (congrFun (congrArg Prod.snd h)))

section Product

variable {P : Type u} {Q : Type v}
variable [PartialOrder P] [BoundedOrder P]
variable [PartialOrder Q] [BoundedOrder Q]
variable {n m : ℕ}

/-- A saturated ranked flag carries covers between any two covering rank
indices, not only between the syntactically adjacent indices in its fields.-/
theorem RankedFlag.map_covBy (f : RankedFlag P n)
    {i j : Fin (n + 1)} (hij : i ⋖ j) : f i ⋖ f j := by
  have hij' : i.1 + 1 = j.1 := by
    exact Nat.covBy_iff_add_one_eq.mp (Fin.covBy_iff.mp hij)
  let k : Fin n := ⟨i.1, by omega⟩
  have hi : i = k.castSucc := Fin.ext (by rfl)
  have hj : j = k.succ := Fin.ext (by
    change j.1 = i.1 + 1
    exact hij'.symm)
  rw [hi, hj]
  exact f.covBy_succ k

/-- Interleave two saturated factor flags along a shuffle path.-/
def RankedFlag.prodOfShuffle (f : RankedFlag P n) (g : RankedFlag Q m)
    (s : ShufflePath n m) : RankedFlag (P × Q) (n + m) where
  toFun k := (f (s.left k), g (s.right k))
  map_zero := by
    apply Prod.ext
    · rw [s.left_zero, f.map_zero]
      rfl
    · rw [s.right_zero, g.map_zero]
      rfl
  map_last := by
    apply Prod.ext
    · rw [s.left_last, f.map_last]
      rfl
    · rw [s.right_last, g.map_last]
      rfl
  covBy_succ k := by
    rcases s.step k with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · exact Prod.covBy_iff.mpr (Or.inl
        ⟨f.map_covBy hl, congrArg g hr⟩)
    · exact Prod.covBy_iff.mpr (Or.inr
        ⟨g.map_covBy hr, congrArg f hl⟩)

/- The coordinate projections of an interleaved product flag recover the two
factor flags. These identities are the key to comparing shuffles whose
factor chain lengths are not fixed in advance. -/
theorem RankedFlag.prodOfShuffle_fst_range
    (f : RankedFlag P n) (g : RankedFlag Q m) (s : ShufflePath n m) :
    Prod.fst '' (prodOfShuffle f g s).toFlag.carrier = Set.range f := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := (prodOfShuffle f g s).mem_toFlag_iff z |>.mp hz
    exact ⟨s.left k, by simpa [prodOfShuffle] using congrArg Prod.fst hk⟩
  · rintro ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := s.left_surjective i
    refine ⟨(f i, g (s.right k)), ?_, ?_⟩
    · exact (prodOfShuffle f g s).mem_toFlag_iff _ |>.mpr ⟨k, by
        simp [prodOfShuffle, hk]
      ⟩
    · rfl

theorem RankedFlag.prodOfShuffle_snd_range
    (f : RankedFlag P n) (g : RankedFlag Q m) (s : ShufflePath n m) :
    Prod.snd '' (prodOfShuffle f g s).toFlag.carrier = Set.range g := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨k, hk⟩ := (prodOfShuffle f g s).mem_toFlag_iff z |>.mp hz
    exact ⟨s.right k, by simpa [prodOfShuffle] using congrArg Prod.snd hk⟩
  · rintro ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := s.right_surjective j
    refine ⟨(f (s.left k), g j), ?_, ?_⟩
    · exact (prodOfShuffle f g s).mem_toFlag_iff _ |>.mpr ⟨k, by
        simp [prodOfShuffle, hk]
      ⟩
    · rfl

/-- The interleaved product flag remembers both factor flags and the whole
shuffle path.-/
theorem RankedFlag.prodOfShuffle_injective :
    Function.Injective
      (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
        RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2) := by
  rintro ⟨f, g, s⟩ ⟨f', g', t⟩ h
  have hst : s = t := by
    have hout (k : Fin (n + m + 1)) :
        (f (s.left k), g (s.right k)) =
          (f' (t.left k), g' (t.right k)) := by
      exact congrArg (fun z : RankedFlag (P × Q) (n + m) ↦ z k) h
    have hleftMove (k : Fin (n + m)) :
        s.left k.castSucc ≠ s.left k.succ ↔
          t.left k.castSucc ≠ t.left k.succ := by
      rw [← f.injective.ne_iff, ← f'.injective.ne_iff]
      have h₀ := congrArg Prod.fst (hout k.castSucc)
      have h₁ := congrArg Prod.fst (hout k.succ)
      change f (s.left k.castSucc) = f' (t.left k.castSucc) at h₀
      change f (s.left k.succ) = f' (t.left k.succ) at h₁
      rw [h₀, h₁]
    have hcoords : ∀ k : Fin (n + m + 1),
        s.left k = t.left k ∧ s.right k = t.right k := by
      intro k
      induction k using Fin.induction with
      | zero => exact ⟨s.left_zero.trans t.left_zero.symm,
          s.right_zero.trans t.right_zero.symm⟩
      | succ k ih =>
          rcases s.step k with hs | hs <;> rcases t.step k with ht | ht
          · constructor
            · apply Fin.ext
              rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hs ht
              have hi := congrArg Fin.val ih.1
              omega
            · exact hs.2.symm.trans (ih.2.trans ht.2)
          · exact False.elim ((hleftMove k).mp hs.1.ne ht.2)
          · exact False.elim ((hleftMove k).mpr ht.1.ne hs.2)
          · constructor
            · exact hs.2.symm.trans (ih.1.trans ht.2)
            · apply Fin.ext
              rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at hs ht
              have hi := congrArg Fin.val ih.2
              omega
    apply ShufflePath.ext
    · exact fun k ↦ (hcoords k).1
    · exact fun k ↦ (hcoords k).2
  subst t
  have hf : f = f' := by
    apply RankedFlag.ext
    intro i
    obtain ⟨k, hk⟩ := s.left_surjective i
    have hv := congrArg
      (fun z : RankedFlag (P × Q) (n + m) ↦ (z k).1) h
    change f (s.left k) = f' (s.left k) at hv
    simpa only [hk] using hv
  have hg : g = g' := by
    apply RankedFlag.ext
    intro i
    obtain ⟨k, hk⟩ := s.right_surjective i
    have hv := congrArg
      (fun z : RankedFlag (P × Q) (n + m) ↦ (z k).2) h
    change g (s.right k) = g' (s.right k) at hv
    simpa only [hk] using hv
  cases hf
  cases hg
  rfl

/- The previous injectivity theorem fixes the two factor lengths.  The
projection identities upgrade it to a single injection ranging over all
lengths: the two projection ranges recover the lengths by cardinality. -/
def allRankedFlagProductEmbedding :
    (Σ n : ℕ, Σ m : ℕ,
      RankedFlag P n × RankedFlag Q m × ShufflePath n m) ↪
      Flag (P × Q) where
  toFun x := RankedFlag.toFlag
    (RankedFlag.prodOfShuffle x.2.2.1 x.2.2.2.1 x.2.2.2.2)
  inj' := by
    rintro ⟨n, m, f, g, s⟩ ⟨n', m', f', g', s'⟩ h
    have hfst : Set.range f = Set.range f' := by
      rw [← RankedFlag.prodOfShuffle_fst_range f g s,
        ← RankedFlag.prodOfShuffle_fst_range f' g' s']
      exact congrArg (fun z : Flag (P × Q) ↦ Prod.fst '' z.carrier) h
    have hsnd : Set.range g = Set.range g' := by
      rw [← RankedFlag.prodOfShuffle_snd_range f g s,
        ← RankedFlag.prodOfShuffle_snd_range f' g' s']
      exact congrArg (fun z : Flag (P × Q) ↦ Prod.snd '' z.carrier) h
    have hcard_f := congrArg (fun S : Set P => Nat.card S) hfst
    have hcard_g := congrArg (fun S : Set Q => Nat.card S) hsnd
    have hcard_n : n + 1 = n' + 1 := by
      simpa only [Nat.card_range_of_injective f.injective,
        Nat.card_range_of_injective f'.injective, Nat.card_fin] using hcard_f
    have hcard_m : m + 1 = m' + 1 := by
      simpa only [Nat.card_range_of_injective g.injective,
        Nat.card_range_of_injective g'.injective, Nat.card_fin] using hcard_g
    have hn : n = n' := by omega
    have hm : m = m' := by omega
    subst n'
    subst m'
    have hprod :
        RankedFlag.prodOfShuffle f g s = RankedFlag.prodOfShuffle f' g' s' :=
      RankedFlag.toFlag_injective h
    have hcode := RankedFlag.prodOfShuffle_injective (P := P) (Q := Q)
      (show (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
        RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2) (f, g, s) =
        (fun x : RankedFlag P n × RankedFlag Q m × ShufflePath n m ↦
          RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2) (f', g', s') by
        exact hprod)
    cases hcode
    rfl

/-- The canonical embedding of two factor flags and a shuffle path into a
product flag.-/
def rankedFlagProductEmbedding :
    RankedFlag P n × RankedFlag Q m × ShufflePath n m ↪
      RankedFlag (P × Q) (n + m) :=
  ⟨fun x ↦ RankedFlag.prodOfShuffle x.1 x.2.1 x.2.2,
    RankedFlag.prodOfShuffle_injective⟩

/-- Two factor flags and every available shuffle path give distinct product
flags.-/
theorem rankedFlag_product_card_lower_bound [Finite P] [Finite Q] :
    Nat.card (RankedFlag P n) * Nat.card (RankedFlag Q m) *
        Nat.card (ShufflePath n m) ≤
      Nat.card (RankedFlag (P × Q) (n + m)) := by
  simpa only [Nat.card_prod, Nat.mul_assoc] using
    Nat.card_le_card_of_injective rankedFlagProductEmbedding
      rankedFlagProductEmbedding.injective

end Product

end HansenCograph
