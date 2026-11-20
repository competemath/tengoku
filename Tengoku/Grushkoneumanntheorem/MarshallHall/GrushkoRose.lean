import Tengoku.Grushkoneumanntheorem.MarshallHall.GrushkoFoldStep

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
## The canonical subdivided rose

This file constructs the initial labelled graph for a finite tuple in a binary
free product.  Each tuple entry is represented by a path around its own
subdivided petal; all petal endpoints are the common base vertex.  The
construction is intentionally independent of the fold operation, so the
later induction can use it as a genuine finite marked graph rather than as a
picture of a word.
-/

open Function Monoid.Coprod Quiver

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

def RoseVertex {n : ℕ} (w : Fin n → List (Sum G H)) :=
  Option (Σ i : Fin n, Fin ((w i).length - 1))

def rosePosition {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin ((w i).length + 1)) : RoseVertex w :=
  if h0 : k.val = 0 then none
  else if hlast : k.val = (w i).length then none
  else some ⟨i, ⟨k.val - 1, by omega⟩⟩

/--
@isnad1 id=eq.0h5v.s6.6706a0c9641d from=translated src=- shape=cd1607c8 vocab=058b5633
-/
@[simp] theorem rosePosition_zero {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    rosePosition w i ⟨0, by omega⟩ = none := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/--
@isnad1 id=eq.0h6v.s7.5d9b3f3308ae from=translated src=- shape=e1f2a6f7 vocab=7b198c36
-/
@[simp] theorem rosePosition_interior {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin ((w i).length - 1)) :
    rosePosition w i ⟨k.val + 1, by omega⟩ = some ⟨i, k⟩ := by
  simp [rosePosition]
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

structure RoseEdge {n : ℕ} (w : Fin n → List (Sum G H)) where
  i : Fin n
  k : Fin (w i).length
  forward : Bool

def RoseEdge.flip {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseEdge w
  | ⟨i, k, true⟩ => ⟨i, k, false⟩
  | ⟨i, k, false⟩ => ⟨i, k, true⟩

def roseEdgeSource {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseVertex w
  | ⟨i, k, true⟩ => rosePosition w i ⟨k.val, by omega⟩
  | ⟨i, k, false⟩ => rosePosition w i ⟨k.val + 1, by omega⟩

def roseEdgeTarget {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → RoseVertex w
  | ⟨i, k, true⟩ => rosePosition w i ⟨k.val + 1, by omega⟩
  | ⟨i, k, false⟩ => rosePosition w i ⟨k.val, by omega⟩

/--
@isnad1 id=eq.0h5v.s5.a4fea30d3b3c from=translated src=- shape=2f79ba4c vocab=4b5b3262
-/
theorem roseEdgeSource_flip {n : ℕ} {w : Fin n → List (Sum G H)}
    (e : RoseEdge w) :
    roseEdgeSource (RoseEdge.flip e) = roseEdgeTarget e := by
  cases e with
  | mk i k forward =>
      cases forward <;> rfl

/--
@isnad1 id=eq.0h5v.s5.0727957df07c from=translated src=- shape=2f79ba4c vocab=4b5b3262
-/
theorem roseEdgeTarget_flip {n : ℕ} {w : Fin n → List (Sum G H)}
    (e : RoseEdge w) :
    roseEdgeTarget (RoseEdge.flip e) = roseEdgeSource e := by
  cases e with
  | mk i k forward =>
      cases forward <;> rfl

def roseEdgeLabel {n : ℕ} {w : Fin n → List (Sum G H)} :
    RoseEdge w → Sum G H
  | ⟨i, k, true⟩ => (w i).get k
  | ⟨i, k, false⟩ => factorWordInv ((w i).get k)

instance roseQuiver {n : ℕ} (w : Fin n → List (Sum G H)) :
    Quiver (RoseVertex w) where
  Hom a b := {e : RoseEdge w // roseEdgeSource e = a ∧ roseEdgeTarget e = b}

def roseReverseArrow {n : ℕ} {w : Fin n → List (Sum G H)}
    {a b : RoseVertex w} (e : a ⟶ b) : b ⟶ a :=
  ⟨RoseEdge.flip e.1, by rw [roseEdgeSource_flip, e.2.2],
    by rw [roseEdgeTarget_flip, e.2.1]⟩

instance roseHasReverse {n : ℕ} (w : Fin n → List (Sum G H)) :
    HasInvolutiveReverse (RoseVertex w) where
  reverse' := fun {_ _} e => roseReverseArrow (G := G) (H := H) e
  inv' := by
    intro a b e
    apply Subtype.ext
    change RoseEdge.flip (RoseEdge.flip e.1) = e.1
    cases e.1 with
    | mk i k forward =>
        cases forward <;> rfl

/--
@isnad1 id=ne.0h5v.s6.ea8608d1c15b from=translated src=- shape=bf2ab196 vocab=7c2c9e3e
-/
theorem rose_allArrow_reverse_ne {n : ℕ}
    (w : Fin n → List (Sum G H))
    (e : AllArrow (V := RoseVertex w)) :
    allArrowReverse e ≠ e := by
  rintro h
  cases e with
  | mk a be =>
    cases be with
    | mk b e =>
      cases e with
      | mk edge hsrc =>
        have hab : b = a := congrArg allArrowSource h
        subst b
        have hsnd : (⟨a, Quiver.reverse ⟨edge, hsrc⟩⟩ :
            Σ b : RoseVertex w, (a ⟶ b)) =
            ⟨a, ⟨edge, hsrc⟩⟩ := by
          injection h
        have hhom : (Quiver.reverse ⟨edge, hsrc⟩ : a ⟶ a) =
            ⟨edge, hsrc⟩ := by
          injection hsnd
        have hedge : RoseEdge.flip edge = edge := by
          have hedge' := congrArg Subtype.val hhom
          change RoseEdge.flip edge = edge at hedge'
          exact hedge'
        cases edge with
        | mk i k forward =>
          cases forward <;> simp [RoseEdge.flip] at hedge

def roseLabelling {n : ℕ} (w : Fin n → List (Sum G H)) :
    BinaryLabelling (G := G) (H := H) (V := RoseVertex w) where
  label := fun e => roseEdgeLabel e.1
  reverse_label := by
    intro a b e
    change roseEdgeLabel (RoseEdge.flip e.1) =
      factorWordInv (roseEdgeLabel e.1)
    cases e.1 with
    | mk i k forward =>
        cases forward
        · simpa [roseEdgeLabel, RoseEdge.flip, factorWordInv] using
            (factorWordInv_factorWordInv
              (G := G) (H := H) ((w i).get k)).symm
        · rfl

def roseForwardArrow {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) (k : Fin (w i).length) :
    rosePosition w i ⟨k.val, by omega⟩ ⟶
      rosePosition w i ⟨k.val + 1, by omega⟩ :=
  ⟨⟨i, k, true⟩, rfl, rfl⟩

def roseForwardPathAux {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) : ∀ (k : ℕ) (_hk : k ≤ (w i).length),
      @Quiver.Path (RoseVertex w) (roseQuiver w)
        none (rosePosition w i ⟨k, by omega⟩)
  | 0, hk => Path.nil
  | k + 1, hk =>
      let p := roseForwardPathAux w i k (by omega)
      let e := roseForwardArrow w i ⟨k, by omega⟩
      p.cons e

/--
@isnad1 id=eq.1h6v.s7.bc816cdd661f from=translated src=- shape=85bdaf4a vocab=3b6c9aca
-/
theorem roseForwardPathAux_labels {n : ℕ} (w : Fin n → List (Sum G H))
    (i : Fin n) :
    ∀ (k : ℕ) (hk : k ≤ (w i).length),
      (roseLabelling w).pathLabels
          (roseForwardPathAux w i k hk) = (w i).take k := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      rw [roseForwardPathAux]
      simp only [BinaryLabelling.pathLabels, List.append_assoc]
      rw [ih (by omega)]
      simpa [roseLabelling, roseForwardArrow, roseEdgeLabel] using
        (List.take_concat_get' (w i) k (by omega))

noncomputable instance roseVertexFintype {n : ℕ} (w : Fin n → List (Sum G H)) :
    Fintype (RoseVertex w) := by
  dsimp [RoseVertex]
  infer_instance

/--
@isnad1 id=eq.0h3v.s5.07c68c47f79f from=translated src=- shape=ea41cdc8 vocab=556de29d
-/
theorem binaryReducedLetters_length (x : G ∗ H) :
    (binaryReducedLetters (G := G) (H := H) x).length = factorWordLength x := by
  simpa [binaryReducedLetters, binaryReducedLength] using
    (factorWordLength_eq_binaryReducedLength (G := G) (H := H) x).symm

end GeneralGrushko
end MarshallHall
