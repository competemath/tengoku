/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Tengoku

/-! # Wires

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

@[expose] public section

namespace Circuit

/-- A bundle of `I` wires, each carrying a value of type `V`. -/
def Wires (V : Type u) (I : ℕ) := Vector V I

instance [Preorder V] : Preorder (Wires V I) where
  le a b := ∀ i : Fin I, a.get i ≤ b.get i
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)
  lt_iff_le_not_ge _ _ := by rfl

/--
@isnad1 id=eq.1h4v.s5.8340b767c08c from=translated src=- shape=c70e8f1d vocab=94086008
-/
lemma Wires.ext : ∀ {n} {a b : Wires V n}, (∀ i : Fin n, a.get i = b.get i) → a = b := by
  intro n a b h; apply Vector.ext; intro i hi; exact h ⟨i, hi⟩

/--
@isnad1 id=eq.0h4v.s4.6b288fa405e8 from=translated src=- shape=a9a79140 vocab=148a128d
-/
@[simp]
lemma Wires.get_ofFn :
    ∀ {n : ℕ} {α : Type u} (f : Fin n → α) (i : Fin n), (Vector.ofFn f).get i = f i := by
  intro n α f i
  simp only [Vector.get, Vector.toArray_ofFn, Array.getElem_ofFn]; congr 1

/--
@isnad1 id=eq.1h5v.s5.9d241cc9fd73 from=translated src=- shape=1523043c vocab=466ce86d
-/
@[simp]
lemma Wires.get_cast {n m : ℕ} (h : n = m) (v : Wires V n) (i : Fin m) :
    (v.cast h).get i = v.get ⟨i.val, h ▸ i.isLt⟩ := by
  subst h; rfl

/--
@isnad1 id=eq.0h6v.s5.c46ce9d6bc9b from=translated src=- shape=6dea65d2 vocab=348be295
-/
lemma Wires.get_append_left {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin n) :
    (a.append b).get (Fin.castAdd m i) = a.get i := by
  unfold Wires at a b
  simp only [Vector.get, Fin.val_cast, Fin.val_castAdd, Vector.getElem_toArray]
  exact Vector.getElem_append_left i.isLt

/--
@isnad1 id=eq.0h6v.s5.ff3f663a6479 from=translated src=- shape=ba032193 vocab=b5048941
-/
lemma Wires.get_append_right {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin m) :
    (a.append b).get (Fin.natAdd n i) = b.get i := by
  unfold Wires at a b
  simp only [Vector.get, Fin.val_cast, Fin.val_natAdd, Vector.getElem_toArray]
  have h := Vector.getElem_append_right (xs := a) (ys := b) (i := n + i.val) (by omega) (by omega)
  simp only [Nat.add_sub_cancel_left] at h
  exact h

/--
@isnad1 id=eq.0h6v.s7.a18fd8c90597 from=translated src=- shape=1e801c70 vocab=a70169f0
-/
lemma Wires.get_append {n m : ℕ} (a : Wires V n) (b : Wires V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Wires.get_append_left, Fin.val_castAdd, j.isLt]
  · rw [Wires.get_append_right, dite_eq_right (by simp : ¬ (Fin.natAdd n j).val < n)]
    exact congrArg b.get (Fin.ext (by simp))

/--
@isnad1 id=eq.0h5v.s5.6bb06d87b70b from=translated src=- shape=a727da36 vocab=42049925
-/
lemma Wires.get_take {n k : ℕ} (a : Wires V n) (i : Fin (min k n)) :
    (a.take k).get i = a.get ⟨i.val, by omega⟩ := by
  unfold Wires at a
  simp only [Vector.get, Fin.val_cast, Vector.getElem_toArray, Vector.getElem_take]

/--
@isnad1 id=eq.0h5v.s6.da4b74e7ca0e from=translated src=- shape=e1d2389d vocab=bb8c1dde
-/
lemma Wires.get_drop {n k : ℕ} (a : Wires V n) (i : Fin (n - k)) :
    (a.drop k).get i = a.get ⟨k + i.val, by omega⟩ := by
  unfold Wires at a
  simp [Vector.get]

/-! The lemmas above are stated for `Wires`. `Vector.cast`, `Vector.take`, `Vector.drop` and
`Vector.append` all report their results at type `Vector`, and `simp` matches argument types up to
reducible unfolding only, so the same facts are restated below for `Vector`-typed arguments. -/

/--
@isnad1 id=eq.1h5v.s5.314f5e7af15f from=translated src=- shape=1523043c vocab=441dc81c
-/
lemma Wires.get_cast_vector {n m : ℕ} (h : n = m) (v : Vector V n) (i : Fin m) :
    (v.cast h).get i = v.get ⟨i.val, h ▸ i.isLt⟩ :=
  Wires.get_cast h v i

/--
@isnad1 id=eq.0h6v.s7.bad5eab5c9b7 from=translated src=- shape=1e801c70 vocab=398c6e2f
-/
lemma Wires.get_append_vector {n m : ℕ} (a : Vector V n) (b : Vector V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

/--
@isnad1 id=eq.0h6v.s7.af2a3872d489 from=translated src=- shape=2eeb1dcd vocab=5a44069b
-/
lemma Wires.get_append_wires_vector {n m : ℕ} (a : Wires V n) (b : Vector V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

/--
@isnad1 id=eq.0h6v.s7.2e9905feced1 from=translated src=- shape=2eeb1dcd vocab=5a44069b
-/
lemma Wires.get_append_vector_wires {n m : ℕ} (a : Vector V n) (b : Wires V m) (i : Fin (n + m)) :
    (a.append b).get i =
      if h : i.val < n then a.get ⟨i.val, h⟩ else b.get ⟨i.val - n, by omega⟩ :=
  Wires.get_append a b i

/--
@isnad1 id=eq.0h5v.s5.c9a31ce0798e from=translated src=- shape=a727da36 vocab=49d8dfdc
-/
lemma Wires.get_take_vector {n k : ℕ} (a : Vector V n) (i : Fin (min k n)) :
    (a.take k).get i = a.get ⟨i.val, by omega⟩ :=
  Wires.get_take a i

/--
@isnad1 id=eq.0h5v.s6.06955a3442a8 from=translated src=- shape=e1d2389d vocab=68233071
-/
lemma Wires.get_drop_vector {n k : ℕ} (a : Vector V n) (i : Fin (n - k)) :
    (a.drop k).get i = a.get ⟨k + i.val, by omega⟩ :=
  Wires.get_drop a i

end Circuit
