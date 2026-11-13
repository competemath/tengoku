/-
# Binary operations in a set operad

A binary element `g : S (Fin 2)` of a set operad acts on the operad itself: `bin g x y`, for
`x : S A` and `y : S B`, fills the two inputs of `g` with `x` and `y`, and has inputs `A ⊕ B`.
This is the calculus in which quadratic presentations are verified:

* relabellings move to the outside (`bin_map_left`, `bin_map_right`, `comp_map_left_of`,
  `comp_map_right`) and merge (`map_map`), so that every expression becomes a relabelling of a
  tree of `bin`s, and two such agree when the relabellings agree pointwise;
* composing into an input of `bin g u v` composes into `u` or `v` (`comp_inl_bin`,
  `comp_inr_bin`), and `bin g one one` is `g` (`bin_one_one`);
* a relation between two-fold composites of generators, stated with identities in the three
  leaves, holds with arbitrary elements in the leaves (`bin_assoc_of`, `bin_right_of`). This is
  the step from a relator in arity three to the identity it imposes on every algebra, and it is
  proved by substituting into the three leaves (`subst3`).

The first input of `g` is `0 : Fin 2` and the second is `1`; after filling the first, the second
is `slotOne : Without (Fin 2) 0`.
-/
import Tengoku.LeanOperads.Operad.SetPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The input types below are nested sums of subtypes, and deciding equality on them takes more
instances than the default search allows. -/
set_option synthInstance.maxSize 1024

universe v

namespace Operad

open Sym

namespace Sym

/-- The second input of a binary operation, once the first has been filled.-/
def slotOne : Without (Fin 2) 0 := ⟨1, by decide⟩

lemma eq_slotOne (j : Without (Fin 2) 0) : j = slotOne := by
  obtain ⟨k, hk⟩ := j
  have hk' : (k : ℕ) ≠ 0 := fun h => hk (Fin.ext h)
  have : k = 1 := Fin.ext (by have := k.isLt; simp only [Fin.isValue, Fin.val_one]; omega)
  subst this
  rfl

/--
@isnad1 id=false.1h2v.s7.297984ec6696 from=translated src=- shape=275330a1 vocab=b3cd8c24
-/
lemma ne_slotOne {A : Type} {j : Without (Fin 2) 0}
    (h : (Sum.inl j : Without (Fin 2) 0 ⊕ A) ≠ Sum.inl slotOne) : False :=
  h (congrArg Sum.inl (eq_slotOne j))

/-- The inputs of a binary operation with both inputs filled, in order.-/
def binEquiv (A B : Type) [DecidableEq A] :
    Without (Without (Fin 2) 0 ⊕ A) (Sum.inl slotOne) ⊕ B ≃ A ⊕ B where
  toFun x :=
    match x with
    | Sum.inl ⟨Sum.inl _, h⟩ => (ne_slotOne h).elim
    | Sum.inl ⟨Sum.inr a, _⟩ => Sum.inl a
    | Sum.inr b => Sum.inr b
  invFun x :=
    match x with
    | Sum.inl a => Sum.inl ⟨Sum.inr a, by simp⟩
    | Sum.inr b => Sum.inr b
  left_inv := by
    rintro (⟨j | a, h⟩ | b)
    · exact (ne_slotOne h).elim
    · rfl
    · rfl
  right_inv := by rintro (a | b) <;> rfl

/--
@isnad1 id=eq.1h3v.s11.7efe67f3cce5 from=translated src=- shape=f4553ab4 vocab=b6f76433
-/
@[simp] lemma binEquiv_inl_inr (A B : Type) [DecidableEq A] (a : A) (h) :
    binEquiv A B (Sum.inl ⟨Sum.inr a, h⟩) = Sum.inl a := rfl

/--
@isnad1 id=eq.0h3v.s10.7ec28e6cd716 from=translated src=- shape=4dcad7e3 vocab=b774b699
-/
@[simp] lemma binEquiv_inr (A B : Type) [DecidableEq A] (b : B) :
    binEquiv A B (Sum.inr b) = Sum.inr b := rfl

/-- The two inputs of a binary operation as `Unit ⊕ Unit`.-/
def finTwoSum : Fin 2 ≃ Unit ⊕ Unit where
  toFun k := if k = 0 then Sum.inl () else Sum.inr ()
  invFun x :=
    match x with
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  left_inv := by decide
  right_inv := by rintro (⟨⟩ | ⟨⟩) <;> rfl

/-- The inputs of `bin g u v ∘ᵢ y` when `i` is an input of `u`.-/
def binLeftEquiv {A B C : Type} [DecidableEq A] [DecidableEq B] (a : A) :
    (Without A a ⊕ C) ⊕ B ≃ Without (A ⊕ B) (Sum.inl a) ⊕ C where
  toFun x :=
    match x with
    | Sum.inl (Sum.inl a') => Sum.inl ⟨Sum.inl a'.1, fun h => a'.2 (Sum.inl_injective h)⟩
    | Sum.inl (Sum.inr c) => Sum.inr c
    | Sum.inr b => Sum.inl ⟨Sum.inr b, by simp⟩
  invFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a', h⟩ => Sum.inl (Sum.inl ⟨a', fun h' => h (congrArg Sum.inl h')⟩)
    | Sum.inl ⟨Sum.inr b, _⟩ => Sum.inr b
    | Sum.inr c => Sum.inl (Sum.inr c)
  left_inv := by rintro ((a' | c) | b) <;> rfl
  right_inv := by rintro (⟨a' | b, h⟩ | c) <;> rfl

/-- The inputs of `bin g u v ∘ᵢ y` when `i` is an input of `v`.-/
def binRightEquiv {A B C : Type} [DecidableEq A] [DecidableEq B] (b : B) :
    A ⊕ (Without B b ⊕ C) ≃ Without (A ⊕ B) (Sum.inr b) ⊕ C where
  toFun x :=
    match x with
    | Sum.inl a => Sum.inl ⟨Sum.inl a, by simp⟩
    | Sum.inr (Sum.inl b') => Sum.inl ⟨Sum.inr b'.1, fun h => b'.2 (Sum.inr_injective h)⟩
    | Sum.inr (Sum.inr c) => Sum.inr c
  invFun x :=
    match x with
    | Sum.inl ⟨Sum.inl a, _⟩ => Sum.inl a
    | Sum.inl ⟨Sum.inr b', h⟩ => Sum.inr (Sum.inl ⟨b', fun h' => h (congrArg Sum.inr h')⟩)
    | Sum.inr c => Sum.inr (Sum.inr c)
  left_inv := by rintro (a | (b' | c)) <;> rfl
  right_inv := by rintro (⟨a | b', h⟩ | c) <;> rfl

/-! ### Substituting at three inputs -/

section Subst3

variable {L : Type} [DecidableEq L]

/-- The second input, once the first has been filled.-/
def subst3Slot₂ (ℓ : Fin 3 ≃ L) (A : Type) : Without L (ℓ 0) ⊕ A :=
  Sum.inl ⟨ℓ 1, ℓ.injective.ne (by decide)⟩

/-- The third input, once the first two have been filled.-/
def subst3Slot₃ (ℓ : Fin 3 ≃ L) (A B : Type) [DecidableEq A] :
    Without (Without L (ℓ 0) ⊕ A) (subst3Slot₂ ℓ A) ⊕ B :=
  Sum.inl ⟨Sum.inl ⟨ℓ 2, ℓ.injective.ne (by decide)⟩, fun h =>
    ℓ.injective.ne (show (2 : Fin 3) ≠ 1 by decide) (congrArg Subtype.val (Sum.inl_injective h))⟩

/--
@isnad1 id=false.3h5v.s10.643a941b3288 from=translated src=- shape=2a58350f vocab=2d4dcdcf
-/
lemma subst3_absurd {A B : Type} [DecidableEq A] (ℓ : Fin 3 ≃ L) {l : L} {h0 : l ≠ ℓ 0}
    {h1 : (Sum.inl ⟨l, h0⟩ : Without L (ℓ 0) ⊕ A) ≠ subst3Slot₂ ℓ A}
    (h2 : (Sum.inl ⟨Sum.inl ⟨l, h0⟩, h1⟩ : Without (Without L (ℓ 0) ⊕ A) (subst3Slot₂ ℓ A) ⊕ B)
      ≠ subst3Slot₃ ℓ A B) : False := by
  obtain ⟨k, rfl⟩ := ℓ.surjective l
  fin_cases k
  · exact h0 rfl
  · exact h1 rfl
  · exact h2 rfl

/-- The leaves of a left comb, in order.-/
def fin3Left : Fin 3 ≃ (Unit ⊕ Unit) ⊕ Unit where
  toFun k :=
    if k = 0 then Sum.inl (Sum.inl ()) else if k = 1 then Sum.inl (Sum.inr ()) else Sum.inr ()
  invFun x :=
    match x with
    | Sum.inl (Sum.inl _) => 0
    | Sum.inl (Sum.inr _) => 1
    | Sum.inr _ => 2
  left_inv := by decide
  right_inv := by rintro ((⟨⟩ | ⟨⟩) | ⟨⟩) <;> rfl

/-- The leaves of a right comb, in order.-/
def fin3Right : Fin 3 ≃ Unit ⊕ (Unit ⊕ Unit) where
  toFun k :=
    if k = 0 then Sum.inl () else if k = 1 then Sum.inr (Sum.inl ()) else Sum.inr (Sum.inr ())
  invFun x :=
    match x with
    | Sum.inl _ => 0
    | Sum.inr (Sum.inl _) => 1
    | Sum.inr (Sum.inr _) => 2
  left_inv := by decide
  right_inv := by rintro (⟨⟩ | (⟨⟩ | ⟨⟩)) <;> rfl

/--
@isnad1 id=eq.0h0v.s5.158d17611284 from=translated src=- shape=56fc9f19 vocab=d6fa6daa
-/
lemma fin3Right_eq : fin3Right = fin3Left.trans (Equiv.sumAssoc Unit Unit Unit) := by
  ext k
  fin_cases k <;> rfl

end Subst3

end Sym

namespace SetOperad

variable {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]

/-! ## Moving relabellings -/

section Moves

variable {A A' B B' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C]

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/--
@isnad1 id=eq.0h7v.s6.fa2b6b643527 from=translated src=- shape=a29c14c8 vocab=5cc32ea5
-/
lemma map_map (e : A ≃ B) (f : B ≃ C) (x : S A) : map f (map e x) = map (e.trans f) x :=
  (map_trans e f x).symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.1h6v.s6.7112cf1e9ce2 from=translated src=- shape=f6e7af38 vocab=ac222f92
-/
lemma map_congr {e f : A ≃ B} (h : ∀ a, e a = f a) (x : S A) : map e x = map f x := by
  rw [Equiv.ext h]

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.1h4v.s6.3fb45f5e49b0 from=translated src=- shape=b2d1fe4a vocab=ac222f92
-/
lemma map_eq_self {e : A ≃ A} (h : ∀ a, e a = a) (x : S A) : map e x = x := by
  rw [map_congr (f := Equiv.refl A) h, map_refl]

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
lemma eq_map_symm_of_map_eq {e : A ≃ B} {x : S A} {y : S B} (h : map e x = y) :
    x = map e.symm y := by
  rw [← h, map_symm_map]

omit [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
/-- The right unit, solved for the composite.
@isnad1 id=eq.0h4v.s7.5eb2d0b91a6d from=translated src=- shape=844452bb vocab=37846557
-/
lemma comp_one' (i : A) (x : S A) : comp i x one = map (rightUnitEquiv i).symm x :=
  eq_map_symm_of_map_eq (comp_one i x)

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B']
  [Fintype C] [DecidableEq C] in
/-- The left unit, solved for the composite.
@isnad1 id=eq.0h3v.s7.c947557e8a9a from=translated src=- shape=4e6ecc17 vocab=23264356
-/
lemma one_comp' (y : S B) : comp () one y = map (leftUnitEquiv B).symm y :=
  eq_map_symm_of_map_eq (one_comp y)

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.0h8v.s9.66c0b07e26a0 from=translated src=- shape=d15b192f vocab=499af691
-/
lemma comp_map_left (σ : A ≃ A') (i : A) (x : S A) (y : S B) :
    comp (σ i) (map σ x) y = map (compEquiv σ (Equiv.refl B) i) (comp i x y) := by
  rw [map_comp, map_refl]

omit [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.0h8v.s8.822e40453007 from=translated src=- shape=aae14139 vocab=c367d508
-/
lemma comp_map_right (τ : B ≃ B') (i : A) (x : S A) (y : S B) :
    comp i x (map τ y) = map (Equiv.sumCongr (Equiv.refl (Without A i)) τ) (comp i x y) := by
  have h := map_comp (S := S) (Equiv.refl A) τ i x y
  rw [map_refl] at h
  have e : compEquiv (Equiv.refl A) τ i = Equiv.sumCongr (Equiv.refl (Without A i)) τ := by
    ext c; rcases c with a | b <;> rfl
  rw [e] at h
  exact h.symm

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- Composing at two equal inputs.
@isnad1 id=eq.1h7v.s8.7c6bdf865c71 from=translated src=- shape=4cb1b7ce vocab=f2c5918f
-/
lemma comp_slot {i i' : A} (h : i = i') (x : S A) (y : S B) :
    comp i' x y = map (slotEquiv h) (comp i x y) := by
  subst h
  exact (map_eq_self (fun c => by rcases c with a | b <;> rfl) _).symm

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **Relabelling the outer operation of a composite**, with the input named on either side. Used
as `rw [comp_map_left_of _ (i := i) ?h]`, which leaves `σ i = i'` to be closed by `rfl`.
@isnad1 id=eq.1h9v.s8.4b9a3e722431 from=translated src=- shape=f9475628 vocab=f51b6176
-/
lemma comp_map_left_of (σ : A ≃ A') {i : A} {i' : A'} (h : σ i = i') (x : S A) (y : S B) :
    comp i' (map σ x) y
      = map ((compEquiv σ (Equiv.refl B) i).trans (slotEquiv h)) (comp i x y) := by
  subst h
  rw [comp_map_left]
  exact map_congr (fun c => by rcases c with a | b <;> rfl) _

end Moves

/-! ## Filling both inputs of a binary operation -/

section Binary

variable {A A' B B' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C]

/-- **Fill the two inputs of a binary operation.**-/
def bin (g : S (Fin 2)) (x : S A) (y : S B) : S (A ⊕ B) :=
  map (binEquiv A B) (comp (Sum.inl slotOne) (comp (0 : Fin 2) g x) y)

omit [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.0h8v.s7.56858e2bba3d from=translated src=- shape=4bc2bee9 vocab=087bf5a9
-/
lemma bin_map_left (g : S (Fin 2)) (σ : A ≃ A') (x : S A) (y : S B) :
    bin g (map σ x) y = map (Equiv.sumCongr σ (Equiv.refl B)) (bin g x y) := by
  unfold bin
  rw [comp_map_right, comp_map_left_of _ (i := Sum.inl slotOne) ?h]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | a, hj⟩ | b
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.0h8v.s7.34c804dc3d42 from=translated src=- shape=bd513314 vocab=087bf5a9
-/
lemma bin_map_right (g : S (Fin 2)) (τ : B ≃ B') (x : S A) (y : S B) :
    bin g x (map τ y) = map (Equiv.sumCongr (Equiv.refl A) τ) (bin g x y) := by
  unfold bin
  rw [comp_map_right]
  simp only [map_map]
  refine map_congr (fun c => ?_) _
  rcases c with ⟨j | a, hj⟩ | b
  · exact (ne_slotOne hj).elim
  · rfl
  · rfl

omit [Fintype C] [DecidableEq C] in
/--
@isnad1 id=eq.0h10v.s7.1857b208b060 from=translated src=- shape=86da3a22 vocab=a1f553d6
-/
lemma bin_map (g : S (Fin 2)) (σ : A ≃ A') (τ : B ≃ B') (x : S A) (y : S B) :
    bin g (map σ x) (map τ y) = map (Equiv.sumCongr σ τ) (bin g x y) := by
  rw [bin_map_left, bin_map_right, map_map]
  exact map_congr (fun c => by rcases c with a | b <;> rfl) _

omit [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype B] [DecidableEq B]
  [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **Filling both inputs with the identity** gives back the operation.
@isnad1 id=eq.0h2v.s6.e29a40fffc27 from=translated src=- shape=bd332fa6 vocab=25332fef
-/
lemma bin_one_one (g : S (Fin 2)) : bin g one one = map finTwoSum g := by
  unfold bin
  rw [comp_one', comp_one']
  simp only [map_map]
  exact map_congr (fun k => by fin_cases k <;> rfl) _

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] [Fintype C] [DecidableEq C] in
/-- **The transposed operation** fills its inputs in the other order.
@isnad1 id=eq.0h6v.s7.5d282bea0a63 from=translated src=- shape=080713dd vocab=297331f9
-/
lemma bin_swap (g : S (Fin 2)) (x : S A) (y : S B) :
    bin (map (Equiv.swap 0 1) g) x y = map (Equiv.sumComm B A) (bin g y x) := by
  unfold bin
  rw [comp_map_left_of _ (i := (1 : Fin 2)) ?h1,
    comp_map_left_of _ (i := Sum.inl (⟨0, by decide⟩ : Without (Fin 2) 1)) ?h2,
    eq_map_symm_of_map_eq (comp_assoc_par (show (1 : Fin 2) ≠ 0 by decide) g x y)]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | b, hj⟩ | a
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
  · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- **Composing into the first argument** of a filled binary operation.
@isnad1 id=eq.0h9v.s9.46cef9d5ffd1 from=translated src=- shape=9e323415 vocab=cad7c6bc
-/
lemma comp_inl_bin (g : S (Fin 2)) (a : A) (u : S A) (v : S B) (y : S C) :
    comp (Sum.inl a) (bin g u v) y = map (binLeftEquiv a) (bin g (comp a u y) v) := by
  unfold bin
  rw [comp_map_left_of _ (i := Sum.inl ⟨Sum.inr a, by simp⟩) ?h1,
    eq_map_symm_of_map_eq (comp_assoc_par
      (show (Sum.inl slotOne : Without (Fin 2) 0 ⊕ A) ≠ Sum.inr a by simp) (comp 0 g u) v y),
    eq_map_symm_of_map_eq (comp_assoc_seq (0 : Fin 2) a g u y),
    comp_map_left_of _ (i := Sum.inl slotOne) ?h2]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | (a' | c), hj⟩ | b
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
    · rfl
  · rfl
  · rfl

omit [Fintype A'] [DecidableEq A'] [Fintype B'] [DecidableEq B'] in
/-- **Composing into the second argument** of a filled binary operation.
@isnad1 id=eq.0h9v.s9.c45c5ea7e564 from=translated src=- shape=b0ced3c4 vocab=11055757
-/
lemma comp_inr_bin (g : S (Fin 2)) (b : B) (u : S A) (v : S B) (y : S C) :
    comp (Sum.inr b) (bin g u v) y = map (binRightEquiv b) (bin g u (comp b v y)) := by
  unfold bin
  rw [comp_map_left_of _ (i := Sum.inr b) ?h1,
    eq_map_symm_of_map_eq (comp_assoc_seq (Sum.inl slotOne) b (comp 0 g u) v y)]
  · simp only [map_map]
    refine map_congr (fun c => ?_) _
    rcases c with ⟨j | a, hj⟩ | (b' | c)
    · exact (ne_slotOne hj).elim
    · rfl
    · rfl
    · rfl
  · rfl

end Binary

/-! ## Substituting into three inputs -/

section Subst3

variable {A B C L L' : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
  [Fintype C] [DecidableEq C] [Fintype L] [DecidableEq L] [Fintype L'] [DecidableEq L']

/-- **Commutativity holds generically.**
@isnad1 id=eq.1h6v.s8.c5e2c7fb8b5d from=translated src=- shape=c8609603 vocab=297331f9
-/
theorem bin_comm_of {g : S (Fin 2)} (h : map (Equiv.swap 0 1) g = g) (x : S A) (y : S B) :
    bin g y x = map (Equiv.sumComm A B) (bin g x y) := by
  rw [← bin_swap, h]

end Subst3

/-! ## Morphisms preserve filling -/

section Hom

universe w₁ w₂

/--
@isnad1 id=eq.0h8v.s7.333c0f0bec66 from=translated src=- shape=5106162c vocab=8169fee0
-/
lemma _root_.Operad.SetOperadHom.app_bin
    {T₁ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w₁} [SetOperad T₁]
    {T₂ : (A : Type) → [Fintype A] → [DecidableEq A] → Type w₂} [SetOperad T₂]
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (φ : SetOperadHom T₁ T₂) (g : T₁ (Fin 2)) (x : T₁ A) (y : T₁ B) :
    φ.app (A ⊕ B) (bin g x y) = bin (φ.app _ g) (φ.app A x) (φ.app B y) := by
  unfold bin
  rw [φ.app_map, φ.app_comp, φ.app_comp]

end Hom

end SetOperad

/-! ## Filling, in the syntax -/

namespace Syn

variable {T : ℕ → Type*} {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Fill the two inputs of a binary expression.-/
def bin (g : Syn T (Fin 2)) (x : Syn T A) (y : Syn T B) : Syn T (A ⊕ B) :=
  .map (binEquiv A B) (.comp (Sum.inl slotOne) (.comp (0 : Fin 2) g x) y)

/--
@isnad1 id=eq.0h8v.s7.f126a9910843 from=translated src=- shape=58075daf vocab=05e15c96
-/
@[simp] lemma eval_bin {S : (A : Type) → [Fintype A] → [DecidableEq A] → Type v} [SetOperad S]
    (f : ∀ n, T n → S (Fin n)) (g : Syn T (Fin 2)) (x : Syn T A) (y : Syn T B) :
    eval f (bin g x y) = SetOperad.bin (eval f g) (eval f x) (eval f y) := rfl

end Syn

/--
@isnad1 id=eq.0h7v.s7.9581d74e27ea from=translated src=- shape=cebe700d vocab=9d8064a4
-/
lemma Pres.mk_bin {T : ℕ → Type*}
    {ρ : ∀ {A : Type} [Fintype A] [DecidableEq A], Syn T A → Syn T A → Prop}
    {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (g : Syn T (Fin 2)) (x : Syn T A) (y : Syn T B) :
    Pres.mk (ρ := ρ) (Syn.bin g x y) = SetOperad.bin (Pres.mk g) (Pres.mk x) (Pres.mk y) := rfl

end Operad
