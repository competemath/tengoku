/-
# The associative operad, as the linearization of the set operad of linear orders

`Sym.LinOrd A` is the set of strict linear orders on `A`. Composing a linear order `s` on `B` into
the input `i` of a linear order `r` on `A` puts the block `B`, ordered by `s`, where `i` was: two
inputs from `A ∖ i` compare as in `r`, two from `B` as in `s`, and an input `a` of `A ∖ i` comes
before every input of `B` exactly when `a` comes before `i` (`Sym.LinOrd.comp`). This is a set
operad (`Sym.instSetOperadLinOrd`), and its linearization is **the symmetric associative operad**
`Sym.Ass R` (`Sym.Ass R A` has a basis indexed by the linear orders on `A`). The empty set has
one linear order, so `Sym.Ass` is the operad of *unital* associative algebras, unlike the
presented `Ass` of `Operad.AssPres`.

Forgetting the order is a morphism of set operads onto the commutative operad, and its
linearization is the augmentation `Sym.Ass.toCom : Ass → Com` (`Sym.Ass.toCom_single`). The
standard orders of the `Fin n` form a copy of the non-symmetric associative operad inside the
underlying non-symmetric operad of `Ass` (`Sym.Ass.ofNS`): the positional insertion bijection
carries a composite of standard orders to the standard order (`LinOrd.map_insertEquiv_comp_std`).
-/
import Tengoku.LeanOperads.Operad.SetOperad
import Tengoku.LeanOperads.Operad.SymNS

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u

namespace Operad

namespace Sym

/-- **A strict linear order** on `A`, as a relation.-/
structure LinOrd (A : Type) where
  /-- The order relation.-/
  lt : A → A → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ a b c, lt a b → lt b c → lt a c
  total : ∀ a b, a ≠ b → lt a b ∨ lt b a

namespace LinOrd

variable {A B D : Type}

/--
@isnad1 id=eq.1h3v.s4.15a31ee9eb5b from=translated src=- shape=0a505081 vocab=c450f847
-/
@[ext] lemma ext {x y : LinOrd A} (h : ∀ a b, x.lt a b ↔ y.lt a b) : x = y := by
  cases x
  cases y
  congr
  funext a b
  exact propext (h a b)

/-- Relabelling a linear order along a bijection.-/
def map {A B : Type} (e : A ≃ B) (x : LinOrd A) : LinOrd B where
  lt b b' := x.lt (e.symm b) (e.symm b')
  irrefl _ := x.irrefl _
  trans _ _ _ h h' := x.trans _ _ _ h h'
  total _ _ h := x.total _ _ fun h' => h (e.symm.injective h')

/--
@isnad1 id=iff.0h6v.s6.2a1c696ca6ba from=translated src=- shape=871214be vocab=2b315c32
-/
@[simp] lemma map_lt (e : A ≃ B) (x : LinOrd A) (b b' : B) :
    (map e x).lt b b' ↔ x.lt (e.symm b) (e.symm b') := Iff.rfl

/-- The unique linear order on one point.-/
def one : LinOrd Unit where
  lt _ _ := False
  irrefl _ := id
  trans _ _ _ h _ := h
  total a b h := absurd (Subsingleton.elim a b) h

variable [DecidableEq A]

/-- The order relation of a composite: the block `B` takes the place of `i`.-/
def compLt (r : A → A → Prop) (s : B → B → Prop) (i : A) :
    Without A i ⊕ B → Without A i ⊕ B → Prop
  | .inl a, .inl a' => r a.1 a'.1
  | .inl a, .inr _ => r a.1 i
  | .inr _, .inl a' => r i a'.1
  | .inr b, .inr b' => s b b'

/--
@isnad1 id=eq.0h7v.s6.1af06914738d from=translated src=- shape=f4df74ea vocab=33dc2ce7
-/
@[simp] lemma compLt_inl_inl (r : A → A → Prop) (s : B → B → Prop) (i : A) (a a' : Without A i) :
    compLt r s i (.inl a) (.inl a') = r a.1 a'.1 := rfl

/--
@isnad1 id=eq.0h7v.s5.762f32ac688c from=translated src=- shape=7f3810e2 vocab=7ac995b3
-/
@[simp] lemma compLt_inl_inr (r : A → A → Prop) (s : B → B → Prop) (i : A) (a : Without A i)
    (b : B) : compLt r s i (.inl a) (.inr b) = r a.1 i := rfl

/--
@isnad1 id=eq.0h7v.s5.0d3e474e63bc from=translated src=- shape=2a9fd7e1 vocab=7ac995b3
-/
@[simp] lemma compLt_inr_inl (r : A → A → Prop) (s : B → B → Prop) (i : A) (b : B)
    (a : Without A i) : compLt r s i (.inr b) (.inl a) = r i a.1 := rfl

/--
@isnad1 id=eq.0h7v.s5.e2d38d26f8aa from=translated src=- shape=9da027b3 vocab=c22cf07f
-/
@[simp] lemma compLt_inr_inr (r : A → A → Prop) (s : B → B → Prop) (i : A) (b b' : B) :
    compLt r s i (.inr b) (.inr b') = s b b' := rfl

/-- **Composition of linear orders**: the order `y` on `B` is inserted at the position of `i`.-/
def comp (i : A) (x : LinOrd A) (y : LinOrd B) : LinOrd (Without A i ⊕ B) where
  lt := compLt x.lt y.lt i
  irrefl := by
    rintro (a | b)
    · exact x.irrefl _
    · exact y.irrefl _
  trans := by
    rintro (a | b) (a' | b') (a'' | b'') h h' <;> simp only [compLt] at h h' ⊢
    · exact x.trans _ _ _ h h'
    · exact x.trans _ _ _ h h'
    · exact x.trans _ _ _ h h'
    · exact h
    · exact x.trans _ _ _ h h'
    · exact absurd (x.trans _ _ _ h h') (x.irrefl _)
    · exact h'
    · exact y.trans _ _ _ h h'
  total := by
    rintro (a | b) (a' | b') h <;> simp only [compLt]
    · exact x.total _ _ fun h' => h (congrArg Sum.inl (Subtype.ext h'))
    · exact x.total _ _ a.2
    · exact x.total _ _ (Ne.symm a'.2)
    · exact y.total _ _ fun h' => h (congrArg Sum.inr h')

/--
@isnad1 id=iff.0h7v.s5.ccc48f21b714 from=translated src=- shape=73bd3325 vocab=609f58a0
-/
@[simp] lemma comp_lt (i : A) (x : LinOrd A) (y : LinOrd B) (u v : Without A i ⊕ B) :
    (comp i x y).lt u v ↔ compLt x.lt y.lt i u v := Iff.rfl

end LinOrd

open LinOrd in
/-- **The set operad of linear orders.**-/
instance instSetOperadLinOrd : SetOperad (fun A _ _ => LinOrd A) where
  map e x := LinOrd.map e x
  map_refl x := LinOrd.ext fun _ _ => Iff.rfl
  map_trans e f x := LinOrd.ext fun _ _ => Iff.rfl
  one := LinOrd.one
  comp i x y := LinOrd.comp i x y
  map_comp σ τ i x y := by
    refine LinOrd.ext ?_
    rintro (a | b) (a' | b') <;> simp
  comp_one {A} _ _ i x := by
    refine LinOrd.ext fun a a' => ?_
    by_cases ha : a = i <;> by_cases ha' : a' = i
    · subst ha
      subst ha'
      simp only [map_lt, rightUnitEquiv_symm_self, comp_lt, compLt_inr_inr]
      exact ⟨fun h => h.elim, fun h => absurd h (x.irrefl _)⟩
    · subst ha
      simp [rightUnitEquiv_symm_self, rightUnitEquiv_symm_of_ne ha']
    · subst ha'
      simp [rightUnitEquiv_symm_self, rightUnitEquiv_symm_of_ne ha]
    · simp [rightUnitEquiv_symm_of_ne ha, rightUnitEquiv_symm_of_ne ha']
  one_comp y := LinOrd.ext fun _ _ => Iff.rfl
  comp_assoc_seq i j x y z := by
    refine LinOrd.ext ?_
    rintro (a | b | d) (a' | b' | d') <;> simp
  comp_assoc_par hik x y z := by
    refine LinOrd.ext ?_
    rintro (⟨(a | d), ha⟩ | b) (⟨(a' | d'), ha'⟩ | b') <;> simp

/-- **The symmetric associative operad**: `Ass R A` is free on the linear orders on `A`.-/
abbrev Ass (R : Type u) [CommRing R] := Lin R (fun A _ _ => LinOrd A)

namespace Ass

variable (R : Type u) [CommRing R]

/-- Forgetting the order, as a morphism of set operads into the underlying set operad of `Com`.-/
def forget : SetOperadHom (fun A _ _ => LinOrd A) (Und R (Com R)) where
  app _ _ _ _ := Und.of R (Com R) (1 : R)
  app_map _ _ := rfl
  app_one := rfl
  app_comp _ _ _ := by
    show (1 : R) = 1 * 1
    rw [mul_one]

/-- **The augmentation** `Ass → Com`, sending every linear order to `1`.-/
noncomputable def toCom : SymOperadHom R (Ass R) (Com R) := (forget R).linExtend

end Ass

/-! ## The standard orders -/

namespace LinOrd

/-- The standard order on `Fin n`.-/
def std (n : ℕ) : LinOrd (Fin n) where
  lt a b := a < b
  irrefl a := lt_irrefl a
  trans _ _ _ h h' := lt_trans h h'
  total _ _ h := lt_or_gt_of_ne h

/--
@isnad1 id=iff.0h3v.s4.74e8a1aaf884 from=translated src=- shape=4c2bdad3 vocab=44a7bd90
-/
@[simp] lemma std_lt (n : ℕ) (a b : Fin n) : (std n).lt a b ↔ a < b := Iff.rfl

/-- **The positional insertion carries a composite of standard orders to the standard order.**
@isnad1 id=eq.0h3v.s7.b4baed488f12 from=translated src=- shape=2b9603e4 vocab=9b36c02c
-/
theorem map_insertEquiv_comp_std (a b n : ℕ) :
    map (insertEquiv a b n) (comp (⟨a, by omega⟩ : Fin (a + 1 + b)) (std (a + 1 + b)) (std n))
      = std (a + n + b) := by
  ext u v
  obtain ⟨x, rfl⟩ := (insertEquiv a b n).surjective u
  obtain ⟨y, rfl⟩ := (insertEquiv a b n).surjective v
  simp only [map_lt, Equiv.symm_apply_apply, comp_lt, std_lt, Fin.lt_def]
  rcases x with k | j <;> rcases y with k' | j'
  · have hk : (k.1 : ℕ) ≠ a := fun h => k.2 (Fin.ext h)
    have hk' : (k'.1 : ℕ) ≠ a := fun h => k'.2 (Fin.ext h)
    simp only [compLt_inl_inl, std_lt, Fin.lt_def, insertEquiv_inl_val]
    split_ifs <;> omega
  · have hk : (k.1 : ℕ) ≠ a := fun h => k.2 (Fin.ext h)
    simp only [compLt_inl_inr, std_lt, Fin.lt_def, insertEquiv_inl_val, insertEquiv_inr_val]
    split_ifs <;> omega
  · have hk' : (k'.1 : ℕ) ≠ a := fun h => k'.2 (Fin.ext h)
    simp only [compLt_inr_inl, std_lt, Fin.lt_def, insertEquiv_inl_val, insertEquiv_inr_val]
    split_ifs <;> omega
  · simp only [compLt_inr_inr, std_lt, Fin.lt_def, insertEquiv_inr_val]
    omega

/--
@isnad1 id=eq.0h0v.s4.b422cdebe818 from=translated src=- shape=1e9f3431 vocab=6196cfcc
-/
lemma map_unitFinOne_one : map unitFinOne one = std 1 := by
  ext u v
  simp only [map_lt, std_lt]
  exact ⟨fun h => h.elim, fun h => absurd h (by omega)⟩

end LinOrd

namespace Ass

variable (R : Type u) [CommRing R]

end Ass

end Sym

end Operad
