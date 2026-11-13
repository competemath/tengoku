/-
# Colored operads

A **colored operad** with colors `C` has operations with a finite set of inputs `A` colored by
`c : A → C` and an output color `d`; the input `i` of an operation can be filled by an operation
whose output color is the color of that input. Relabellings and compositions carry proofs that the
colors match, so that no transport along equalities of colors enters the axioms.

* `ColOperad`: colored operads in `R`-modules, in the species convention of `Operad.SymOperad`.
* `ColOperadHom`: their morphisms.
* `ColEnd R V`: **the endomorphism colored operad** of a family of modules `V : C → Type`, the
  multilinear maps `∏ₐ V (c a) → V d`; `ColAlgebra`: an algebra over a colored operad, a morphism
  into it.
* **Operads are one-colored operads** (`SymOperad.toCol`), with the same algebras
  (`SymOperad.colAlgebraEquiv`).
-/
import Tengoku.LeanOperads.Operad.EndOperad

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v w x

namespace Operad

open Sym

/-- The colors of the inputs of a composite.-/
abbrev compColor {C : Type w} {A B : Type} [DecidableEq A] (cA : A → C) (i : A) (cB : B → C) :
    Without A i ⊕ B → C :=
  Sum.elim (fun a => cA a.1) cB

/-- **A colored operad in `R`-modules**: relabellings preserving the colors, units of every color,
and partial compositions along matching colors.-/
class ColOperad (R : Type u) [CommRing R] (C : Type w)
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type v)
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (P A c d)] where
  /-- Relabelling the inputs along a bijection preserving the colors.-/
  map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {c : A → C}
    {c' : B → C} {d : C} (e : A ≃ B) (h : ∀ a, c' (e a) = c a) : P A c d →ₗ[R] P B c' d
  /-- Relabelling along the identity changes nothing.-/
  map_refl {A : Type} [Fintype A] [DecidableEq A] {c : A → C} {d : C}
    (h : ∀ a, c ((Equiv.refl A) a) = c a) (x : P A c d) : map (Equiv.refl A) h x = x
  /-- Relabelling is functorial.-/
  map_trans {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype D]
    [DecidableEq D] {c : A → C} {c' : B → C} {c'' : D → C} {d : C} (e : A ≃ B) (f : B ≃ D)
    (h₁ : ∀ a, c' (e a) = c a) (h₂ : ∀ b, c'' (f b) = c' b) (h₃ : ∀ a, c'' ((e.trans f) a) = c a)
    (x : P A c d) : map (e.trans f) h₃ x = map f h₂ (map e h₁ x)
  /-- The identity operation of each color.-/
  one (c : C) : P Unit (fun _ => c) c
  /-- **Partial composition**: insert an operation with output color `d'` at an input `i` of that
  color.-/
  comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {cA : A → C}
    {cB : B → C} {d d' : C} (i : A) (h : d' = cA i) :
    P A cA d →ₗ[R] P B cB d' →ₗ[R] P (Without A i ⊕ B) (compColor cA i cB) d
  /-- **Equivariance**: composition is natural in bijections of both input sets.-/
  map_comp {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] {cA : A → C} {cA' : A' → C}
    {cB : B → C} {cB' : B' → C} {d d' : C} (σ : A ≃ A') (τ : B ≃ B') (i : A)
    (hσ : ∀ a, cA' (σ a) = cA a) (hτ : ∀ b, cB' (τ b) = cB b) (h : d' = cA i)
    (h' : d' = cA' (σ i))
    (hc : ∀ z, compColor cA' (σ i) cB' (compEquiv σ τ i z) = compColor cA i cB z)
    (x : P A cA d) (y : P B cB d') :
    map (compEquiv σ τ i) hc (comp i h x y) = comp (σ i) h' (map σ hσ x) (map τ hτ y)
  /-- The right unit law.-/
  comp_one {A : Type} [Fintype A] [DecidableEq A] {cA : A → C} {d : C} (i : A)
    (hc : ∀ z, cA (rightUnitEquiv i z) = compColor cA i (fun _ => cA i) z) (x : P A cA d) :
    map (rightUnitEquiv i) hc (comp i rfl x (one (cA i))) = x
  /-- The left unit law.-/
  one_comp {B : Type} [Fintype B] [DecidableEq B] {cB : B → C} {d : C}
    (hc : ∀ z, cB (leftUnitEquiv B z) = compColor (fun _ : Unit => d) () cB z) (y : P B cB d) :
    map (leftUnitEquiv B) hc (comp () rfl (one d) y) = y
  /-- Sequential associativity.-/
  comp_assoc_seq {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {cA : A → C} {cB : B → C} {cD : D → C} {dA dB dD : C} (i : A)
    (j : B) (h₁ : dB = cA i) (h₂ : dD = cB j)
    (hc : ∀ z, compColor cA i (compColor cB j cD) (seqEquiv i j D z)
      = compColor (compColor cA i cB) (Sum.inr j) cD z)
    (x : P A cA dA) (y : P B cB dB) (z : P D cD dD) :
    map (seqEquiv i j D) hc (comp (Sum.inr j) h₂ (comp i h₁ x y) z)
      = comp i h₁ x (comp j h₂ y z)
  /-- Parallel associativity.-/
  comp_assoc_par {A B D : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype D] [DecidableEq D] {cA : A → C} {cB : B → C} {cD : D → C} {dA dB dD : C} {i k : A}
    (hik : i ≠ k) (h₁ : dB = cA i) (h₂ : dD = cA k)
    (hc : ∀ z, compColor (compColor cA k cD) (Sum.inl ⟨i, hik⟩) cB (parEquiv hik B D z)
      = compColor (compColor cA i cB) (Sum.inl ⟨k, Ne.symm hik⟩) cD z)
    (x : P A cA dA) (y : P B cB dB) (z : P D cD dD) :
    map (parEquiv hik B D) hc (comp (Sum.inl ⟨k, Ne.symm hik⟩) h₂ (comp i h₁ x y) z)
      = comp (Sum.inl ⟨i, hik⟩) h₁ (comp k h₂ x z) y

/-- **A morphism of colored operads**: a family of linear maps commuting with relabelling,
preserving the units and the compositions.-/
structure ColOperadHom (R : Type u) [CommRing R] (C : Type w)
    (P : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type v)
    (Q : (A : Type) → [Fintype A] → [DecidableEq A] → (A → C) → C → Type x)
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (P A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), AddCommGroup (Q A c d)]
    [∀ (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C), Module R (Q A c d)]
    [ColOperad R C P] [ColOperad R C Q] where
  /-- The component at colored inputs and an output color.-/
  app (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C) : P A c d →ₗ[R] Q A c d
  /-- Components commute with relabelling.-/
  app_map {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {c : A → C}
    {c' : B → C} {d : C} (e : A ≃ B) (h : ∀ a, c' (e a) = c a) (x : P A c d) :
    app B c' d (ColOperad.map (R := R) e h x) = ColOperad.map (R := R) e h (app A c d x)
  /-- The units go to the units.-/
  app_one (c : C) : app Unit (fun _ => c) c (ColOperad.one R c) = ColOperad.one R c
  /-- Compositions go to compositions.-/
  app_comp {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] {cA : A → C}
    {cB : B → C} {d d' : C} (i : A) (h : d' = cA i) (x : P A cA d) (y : P B cB d') :
    app (Without A i ⊕ B) (compColor cA i cB) d (ColOperad.comp (R := R) i h x y)
      = ColOperad.comp (R := R) i h (app A cA d x) (app B cB d' y)

/-! ## Operads as one-colored operads -/

/-- **The one-colored species of a species.**-/
@[nolint unusedArguments]
def OneCol (P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v) :
    (A : Type) → [Fintype A] → [DecidableEq A] → (A → Unit) → Unit → Type v :=
  fun A _ _ _ _ => P A

section OneCol

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)]

instance OneCol.instAddCommGroup (A : Type) [Fintype A] [DecidableEq A] (c : A → Unit)
    (d : Unit) : AddCommGroup (OneCol P A c d) :=
  inferInstanceAs (AddCommGroup (P A))

instance OneCol.instModule (A : Type) [Fintype A] [DecidableEq A] (c : A → Unit) (d : Unit) :
    Module R (OneCol P A c d) :=
  inferInstanceAs (Module R (P A))

variable [SymOperad R P]

/-- **An operad is a one-colored operad.**-/
noncomputable instance SymOperad.toCol : ColOperad R Unit (OneCol P) where
  map e _ := SymOperad.map (R := R) (P := P) e
  map_refl _ x := SymOperad.map_refl (R := R) (P := P) x
  map_trans e f _ _ _ x := SymOperad.map_trans (R := R) (P := P) e f x
  one _ := SymOperad.one R
  comp i _ := SymOperad.comp (R := R) (P := P) i
  map_comp σ τ i _ _ _ _ _ x y := SymOperad.map_comp (R := R) (P := P) σ τ i x y
  comp_one i _ x := SymOperad.comp_one (R := R) (P := P) i x
  one_comp _ y := SymOperad.one_comp (R := R) (P := P) y
  comp_assoc_seq i j _ _ _ x y z := SymOperad.comp_assoc_seq (R := R) (P := P) i j x y z
  comp_assoc_par hik _ _ _ x y z := SymOperad.comp_assoc_par (R := R) (P := P) hik x y z

end OneCol

/-! ## Morphisms of one-colored operads -/

section OneColHom

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {Q : (A : Type) → [Fintype A] → [DecidableEq A] → Type x}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (Q A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (Q A)] [SymOperad R Q]

/-- **Morphisms of one-colored operads are morphisms of operads.**-/
def SymOperad.colHomEquiv : ColOperadHom R Unit (OneCol P) (OneCol Q) ≃ SymOperadHom R P Q where
  toFun φ :=
    { app A _ _ := φ.app A (fun _ => ()) ()
      app_map e x := φ.app_map e (fun _ => rfl) x
      app_one := φ.app_one ()
      app_comp i x y := φ.app_comp i rfl x y }
  invFun f :=
    { app A _ _ _ _ := f.app A
      app_map e _ x := f.app_map e x
      app_one _ := f.app_one
      app_comp i _ x y := f.app_comp i x y }
  left_inv φ := by
    obtain ⟨app, h1, h2, h3⟩ := φ
    congr
  right_inv _ := rfl

end OneColHom

/-! ## The endomorphism colored operad -/

section ColEnd

variable {R : Type u} [CommRing R] {C : Type w} {V : C → Type v} [∀ c, AddCommGroup (V c)]
  [∀ c, Module R (V c)]

variable (R V) in
/-- Transport along an equality of colors.-/
def castV : ∀ {c c' : C}, c = c' → V c →ₗ[R] V c'
  | _, _, rfl => LinearMap.id

/--
@isnad1 id=eq.1h5v.s7.759b76245435 from=translated src=- shape=2271ebc7 vocab=cd85ec90
-/
@[simp] lemma castV_self {c : C} (h : c = c) (x : V c) : castV R V h x = x := rfl

/--
@isnad1 id=eq.2h7v.s8.61235f356315 from=translated src=- shape=f75b198c vocab=3fbd2289
-/
lemma castV_castV {c c' c'' : C} (h : c = c') (h' : c' = c'') (x : V c) :
    castV R V h' (castV R V h x) = castV R V (h.trans h') x := by
  subst h
  subst h'
  rfl

variable (R V) in
/-- **The endomorphism colored operad** of a family of modules: the multilinear maps
`∏ₐ V (c a) → V d`.-/
@[nolint unusedArguments]
abbrev ColEnd (A : Type) [Fintype A] [DecidableEq A] (c : A → C) (d : C) : Type _ :=
  MultilinearMap R (fun a => V (c a)) (V d)

section Feed

variable {A B : Type} [DecidableEq A] {cA : A → C} {cB : B → C} {d' : C}

variable (R) in
/-- Feed `w`, of the color of the input `i`, into that input, the other inputs read off `v`.-/
def cfeed (i : A) (h : d' = cA i) (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z))
    (w : V d') : ∀ a, V (cA a) :=
  fun a => if ha : a = i then castV R V (h.trans (congrArg cA ha.symm)) w
    else v (Sum.inl ⟨a, ha⟩)

/--
@isnad1 id=eq.1h11v.s7.446536eb9b20 from=translated src=- shape=0173872c vocab=56fd3db4
-/
lemma cfeed_self (i : A) (h : d' = cA i) (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z))
    (w : V d') : cfeed R i h v w i = castV R V h w :=
  dite_eq_left rfl

/--
@isnad1 id=eq.2h12v.s7.125786dd0954 from=translated src=- shape=9be9819e vocab=52d5428d
-/
lemma cfeed_of_ne {i a : A} (ha : a ≠ i) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') :
    cfeed R i h v w a = v (Sum.inl ⟨a, ha⟩) :=
  dite_eq_right ha

variable [DecidableEq B]

/--
@isnad1 id=eq.1h13v.s7.7b946cf55692 from=translated src=- shape=0761d6e5 vocab=685d8fa0
-/
lemma cfeed_update_inr (i : A) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') (b : B) (z : V (cB b)) :
    cfeed R i h (Function.update v (Sum.inr b) z) w = cfeed R i h v w := by
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

omit [DecidableEq B] in
/--
@isnad1 id=eq.1h11v.s8.22aa7ad48c7c from=translated src=- shape=e3ca6e5c vocab=6cc28fd2
-/
lemma cfeed_eq_update (i : A) (h : d' = cA i)
    (v : ∀ z : Without A i ⊕ B, V (compColor cA i cB z)) (w : V d') :
    cfeed R i h v w = Function.update (cfeed R i h v 0) i (castV R V h w) := by
  funext a
  by_cases ha : a = i
  · subst ha
    rw [Function.update_self, cfeed_self]
  · rw [Function.update_of_ne ha, cfeed_of_ne ha, cfeed_of_ne ha]

end Feed

variable {A A' B B' : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
  [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B']

omit [Fintype A] [Fintype B] in
/--
@isnad1 id=eq.1h11v.s10.4a4d0e24e847 from=translated src=- shape=a60f97cc vocab=a5772380
-/
lemma castV_update_comp {c : A → C} {c' : B → C} (e : A ≃ B) (hc : ∀ a, c' (e a) = c a)
    (v : ∀ b, V (c' b)) (a₀ : A) (z : V (c' (e a₀))) :
    (fun a => castV R V (hc a) (Function.update v (e a₀) z (e a)))
      = Function.update (fun a => castV R V (hc a) (v (e a))) a₀ (castV R V (hc a₀) z) := by
  funext a
  by_cases ha : a = a₀
  · subst ha
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (e.injective.ne ha), Function.update_of_ne ha]

variable (R V) in
/-- Relabelling in the endomorphism colored operad, transporting the colors.-/
def ColEnd.map {c : A → C} {c' : B → C} {d : C} (e : A ≃ B) (hc : ∀ a, c' (e a) = c a) :
    ColEnd R V A c d →ₗ[R] ColEnd R V B c' d where
  toFun f := MultilinearMap.mk' (fun v => f fun a => castV R V (hc a) (v (e a)))
    (fun v b x y => by
      obtain ⟨a₀, rfl⟩ := e.surjective b
      simp only [castV_update_comp, map_add, f.map_update_add])
    (fun v b r x => by
      obtain ⟨a₀, rfl⟩ := e.surjective b
      simp only [castV_update_comp, map_smul, f.map_update_smul])
  map_add' _ _ := MultilinearMap.ext fun _ => rfl
  map_smul' _ _ := MultilinearMap.ext fun _ => rfl

/--
@isnad1 id=eq.1h11v.s10.31f79d9942ce from=translated src=- shape=0dccdb1f vocab=e458648d
-/
@[simp] lemma ColEnd.map_apply {c : A → C} {c' : B → C} {d : C} (e : A ≃ B)
    (hc : ∀ a, c' (e a) = c a) (f : ColEnd R V A c d) (v : ∀ b, V (c' b)) :
    ColEnd.map R V e hc f v = f fun a => castV R V (hc a) (v (e a)) :=
  rfl

variable (R V) in
/-- The unit of each color: the identity.-/
def ColEnd.one (c : C) : ColEnd R V Unit (fun _ => c) c :=
  MultilinearMap.ofSubsingleton R (V c) (V c) () LinearMap.id

/--
@isnad1 id=eq.0h5v.s7.1f71790fb6e2 from=translated src=- shape=d81ef7f5 vocab=3cc03d11
-/
@[simp] lemma ColEnd.one_apply (c : C) (v : Unit → V c) : ColEnd.one R V c v = v () := rfl

end ColEnd

/-! ## Algebras over one-colored operads -/

section OneColAlg

variable {R : Type u} [CommRing R] {P : (A : Type) → [Fintype A] → [DecidableEq A] → Type v}
  [∀ (A : Type) [Fintype A] [DecidableEq A], AddCommGroup (P A)]
  [∀ (A : Type) [Fintype A] [DecidableEq A], Module R (P A)] [SymOperad R P]
  {V : Type w} [AddCommGroup V] [Module R V]

end OneColAlg

end Operad
