/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.RoseTree.Defs
public import Tengoku

/-!
# LeanPool.QuasiBorelSpaces.RoseTree.Basic

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.RoseTree.Basic`.
-/

@[expose] public section

universe u

variable {A B C D : Type*}

namespace Rose

/--
@isnad1 id=eq.0h2v.s4.9debb0df6ed2 from=translated src=- shape=0913e22b vocab=3b580621
-/
@[simp]
lemma eta (t : Rose A) : mk t.label t.children = t := by
  cases t
  rfl

/--
@isnad1 id=eq.0h4v.s4.5561a99fb6a4 from=translated src=- shape=22a4d473 vocab=a7256a49
-/
@[simp]
lemma label_bind (f : A → Rose B) (t : Rose A) : (bind f t).label = (f t.label).label := by
  cases t
  simp only [bind.eq_1]

/--
@isnad1 id=eq.0h4v.s5.e59b8aa04fb8 from=translated src=- shape=e9f7bab0 vocab=ac0eb42f
-/
@[simp]
lemma children_bind
    (f : A → Rose B) (t : Rose A)
    : (bind f t).children = (f t.label).children ++ List.map (bind f) t.children := by
  cases t
  simp only [bind.eq_1]

/--
@isnad1 id=eq.0h4v.s4.b24fe4fc88ef from=translated src=- shape=b4010056 vocab=3ec1492d
-/
@[simp]
lemma label_map (f : A → B) (t : Rose A) : (map f t).label = f t.label := by
  simp only [map, label_bind]

/--
@isnad1 id=eq.0h4v.s5.e4695c5be199 from=translated src=- shape=bebad844 vocab=2410b48d
-/
@[simp]
lemma children_map
    (f : A → B) (t : Rose A)
    : (map f t).children = List.map (map f) t.children := by
  simp only [map, children_bind, List.nil_append]

/--
@isnad1 id=var.0h4v.s5.c7cfac4503a4 from=translated src=- shape=b9458c48 vocab=72d24488
-/
@[induction_eliminator]
lemma induction
    (motive : Rose A → Prop)
    (mk : (label : A)
        → (children : List (Rose A))
        → (ih : ∀ t ∈ children, motive t)
        → motive (.mk label children))
    (t : Rose A)
    : motive t := by
  induction t using rec with
  | mk label children ih =>
    apply mk
    apply ih
  | nil =>
    simp only [List.not_mem_nil, false_implies, implies_true]
  | cons label children ih tail_ih =>
    simpa only [List.mem_cons, forall_eq_or_imp, ih, true_and] using tail_ih

/--
@isnad1 id=var.0h4v.s6.698910a0761f from=translated src=- shape=f991d4d4 vocab=8a9ad4e2
-/
lemma induction'
    (motive : Rose A → Prop)
    (mk : (label : A)
        → (children : List (Rose A))
        → (ih : ∀ i : Fin children.length, motive children[i])
        → motive (.mk label children))
    (t : Rose A)
    : motive t := by
  induction t with | mk label children ih =>
  grind

/--
@isnad1 id=eq.0h2v.s4.e1aa5934cc0a from=translated src=- shape=6e5b7341 vocab=df393804
-/
lemma bind_pure (t : Rose A) : bind (fun x ↦ ⟨x, []⟩) t = t := by
  induction t with | mk label children ih =>
  simp only [bind, List.nil_append, mk.injEq, true_and]
  nth_rw 2 [← List.map_id' children]
  simpa only [List.map_inj_left] using ih

/--
@isnad1 id=eq.0h1v.s4.da6740341c56 from=translated src=- shape=e6de160c vocab=fba6dc86
-/
@[simp]
lemma bind_pure_fun : bind (A := A) (fun x ↦ ⟨x, []⟩) = id := by
  ext
  apply bind_pure

/--
@isnad1 id=eq.0h6v.s5.31ba03570a39 from=translated src=- shape=5d4823bf vocab=7d69e9a0
-/
@[simp]
lemma bind_bind
    (f : B → Rose C) (g : A → Rose B) (t : Rose A)
    : bind f (bind g t) = bind (fun x ↦ bind f (g x)) t := by
  induction t with | mk label children ih =>
  simp_all only [
    bind.eq_1, List.map_append, List.map_map, label_bind, children_bind,
    List.append_assoc, mk.injEq, List.append_cancel_left_eq, List.map_inj_left,
    Function.comp_apply, implies_true, and_self]

/--
@isnad1 id=eq.0h5v.s5.b613e44ea177 from=translated src=- shape=1a49ef37 vocab=c111f4f3
-/
@[simp]
lemma bind_comp
    (f : B → Rose C) (g : A → Rose B)
    : bind f ∘ bind g = bind (bind f ∘ g) := by
  ext t
  apply bind_bind

/--
@isnad1 id=eq.0h7v.s6.04342094a666 from=translated src=- shape=e6ff0043 vocab=c111f4f3
-/
@[simp]
lemma bind_comp_r
    (f : B → Rose C) (g : A → Rose B) (h : D → Rose A)
    : bind f ∘ bind g ∘ h = bind (bind f ∘ g) ∘ h := by
  ext t
  apply bind_bind

/--
@isnad1 id=eq.0h3v.s5.f861ed9ecca5 from=translated src=- shape=14b85909 vocab=39360bc6
-/
@[simp]
lemma fold_eq_bind
    (f : A → Rose B)
    : fold (fun x xs ↦ ⟨(f x).label, (f x).children ++ xs⟩) = bind f := by
  ext t
  induction t with | mk label children ih
  simp only [
    fold.eq_1, bind.eq_1, mk.injEq, List.append_cancel_left_eq,
    List.map_inj_left, true_and]
  exact ih

/--
@isnad1 id=eq.0h5v.s5.0d731edfb7f3 from=translated src=- shape=3ee527bf vocab=4294e346
-/
@[simp]
lemma map_mk
    (f : A → B) (x : A) (xs : List (Rose A))
    : map f ⟨x, xs⟩ = ⟨f x, List.map (map f) xs⟩ := by
  unfold map
  simp only [bind.eq_1, List.nil_append]

/--
@isnad1 id=eq.1h3v.s4.594f366121d3 from=translated src=- shape=167c5c98 vocab=1f00e58f
-/
@[simp]
lemma map_id {f : A → A} (hf : ∀ x, f x = x) (t) : map f t = t := by
  unfold map
  simp only [hf, bind_pure_fun, id_eq]

/--
@isnad1 id=eq.0h6v.s5.2c32f7264756 from=translated src=- shape=ee6c6f1a vocab=1f00e58f
-/
@[simp]
lemma map_map
    (f : B → C) (g : A → B) (t : Rose A)
    : map f (map g t) = map (fun x ↦ f (g x)) t := by
  unfold map
  simp only [bind_bind, bind.eq_1, List.map_nil, List.append_nil]

/--
@isnad1 id=eq.0h6v.s5.b6f5964d1c22 from=translated src=- shape=e929fda3 vocab=272d447a
-/
@[simp]
lemma map_bind
    (f : B → C) (g : A → Rose B) (t : Rose A)
    : map f (bind g t) = bind (fun x ↦ map f (g x)) t := by
  unfold map
  simp only [bind_bind]

/--
@isnad1 id=eq.0h6v.s5.94a082adf181 from=translated src=- shape=2bba2904 vocab=272d447a
-/
@[simp]
lemma bind_map
    (f : B → Rose C) (g : A → B) (t : Rose A)
    : bind f (map g t) = bind (fun x ↦ f (g x)) t := by
  unfold map
  simp only [bind_bind, bind.eq_1, List.map_nil, List.append_nil, eta]

/--
@isnad1 id=eq.0h4v.s5.6036ff0883a0 from=translated src=- shape=da5ced11 vocab=30b7e710
-/
@[simp]
lemma bind_eq_map (f : A → B) (t : Rose A) : bind (fun x ↦ ⟨f x, []⟩) t = map f t := by rfl

/--
@isnad1 id=eq.0h6v.s5.d5dbeb852dd9 from=translated src=- shape=192f189a vocab=37e5b0a5
-/
@[simp]
lemma fold_map
    (f : B → List C → C) (g : A → B) (t : Rose A)
    : fold f (map g t) = fold (fun x ↦ f (g x)) t := by
  induction t with | mk label children ih =>
  simp only [map_mk, fold.eq_1, List.map_map]
  congr 1
  simpa only [List.map_inj_left, Function.comp_apply] using ih

/--
@isnad1 id=eq.0h4v.s4.0c56159004c1 from=translated src=- shape=98bd048e vocab=522379d5
-/
@[simp]
lemma bind_eq {B} (t : Rose A) (f : A → Rose B) : Bind.bind t f = bind f t := rfl

/--
@isnad1 id=eq.0h2v.s4.43d36357f7c7 from=translated src=- shape=7faf62be vocab=d93f1fe7
-/
@[simp]
lemma pure_eq (x : A) : (pure x : Rose A) = ⟨x, []⟩ := rfl

/--
@isnad1 id=eq.0h4v.s5.fb72878c98fc from=translated src=- shape=0cccb03b vocab=760045b8
-/
@[simp]
lemma seq_eq {B} (f : Rose (A → B)) (t : Rose A) : f <*> t = bind (fun f ↦ map f t) f := rfl

/--
@isnad1 id=eq.0h4v.s4.f4773d1d0329 from=translated src=- shape=c615846d vocab=ed4aff86
-/
@[simp]
lemma map_eq {B} (f : A → B) (t : Rose A) : f <$> t = map f t := rfl

/--
@isnad1 id=eq.0h4v.s5.747d009dda30 from=translated src=- shape=b7ce891a vocab=dc69dd5a
-/
@[simp]
lemma seqLeft_eq {B} (t : Rose A) (u : Rose B) : t <* u = bind (fun x ↦ map (fun _ ↦ x) u) t := rfl

/--
@isnad1 id=eq.0h4v.s5.07133214bb1a from=translated src=- shape=cefb8973 vocab=92c8c1ab
-/
@[simp]
lemma seqRight_eq {B} (t : Rose A) (u : Rose B) : t *> u = bind (fun _ ↦ u) t := rfl

@[simp]
private lemma traverse_map
    {F : Type _ → Type _} [Applicative F]
    (f : B → F C)
    (g : A → B) (xs : List A)
    : List.traverse f (List.map g xs) = List.traverse (fun x ↦ f (g x)) xs := by
  induction xs with
  | nil => simp only [List.map_nil, List.traverse.eq_1]
  | cons head tail ih => simp only [List.map_cons, List.traverse, ih]

@[simp]
private lemma traverse_pure
    {F : Type _ → Type _} [Applicative F] [LawfulApplicative F]
    (xs : List A)
    : List.traverse (pure : _ → F _) xs = pure xs := by
  induction xs with
  | nil => simp [List.traverse.eq_1]
  | cons head tail ih => simp [List.traverse.eq_2, ih]

/--
@isnad1 id=eq.0h2v.s4.f920af19f3d0 from=translated src=- shape=bdeadc95 vocab=ca83f6c6
-/
@[simp]
lemma decode_encode [Encodable A] (t : Rose A) : decode (encode t) = some t := by
  induction t with | mk label children ih =>
  simp only [encode]
  unfold decode
  simp only [
    Nat.unpair_pair, Encodable.decode₂_encode, Fin.getElem_fin,
    List.ofFn_getElem_eq_map, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  rw [Nat.unpair_pair, Encodable.encodek]
  simp only [List.map_map]
  rw [←List.ofFn_getElem_eq_map]
  simp only [
    Function.comp_apply, List.getElem_mem, ih,
    List.ofFn_getElem_eq_map, traverse_map, id_eq]
  change Option.bind (List.traverse pure children) _ = _
  simp only [traverse_pure]
  simp only [Option.pure_def, Option.bind_some]

instance [Encodable A] : Encodable (Rose A) where
  encode := encode
  decode := decode
  encodek := decode_encode

instance [Countable A] : Countable (Rose A) := by
  have := Encodable.ofCountable A
  infer_instance

/--
@isnad1 id=iff.0h5v.s5.3e6df83bcf87 from=translated src=- shape=050b8b4f vocab=4ee1469e
-/
@[simp]
lemma le_mk
    [LE A] (x y : A) (xs ys : List (Rose A))
    : mk x xs ≤ mk y ys ↔ x ≤ y ∧ List.Forall₂ (· ≤ ·) xs ys := by
  simp only [LE.le, fold.eq_1, List.forall₂_map_left_iff, id_eq]

instance [Preorder A] : Preorder (Rose A) where
  le_refl x := by
    induction x with | mk label children ih =>
    simpa only [le_mk, le_refl, List.forall₂_same, true_and] using ih
  le_trans t u v h₁ h₂ := by
    induction t generalizing u v with | mk _ xs ih =>
    cases u with | mk _ ys =>
    cases v with | mk _ zs =>
    simp only [le_mk] at ⊢ h₁ h₂
    apply And.intro
    · exact h₁.1.trans h₂.1
    · induction xs generalizing ys zs with
      | nil =>
        simp_all only [
          List.not_mem_nil, IsEmpty.forall_iff, implies_true,
          List.forall₂_nil_left_iff, List.forall₂_same]
      | cons _ _ ih' =>
        cases ys with
        | nil => simp only [List.forall₂_nil_right_iff, reduceCtorEq, and_false] at h₁
        | cons _ _ =>
          cases zs with
          | nil => simp only [List.forall₂_nil_right_iff, reduceCtorEq, and_false] at h₂
          | cons _ _ =>
            simp only [List.forall₂_cons] at ⊢ h₁ h₂
            grind

instance [PartialOrder A] : PartialOrder (Rose A) where
  le_antisymm t u := by
    induction t generalizing u with | mk _ xs ih =>
    cases u with | mk _ ys =>
    simp only [le_mk, mk.injEq, and_imp]
    intro h₁ h₂ h₃ h₄
    apply And.intro
    · apply le_antisymm h₁ h₃
    · induction xs generalizing ys with
      | nil =>
        simp only [List.forall₂_nil_left_iff] at h₂
        simp only [h₂]
      | cons _ _ ih' =>
        cases ys with
        | nil => simp only [List.forall₂_nil_left_iff, reduceCtorEq] at h₄
        | cons _ _ =>
          simp only [List.forall₂_cons] at h₂ h₄
          grind

end Rose
