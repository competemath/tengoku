import Tengoku.StringDiagramsLean.StringDiagrams.Chord.Realisation
import Tengoku.Seed.CategoryTheory.Preadditive.Basic
import Tengoku.Seed.Algebra.Group.Subgroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Interpretations of chord diagrams modulo lower order terms

An interpretation of chord diagrams in a category `C` (`MoveInterp`) assigns an object
`F.obj l` to every list of letters `l` (a boundary word) and a morphism
`F.map l m : F.obj l ⟶ F.obj (lstep d l m)` to every move `m` applied to `l` (a cup or a
crossing, whiskered by the identities of the other strands). The image of a diagram `D` read from
the bottom is the composite `F.eval l D` of the images of its moves.

For a preadditive `C`, a *filtration by lower order terms* (`MoveInterp.Filtration`) is a family
of subgroups `Φ.sub n l l'` of `F.obj l ⟶ F.obj l'` (morphisms "of order less than `n`
crossings") such that composing with the image of a move of `k` crossings (`Move.ncross`: `0`
for a cup, `1` for a crossing) maps `Φ.sub n` into `Φ.sub (n + k)`. The trivial filtration
`Filtration.bot` expresses equality on the nose.

The filtration *respects the moves* (`Filtration.Respects`) if each generating move `Step L R`
holds, applied to any boundary word, modulo `Φ.sub (ncross L)`: distant commutations (in a
presented category these are instances of the interchange law and hold exactly), the braid
relation modulo terms with fewer than three crossings, and the pitchfork move modulo terms
without crossings.

## Main results

* `Filtration.near_of_equiv`: if `Φ` respects the moves, equivalent diagrams have equal images
  modulo `Φ.sub (ncross D)` (`Filtration.Near`); all equivalent diagrams have the same number of
  crossings (`Equiv.ncross_eq`).
* `Filtration.near_canon_or_reducible`: the image of every diagram that fits on the empty word
  equals, modulo lower order terms, the image of the canonical diagram of its final pairing, or
  the image of a diagram containing a double crossing or a curl.
* `Filtration.bot`, `Filtration.near_bot_iff`: the case of equality on the nose.
-/

namespace StringDiagrams.Chord

open CategoryTheory

universe u v w

variable {α : Type u}

/-! ## Crossing numbers -/

/-- The number of crossings of a move.-/
def Move.ncross : Move α → ℕ
  | .cup _ _ => 0
  | .cross _ => 1

/-- The number of crossings of a diagram.-/
def ncross (D : List (Move α)) : ℕ := (D.map Move.ncross).sum

/--
@isnad1 id=eq.0h1v.s3.f5be78b454ca from=translated src=- shape=d9710dfd vocab=ddb3254a
-/
@[simp] theorem ncross_nil : ncross ([] : List (Move α)) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s4.2e3781114f62 from=translated src=- shape=82b3498f vocab=7b9c0ad5
-/
@[simp] theorem ncross_cons (m : Move α) (D : List (Move α)) :
    ncross (m :: D) = m.ncross + ncross D := by
  simp [ncross]

/--
@isnad1 id=eq.0h3v.s5.467373dda630 from=translated src=- shape=3337fb9e vocab=b9a2d9f0
-/
@[simp] theorem ncross_append (D E : List (Move α)) : ncross (D ++ E) = ncross D + ncross E := by
  simp [ncross]

/--
@isnad1 id=eq.1h3v.s4.0ab34b911af7 from=translated src=- shape=2e66215c vocab=19db365c
-/
theorem Step.ncross_eq {L R : List (Move α)} (h : Step L R) : ncross L = ncross R := by
  cases h <;> simp [Move.ncross]

/--
@isnad1 id=eq.1h3v.s4.1f1829eb0585 from=translated src=- shape=2e66215c vocab=9bc2bd34
-/
theorem Rw.ncross_eq {X Y : List (Move α)} (h : Rw X Y) : ncross X = ncross Y := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  simp [hs.ncross_eq]

/-- Equivalent diagrams have the same number of crossings.
@isnad1 id=eq.1h3v.s4.0303a5202064 from=translated src=- shape=2e66215c vocab=925901ac
-/
theorem Equiv.ncross_eq {X Y : List (Move α)} (h : Equiv X Y) : ncross X = ncross Y := by
  induction h with
  | rel X Y h => exact h.ncross_eq
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

/-! ## Interpretations -/

/-- An interpretation of chord diagrams with letters in `α` (and duals given by `d`) in a
category `C`: an object for every boundary word and a morphism for every move applied to a
boundary word.-/
structure MoveInterp (d : α → α) (C : Type w) [Category.{v} C] where
  /-- The object of a boundary word.-/
  obj : List α → C
  /-- The image of a move applied to the boundary word `l`.-/
  map : (l : List α) → (m : Move α) → (obj l ⟶ obj (lstep d l m))

namespace MoveInterp

variable {d : α → α} {C : Type w} [Category.{v} C] (F : MoveInterp d C)

/-- The image of a diagram read from the bottom, starting from the boundary word `l`.-/
def eval : (l : List α) → (D : List (Move α)) → (F.obj l ⟶ F.obj (D.foldl (lstep d) l))
  | _, [] => 𝟙 _
  | l, m :: D => F.map l m ≫ eval (lstep d l m) D

/--
@isnad1 id=eq.0h5v.s6.be58cc6059e5 from=translated src=- shape=e2a29ee9 vocab=4d8112c5
-/
@[simp] theorem eval_nil (l : List α) : F.eval l [] = 𝟙 _ := rfl

/--
@isnad1 id=eq.0h7v.s7.961f4b711f10 from=translated src=- shape=9954a507 vocab=aae9cc96
-/
@[simp] theorem eval_cons (l : List α) (m : Move α) (D : List (Move α)) :
    F.eval l (m :: D) = F.map l m ≫ F.eval (lstep d l m) D := rfl

/-- The image of a diagram depends on the boundary word only up to transport.
@isnad1 id=eq.1h7v.s7.06ecf97b3d6e from=translated src=- shape=51b7bb2d vocab=86b436cf
-/
theorem eval_congr {l l' : List α} (h : l = l') (D : List (Move α)) :
    F.eval l D ≫ eqToHom (congrArg F.obj (congrArg (D.foldl (lstep d)) h)) =
      eqToHom (congrArg F.obj h) ≫ F.eval l' D := by
  subst h; simp

/-- The image of a concatenation of diagrams is the composite of their images.
@isnad1 id=eq.0h7v.s8.d30767820a6b from=translated src=- shape=661ecd93 vocab=50b95861
-/
theorem eval_append (l : List α) (D E : List (Move α)) :
    F.eval l (D ++ E) = F.eval l D ≫ F.eval (D.foldl (lstep d) l) E ≫
      eqToHom (congrArg F.obj (List.foldl_append).symm) := by
  induction D generalizing l with
  | nil => simp
  | cons m D ih => simp [ih]

/-! ## Filtrations by lower order terms -/

variable [Preadditive C]

/-- A filtration by lower order terms: subgroups `sub n l l'` of `F.obj l ⟶ F.obj l'` (terms of
order less than `n` crossings) such that composing with the image of a move of `k` crossings
maps `sub n` into `sub (n + k)`.-/
structure Filtration where
  /-- The terms of order less than `n` crossings.-/
  sub : ℕ → (l l' : List α) → AddSubgroup (F.obj l ⟶ F.obj l')
  /-- Precomposition with the image of a move.-/
  map_comp_mem : ∀ {n : ℕ} {l l' : List α} {m : Move α} {x : F.obj (lstep d l m) ⟶ F.obj l'},
    m.Ok l.length → x ∈ sub n (lstep d l m) l' → F.map l m ≫ x ∈ sub (m.ncross + n) l l'
  /-- Postcomposition with the image of a move.-/
  comp_map_mem : ∀ {n : ℕ} {l l' : List α} {m : Move α} {x : F.obj l ⟶ F.obj l'},
    m.Ok l'.length → x ∈ sub n l l' → x ≫ F.map l' m ∈ sub (n + m.ncross) l (lstep d l' m)

/-- The trivial filtration: equality on the nose.-/
def Filtration.bot : F.Filtration where
  sub _ _ _ := ⊥
  map_comp_mem _ hx := by rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, Limits.comp_zero]
  comp_map_mem _ hx := by rw [AddSubgroup.mem_bot] at hx ⊢; rw [hx, Limits.zero_comp]

namespace Filtration

variable {F} (Φ : F.Filtration)

/--
@isnad1 id=mem.2h10v.s9.ccc317c9597d from=translated src=- shape=b337b80a vocab=4d372650
-/
theorem comp_eqToHom_mem {n : ℕ} {l l' l'' : List α} {x : F.obj l ⟶ F.obj l'} (h : l' = l'')
    (hx : x ∈ Φ.sub n l l') : x ≫ eqToHom (congrArg F.obj h) ∈ Φ.sub n l l'' := by
  subst h; simpa using hx

/--
@isnad1 id=mem.2h10v.s9.b82ee9340430 from=translated src=- shape=111c02ec vocab=08b93033
-/
theorem eval_comp_mem {n : ℕ} {l₀ l : List α} {x : F.obj l₀ ⟶ F.obj l} (hx : x ∈ Φ.sub n l₀ l)
    {D : List (Move α)} (hf : Fits l.length D) :
    x ≫ F.eval l D ∈ Φ.sub (n + ncross D) l₀ (D.foldl (lstep d) l) := by
  induction D generalizing n l with
  | nil =>
    change x ≫ 𝟙 (F.obj l) ∈ Φ.sub (n + 0) l₀ l
    rw [Category.comp_id]; exact hx
  | cons m D ih =>
    obtain ⟨hm, hf⟩ := hf
    rw [← length_lstep (d := d)] at hf
    have := ih (Φ.comp_map_mem hm hx) hf
    rw [ncross_cons, ← Nat.add_assoc]
    change x ≫ (F.map l m ≫ F.eval (lstep d l m) D) ∈
      Φ.sub _ l₀ (D.foldl (lstep d) (lstep d l m))
    rw [← Category.assoc]
    exact this

/--
@isnad1 id=mem.2h10v.s9.0d977d7486c7 from=translated src=- shape=1e95ecb0 vocab=08b93033
-/
theorem mem_eval_comp {n : ℕ} {l l' : List α} {D : List (Move α)}
    {x : F.obj (D.foldl (lstep d) l) ⟶ F.obj l'} (hx : x ∈ Φ.sub n _ l') (hf : Fits l.length D) :
    F.eval l D ≫ x ∈ Φ.sub (ncross D + n) l l' := by
  induction D generalizing n l with
  | nil =>
    rw [ncross_nil, Nat.zero_add]
    exact Eq.mpr (congrArg (· ∈ Φ.sub n l l') (Category.id_comp x)) hx
  | cons m D ih =>
    obtain ⟨hm, hf⟩ := hf
    rw [← length_lstep (d := d)] at hf
    have := Φ.map_comp_mem hm (ih hx hf)
    rw [ncross_cons, Nat.add_assoc]
    exact Eq.mpr (congrArg (· ∈ Φ.sub _ l l') (Category.assoc _ _ x)) this

/-- The images of `X` and `Y`, applied to the boundary word `l`, agree modulo `Φ.sub n`.-/
def Near (n : ℕ) (l : List α) (X Y : List (Move α)) : Prop :=
  ∀ e : X.foldl (lstep d) l = Y.foldl (lstep d) l,
    F.eval l X ≫ eqToHom (congrArg F.obj e) - F.eval l Y ∈ Φ.sub n l (Y.foldl (lstep d) l)

/-- For the trivial filtration, `Near` is equality of the images.
@isnad1 id=iff.0h8v.s7.822626e13f21 from=translated src=- shape=f6c05833 vocab=e57c2419
-/
theorem near_bot_iff {n : ℕ} {l : List α} {X Y : List (Move α)} :
    (Filtration.bot F).Near n l X Y ↔ ∀ e : X.foldl (lstep d) l = Y.foldl (lstep d) l,
      F.eval l X ≫ eqToHom (congrArg F.obj e) = F.eval l Y := by
  simp only [Near, Filtration.bot, AddSubgroup.mem_bot, sub_eq_zero]

/--
@isnad1 id=near.0h8v.s5.33c4ad28073b from=translated src=- shape=8fd26322 vocab=42c1dd90
-/
theorem Near.refl (n : ℕ) (l : List α) (X : List (Move α)) : Φ.Near n l X X := by
  intro e; simp

/--
@isnad1 id=near.2h9v.s6.3cfb949d2851 from=translated src=- shape=eabd40f9 vocab=9cc224d8
-/
theorem Near.symm {n : ℕ} {l : List α} {X Y : List (Move α)} (h : Φ.Near n l X Y)
    (e : X.foldl (lstep d) l = Y.foldl (lstep d) l) : Φ.Near n l Y X := by
  intro e'
  have := Φ.comp_eqToHom_mem e' (neg_mem (h e))
  convert this using 1
  simp [Preadditive.sub_comp]

/--
@isnad1 id=near.4h10v.s7.8c76806257ff from=translated src=- shape=f73817e0 vocab=9cc224d8
-/
theorem Near.trans {n : ℕ} {l : List α} {X Y Z : List (Move α)} (h : Φ.Near n l X Y)
    (h' : Φ.Near n l Y Z) (e : X.foldl (lstep d) l = Y.foldl (lstep d) l)
    (e' : Y.foldl (lstep d) l = Z.foldl (lstep d) l) : Φ.Near n l X Z := by
  intro e''
  have := add_mem (Φ.comp_eqToHom_mem e' (h e)) (h' e')
  convert this using 1
  simp [Preadditive.sub_comp]

/-- A common first move.
@isnad1 id=near.2h10v.s6.8239d91c9e45 from=translated src=- shape=300199ba vocab=3cd15a15
-/
theorem Near.cons {n : ℕ} {l : List α} {X Y : List (Move α)} {m : Move α}
    (h : Φ.Near n (lstep d l m) X Y) (hm : m.Ok l.length) :
    Φ.Near (m.ncross + n) l (m :: X) (m :: Y) := by
  intro e
  have := Φ.map_comp_mem hm (h e)
  rw [Preadditive.comp_sub, ← Category.assoc] at this
  exact this

/-- A common prefix.
@isnad1 id=near.2h10v.s7.152fc2bdd55b from=translated src=- shape=8818fb6a vocab=3af782eb
-/
theorem Near.prefix {n : ℕ} {l : List α} {X Y : List (Move α)} (A : List (Move α))
    (h : Φ.Near n (A.foldl (lstep d) l) X Y) (hA : Fits l.length A) :
    Φ.Near (ncross A + n) l (A ++ X) (A ++ Y) := by
  induction A generalizing l with
  | nil => simpa using h
  | cons m A ih =>
    obtain ⟨hm, hA⟩ := hA
    rw [← length_lstep (d := d)] at hA
    have := (ih h hA).cons Φ hm
    rw [ncross_cons, Nat.add_assoc]
    exact this

/--
@isnad1 id=eq.3h10v.s8.6ebececd3fff from=translated src=- shape=545c18eb vocab=5739d495
-/
theorem comp_sub_comp_eq {X Y Y' Z Z' : C} (f : X ⟶ Y) (f' : X ⟶ Y') (g : Y ⟶ Z) (g' : Y' ⟶ Z')
    (h : Y = Y') (h' : Z = Z') (hg : g ≫ eqToHom h' = eqToHom h ≫ g') :
    (f ≫ g) ≫ eqToHom h' - f' ≫ g' = (f ≫ eqToHom h - f') ≫ g' := by
  subst h h'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hg ⊢
  rw [hg, Preadditive.sub_comp]

/-- A common suffix.
@isnad1 id=near.3h10v.s7.535d9d8c0b6e from=translated src=- shape=7043742e vocab=3af782eb
-/
theorem Near.append {n : ℕ} {l : List α} {X Y : List (Move α)} (h : Φ.Near n l X Y)
    (e : X.foldl (lstep d) l = Y.foldl (lstep d) l) (B : List (Move α))
    (hB : Fits (Y.foldl (lstep d) l).length B) :
    Φ.Near (n + ncross B) l (X ++ B) (Y ++ B) := by
  intro e'
  have hg : (F.eval (X.foldl (lstep d) l) B ≫
      eqToHom (congrArg F.obj (List.foldl_append (f := lstep d) (b := l) (l := X) (l' := B)).symm)) ≫
      eqToHom (congrArg F.obj e') = eqToHom (congrArg F.obj e) ≫
      (F.eval (Y.foldl (lstep d) l) B ≫
        eqToHom (congrArg F.obj (List.foldl_append (f := lstep d) (b := l) (l := Y) (l' := B)).symm)) := by
    rw [← Category.assoc, ← F.eval_congr e B]
    simp
  rw [eval_append, eval_append, comp_sub_comp_eq _ _ _ _ _ _ hg, ← Category.assoc]
  exact Φ.comp_eqToHom_mem List.foldl_append.symm (Φ.eval_comp_mem (h e) hB)

/-- **Soundness of the moves.** The filtration respects the moves if every generating move
holds, applied to any boundary word on which it fits, modulo terms of lower order than its
number of crossings.-/
def Respects : Prop :=
  ∀ ⦃L R : List (Move α)⦄, Step L R → ∀ l : List α, Fits l.length L → Φ.Near (ncross L) l L R

variable {Φ}

/--
@isnad1 id=near.3h8v.s6.fa64bb0b68d2 from=translated src=- shape=4caad1ad vocab=9f4ffb62
-/
theorem Respects.near_rw (hΦ : Φ.Respects) {l : List α} {X Y : List (Move α)} (h : Rw X Y)
    (hf : Fits l.length X) : Φ.Near (ncross X) l X Y := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  rw [List.append_assoc] at hf ⊢
  rw [List.append_assoc]
  rw [fits_append] at hf
  obtain ⟨hA, hLB⟩ := hf
  rw [← foldl_lstep_len (d := d)] at hLB
  rw [fits_append] at hLB
  obtain ⟨hL, hB⟩ := hLB
  have hLR := hs.fits_letters (d := d) (A.foldl (lstep d) l)
  have e := hLR.2 hL
  rw [← foldl_lstep_len (d := d), e] at hB
  have := (hΦ hs _ hL).append Φ e B hB
  have := this.prefix Φ A hA
  rw [ncross_append, ncross_append]
  exact this

/-- **Equivalent diagrams have equal images modulo lower order terms.** If the filtration
respects the moves, then for equivalent diagrams `X` and `Y` fitting on the boundary word `l`,
the images of `X` and `Y` agree modulo terms of order less than the number of crossings of `X`.
@isnad1 id=near.3h8v.s6.d9573ff60433 from=translated src=- shape=4caad1ad vocab=0ad65264
-/
theorem near_of_equiv (hΦ : Φ.Respects) {l : List α} {X Y : List (Move α)} (h : Equiv X Y)
    (hf : Fits l.length X) : Φ.Near (ncross X) l X Y := by
  induction h with
  | rel X Y h => exact hΦ.near_rw h hf
  | refl X => exact Near.refl Φ _ _ _
  | symm X Y h ih =>
    have hfX : Fits l.length X := ((Equiv.fits_letters (d := d) h l).1).2 hf
    rw [← Equiv.ncross_eq h]
    exact (ih hfX).symm Φ ((Equiv.fits_letters (d := d) h l).2 hfX)
  | trans X Y Z h h' ih ih' =>
    have hfY : Fits l.length Y := ((Equiv.fits_letters (d := d) h l).1).1 hf
    have e := (Equiv.fits_letters (d := d) h l).2 hf
    have e' := (Equiv.fits_letters (d := d) h' l).2 hfY
    have := ih' hfY
    rw [← Equiv.ncross_eq h] at this
    exact (ih hf).trans Φ this e e'

/-- **The normal form modulo lower order terms.** If the filtration respects the moves, the
image of every diagram `D` fitting on the empty boundary word agrees, modulo terms of order less
than the number of crossings of `D`, with the image of a diagram containing a double crossing,
with the image of a diagram containing a curl, or with the image of the canonical diagram of the
final pairing of `D`.
@isnad1 id=or.2h6v.s7.888318e27ddf from=translated src=- shape=6c31eaf5 vocab=9b205561
-/
theorem near_canon_or_reducible (hΦ : Φ.Respects) {D : List (Move α)} (hf : Fits 0 D) :
    (∃ A B : List (Move α), ∃ p : ℕ,
        Φ.Near (ncross D) [] D (A ++ [.cross p, .cross p] ++ B)) ∨
      (∃ A B : List (Move α), ∃ p : ℕ, ∃ a : α,
        Φ.Near (ncross D) [] D (A ++ [.cup p a, .cross p] ++ B)) ∨
      Φ.Near (ncross D) [] D (canon (run d D)) := by
  rcases equiv_canon_or_reducible (d := d) hf with ⟨A, B, p, h | ⟨a, h⟩⟩ | h
  · exact Or.inl ⟨A, B, p, near_of_equiv hΦ h hf⟩
  · exact Or.inr (Or.inl ⟨A, B, p, a, near_of_equiv hΦ h hf⟩)
  · exact Or.inr (Or.inr (near_of_equiv hΦ h hf))

end Filtration

end MoveInterp

end StringDiagrams.Chord
