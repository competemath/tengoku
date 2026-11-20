import Tengoku.Grushkoneumanntheorem.MarshallHall.GrushkoGeneral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
## Reduced words for the binary free product

`Mathlib.GroupTheory.CoprodI` contains the normal-form theorem for an
indexed free product.  The binary coproduct has a separate implementation,
so this file supplies the small, explicit bridge needed by the Grushko
reduction argument.  In particular, the reduced-word object below is tied to
the actual inclusions `Monoid.Coprod.inl` and `Monoid.Coprod.inr`.
-/

open Function Monoid.Coprod

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]

def binaryFamily (G H : Type u) : Bool → Type u
  | false => G
  | true => H

instance binaryFamilyGroup (G H : Type u) [Group G] [Group H] :
    ∀ b, Group (binaryFamily G H b) := by
  intro b
  cases b
  · change Group G
    exact inferInstance
  · change Group H
    exact inferInstance

noncomputable instance binaryFamilyDecidableEq (G H : Type u) :
    ∀ b, DecidableEq (binaryFamily G H b) := by
  intro b
  cases b <;> exact Classical.decEq _

abbrev binaryIndexedProduct :=
  Monoid.CoprodI (binaryFamily G H)

def indexedLeft : G →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.CoprodI.of (M := binaryFamily G H) (i := false)

def indexedRight : H →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.CoprodI.of (M := binaryFamily G H) (i := true)

def binaryToIndexed : G ∗ H →* binaryIndexedProduct (G := G) (H := H) :=
  Monoid.Coprod.lift (indexedLeft (G := G) (H := H))
    (indexedRight (G := G) (H := H))

def indexedToBinaryFamily :
    (b : Bool) → binaryFamily G H b →* G ∗ H
  | false => Monoid.Coprod.inl
  | true => Monoid.Coprod.inr

def indexedToBinary : binaryIndexedProduct (G := G) (H := H) →* G ∗ H :=
  Monoid.CoprodI.lift (M := binaryFamily G H)
    (indexedToBinaryFamily (G := G) (H := H))

/--
@isnad1 id=eq.0h3v.s9.83d5cee8d9ed from=translated src=- shape=351083ae vocab=d94d7229
-/
@[simp] theorem binaryToIndexed_inl (g : G) :
    binaryToIndexed (G := G) (H := H) (Monoid.Coprod.inl g) = indexedLeft g := by
  rfl

/--
@isnad1 id=eq.0h3v.s9.731f70396021 from=translated src=- shape=ea8aa0ab vocab=5fbd7d2f
-/
@[simp] theorem binaryToIndexed_inr (h : H) :
    binaryToIndexed (G := G) (H := H) (Monoid.Coprod.inr h) = indexedRight h := by
  rfl

/--
@isnad1 id=eq.0h3v.s9.b7a893ebc56b from=translated src=- shape=351083ae vocab=a7c9f7b3
-/
@[simp] theorem indexedToBinary_left (g : G) :
    indexedToBinary (G := G) (H := H) (indexedLeft g) = Monoid.Coprod.inl g := by
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
@isnad1 id=eq.0h3v.s9.224cfe2348ce from=translated src=- shape=ea8aa0ab vocab=70ea4fd7
-/
@[simp] theorem indexedToBinary_right (h : H) :
    indexedToBinary (G := G) (H := H) (indexedRight h) = Monoid.Coprod.inr h := by
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
@isnad1 id=eq.0h2v.s8.f98821c6109e from=translated src=- shape=d67f56b5 vocab=4130015e
-/
theorem indexedToBinary_comp_binaryToIndexed :
    (indexedToBinary (G := G) (H := H)).comp
        (binaryToIndexed (G := G) (H := H)) = MonoidHom.id _ := by
  apply Monoid.Coprod.hom_ext
  · ext g
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inl g)) =
      Monoid.Coprod.inl g
    rw [binaryToIndexed_inl, indexedToBinary_left]
  · ext h
    change indexedToBinary (binaryToIndexed (Monoid.Coprod.inr h)) =
      Monoid.Coprod.inr h
    rw [binaryToIndexed_inr, indexedToBinary_right]

/--
@isnad1 id=eq.0h2v.s8.ee33fd0672af from=translated src=- shape=d67f56b5 vocab=4130015e
-/
theorem binaryToIndexed_comp_indexedToBinary :
    (binaryToIndexed (G := G) (H := H)).comp
        (indexedToBinary (G := G) (H := H)) = MonoidHom.id _ := by
  classical
  apply Monoid.CoprodI.ext_hom
  intro b
  cases b
  · ext g
    change G at g
    change binaryToIndexed (indexedToBinary (indexedLeft g)) = indexedLeft g
    rw [indexedToBinary_left, binaryToIndexed_inl]
  · ext h
    change H at h
    change binaryToIndexed (indexedToBinary (indexedRight h)) = indexedRight h
    rw [indexedToBinary_right, binaryToIndexed_inr]

def binaryIndexedEquiv : (G ∗ H) ≃* binaryIndexedProduct (G := G) (H := H) :=
  { toFun := binaryToIndexed
    invFun := indexedToBinary
    left_inv := by
      intro x
      have h := congrArg (fun f : (G ∗ H) →* G ∗ H => f x)
        (indexedToBinary_comp_binaryToIndexed (G := G) (H := H))
      exact h
    right_inv := by
      intro x
      have h := congrArg (fun f : binaryIndexedProduct (G := G) (H := H) →*
          binaryIndexedProduct (G := G) (H := H) => f x)
        (binaryToIndexed_comp_indexedToBinary (G := G) (H := H))
      exact h
    map_mul' := map_mul binaryToIndexed }

def binaryReducedWord (x : G ∗ H) :
    Monoid.CoprodI.Word (binaryFamily G H) := by
  classical
  exact Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
    (binaryToIndexed x)

/--
@isnad1 id=eq.0h3v.s8.36b79dbf3b6f from=translated src=- shape=371a2094 vocab=a19a1465
-/
theorem binaryReducedWord_prod (x : G ∗ H) :
    Monoid.CoprodI.Word.prod (binaryReducedWord (G := G) (H := H) x) =
      binaryToIndexed x := by
  classical
  change (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm
      (binaryReducedWord (G := G) (H := H) x) = binaryToIndexed x
  rw [binaryReducedWord]
  exact (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm_apply_apply
    (binaryToIndexed x)

/--
@isnad1 id=eq.0h2v.s7.71e57b3b763f from=translated src=- shape=735997ca vocab=0a27d05e
-/
@[simp] theorem binaryReducedWord_one :
    binaryReducedWord (G := G) (H := H) (1 : G ∗ H) =
      Monoid.CoprodI.Word.empty := by
  classical
  simp [binaryReducedWord, Monoid.CoprodI.Word.equiv]

def binaryLetterToIndexed : Sum G H → binaryIndexedProduct (G := G) (H := H)
  | Sum.inl g => indexedLeft g
  | Sum.inr h => indexedRight h

/--
@isnad1 id=eq.0h3v.s8.05164a4b636d from=translated src=- shape=861a987f vocab=9a5b8c7d
-/
theorem binaryToIndexed_factorWordProd (u : List (Sum G H)) :
    binaryToIndexed (G := G) (H := H) (factorWordProd u) =
      (u.map (binaryLetterToIndexed (G := G) (H := H))).prod := by
  induction u with
  | nil => simp [factorWordProd]
  | cons a u ih =>
      cases a <;>
        simp [factorWordProd, separatedMap, binaryLetterToIndexed, ih]

/-! Reversing an oriented labelled path reverses the order and inverts every
label.  This is the algebraic operation used by the graph-fold bookkeeping. -/
def factorWordInv : Sum G H → Sum G H
  | Sum.inl g => Sum.inl g⁻¹
  | Sum.inr h => Sum.inr h⁻¹

/--
@isnad1 id=eq.0h3v.s4.d8a54d2349f4 from=translated src=- shape=dcd7fad7 vocab=893df05c
-/
@[simp] theorem factorWordInv_factorWordInv (a : Sum G H) :
    factorWordInv (factorWordInv (G := G) (H := H) a) = a := by
  cases a <;> simp [factorWordInv]

/--
@isnad1 id=eq.0h3v.s6.3a239c147ab4 from=translated src=- shape=211a0b85 vocab=df0735cd
-/
@[simp] theorem separatedMap_factorWordInv (a : Sum G H) :
    separatedMap (factorWordInv (G := G) (H := H) a) =
      (separatedMap (G := G) (H := H) a)⁻¹ := by
  cases a <;> rfl

/--
@isnad1 id=eq.0h3v.s6.d5470415b692 from=translated src=- shape=96ca2b2f vocab=fb8e2300
-/
theorem factorWordProd_reverse_inv (u : List (Sum G H)) :
    factorWordProd (G := G) (H := H)
        (u.reverse.map (factorWordInv (G := G) (H := H))) =
      (factorWordProd (G := G) (H := H) u)⁻¹ := by
  induction u with
  | nil => simp [factorWordProd]
  | cons a u ih =>
      rw [List.reverse_cons, List.map_append, factorWordProd_append, ih]
      simp [factorWordProd, separatedMap_factorWordInv, mul_inv_rev]

/--
@isnad1 id=le.0h4v.s7.a22178abf610 from=translated src=- shape=8c11d293 vocab=9d1d71ec
-/
theorem word_length_rcons_le {b : Bool}
    (p : Monoid.CoprodI.Word.Pair (binaryFamily G H) b) :
    (Monoid.CoprodI.Word.rcons p).toList.length ≤ p.tail.toList.length + 1 := by
  classical
  by_cases hp : p.head = 1
  · simp [Monoid.CoprodI.Word.rcons, hp]
  · simp [Monoid.CoprodI.Word.rcons, hp, Monoid.CoprodI.Word.cons]

/--
@isnad1 id=le.0h4v.s8.c4ad0043f0fd from=translated src=- shape=ed0528fa vocab=d3877ff5
-/
theorem word_pair_tail_length_le {b : Bool}
    (w : Monoid.CoprodI.Word (binaryFamily G H)) :
    (Monoid.CoprodI.Word.equivPair b w).tail.toList.length ≤ w.toList.length := by
  classical
  let p := Monoid.CoprodI.Word.equivPair b w
  have hrcons : Monoid.CoprodI.Word.rcons p = w := by
    rw [← Monoid.CoprodI.Word.equivPair_symm]
    exact (Monoid.CoprodI.Word.equivPair b).symm_apply_apply w
  change p.tail.toList.length ≤ w.toList.length
  by_cases hp : p.head = 1
  · rw [Monoid.CoprodI.Word.rcons, dite_eq_left hp] at hrcons
    simp [hrcons]
  · rw [Monoid.CoprodI.Word.rcons, dite_eq_right hp] at hrcons
    have hlen : w.toList.length = p.tail.toList.length + 1 := by
      calc
        w.toList.length =
            (Monoid.CoprodI.Word.cons p.head p.tail p.fstIdx_ne hp).toList.length := by
          rw [hrcons]
        _ = p.tail.toList.length + 1 := by
          simp [Monoid.CoprodI.Word.cons]
    omega

/--
@isnad1 id=le.0h5v.s10.ed2c65ad34bf from=translated src=- shape=e814488d vocab=71eb13a6
-/
theorem word_length_mul_left_le {b : Bool} (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
      (Monoid.CoprodI.of a * x)).toList.length ≤
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).toList.length + 1 := by
  classical
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) = Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    calc
      e.symm (e (Monoid.CoprodI.of a * x)) = Monoid.CoprodI.of a * x :=
        e.symm_apply_apply _
      _ = Monoid.CoprodI.of a * e.symm (e x) := by
        rw [e.symm_apply_apply]
      _ = e.symm (Monoid.CoprodI.of a • e x) := by
        change Monoid.CoprodI.of a * Monoid.CoprodI.Word.prod (e x) =
          Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
        rw [Monoid.CoprodI.Word.prod_smul]
  rw [he]
  let q : Monoid.CoprodI.Word.Pair (binaryFamily G H) b :=
    { Monoid.CoprodI.Word.equivPair b (e x) with
      head := a * (Monoid.CoprodI.Word.equivPair b (e x)).head }
  have hq : Monoid.CoprodI.of a • e x = Monoid.CoprodI.Word.rcons q := by
    rw [← Monoid.CoprodI.Word.smul_eq_of_smul]
    simpa [q] using
      (Monoid.CoprodI.Word.smul_def (M := binaryFamily G H) a (e x))
  rw [hq]
  have htail := word_pair_tail_length_le (G := G) (H := H) (b := b) (e x)
  have htail' : q.tail.toList.length ≤ (e x).toList.length := by
    simpa [q] using htail
  exact (word_length_rcons_le (G := G) (H := H) q).trans
    (Nat.add_le_add_right htail' 1)

def binaryReducedLength (x : G ∗ H) : ℕ :=
  (binaryReducedWord (G := G) (H := H) x).toList.length

/--
@isnad1 id=eq.0h3v.s8.a601ecae0465 from=translated src=- shape=cede8f55 vocab=793b4cb3
-/
@[simp] theorem binaryToIndexed_separatedMap (a : Sum G H) :
    binaryToIndexed (G := G) (H := H) (separatedMap a) =
      binaryLetterToIndexed (G := G) (H := H) a := by
  cases a <;> simp [separatedMap, binaryLetterToIndexed]

/--
@isnad1 id=le.0h3v.s5.476cf3346849 from=translated src=- shape=68bb6ea1 vocab=70621798
-/
theorem binaryReducedLength_factorWordProd_le (u : List (Sum G H)) :
    binaryReducedLength (G := G) (H := H) (factorWordProd u) ≤ u.length := by
  classical
  induction u with
  | nil =>
      change (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (binaryToIndexed (factorWordProd ([] : List (Sum G H))))).toList.length ≤ 0
      simp [factorWordProd, Monoid.CoprodI.Word.equiv]
  | cons a u ih =>
      have hword : binaryReducedWord (G := G) (H := H) (factorWordProd (a :: u)) =
          Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
            (binaryLetterToIndexed (G := G) (H := H) a *
              binaryToIndexed (G := G) (H := H) (factorWordProd u)) := by
        apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
        change Monoid.CoprodI.Word.prod
            (binaryReducedWord (G := G) (H := H) (factorWordProd (a :: u))) =
          Monoid.CoprodI.Word.prod
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
              (binaryLetterToIndexed (G := G) (H := H) a *
                binaryToIndexed (G := G) (H := H) (factorWordProd u)))
        rw [binaryReducedWord_prod]
        change binaryToIndexed (G := G) (H := H) (factorWordProd (a :: u)) =
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
              (binaryLetterToIndexed (G := G) (H := H) a *
                binaryToIndexed (G := G) (H := H) (factorWordProd u)))
        rw [(Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm_apply_apply]
        cases a <;>
          simp [factorWordProd, separatedMap, binaryLetterToIndexed]
      rw [binaryReducedLength, hword]
      cases a with
      | inl g =>
          exact (word_length_mul_left_le (G := G) (H := H) (b := false) g _).trans
            (Nat.succ_le_succ ih)
      | inr h =>
          exact (word_length_mul_left_le (G := G) (H := H) (b := true) h _).trans
            (Nat.succ_le_succ ih)

def binarySigmaToSum : Sigma (binaryFamily G H) → Sum G H
  | ⟨false, g⟩ => Sum.inl g
  | ⟨true, h⟩ => Sum.inr h

/--
@isnad1 id=eq.0h3v.s8.ceb010b570fc from=translated src=- shape=b755955b vocab=12aa3300
-/
@[simp] theorem binaryLetterToIndexed_sigma (z : Sigma (binaryFamily G H)) :
    binaryLetterToIndexed (G := G) (H := H) (binarySigmaToSum z) =
      Monoid.CoprodI.of z.2 := by
  cases z with
  | mk b z =>
      cases b <;> rfl

def binaryReducedLetters (x : G ∗ H) : List (Sum G H) :=
  (binaryReducedWord (G := G) (H := H) x).toList.map binarySigmaToSum

/--
@isnad1 id=eq.0h3v.s9.cd4f69215a41 from=translated src=- shape=ac5afaf4 vocab=ecf32317
-/
theorem binaryLetterToIndexed_map_prod
    (l : List (Sigma (binaryFamily G H))) :
    ((l.map binarySigmaToSum).map (binaryLetterToIndexed (G := G) (H := H))).prod =
      (l.map (fun z => Monoid.CoprodI.of z.2)).prod := by
  induction l with
  | nil => rfl
  | cons z zs ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [binaryLetterToIndexed_sigma, ih]

/--
@isnad1 id=eq.0h3v.s5.3acb6da4df97 from=translated src=- shape=dcd7fad7 vocab=c9a5c7f3
-/
theorem factorWordProd_binaryReducedLetters (x : G ∗ H) :
    factorWordProd (binaryReducedLetters (G := G) (H := H) x) = x := by
  classical
  apply (binaryIndexedEquiv (G := G) (H := H)).injective
  calc
    binaryToIndexed (G := G) (H := H)
        (factorWordProd (binaryReducedLetters (G := G) (H := H) x)) =
        ((binaryReducedLetters (G := G) (H := H) x).map
          (binaryLetterToIndexed (G := G) (H := H))).prod :=
      binaryToIndexed_factorWordProd _
    _ = ((binaryReducedWord (G := G) (H := H) x).toList.map
          (fun z => Monoid.CoprodI.of z.2)).prod := by
      simpa [binaryReducedLetters, List.map_map] using
        (binaryLetterToIndexed_map_prod (G := G) (H := H)
          ((binaryReducedWord (G := G) (H := H) x).toList))
    _ = Monoid.CoprodI.Word.prod (binaryReducedWord (G := G) (H := H) x) := rfl
    _ = binaryToIndexed (G := G) (H := H) x :=
      binaryReducedWord_prod (G := G) (H := H) x

/--
@isnad1 id=le.0h3v.s5.f069bf2e38f4 from=translated src=- shape=e65acbe9 vocab=799d114d
-/
theorem binaryReducedLength_le_factorWordLength (x : G ∗ H) :
    binaryReducedLength (G := G) (H := H) x ≤ factorWordLength x := by
  obtain ⟨u, hu, hux⟩ := factorWordLength_spec x
  calc
    binaryReducedLength x = binaryReducedLength (factorWordProd u) :=
      (congrArg binaryReducedLength hux).symm
    _ ≤ u.length := binaryReducedLength_factorWordProd_le u
    _ = factorWordLength x := hu

/--
@isnad1 id=le.0h3v.s5.0ff0bab95f81 from=translated src=- shape=e65acbe9 vocab=799d114d
-/
theorem factorWordLength_le_binaryReducedLength (x : G ∗ H) :
    factorWordLength x ≤ binaryReducedLength x := by
  let u := binaryReducedLetters (G := G) (H := H) x
  have hu : factorWordProd u = x := by
    simpa [u] using factorWordProd_binaryReducedLetters (G := G) (H := H) x
  calc
    factorWordLength x = factorWordLength (factorWordProd u) := by rw [hu]
    _ ≤ u.length := factorWordLength_wordProd_le u
    _ = binaryReducedLength x := by
      simp [u, binaryReducedLength, binaryReducedLetters]

/--
@isnad1 id=eq.0h3v.s5.be069b061976 from=translated src=- shape=e65acbe9 vocab=84b3dab7
-/
theorem factorWordLength_eq_binaryReducedLength (x : G ∗ H) :
    factorWordLength x = binaryReducedLength x :=
  le_antisymm (factorWordLength_le_binaryReducedLength x)
    (binaryReducedLength_le_factorWordLength x)

/-! ### The shape of a reduced binary word -/

/-- The factor index of a binary letter, expressed in the index type used by
the indexed free-product normal form.-/
def binarySumIndex : Sum G H → Bool
  | Sum.inl _ => false
  | Sum.inr _ => true

/--
@isnad1 id=eq.0h3v.s4.85342e87c552 from=translated src=- shape=7e266f04 vocab=b7230a93
-/
@[simp] theorem binarySumIndex_inl (g : G) :
    binarySumIndex (G := G) (H := H) (Sum.inl g) = false := rfl

/--
@isnad1 id=eq.0h3v.s4.efad2fdc0e29 from=translated src=- shape=c3dc103f vocab=d83a15e1
-/
@[simp] theorem binarySumIndex_inr (h : H) :
    binarySumIndex (G := G) (H := H) (Sum.inr h) = true := rfl

/--
@isnad1 id=eq.0h3v.s4.717464f53b86 from=translated src=- shape=9115df34 vocab=962111c6
-/
@[simp] theorem binarySumIndex_factorWordInv (a : Sum G H) :
    binarySumIndex (factorWordInv (G := G) (H := H) a) =
      binarySumIndex a := by
  cases a <;> rfl

/--
@isnad1 id=eq.0h3v.s4.1d4fe5632c77 from=translated src=- shape=1a4668ce vocab=4aa57d12
-/
@[simp] theorem binarySumIndex_sigma (z : Sigma (binaryFamily G H)) :
    binarySumIndex (G := G) (H := H) (binarySigmaToSum z) = z.1 := by
  cases z with
  | mk b z => cases b <;> rfl

/--
@isnad1 id=false.2h4v.s6.aab168393105 from=translated src=- shape=6ed13a17 vocab=bf54b19d
-/
theorem binaryReducedLetters_ne_one (x : G ∗ H) :
    ∀ a ∈ binaryReducedLetters (G := G) (H := H) x,
      a = Sum.inl 1 ∨ a = Sum.inr 1 → False := by
  intro a ha hbad
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  cases hbad with
  | inl h =>
      cases z with
      | mk b z =>
          cases b with
          | false =>
              change G at z
              have hz1 : z = 1 := by
                simpa [binarySigmaToSum] using h
              exact (binaryReducedWord (G := G) (H := H) x).ne_one
                ⟨false, z⟩ hz hz1
          | true => simp_all [binarySigmaToSum]
  | inr h =>
      cases z with
      | mk b z =>
          cases b with
          | false => simp_all [binarySigmaToSum]
          | true =>
              change H at z
              have hz1 : z = 1 := by
                simpa [binarySigmaToSum] using h
              exact (binaryReducedWord (G := G) (H := H) x).ne_one
                ⟨true, z⟩ hz hz1

/--
@isnad1 id=ischain.0h3v.s6.1e215ca8881d from=translated src=- shape=ac11cc1b vocab=43d7734e
-/
theorem binaryReducedWord_chain_ne (x : G ∗ H) :
    (binaryReducedWord (G := G) (H := H) x).toList.IsChain
      (fun a b => a.1 ≠ b.1) :=
  (binaryReducedWord (G := G) (H := H) x).chain_ne

/--
@isnad1 id=ischain.0h3v.s5.8fb20dda5f1e from=translated src=- shape=3b888a8f vocab=49c5d3f3
-/
theorem binaryReducedLetters_chain_ne (x : G ∗ H) :
    (binaryReducedLetters (G := G) (H := H) x).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
  rw [binaryReducedLetters, List.isChain_map]
  exact (binaryReducedWord_chain_ne (G := G) (H := H) x).imp
    (by
      intro z z' h
      simpa only [binarySumIndex_sigma] using h)

/--
@isnad1 id=and.1h4v.s6.5597407ba635 from=translated src=- shape=58e8e5fc vocab=bf54b19d
-/
theorem binaryReducedLetters_mem_ne_one (x : G ∗ H)
    {a : Sum G H} (ha : a ∈ binaryReducedLetters (G := G) (H := H) x) :
    a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
  constructor <;> intro h
  · exact binaryReducedLetters_ne_one (G := G) (H := H) x a ha (Or.inl h)
  · exact binaryReducedLetters_ne_one (G := G) (H := H) x a ha (Or.inr h)

/-! ### Exact multiplication in the different-factor case -/

/--
@isnad1 id=eq.2h5v.s10.08051d0e38c6 from=translated src=- shape=7b06807b vocab=aae03753
-/
theorem word_cons_of_fstIdx_ne {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (hidx : (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).fstIdx ≠ some b)
    (ha : a ≠ 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.cons a
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) hidx ha := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.cons a
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) hidx ha)
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
    rw [Monoid.CoprodI.Word.prod_smul]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.of a * e.symm (e x)
    rw [e.symm_apply_apply]
  rw [he, Monoid.CoprodI.Word.prod_cons,
    Monoid.CoprodI.Word.prod_smul]

/--
@isnad1 id=eq.2h5v.s10.dbbe8a6a89df from=translated src=- shape=9fe4444b vocab=54a51779
-/
theorem word_length_cons_of_fstIdx_ne {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (hidx : (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).fstIdx ≠ some b)
    (ha : a ≠ 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x).toList.length + 1 := by
  rw [word_cons_of_fstIdx_ne a x hidx ha]
  simp [Monoid.CoprodI.Word.cons]

/--
@isnad1 id=eq.0h5v.s11.0cfc8f56de46 from=translated src=- shape=abd24edf vocab=d7d056c0
-/
theorem word_rcons_of_factor_mul {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.rcons
        { Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) with
          head := a * (Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head } := by
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)) =
    Monoid.CoprodI.Word.prod
      (Monoid.CoprodI.Word.rcons
        { Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x) with
          head := a * (Monoid.CoprodI.Word.equivPair b
            (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head })
  let e := Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
  have he : e (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.of a • e x := by
    apply e.symm.injective
    rw [e.symm_apply_apply]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.Word.prod (Monoid.CoprodI.of a • e x)
    rw [Monoid.CoprodI.Word.prod_smul]
    change Monoid.CoprodI.of a * x =
      Monoid.CoprodI.of a * e.symm (e x)
    rw [e.symm_apply_apply]
  rw [he, Monoid.CoprodI.Word.of_smul_def b (e x) a]

/--
@isnad1 id=eq.0h5v.s11.59c1d85a0bfd from=translated src=- shape=8c80fbe0 vocab=5936ad27
-/
theorem word_length_factor_mul {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H)) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      if a * (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1 then
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length
      else
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length + 1 := by
  rw [word_rcons_of_factor_mul]
  by_cases h : a * (Monoid.CoprodI.Word.equivPair b
      (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1
  · simp [Monoid.CoprodI.Word.rcons, h]
  · simp [Monoid.CoprodI.Word.rcons, h, Monoid.CoprodI.Word.cons]

/--
@isnad1 id=eq.1h5v.s11.687ffe3f50f8 from=translated src=- shape=5e74aa38 vocab=f38ce4ba
-/
theorem word_tail_of_factor_mul_eq_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail := by
  rw [word_rcons_of_factor_mul]
  simp [Monoid.CoprodI.Word.rcons, h]

/--
@isnad1 id=eq.1h5v.s11.14cc82773059 from=translated src=- shape=ec5318f9 vocab=d35ec66d
-/
theorem word_cons_of_factor_mul_ne_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head ≠ 1) :
    Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x) =
      Monoid.CoprodI.Word.cons
        (a * (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head)
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail
        (Monoid.CoprodI.Word.equivPair b
          (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).fstIdx_ne h := by
  rw [word_rcons_of_factor_mul]
  simp [Monoid.CoprodI.Word.rcons, h, Monoid.CoprodI.Word.cons]

/--
@isnad1 id=eq.1h5v.s11.7a984ec9307b from=translated src=- shape=d5729877 vocab=813f039a
-/
theorem word_length_factor_mul_eq_tail_of_mul_eq_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head = 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length := by
  rw [word_tail_of_factor_mul_eq_one a x h]

/--
@isnad1 id=eq.1h5v.s11.a20c27ccc1f5 from=translated src=- shape=2cd1e843 vocab=9aa95ad9
-/
theorem word_length_factor_mul_eq_tail_add_one_of_mul_ne_one {b : Bool}
    (a : binaryFamily G H b)
    (x : binaryIndexedProduct (G := G) (H := H))
    (h : a * (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).head ≠ 1) :
    (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)
        (Monoid.CoprodI.of a * x)).toList.length =
      (Monoid.CoprodI.Word.equivPair b
        (Monoid.CoprodI.Word.equiv (M := binaryFamily G H) x)).tail.toList.length + 1 := by
  rw [word_cons_of_factor_mul_ne_one a x h]
  simp [Monoid.CoprodI.Word.cons]

def sumToSigma : Sum G H → Sigma (binaryFamily G H)
  | Sum.inl g => ⟨false, g⟩
  | Sum.inr h => ⟨true, h⟩

/--
@isnad1 id=eq.0h3v.s4.629c86080be8 from=translated src=- shape=dcd7fad7 vocab=ac2f0015
-/
@[simp] theorem binarySigmaToSum_sumToSigma (a : Sum G H) :
    binarySigmaToSum (G := G) (H := H) (sumToSigma (G := G) (H := H) a) = a := by
  cases a <;> rfl

/--
@isnad1 id=eq.0h3v.s5.47f9a098d95b from=translated src=- shape=93274bf5 vocab=33bc2006
-/
@[simp] theorem sumToSigma_snd_inl (g : G) :
    (sumToSigma (G := G) (H := H) (Sum.inl g)).2 = g := rfl

/--
@isnad1 id=eq.0h3v.s5.03742e95f42f from=translated src=- shape=cae3290a vocab=094719c0
-/
@[simp] theorem sumToSigma_snd_inr (h : H) :
    (sumToSigma (G := G) (H := H) (Sum.inr h)).2 = h := rfl

/--
@isnad1 id=eq.0h3v.s4.f16f6e21449f from=translated src=- shape=afdb2920 vocab=1c4e2056
-/
@[simp] theorem sumToSigma_fst (a : Sum G H) :
    (sumToSigma (G := G) (H := H) a).1 =
      binarySumIndex (G := G) (H := H) a := by
  cases a <;> rfl

/--
@isnad1 id=ex.2h3v.s7.60123f5db486 from=translated src=- shape=98119d1f vocab=ef3b22b2
-/
theorem reducedWord_of_sumList {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    ∃ w : Monoid.CoprodI.Word (binaryFamily G H),
      w.toList = u.map (sumToSigma (G := G) (H := H)) := by
  let v : List (Sigma (binaryFamily G H)) :=
    u.map (sumToSigma (G := G) (H := H))
  have hv_ne : ∀ z ∈ v, z.2 ≠ 1 := by
    intro z hz
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
    cases a with
    | inl g =>
        change g ≠ (1 : G)
        intro hg
        apply (hne (Sum.inl g) ha).1
        exact congrArg (fun z : G => Sum.inl z) hg
    | inr h =>
        change h ≠ (1 : H)
        intro hh
        apply (hne (Sum.inr h) ha).2
        exact congrArg (fun z : H => Sum.inr z) hh
  have hv_chain : v.IsChain (fun a b => a.1 ≠ b.1) := by
    dsimp [v]
    rw [List.isChain_map]
    exact hchain.imp (by
      intro a b hab
      simpa only [sumToSigma_fst] using hab)
  exact ⟨{ toList := v, ne_one := hv_ne, chain_ne := hv_chain }, rfl⟩

/--
@isnad1 id=eq.2h3v.s11.fab88572f868 from=translated src=- shape=5ec954bc vocab=1f76b80f
-/
theorem binaryReducedWord_factorWordProd_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    binaryReducedWord (G := G) (H := H) (factorWordProd u) =
      { toList := u.map (sumToSigma (G := G) (H := H)),
        ne_one := by
          intro z hz
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
          cases a with
          | inl g =>
              change g ≠ (1 : G)
              intro hg
              apply (hne (Sum.inl g) ha).1
              exact congrArg (fun z : G => Sum.inl z) hg
          | inr h =>
              change h ≠ (1 : H)
              intro hh
              apply (hne (Sum.inr h) ha).2
              exact congrArg (fun z : H => Sum.inr z) hh,
        chain_ne := by
          rw [List.isChain_map]
          exact hchain.imp (by
            intro a b hab
            simpa only [sumToSigma_fst] using hab) } := by
  let w : Monoid.CoprodI.Word (binaryFamily G H) :=
    { toList := u.map (sumToSigma (G := G) (H := H)),
      ne_one := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hz
        cases a with
        | inl g =>
            change g ≠ (1 : G)
            intro hg
            apply (hne (Sum.inl g) ha).1
            exact congrArg (fun z : G => Sum.inl z) hg
        | inr h =>
            change h ≠ (1 : H)
            intro hh
            apply (hne (Sum.inr h) ha).2
            exact congrArg (fun z : H => Sum.inr z) hh,
      chain_ne := by
        rw [List.isChain_map]
        exact hchain.imp (by
          intro a b hab
          simpa only [sumToSigma_fst] using hab) }
  have hprod : Monoid.CoprodI.Word.prod w =
      binaryToIndexed (G := G) (H := H) (factorWordProd u) := by
    rw [binaryToIndexed_factorWordProd]
    dsimp [w, Monoid.CoprodI.Word.prod]
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro a ha
    cases a <;> rfl
  apply (Monoid.CoprodI.Word.equiv (M := binaryFamily G H)).symm.injective
  change Monoid.CoprodI.Word.prod
      (binaryReducedWord (G := G) (H := H) (factorWordProd u)) =
    Monoid.CoprodI.Word.prod w
  rw [binaryReducedWord_prod]
  exact hprod.symm

/--
@isnad1 id=eq.2h3v.s6.16cd235c24df from=translated src=- shape=5818e737 vocab=af27d94c
-/
theorem factorWordLength_factorWordProd_eq_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    factorWordLength (factorWordProd u) = u.length := by
  rw [factorWordLength_eq_binaryReducedLength,
    binaryReducedLength,
    binaryReducedWord_factorWordProd_of_reduced (u := u) hne hchain]
  simp

/--
@isnad1 id=ne.3h3v.s7.671dceb9c94f from=translated src=- shape=489390d9 vocab=a0644c3e
-/
theorem factorWordProd_ne_one_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b))
    (hpos : u ≠ []) :
    factorWordProd u ≠ 1 := by
  intro hprod
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  have hzero : factorWordLength (factorWordProd u) = 0 := by
    rw [hprod]
    simp
  have : u.length = 0 := by
    rw [← hlen, hzero]
  exact hpos (List.length_eq_zero_iff.mp this)

/--
@isnad1 id=iff.2h3v.s7.90f0f7e2bb11 from=translated src=- shape=c598d53c vocab=a0644c3e
-/
theorem factorWordProd_eq_one_iff_of_reduced {u : List (Sum G H)}
    (hne : ∀ a ∈ u, a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1)
    (hchain : u.IsChain (fun a b =>
      binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b)) :
    factorWordProd u = 1 ↔ u = [] := by
  constructor
  · intro hprod
    by_contra hne_nil
    exact factorWordProd_ne_one_of_reduced hne hchain hne_nil hprod
  · intro hu
    simp [hu, factorWordProd]

/--
@isnad1 id=eq.2h4v.s9.369bfaa2f33c from=translated src=- shape=a9492210 vocab=1fdad86d
-/
theorem factorWordLength_inl_mul_inr (g : G) (h : H)
    (hg : g ≠ 1) (hh : h ≠ 1) :
    factorWordLength (inl g * inr h) = 2 := by
  have hne : ∀ a ∈ ([Sum.inl g, Sum.inr h] : List (Sum G H)),
      a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by simp [hg], by simp⟩
    · exact ⟨by simp, by simp [hh]⟩
  have hchain : ([Sum.inl g, Sum.inr h] : List (Sum G H)).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
    simp
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  simpa [factorWordProd, separatedMap] using hlen

/--
@isnad1 id=eq.2h4v.s9.8185fc19144c from=translated src=- shape=4cb75ce4 vocab=1fdad86d
-/
theorem factorWordLength_inr_mul_inl (h : H) (g : G)
    (hh : h ≠ 1) (hg : g ≠ 1) :
    factorWordLength (inr h * inl g) = 2 := by
  have hne : ∀ a ∈ ([Sum.inr h, Sum.inl g] : List (Sum G H)),
      a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by simp, by simp [hh]⟩
    · exact ⟨by simp [hg], by simp⟩
  have hchain : ([Sum.inr h, Sum.inl g] : List (Sum G H)).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
    simp
  have hlen := factorWordLength_factorWordProd_eq_of_reduced
    (G := G) (H := H) hne hchain
  simpa [factorWordProd, separatedMap] using hlen

/-! ### Nielsen-minimal tuples and the certified descent measure -/

/-- The total canonical syllable length of a finite tuple in the binary free
product.-/
def tupleFactorLength {n : ℕ} (x : Fin n → G ∗ H) : ℕ :=
  ∑ i, factorWordLength (x i)

/-- A tuple is minimal when its total canonical syllable length is least in its
Nielsen-equivalence class.-/
def NielsenMinimal {n : ℕ} (x : Fin n → G ∗ H) : Prop :=
  ∀ y, NielsenEquivalent x y → tupleFactorLength x ≤ tupleFactorLength y

/-- A tuple is Nielsen-reduced when no elementary multiplication or inverse
  multiplication strictly shortens one of its entries.  This is the local
  normal-form condition extracted from a globally minimal tuple.-/
def NielsenReduced {n : ℕ} (x : Fin n → G ∗ H) : Prop :=
  ∀ i j, i ≠ j →
    factorWordLength (x i) ≤ factorWordLength (x i * x j) ∧
      factorWordLength (x i) ≤ factorWordLength (x i * (x j)⁻¹) ∧
      factorWordLength (x i) ≤ factorWordLength (x j * x i)

def NielsenLengthRepresented {n : ℕ} (x : Fin n → G ∗ H) (k : ℕ) : Prop :=
  ∃ y, NielsenEquivalent x y ∧ tupleFactorLength y = k

noncomputable def nielsenMinLength {n : ℕ} (x : Fin n → G ∗ H) : ℕ := by
  classical
  exact Nat.find (show ∃ k, NielsenLengthRepresented x k from
    ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)

/--
@isnad1 id=nielsenl.0h4v.s5.c748ad4d1a10 from=translated src=- shape=1c639abf vocab=e9be9561
-/
theorem nielsenMinLength_spec {n : ℕ} (x : Fin n → G ∗ H) :
    NielsenLengthRepresented x (nielsenMinLength x) := by
  classical
  exact Nat.find_spec (show ∃ k, NielsenLengthRepresented x k from
    ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)

/--
@isnad1 id=ex.0h4v.s6.4352c5feea1c from=translated src=- shape=e145c2b9 vocab=8fb02349
-/
theorem exists_nielsen_minimal {n : ℕ} (x : Fin n → G ∗ H) :
    ∃ y, NielsenEquivalent x y ∧ NielsenMinimal y ∧
      tupleFactorLength y = nielsenMinLength x := by
  classical
  obtain ⟨y, hy, hlen⟩ := nielsenMinLength_spec x
  refine ⟨y, hy, ?_, hlen⟩
  intro z hyz
  have hxz : NielsenEquivalent x z :=
    Relation.ReflTransGen.trans hy hyz
  have hmin := Nat.find_min'
    (show ∃ k, NielsenLengthRepresented x k from
      ⟨tupleFactorLength x, x, Relation.ReflTransGen.refl, rfl⟩)
    (show NielsenLengthRepresented x (tupleFactorLength z) from
      ⟨z, hxz, rfl⟩)
  rw [hlen]
  exact hmin

/--
@isnad1 id=eq.0h6v.s7.875472a12c3f from=translated src=- shape=344c72df vocab=b5a4ff5b
-/
theorem tupleFactorLength_update {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) (a : G ∗ H) :
    tupleFactorLength (Function.update x i a) =
      factorWordLength a +
        ∑ k ∈ (Finset.univ.erase i), factorWordLength (x k) := by
  rw [tupleFactorLength]
  have hfun :
      (fun k => factorWordLength (Function.update x i a k)) =
        Function.update (fun k => factorWordLength (x k)) i
          (factorWordLength a) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · simp [hki]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.erase_eq]

/--
@isnad1 id=eq.0h5v.s6.5d12a28fe78e from=translated src=- shape=3f9386c5 vocab=bdcadaed
-/
theorem tupleFactorLength_split {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) :
    tupleFactorLength x =
      factorWordLength (x i) +
        ∑ k ∈ (Finset.univ.erase i), factorWordLength (x k) := by
  rw [tupleFactorLength]
  have h := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun k => factorWordLength (x k)) (Finset.mem_univ i)
  simpa [Finset.erase_eq, Nat.add_comm] using h.symm

/--
@isnad1 id=lt.1h6v.s6.74089846f954 from=translated src=- shape=906cc9a0 vocab=91c6489f
-/
theorem tupleFactorLength_update_lt {n : ℕ} (x : Fin n → G ∗ H)
    (i : Fin n) (a : G ∗ H)
    (ha : factorWordLength a < factorWordLength (x i)) :
    tupleFactorLength (Function.update x i a) < tupleFactorLength x := by
  rw [tupleFactorLength_update, tupleFactorLength_split]
  exact Nat.add_lt_add_right ha _

/--
@isnad1 id=le.2h6v.s7.fe09d24f809f from=translated src=- shape=f7177e6f vocab=ee30ccab
-/
theorem nielsenMinimal_tupleFactorLength_le_mulRight {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x i * x j)) := by
  apply hmin
  exact Relation.ReflTransGen.single
    (NielsenStep.mulRight i j hij rfl)

/--
@isnad1 id=not.2h6v.s7.8a5798b58b5e from=translated src=- shape=e6fbf2ef vocab=9bb2a390
-/
theorem nielsenMinimal_no_strict_mulRight_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x i * x j) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulRight hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x i * x j) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

/-! ### Inverse Nielsen moves -/

/--
@isnad1 id=nielsene.1h5v.s6.4c4918ea3743 from=translated src=- shape=7c1bbd79 vocab=816be762
-/
theorem nielsenEquivalent_mulRight_inv {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x (Function.update x i (x i * (x j)⁻¹)) := by
  let y : Fin n → A := Function.update x j (x j)⁻¹
  let z : Fin n → A := Function.update y i (y i * y j)
  let w : Fin n → A := Function.update z j (z j)⁻¹
  have hxy : NielsenStep x y := NielsenStep.invert j rfl
  have hyz : NielsenStep y z := NielsenStep.mulRight i j hij rfl
  have hzw : NielsenStep z w := NielsenStep.invert j rfl
  have hxyz : NielsenEquivalent x z :=
    Relation.ReflTransGen.trans (Relation.ReflTransGen.single hxy)
      (Relation.ReflTransGen.single hyz)
  have hxyzw : NielsenEquivalent x w :=
    Relation.ReflTransGen.trans hxyz (Relation.ReflTransGen.single hzw)
  have hw : w = Function.update x i (x i * (x j)⁻¹) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [w, z, y, hij]
    · by_cases hkj : k = j
      · subst k
        simp [w, z, y, hki, hij]
      · simp [w, z, y, hki, hkj, hij]
  rw [← hw]
  exact hxyzw

/--
@isnad1 id=nielsene.1h4v.s4.c0198d7e75e4 from=translated src=- shape=1c9bb10e vocab=3b33ac21
-/
theorem nielsenEquivalent_symm {A : Type*} [Group A] {n : ℕ}
    {x y : Fin n → A} (h : NielsenEquivalent x y) :
    NielsenEquivalent y x := by
  have step_symm : ∀ {u v : Fin n → A}, NielsenStep u v →
      NielsenEquivalent v u := by
    intro u v hstep
    cases hstep with
    | perm e hEq =>
        subst v
        apply Relation.ReflTransGen.single
        apply NielsenStep.perm e.symm
        funext i
        simp [Function.comp_apply]
    | invert i hEq =>
        subst v
        apply Relation.ReflTransGen.single
        apply NielsenStep.invert i
        funext k
        by_cases hki : k = i
        · subst k
          simp
        · simp [hki]
    | mulRight i j hij hEq =>
        have hback := nielsenEquivalent_mulRight_inv v i j hij
        have hEqBack : Function.update v i (v i * (v j)⁻¹) = u := by
          rw [hEq]
          funext k
          by_cases hki : k = i
          · subst k
            simp [hij, hij.symm]
          · by_cases hkj : k = j
            · subst k
              simp [hki, hij, hij.symm]
            · simp [hEq, hki, hkj]
        rw [hEqBack] at hback
        exact hback
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | single hstep => exact step_symm hstep
  | trans h₁ h₂ ih₁ ih₂ => exact Relation.ReflTransGen.trans ih₂ ih₁

/--
@isnad1 id=nielsene.0h3v.s4.106188147b19 from=translated src=- shape=112ccd3c vocab=3b33ac21
-/
theorem nielsenEquivalent_refl {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) : NielsenEquivalent x x :=
  Relation.ReflTransGen.refl

/--
@isnad1 id=nielsene.2h5v.s5.5a9c3ba373b2 from=translated src=- shape=31de3456 vocab=3b33ac21
-/
theorem nielsenEquivalent_trans {A : Type*} [Group A] {n : ℕ}
    {x y z : Fin n → A} (hxy : NielsenEquivalent x y)
    (hyz : NielsenEquivalent y z) : NielsenEquivalent x z :=
  Relation.ReflTransGen.trans hxy hyz

/--
@isnad1 id=nielsene.1h5v.s5.b6b3b8c3352f from=translated src=- shape=20097e4a vocab=a3bfdcc6
-/
theorem nielsenEquivalent_mulLeft {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x (Function.update x i (x j * x i)) := by
  let y : Fin n → A := Function.update x i (x i)⁻¹
  let z : Fin n → A := Function.update y j (y j)⁻¹
  let w : Fin n → A := Function.update z i (z i * z j)
  let q : Fin n → A := Function.update w i (w i)⁻¹
  let r : Fin n → A := Function.update q j (q j)⁻¹
  have hxy : NielsenStep x y := NielsenStep.invert i rfl
  have hyz : NielsenStep y z := NielsenStep.invert j rfl
  have hzw : NielsenStep z w := NielsenStep.mulRight i j hij rfl
  have hwq : NielsenStep w q := NielsenStep.invert i rfl
  have hqr : NielsenStep q r := NielsenStep.invert j rfl
  have hxyzw : NielsenEquivalent x w :=
    Relation.ReflTransGen.trans
      (Relation.ReflTransGen.trans (Relation.ReflTransGen.single hxy)
        (Relation.ReflTransGen.single hyz))
      (Relation.ReflTransGen.single hzw)
  have hxyzwq : NielsenEquivalent x q :=
    Relation.ReflTransGen.trans hxyzw (Relation.ReflTransGen.single hwq)
  have hxyzwqr : NielsenEquivalent x r :=
    Relation.ReflTransGen.trans hxyzwq (Relation.ReflTransGen.single hqr)
  have hr : r = Function.update x i (x j * x i) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [r, q, w, z, y, hij, hij.symm]
    · by_cases hkj : k = j
      · subst k
        simp [r, q, w, z, y, hki, hij]
      · simp [r, q, w, z, y, hki, hkj, hij]
  rw [← hr]
  exact hxyzwqr

/-! A conjugation of one entry by another is a composite of elementary moves.
This is the tuple operation used when changing the base point of a folded
graph. -/
/--
@isnad1 id=nielsene.1h5v.s6.a46b8ed0d5d2 from=translated src=- shape=1dfc006b vocab=816be762
-/
theorem nielsenEquivalent_conjugate {A : Type*} [Group A] {n : ℕ}
    (x : Fin n → A) (i j : Fin n) (hij : i ≠ j) :
    NielsenEquivalent x
      (Function.update x i (x j * x i * (x j)⁻¹)) := by
  let y := Function.update x i (x j * x i)
  have hxy : NielsenEquivalent x y := nielsenEquivalent_mulLeft x i j hij
  have hyz : NielsenEquivalent y
      (Function.update y i (y i * (y j)⁻¹)) :=
    nielsenEquivalent_mulRight_inv y i j hij
  have hxyz := nielsenEquivalent_trans hxy hyz
  have hEq : Function.update y i (y i * (y j)⁻¹) =
      Function.update x i (x j * x i * (x j)⁻¹) := by
    funext k
    by_cases hki : k = i
    · subst k
      simp [y, hij, hij.symm, mul_assoc]
    · simp [y, hki, hij]
  rw [hEq] at hxyz
  exact hxyz

/--
@isnad1 id=le.2h6v.s7.30ebefcd0d36 from=translated src=- shape=caec02b4 vocab=2cf93e4a
-/
theorem nielsenMinimal_tupleFactorLength_le_mulRight_inv {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x i * (x j)⁻¹)) := by
  apply hmin
  exact nielsenEquivalent_mulRight_inv x i j hij

/--
@isnad1 id=le.2h6v.s7.4e8cb51cff18 from=translated src=- shape=7bad1ca7 vocab=ee30ccab
-/
theorem nielsenMinimal_tupleFactorLength_le_mulLeft {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    tupleFactorLength x ≤
      tupleFactorLength (Function.update x i (x j * x i)) := by
  exact hmin _ (nielsenEquivalent_mulLeft x i j hij)

/--
@isnad1 id=not.2h6v.s7.d47a6deb81dd from=translated src=- shape=5acea631 vocab=7ba8c388
-/
theorem nielsenMinimal_no_strict_mulRight_inv_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x i * (x j)⁻¹) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulRight_inv hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x i * (x j)⁻¹) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

/--
@isnad1 id=not.2h6v.s7.f24ace708b3d from=translated src=- shape=92ab944a vocab=9bb2a390
-/
theorem nielsenMinimal_no_strict_mulLeft_descent {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x)
    (i j : Fin n) (hij : i ≠ j) :
    ¬ factorWordLength (x j * x i) < factorWordLength (x i) := by
  intro hlt
  have hstep := nielsenMinimal_tupleFactorLength_le_mulLeft hmin i j hij
  have hdesc := tupleFactorLength_update_lt x i (x j * x i) hlt
  exact (Nat.not_lt_of_ge hstep) hdesc

/--
@isnad1 id=nielsenr.1h4v.s5.00ae90dfd9ef from=translated src=- shape=1acced70 vocab=843a1296
-/
theorem nielsenMinimal_nielsenReduced {n : ℕ}
    {x : Fin n → G ∗ H} (hmin : NielsenMinimal x) :
    NielsenReduced x := by
  intro i j hij
  exact ⟨Nat.le_of_not_gt (nielsenMinimal_no_strict_mulRight_descent hmin i j hij),
    Nat.le_of_not_gt (nielsenMinimal_no_strict_mulRight_inv_descent hmin i j hij),
    Nat.le_of_not_gt (nielsenMinimal_no_strict_mulLeft_descent hmin i j hij)⟩

/--
@isnad1 id=ex.0h4v.s6.14d248780179 from=translated src=- shape=e145c2b9 vocab=86a03c33
-/
theorem exists_nielsen_reduced {n : ℕ} (x : Fin n → G ∗ H) :
    ∃ y, NielsenEquivalent x y ∧ NielsenReduced y ∧
      tupleFactorLength y = nielsenMinLength x := by
  obtain ⟨y, hy, hmin, hlen⟩ := exists_nielsen_minimal x
  exact ⟨y, hy, nielsenMinimal_nielsenReduced hmin, hlen⟩

end GeneralGrushko
end MarshallHall
