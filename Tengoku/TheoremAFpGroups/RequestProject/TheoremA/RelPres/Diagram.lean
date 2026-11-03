module

public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.RelPres.HNN
public import Tengoku.TheoremAFpGroups.RequestProject.TheoremA.Reduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `C_R` is closed under `diagramGroup`

Let `ψ : PresentedGroup S ≃* B` be a presentation on `Fin n` and write `x_a = ψ (of a)`.

* **Alphabet.** One copy of the generators for each vertex `v : Fin r`; the letter `X_(v,a)` is
  `copyIdx r n v a = finProdFinEquiv (v, a) : Fin (r * n)` (this also covers `r = 0`, `n = 0`).
* **Relators.** Every old relator renamed along `copyIdx v` (for all `v`), together with the finite
  list `diagExtraRels r n T`: for every occurrence of a triple `(i, j, k) ∈ T` with `i, j, k < r`
  (triples with an index `≥ r` impose nothing in `diagramGroup` either), the words
  `C_(i,j,a,b) = X_(i,a) X_(j,b) X_(i,a)⁻¹ X_(j,b)⁻¹` for **all** `a, b`, and
  `D_(i,j,k,a) = X_(k,a)⁻¹ X_(i,a) X_(j,a)` for all `a`.
* **Enumeration.** `mergeEnum f g` interleaves two enumerators (even inputs call only `f`, odd
  inputs call only `g`); `foldEnum` folds it over a finite list starting from the nowhere-defined
  enumerator `noneEnum`.  `diagEnum e r T` is `extendEnum (copiesEnum e r) id (diagExtraRels r n T)`
  and `enumRelators_diagEnum` gives its relator set exactly.
* **Algebra.** `commute_of_closure` and `eq_mul_of_closure`: the finite relations on generators
  imply the full diagram relations for arbitrary homomorphisms `f_v : B →* H`.
* **Isomorphism.** `diagramPresentationEquiv : PresentedGroup (diagRelSet S r T) ≃* diagramGroup r T B`
  by explicit universal properties, with compatibility lemmas.
* **Closure.** `ClassCR.diagramGroup` and `classCR_diagramGroup_closure` (the exact shape of the
  second conjunct of `UniversalBases`).
-/

open scoped commutatorElement

@[expose] public section

namespace TheoremA.RelPres

open TripleSystem

universe u

variable {R : Set ℕ}

/-! ### Merging enumerators -/

/-- Interleave two enumerators: `mergeEnum f g (2k) = f k`, `mergeEnum f g (2k+1) = g k`.
The parity test is made before either enumerator is called.-/
def mergeEnum {m : ℕ} (f g : ℕ →. RawWord (Fin m)) : ℕ →. RawWord (Fin m) := fun k =>
  bif k.bodd then g k.div2 else f k.div2

/-- The nowhere-defined enumerator.-/
def noneEnum {m : ℕ} : ℕ →. RawWord (Fin m) := fun _ => Part.none

/--
@isnad1 id=isenumer.0h2v.s3.ea72225450ab from=translated src=- shape=c554f1fb vocab=de06f4ec
-/
theorem IsEnumerator.noneEnum {m : ℕ} : IsEnumerator R (noneEnum : ℕ →. RawWord (Fin m)) := by
  unfold IsEnumerator TheoremA.RelPres.noneEnum
  have := RecursiveIn.of_partrec (O := oracle R) Nat.Partrec.none
  convert this using 1
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
@isnad1 id=eq.0h1v.s4.8f8e5d5482fd from=translated src=- shape=03c93127 vocab=7f52c5fa
-/
theorem enumRelators_noneEnum {m : ℕ} :
    enumRelators (noneEnum : ℕ →. RawWord (Fin m)) = ∅ := by
  ext x
  simp [enumRelators, TheoremA.RelPres.noneEnum]

/--
@isnad1 id=iff.0h4v.s6.9293ee2bd363 from=translated src=- shape=84107104 vocab=64d8d0d8
-/
theorem mem_mergeEnum_iff {m : ℕ} (f g : ℕ →. RawWord (Fin m)) (w : RawWord (Fin m)) :
    (∃ k, w ∈ mergeEnum f g k) ↔ (∃ k, w ∈ f k) ∨ (∃ k, w ∈ g k) := by
  constructor
  · rintro ⟨k, hk⟩
    unfold mergeEnum at hk
    cases hb : k.bodd <;> simp only [hb, Bool.cond_true, Bool.cond_false] at hk
    · exact Or.inl ⟨_, hk⟩
    · exact Or.inr ⟨_, hk⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · exact ⟨Nat.bit false k, by simpa [mergeEnum] using hk⟩
    · exact ⟨Nat.bit true k, by simpa [mergeEnum] using hk⟩

/-- **Range of the merged enumerator**: the union of the two ranges.
@isnad1 id=eq.0h3v.s5.9f61a4b018c1 from=translated src=- shape=582e1933 vocab=9a77b77d
-/
theorem enumRelators_mergeEnum {m : ℕ} (f g : ℕ →. RawWord (Fin m)) :
    enumRelators (mergeEnum f g) = enumRelators f ∪ enumRelators g := by
  ext x
  constructor
  · rintro ⟨k, w, hw, rfl⟩
    rcases (mem_mergeEnum_iff f g w).1 ⟨k, hw⟩ with ⟨k', h⟩ | ⟨k', h⟩
    · exact Or.inl ⟨k', w, h, rfl⟩
    · exact Or.inr ⟨k', w, h, rfl⟩
  · rintro (⟨k, w, hw, rfl⟩ | ⟨k, w, hw, rfl⟩)
    · obtain ⟨k', h⟩ := (mem_mergeEnum_iff f g w).2 (Or.inl ⟨k, hw⟩)
      exact ⟨k', w, h, rfl⟩
    · obtain ⟨k', h⟩ := (mem_mergeEnum_iff f g w).2 (Or.inr ⟨k, hw⟩)
      exact ⟨k', w, h, rfl⟩

/-- Merge a finite list of enumerators.-/
def foldEnum {m : ℕ} (L : List (ℕ →. RawWord (Fin m))) : ℕ →. RawWord (Fin m) :=
  L.foldr mergeEnum noneEnum

/--
@isnad1 id=eq.0h2v.s6.104cba5edeb6 from=translated src=- shape=2187b7c7 vocab=c62495e0
-/
theorem enumRelators_foldEnum {m : ℕ} (L : List (ℕ →. RawWord (Fin m))) :
    enumRelators (foldEnum L) = ⋃ f ∈ L, enumRelators f := by
  induction L with
  | nil => simp [foldEnum, enumRelators_noneEnum]
  | cons f L ih =>
    simp only [foldEnum, List.foldr_cons] at ih ⊢
    rw [enumRelators_mergeEnum, ih]
    simp

/-! ### Copies of the alphabet -/

/-- The letter `X_(v,a)` of the alphabet `Fin (r * n)`.-/
def copyIdx (r n : ℕ) (v : Fin r) (a : Fin n) : Fin (r * n) := finProdFinEquiv (v, a)

/--
@isnad1 id=eq.0h3v.s5.9549fbc68eb9 from=translated src=- shape=6434be99 vocab=88268910
-/
theorem copyIdx_surj {r n : ℕ} (x : Fin (r * n)) : copyIdx r n x.divNat x.modNat = x :=
  finProdFinEquiv.apply_symm_apply x

/--
@isnad1 id=eq.0h4v.s4.15c71f016c00 from=translated src=- shape=42de6708 vocab=8f4cd686
-/
@[simp] theorem divNat_copyIdx {r n : ℕ} (v : Fin r) (a : Fin n) :
    (copyIdx r n v a).divNat = v :=
  congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (v, a))

/--
@isnad1 id=eq.0h4v.s4.19d99f903f24 from=translated src=- shape=986c830e vocab=293ab3c3
-/
@[simp] theorem modNat_copyIdx {r n : ℕ} (v : Fin r) (a : Fin n) :
    (copyIdx r n v a).modNat = a :=
  congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (v, a))

/--
@isnad1 id=eq.0h4v.s7.98792e553f53 from=translated src=- shape=e91f7880 vocab=51f8c6e2
-/
@[simp] theorem finProdFinEquiv_symm_copyIdx {r n : ℕ} (v : Fin r) (a : Fin n) :
    finProdFinEquiv.symm (copyIdx r n v a) = (v, a) := by
  simp [copyIdx]

/-- All renamed copies of `e`, one for each vertex.-/
def copiesEnum {n : ℕ} (e : ℕ →. RawWord (Fin n)) (r : ℕ) : ℕ →. RawWord (Fin (r * n)) :=
  foldEnum ((List.finRange r).map fun v => extendEnum e (copyIdx r n v) [])

/--
@isnad1 id=eq.0h3v.s8.9cc406df5798 from=translated src=- shape=7cb77d9c vocab=20657591
-/
theorem enumRelators_copiesEnum {n : ℕ} (e : ℕ →. RawWord (Fin n)) (r : ℕ) :
    enumRelators (copiesEnum e r) = ⋃ v, FreeGroup.map (copyIdx r n v) '' enumRelators e := by
  rw [copiesEnum, enumRelators_foldEnum]
  ext x
  simp [enumRelators_extendEnum]

/-! ### The finite extra relators -/

/-- `C_(i,j,a,b) = X_(i,a) X_(j,b) X_(i,a)⁻¹ X_(j,b)⁻¹`.-/
def commRel {m : ℕ} (x y : Fin m) : RawWord (Fin m) := [(x, true), (y, true), (x, false), (y, false)]

/-- `D_(i,j,k,a) = X_(k,a)⁻¹ X_(i,a) X_(j,a)` (with `x = X_(i,a)`, `y = X_(j,a)`, `z = X_(k,a)`).-/
def diagRel {m : ℕ} (x y z : Fin m) : RawWord (Fin m) := [(z, false), (x, true), (y, true)]

/--
@isnad1 id=eq.0h3v.s5.d8bc2e3d2f68 from=translated src=- shape=3c61cca6 vocab=a8303893
-/
theorem eval_commRel {m : ℕ} (x y : Fin m) :
    (commRel x y).eval = ⁅FreeGroup.of x, FreeGroup.of y⁆ := by
  rw [commutatorElement_def,
    show commRel x y = [(x, true)] ++ [(y, true)] ++ [(x, false)] ++ [(y, false)] from rfl]
  simp only [RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg]

/--
@isnad1 id=eq.0h4v.s6.61e6446c8458 from=translated src=- shape=6162c99d vocab=a98c5c97
-/
theorem eval_diagRel {m : ℕ} (x y z : Fin m) :
    (diagRel x y z).eval = (FreeGroup.of z)⁻¹ * FreeGroup.of x * FreeGroup.of y := by
  rw [show diagRel x y z = [(z, false)] ++ [(x, true)] ++ [(y, true)] from rfl]
  simp only [RawWord.eval_append, RawWord.eval_pos, RawWord.eval_neg]

/-- The `n * n + n` extra relators of one triple occurrence (none if an index is `≥ r`).-/
def tripleRels (r n : ℕ) (t : Triple) : List (RawWord (Fin (r * n))) :=
  if h : t.1 < r ∧ t.2.1 < r ∧ t.2.2 < r then
    ((List.finRange n).flatMap fun a => (List.finRange n).map fun b =>
        commRel (copyIdx r n ⟨t.1, h.1⟩ a) (copyIdx r n ⟨t.2.1, h.2.1⟩ b)) ++
      (List.finRange n).map fun a =>
        diagRel (copyIdx r n ⟨t.1, h.1⟩ a) (copyIdx r n ⟨t.2.1, h.2.1⟩ a)
          (copyIdx r n ⟨t.2.2, h.2.2⟩ a)
  else []

/-- The finite list of all extra relators, for every occurrence of a triple in `T`.-/
def diagExtraRels (r n : ℕ) (T : List Triple) : List (RawWord (Fin (r * n))) :=
  T.flatMap (tripleRels r n)

/--
@isnad1 id=mem.4h6v.s7.c98982fe63d6 from=translated src=- shape=8528245e vocab=86b4e6c8
-/
theorem commRel_mem {r n : ℕ} {T : List Triple} {t : Triple} (ht : t ∈ T) (hi : t.1 < r)
    (hj : t.2.1 < r) (hk : t.2.2 < r) (a b : Fin n) :
    commRel (copyIdx r n ⟨t.1, hi⟩ a) (copyIdx r n ⟨t.2.1, hj⟩ b) ∈ diagExtraRels r n T := by
  refine List.mem_flatMap.2 ⟨t, ht, ?_⟩
  rw [tripleRels, dite_eq_left ⟨hi, hj, hk⟩]
  exact List.mem_append_left _
    (List.mem_flatMap.2 ⟨a, List.mem_finRange _, List.mem_map.2 ⟨b, List.mem_finRange _, rfl⟩⟩)

/--
@isnad1 id=mem.4h5v.s7.074b094b0599 from=translated src=- shape=5f8ae701 vocab=d0572b18
-/
theorem diagRel_mem {r n : ℕ} {T : List Triple} {t : Triple} (ht : t ∈ T) (hi : t.1 < r)
    (hj : t.2.1 < r) (hk : t.2.2 < r) (a : Fin n) :
    diagRel (copyIdx r n ⟨t.1, hi⟩ a) (copyIdx r n ⟨t.2.1, hj⟩ a) (copyIdx r n ⟨t.2.2, hk⟩ a) ∈
      diagExtraRels r n T := by
  refine List.mem_flatMap.2 ⟨t, ht, ?_⟩
  rw [tripleRels, dite_eq_left ⟨hi, hj, hk⟩]
  exact List.mem_append_right _ (List.mem_map.2 ⟨a, List.mem_finRange _, rfl⟩)

/-- Every extra relator is a `C` or a `D` word for some triple occurrence.
@isnad1 id=ex.1h4v.s8.9f3e3dafc70a from=translated src=- shape=29db4831 vocab=ed6714b6
-/
theorem mem_diagExtraRels {r n : ℕ} {T : List Triple} {w : RawWord (Fin (r * n))}
    (hw : w ∈ diagExtraRels r n T) :
    ∃ t ∈ T, ∃ (hi : t.1 < r) (hj : t.2.1 < r) (hk : t.2.2 < r),
      (∃ a b : Fin n, w = commRel (copyIdx r n ⟨t.1, hi⟩ a) (copyIdx r n ⟨t.2.1, hj⟩ b)) ∨
      (∃ a : Fin n, w = diagRel (copyIdx r n ⟨t.1, hi⟩ a) (copyIdx r n ⟨t.2.1, hj⟩ a)
        (copyIdx r n ⟨t.2.2, hk⟩ a)) := by
  obtain ⟨t, ht, hw⟩ := List.mem_flatMap.1 hw
  unfold tripleRels at hw
  split_ifs at hw with h
  · refine ⟨t, ht, h.1, h.2.1, h.2.2, ?_⟩
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨a, -, hw⟩ := List.mem_flatMap.1 hw
      obtain ⟨b, -, rfl⟩ := List.mem_map.1 hw
      exact Or.inl ⟨a, b, rfl⟩
    · obtain ⟨a, -, rfl⟩ := List.mem_map.1 hw
      exact Or.inr ⟨a, rfl⟩
  · simp at hw

/-! ### The presentation and its enumerator -/

/-- The relator set of the presentation `P` of `diagramGroup r T B`.-/
def diagRelSet {n : ℕ} (S : Set (FreeGroup (Fin n))) (r : ℕ) (T : List Triple) :
    Set (FreeGroup (Fin (r * n))) :=
  (⋃ v, FreeGroup.map (copyIdx r n v) '' S) ∪ RawWord.eval '' {w | w ∈ diagExtraRels r n T}

/-- The enumerator of the presentation `P`.-/
def diagEnum {n : ℕ} (e : ℕ →. RawWord (Fin n)) (r : ℕ) (T : List Triple) :
    ℕ →. RawWord (Fin (r * n)) :=
  extendEnum (copiesEnum e r) id (diagExtraRels r n T)

/-- **Exact relator set of the enumerated presentation.**
@isnad1 id=eq.0h4v.s5.14db606de1a3 from=translated src=- shape=e7e2ad7f vocab=4c062748
-/
theorem enumRelators_diagEnum {n : ℕ} (e : ℕ →. RawWord (Fin n)) (r : ℕ) (T : List Triple) :
    enumRelators (diagEnum e r T) = diagRelSet (enumRelators e) r T := by
  rw [diagEnum, enumRelators_extendEnum, enumRelators_copiesEnum, diagRelSet]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x, hx, by simp⟩

/-! ### Finite relations on generators imply all diagram relations -/

section Algebra

variable {B H : Type*} [Group B] [Group H] {s : Set B}

/-- If the images of generators commute pairwise, the full images commute.
@isnad1 id=commute.2h7v.s8.acca2f82cdbc from=translated src=- shape=1f41d1fd vocab=e2dd2e56
-/
theorem commute_of_closure (hs : Subgroup.closure s = ⊤) (f g : B →* H)
    (h : ∀ x ∈ s, ∀ y ∈ s, Commute (f x) (g y)) : ∀ x y, Commute (f x) (g y) := by
  have h1 : ∀ x ∈ s, ∀ y, Commute (f x) (g y) := by
    intro x hx y
    have hy : y ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top y
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact h x hx y hy
    | one => simp
    | mul y z _ _ ihy ihz => rw [map_mul]; exact ihy.mul_right ihz
    | inv y _ ih => rw [map_inv]; exact ih.inv_right
  intro x y
  have hx : x ∈ Subgroup.closure s := hs ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx y
  | one => simp
  | mul x z _ _ ihx ihz => rw [map_mul]; exact ihx.mul_left ihz
  | inv x _ ih => rw [map_inv]; exact ih.inv_left

/-- The pointwise product of two homomorphisms with commuting images.-/
def mulOfCommute (f g : B →* H) (hc : ∀ x y, Commute (f x) (g y)) : B →* H where
  toFun b := f b * g b
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_assoc, ← mul_assoc (f y) (g x) (g y), (hc y x).eq]
    simp only [mul_assoc]

/-- If `f_k = f_i f_j` on generators and the images of `f_i`, `f_j` commute on generators, then
`f_k = f_i f_j` everywhere.-/
theorem eq_mul_of_closure (hs : Subgroup.closure s = ⊤) (fi fj fk : B →* H)
    (hc : ∀ x ∈ s, ∀ y ∈ s, Commute (fi x) (fj y)) (hd : ∀ x ∈ s, fk x = fi x * fj x) :
    ∀ b, fk b = fi b * fj b := by
  have hc' := commute_of_closure hs fi fj hc
  have : fk = mulOfCommute fi fj hc' := MonoidHom.eq_of_eqOn_dense hs fun x hx => by rw [hd x hx]; rfl
  intro b
  rw [this]
  rfl

end Algebra

/-! ### The presentation isomorphism -/

variable {B : Type u} [Group B] {n : ℕ} {S : Set (FreeGroup (Fin n))}
variable (ψ : PresentedGroup S ≃* B) (r : ℕ) (T : List Triple)

/-- The canonical maps `ι_v` satisfy all diagram relations in `diagramGroup r T B`.
@isnad1 id=and.4h4v.s10.e91589c24088 from=translated src=- shape=2f5940b1 vocab=d73e9af3
-/
theorem diagramGroup_ι_rel (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) :
    (∀ g h : B, Commute (diagramGroup.ι r T B ⟨t.1, hi⟩ g) (diagramGroup.ι r T B ⟨t.2.1, hj⟩ h)) ∧
    (∀ g : B, diagramGroup.ι r T B ⟨t.2.2, hk⟩ g =
      diagramGroup.ι r T B ⟨t.1, hi⟩ g * diagramGroup.ι r T B ⟨t.2.1, hj⟩ g) := by
  have mem : ∀ x ∈ relators r T B,
      QuotientGroup.mk' (Subgroup.normalClosure (relators r T B)) x = 1 := by
    intro x hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.subset_normalClosure hx
  constructor
  · intro g h
    have := mem _ ⟨t, ht, hi, hj, hk, Or.inl ⟨g, h, rfl⟩⟩
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute] at this
    exact this
  · intro g
    have := mem _ ⟨t, ht, hi, hj, hk, Or.inr ⟨g, rfl⟩⟩
    rw [map_mul, map_mul, map_inv, mul_assoc, inv_mul_eq_one] at this
    exact this

/-- Generator assignment for the forward map: `X_(v,a) ↦ ι_v(x_a)`.-/
noncomputable def diagFwdGen (x : Fin (r * n)) : diagramGroup r T B :=
  diagramGroup.ι r T B x.divNat (ψ (PresentedGroup.of x.modNat))

/--
@isnad1 id=eq.0h8v.s11.3b3375d71e9f from=translated src=- shape=85e85eca vocab=e4a8a34a
-/
theorem lift_diagFwdGen_copy (v : Fin r) (x : FreeGroup (Fin n)) :
    FreeGroup.lift (diagFwdGen ψ r T) (FreeGroup.map (copyIdx r n v) x) =
      diagramGroup.ι r T B v (ψ (PresentedGroup.mk S x)) := by
  have : (FreeGroup.lift (diagFwdGen ψ r T)).comp (FreeGroup.map (copyIdx r n v)) =
      FreeGroup.lift fun a => diagramGroup.ι r T B v (ψ (PresentedGroup.of a)) :=
    FreeGroup.ext_hom _ _ fun a => by simp [diagFwdGen]
  rw [← MonoidHom.comp_apply, this, lift_presentation]

/-- **Forward map** `P → diagramGroup r T B`.-/
noncomputable def diagFwd : PresentedGroup (diagRelSet S r T) →* diagramGroup r T B :=
  PresentedGroup.toGroup (f := diagFwdGen ψ r T) (rels := diagRelSet S r T) (by
    have hD := diagramGroup_ι_rel r T (B := B)
    rintro x (hx | ⟨w, hw, rfl⟩)
    · obtain ⟨v, s, hs, rfl⟩ := Set.mem_iUnion.1 hx
      rw [lift_diagFwdGen_copy, PresentedGroup.one_of_mem hs, map_one, map_one]
    · obtain ⟨t, ht, hi, hj, hk, ⟨a, b, rfl⟩ | ⟨a, rfl⟩⟩ := mem_diagExtraRels hw
      · rw [eval_commRel, map_commutatorElement, commutatorElement_eq_one_iff_commute]
        simpa [diagFwdGen] using (hD t ht hi hj hk).1 (ψ (PresentedGroup.of a))
          (ψ (PresentedGroup.of b))
      · rw [eval_diagRel]
        have := (hD t ht hi hj hk).2 (ψ (PresentedGroup.of a))
        simp [diagFwdGen, this, mul_assoc])

/--
@isnad1 id=eq.0h7v.s9.310057fa07d3 from=translated src=- shape=448b52e0 vocab=5193ea84
-/
theorem diagFwd_of (x : Fin (r * n)) :
    diagFwd ψ r T (PresentedGroup.of x) = diagFwdGen ψ r T x := by
  simp [diagFwd, PresentedGroup.toGroup.of]

/-- The copied old relators vanish in `P`: the homomorphism `PresentedGroup S → P` at `v`.-/
noncomputable def diagVertexAux (v : Fin r) :
    PresentedGroup S →* PresentedGroup (diagRelSet S r T) :=
  PresentedGroup.toGroup (f := fun a => PresentedGroup.of (copyIdx r n v a)) (by
    intro x hx
    have : FreeGroup.lift (fun a => (PresentedGroup.of (copyIdx r n v a) :
        PresentedGroup (diagRelSet S r T))) =
        (PresentedGroup.mk (diagRelSet S r T)).comp (FreeGroup.map (copyIdx r n v)) :=
      FreeGroup.ext_hom _ _ fun a => by simp [PresentedGroup.of]
    rw [this, MonoidHom.comp_apply]
    exact PresentedGroup.one_of_mem (Or.inl (Set.mem_iUnion.2 ⟨v, x, hx, rfl⟩)))

/-- The homomorphism `j_v : B → P`, with `j_v(x_a) = X_(v,a)`.-/
noncomputable def diagVertex (v : Fin r) : B →* PresentedGroup (diagRelSet S r T) :=
  (diagVertexAux r T v).comp (ψ.symm : B →* PresentedGroup S)

/--
@isnad1 id=eq.0h8v.s9.545850938ed1 from=translated src=- shape=17d7f13a vocab=5364cd53
-/
theorem diagVertex_gen (v : Fin r) (a : Fin n) :
    diagVertex ψ r T v (ψ (PresentedGroup.of a)) = PresentedGroup.of (copyIdx r n v a) := by
  simp [diagVertex, diagVertexAux, PresentedGroup.toGroup.of]

/-- The homomorphisms `j_v` satisfy **all** diagram relations.
@isnad1 id=and.4h7v.s10.44915c37cb1a from=translated src=- shape=ecafb592 vocab=577b5855
-/
theorem diagramRelations_diagVertex (t : Triple) (ht : t ∈ T) (hi : t.1 < r) (hj : t.2.1 < r)
    (hk : t.2.2 < r) :
    (∀ g h : B, Commute (diagVertex ψ r T ⟨t.1, hi⟩ g) (diagVertex ψ r T ⟨t.2.1, hj⟩ h)) ∧
    (∀ g : B, diagVertex ψ r T ⟨t.2.2, hk⟩ g =
      diagVertex ψ r T ⟨t.1, hi⟩ g * diagVertex ψ r T ⟨t.2.1, hj⟩ g) := by
  have hs := closure_range_presentation ψ
  have hc : ∀ x ∈ Set.range fun a => ψ (PresentedGroup.of a),
      ∀ y ∈ Set.range fun a => ψ (PresentedGroup.of a),
      Commute (diagVertex ψ r T ⟨t.1, hi⟩ x) (diagVertex ψ r T ⟨t.2.1, hj⟩ y) := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [diagVertex_gen, diagVertex_gen]
    have h := PresentedGroup.one_of_mem (rels := diagRelSet S r T)
      (Or.inr ⟨_, commRel_mem ht hi hj hk a b, rfl⟩)
    rw [eval_commRel, map_commutatorElement, commutatorElement_eq_one_iff_commute] at h
    exact h
  refine ⟨commute_of_closure hs _ _ hc, eq_mul_of_closure hs _ _ _ hc ?_⟩
  rintro _ ⟨a, rfl⟩
  rw [diagVertex_gen, diagVertex_gen, diagVertex_gen]
  have h := PresentedGroup.one_of_mem (rels := diagRelSet S r T)
    (Or.inr ⟨_, diagRel_mem ht hi hj hk a, rfl⟩)
  rw [eval_diagRel, map_mul, map_mul, map_inv, mul_assoc, inv_mul_eq_one] at h
  exact h

/-- **Backward map** `diagramGroup r T B → P`.-/
noncomputable def diagBwd : diagramGroup r T B →* PresentedGroup (diagRelSet S r T) :=
  QuotientGroup.lift _ (Monoid.CoprodI.lift fun v => diagVertex ψ r T v) (by
    apply Subgroup.normalClosure_le_normal
    rintro x ⟨t, ht, hi, hj, hk, ⟨g, h, rfl⟩ | ⟨g, rfl⟩⟩
    · have := (diagramRelations_diagVertex ψ r T t ht hi hj hk).1 g h
      simp [ofIdx, Monoid.CoprodI.lift_of, map_commutatorElement,
        commutatorElement_eq_one_iff_commute.2 this]
    · have := (diagramRelations_diagVertex ψ r T t ht hi hj hk).2 g
      simp [ofIdx, Monoid.CoprodI.lift_of, this, mul_assoc])

/--
@isnad1 id=eq.0h8v.s9.9976f80ecf9a from=translated src=- shape=82e0ef9b vocab=e29aced8
-/
theorem diagBwd_ι (v : Fin r) (b : B) :
    diagBwd ψ r T (diagramGroup.ι r T B v b) = diagVertex ψ r T v b := by
  simp [diagBwd, diagramGroup.ι, ofIdx]

/--
@isnad1 id=eq.0h8v.s9.b5b4f9c483a8 from=translated src=- shape=6800985c vocab=3455d6d5
-/
theorem diagFwd_diagVertex (v : Fin r) (b : B) :
    diagFwd ψ r T (diagVertex ψ r T v b) = diagramGroup.ι r T B v b := by
  have : (diagFwd ψ r T).comp (diagVertex ψ r T v) = diagramGroup.ι r T B v := by
    apply hom_ext_presentation ψ
    intro a
    simp [diagVertex_gen, diagFwd_of, diagFwdGen]
  exact congrArg (fun F : B →* diagramGroup r T B => F b) this

/-- **The presentation `P` describes `diagramGroup r T B`.**-/
noncomputable def diagramPresentationEquiv :
    PresentedGroup (diagRelSet S r T) ≃* diagramGroup r T B :=
  MonoidHom.toMulEquiv (diagFwd ψ r T) (diagBwd ψ r T)
    (by
      apply PresentedGroup.ext
      intro x
      simp only [MonoidHom.comp_apply, diagFwd_of, diagFwdGen, diagBwd_ι, diagVertex_gen,
        copyIdx_surj, MonoidHom.id_apply])
    (by
      apply QuotientGroup.monoidHom_ext
      apply Monoid.CoprodI.ext_hom
      intro v
      ext b
      have := diagFwd_diagVertex ψ r T v b
      rw [← diagBwd_ι] at this
      simpa [diagramGroup.ι, ofIdx] using this)

/-- Compatibility with the generators: `X_(v,a) ↦ ι_v(x_a)`.
@isnad1 id=eq.0h8v.s10.345ffa28f2d9 from=translated src=- shape=05098aad vocab=e0339593
-/
theorem diagramPresentationEquiv_of (v : Fin r) (a : Fin n) :
    diagramPresentationEquiv ψ r T (PresentedGroup.of (copyIdx r n v a)) =
      diagramGroup.ι r T B v (ψ (PresentedGroup.of a)) := by
  simp [diagramPresentationEquiv, diagFwd_of, diagFwdGen]

/-! ### The closure theorem -/

end TheoremA.RelPres
