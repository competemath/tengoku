import Tengoku.Seed.GroupTheory.CoprodI
import Tengoku.Seed.Algebra.Group.Int.TypeTags
import Tengoku.Seed.Data.Int.Cast.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Injectivity lemmas for indexed free products

This file supplies two reusable criteria for injectivity of maps out of an
indexed free product.  The first says that the free product of a family of
injective component maps is injective.  The second reduces injectivity of a
lift to nontriviality on every nonempty normal-form word.
-/

open Function

namespace Monoid.CoprodI

variable {ι : Type*} {M N : ι → Type*}
variable [∀ i, Group (M i)] [∀ i, Group (N i)]

private def letterMap (f : ∀ i, M i →* N i) : (Σ i, M i) → (Σ i, N i)
  | ⟨i, x⟩ => ⟨i, f i x⟩

private theorem letterMap_injective (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) : Injective (letterMap f) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hij : i = j := congrArg Sigma.fst h
  subst j
  refine Sigma.ext (x := ⟨i, x⟩) (y := ⟨i, y⟩) rfl ?_
  exact heq_of_eq (hf i (eq_of_heq (Sigma.ext_iff.mp h).2))

private def wordMap (f : ∀ i, M i →* N i) (hf : ∀ i, Injective (f i))
    (w : Word M) : Word N where
  toList := w.toList.map (letterMap f)
  ne_one := by
    intro l hl
    rcases List.mem_map.mp hl with ⟨l', hl', rfl⟩
    rcases l' with ⟨i, x⟩
    simp only [letterMap]
    intro hx
    exact w.ne_one ⟨i, x⟩ hl' (hf i (hx.trans (f i).map_one.symm))
  chain_ne := by
    rw [List.isChain_map]
    exact w.chain_ne.imp fun a b hab h => hab (by simpa [letterMap] using h)

private theorem wordMap_injective (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) : Injective (wordMap f hf) := by
  intro u v huv
  apply Word.ext
  have h := congrArg Word.toList huv
  change u.toList.map (letterMap f) = v.toList.map (letterMap f) at h
  exact (List.map_injective_iff.mpr (letterMap_injective f hf))
    h

/-- The homomorphism between indexed free products induced componentwise by
a family of homomorphisms.-/
def familyMap (f : ∀ i, M i →* N i) : CoprodI M →* CoprodI N :=
  lift fun i => (of : N i →* CoprodI N).comp (f i)

private theorem wordMap_prod (f : ∀ i, M i →* N i)
    (hf : ∀ i, Injective (f i)) (w : Word M) :
    (wordMap f hf w).prod = familyMap f w.prod := by
  simp only [Word.prod, wordMap, List.map_map, map_list_prod]
  congr 1

/-- Applying injective maps independently to the factors of an indexed free
product gives an injective homomorphism of indexed free products.
@isnad1 id=injectiv.1h4v.s9.93c05938b18a from=translated src=- shape=41503355 vocab=0bae73b0
-/
theorem familyMap_injective (f : ∀ i, M i →* N i)
    [DecidableEq ι] [∀ i, DecidableEq (M i)] [∀ i, DecidableEq (N i)]
    (hf : ∀ i, Injective (f i)) : Injective (familyMap f) := by
  intro x y hxy
  apply Word.equiv.injective
  apply wordMap_injective f hf
  apply Word.equiv.symm.injective
  change (wordMap f hf (Word.equiv x)).prod =
    (wordMap f hf (Word.equiv y)).prod
  rw [wordMap_prod, wordMap_prod]
  have hx : (Word.equiv x).prod = x := Word.equiv.symm_apply_apply x
  have hy : (Word.equiv y).prod = y := Word.equiv.symm_apply_apply y
  simpa [hx, hy] using hxy

/-- A lift from an indexed free product is injective if every nonempty
normal-form word has nontrivial image.
@isnad1 id=injectiv.1h4v.s10.889875532f88 from=translated src=- shape=b9360dc9 vocab=950e1587
-/
theorem lift_injective_of_neWord_nontrivial
    {I : Type*} {H : I → Type*} [∀ i, Group (H i)]
    {Q : Type*} [Group Q] (f : ∀ i, H i →* Q)
    (hne : ∀ i j (u : NeWord H i j), lift f u.prod ≠ 1) :
    Injective (lift f) := by
  classical
  apply (injective_iff_map_eq_one (lift f)).mpr
  intro x hx
  let u : Word H := Word.equiv x
  have hprod : u.prod = x := by
    change Word.equiv.symm (Word.equiv x) = x
    exact Word.equiv.symm_apply_apply x
  by_cases hu : u = Word.empty
  · rw [← hprod, hu]
    rfl
  · obtain ⟨i, j, v, hv⟩ := NeWord.of_word u hu
    exfalso
    apply hne i j v
    have hvprod : v.prod = u.prod := by
      unfold NeWord.prod
      exact congrArg Word.prod hv
    rw [hvprod, hprod, hx]

namespace NeWord

variable {I : Type*} {H : I → Type*} [∀ i, Group (H i)]

/-- A one-letter reduced word in an infinite cyclic factor, specified by a
nonzero additive exponent.-/
def singletonZ (i : I) (k : ℤ) (hk : k ≠ 0) :
    NeWord (fun _ : I ↦ Multiplicative ℤ) i i :=
  .singleton (Multiplicative.ofAdd k) (by simpa using hk)

/-- Concatenate two reduced nonempty words whose boundary letters lie in the
same factor but have nontrivial product.-/
def merge {i j l : I} (u : NeWord H i j) (v : NeWord H j l)
    (h : u.last * v.head ≠ 1) : NeWord H i l :=
  match u with
  | .singleton x hx => v.mulHead x (by simpa using h)
  | .append front hne tail =>
      .append front hne (merge tail v (by simpa using h))

/--
@isnad1 id=eq.1h7v.s8.060fd1fc8a04 from=translated src=- shape=b8f3fecb vocab=e91d52d2
-/
@[simp] theorem merge_prod {i j l : I} (u : NeWord H i j)
    (v : NeWord H j l) (h : u.last * v.head ≠ 1) :
    (merge u v h).prod = u.prod * v.prod := by
  induction u with
  | singleton x hx => simp [merge]
  | append front hne tail _ ihTail =>
      simp only [merge, append_prod, ihTail, mul_assoc]

/-- Whether a nonempty reduced word has at least two blocks.-/
def IsAppend {i j : I} : NeWord H i j → Prop
  | .singleton _ _ => False
  | .append _ _ _ => True

/--
@isnad1 id=eq.1h6v.s6.3e7802c02e08 from=translated src=- shape=60486191 vocab=1a4b73ff
-/
theorem cast_start_head {G : Type*} [Group G] {i i' j : I} (h : i = i')
    (w : NeWord (fun _ : I ↦ G) i j) :
    (h ▸ w).head = w.head := by cases h; rfl

/--
@isnad1 id=eq.1h6v.s6.8637e1edc861 from=translated src=- shape=07f50ccc vocab=7ac4c57e
-/
theorem cast_start_last {i i' j : I} (h : i = i') (w : NeWord H i j) :
    (h ▸ w).last = w.last := by cases h; rfl

/--
@isnad1 id=eq.1h6v.s7.1f931cd9ad38 from=translated src=- shape=035c2b92 vocab=264238d2
-/
theorem cast_start_prod {i i' j : I} (h : i = i') (w : NeWord H i j) :
    (h ▸ w).prod = w.prod := by cases h; rfl

/--
@isnad1 id=iff.1h6v.s6.b4af99d2ac24 from=translated src=- shape=1ebcdf0c vocab=c36a7e61
-/
theorem cast_start_isAppend {i i' j : I} (h : i = i') (w : NeWord H i j) :
    IsAppend (h ▸ w) ↔ IsAppend w := by cases h; rfl

/--
@isnad1 id=eq.2h7v.s7.7a233191c851 from=translated src=- shape=3fea4a2c vocab=d35afc6e
-/
theorem merge_head_of_isAppend_left {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hu : IsAppend u) :
    (merge u v h).head = u.head := by
  cases u with
  | singleton => contradiction
  | append => rfl

/--
@isnad1 id=eq.2h7v.s7.56bc275b727e from=translated src=- shape=475841f8 vocab=d35afc6e
-/
theorem merge_last_of_isAppend_right {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hv : IsAppend v) :
    (merge u v h).last = v.last := by
  induction u with
  | singleton =>
      cases v with
      | singleton => contradiction
      | append => rfl
  | append front hne tail _ ihTail => exact ihTail v _ hv

/--
@isnad1 id=isappend.2h7v.s7.665b52f3eb56 from=translated src=- shape=a723d013 vocab=d35afc6e
-/
theorem merge_isAppend_of_left {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hu : IsAppend u) :
    IsAppend (merge u v h) := by
  cases u with
  | singleton => contradiction
  | append => trivial

/--
@isnad1 id=isappend.2h7v.s7.e8c9330bc320 from=translated src=- shape=fe7863a1 vocab=d35afc6e
-/
theorem merge_isAppend_of_right {i j k : I} (u : NeWord H i j)
    (v : NeWord H j k) (h : u.last * v.head ≠ 1) (hv : IsAppend v) :
    IsAppend (merge u v h) := by
  cases u with
  | singleton =>
      cases v with
      | singleton => contradiction
      | append => trivial
  | append => trivial

/--
@isnad1 id=eq.2h6v.s8.549f3f48a1ec from=translated src=- shape=e90ec723 vocab=00554c5a
-/
theorem merge_head_singleton {i j : I} (x : H i) (hx : x ≠ 1)
    (v : NeWord H i j) (h : x * v.head ≠ 1) :
    (merge (.singleton x hx) v h).head = x * v.head := by
  simp [merge]

/--
@isnad1 id=eq.2h6v.s8.0850bbc871ae from=translated src=- shape=a4026266 vocab=324bc9c2
-/
theorem merge_last_singleton {i j : I} (u : NeWord H i j)
    (y : H j) (hy : y ≠ 1) (h : u.last * y ≠ 1) :
    (merge u (.singleton y hy) h).last = u.last * y := by
  induction u with
  | singleton => rfl
  | append front hne tail _ ihTail => simpa [merge] using ihTail y hy h

/-- The product of a nonempty reduced word in an indexed free product is
nontrivial.
@isnad1 id=ne.0h5v.s7.28965b6ae8ea from=translated src=- shape=c7cc0696 vocab=ee21db4b
-/
theorem prod_ne_one {i j : I} (w : NeWord H i j) : w.prod ≠ 1 := by
  classical
  intro h
  have heq : w.toWord = (Word.empty : Word H) := by
    apply (Word.equiv (M := H)).symm.injective
    change w.prod = 1
    exact h
  have hlist := congrArg Word.toList heq
  exact w.toList_ne_nil (by simpa [toWord] using hlist)

end NeWord

/-- The map from a free group to the indexed free product of infinite cyclic
groups that sends each free generator to the generator of its factor.-/
def intOfFree (I : Type*) : FreeGroup I →*
    CoprodI (fun _ : I ↦ Multiplicative ℤ) :=
  FreeGroup.lift fun i ↦ of (i := i) (Multiplicative.ofAdd 1)

/-- The inverse-on-generators map associated to `intOfFree`.-/
def intToFree (I : Type*) : CoprodI (fun _ : I ↦ Multiplicative ℤ) →*
    FreeGroup I :=
  lift fun i ↦ zpowersHom (FreeGroup I) (FreeGroup.of i)

/--
@isnad1 id=injectiv.0h1v.s7.3d6f791d9320 from=translated src=- shape=a8466342 vocab=bf08797f
-/
theorem intOfFree_injective (I : Type*) : Function.Injective (intOfFree I) := by
  apply Function.LeftInverse.injective (g := intToFree I)
  intro x
  have hcomp : (intToFree I).comp (intOfFree I) = MonoidHom.id (FreeGroup I) := by
    apply FreeGroup.ext_hom
    intro i
    simp [intToFree, intOfFree]
  exact DFunLike.congr_fun hcomp x

/--
@isnad1 id=eq.0h3v.s8.f5fa2480c9e6 from=translated src=- shape=297c12ec vocab=b7d2b89a
-/
theorem of_int_eq_zpow {I : Type*} (i : I) (k : ℤ) :
    of (i := i) (Multiplicative.ofAdd k) =
      (of (i := i) (Multiplicative.ofAdd 1) :
        CoprodI (fun _ : I ↦ Multiplicative ℤ)) ^ k := by
  rw [← map_zpow]
  congr 1
  simpa using (Int.ofAdd_mul (1 : ℤ) k)

end Monoid.CoprodI

namespace FreeGroup

/-- A nonzero power of the canonical generator of the rank-one free group is
nontrivial.
@isnad1 id=ne.1h1v.s5.b46e80c27339 from=translated src=- shape=c55d2efe vocab=0bd420f3
-/
theorem unitGenerator_zpow_ne_one (k : ℤ) (hk : k ≠ 0) :
    (FreeGroup.of () : FreeGroup Unit) ^ k ≠ 1 := by
  intro h
  apply hk
  calc
    k = freeGroupUnitEquivInt ((FreeGroup.of () : FreeGroup Unit) ^ k) :=
      (freeGroupUnitEquivInt.apply_symm_apply k).symm
    _ = freeGroupUnitEquivInt 1 := congrArg _ h
    _ = 0 := by rfl

end FreeGroup
