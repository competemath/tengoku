import Tengoku.Seed.Data.Fin.Tuple.Sort
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Data.List.FinRange
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Coordinates.AlgebraicPolynomialCZero.Interpolation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Sorted words and symmetrized coefficient arrays

For a linearly ordered index type `I`, every word `a : Fin n → I` has a sorted rearrangement
`sortWord a`. Given values `B a'` on words, `coeff B a` sums `B` over all words whose sorted
rearrangement is `a`; it vanishes unless `a` is sorted. These are the coefficients on
nondecreasing words used in the proof of Proposition I.2. The file also identifies `coeff B a`
with the multiplicity-filtered sum produced by the interpolation identity.
-/

open Finset

namespace AlgebraicPolynomialCZero

variable {I : Type*} [LinearOrder I] {n : ℕ}

/-- The sorted rearrangement of a word.-/
def sortWord (a : Fin n → I) : Fin n → I := a ∘ Tuple.sort a

/--
@isnad1 id=monotone.0h3v.s5.1b8297d9b0f7 from=translated src=- shape=844babb4 vocab=5ed30755
-/
theorem monotone_sortWord (a : Fin n → I) : Monotone (sortWord a) := Tuple.monotone_sort a

/--
@isnad1 id=eq.0h4v.s5.433752c42209 from=translated src=- shape=3c82cc17 vocab=054e92da
-/
theorem count_ofFn_eq {α : Type*} [DecidableEq α] (f : Fin n → α) (j : α) :
    (List.ofFn f).count j = #{r | f r = j} := by
  rw [← Multiset.coe_count, ← Fin.univ_val_map, Multiset.count_map, Finset.card_def,
    Finset.filter_val]
  simp only [eq_comm]

/--
@isnad1 id=eq.0h4v.s5.cac13d728b36 from=translated src=- shape=358e861b vocab=fcb2eb59
-/
theorem wordCount_sortWord (a : Fin n → I) (j : I) : wordCount (sortWord a) j = wordCount a j := by
  apply Fin.ext
  rw [wordCount_val, wordCount_val, ← count_ofFn_eq, ← count_ofFn_eq]
  exact ((Tuple.sort a).ofFn_comp_perm a).count_eq j

/-- A sorted word is the sorted rearrangement of every word with the same multiplicities.
@isnad1 id=eq.2h4v.s6.754e065432b7 from=translated src=- shape=fe721297 vocab=8e3888c3
-/
theorem sortWord_eq_of_wordCount {a a' : Fin n → I} (ha : Monotone a)
    (h : ∀ j, wordCount a' j = wordCount a j) : sortWord a' = a := by
  apply List.ofFn_injective
  apply List.Perm.eq_of_sortedLE (monotone_sortWord a').sortedLE_ofFn ha.sortedLE_ofFn
  refine ((Tuple.sort a').ofFn_comp_perm a').trans ?_
  rw [List.perm_iff_count]
  intro j
  rw [count_ofFn_eq, count_ofFn_eq]
  exact congrArg Fin.val (h j)

/--
@isnad1 id=mem.1h5v.s6.675858e624dc from=translated src=- shape=6bfce033 vocab=2bc827a3
-/
theorem sortWord_mem_image {a a' : Fin n → I} (h : sortWord a' = a) (r : Fin n) :
    a' r ∈ univ.image a := by
  subst h
  exact mem_image.mpr ⟨(Tuple.sort a').symm r, mem_univ _, by simp [sortWord]⟩

/--
@isnad1 id=eq.1h6v.s6.86ba98f272ea from=translated src=- shape=5d398f78 vocab=aafb46ff
-/
theorem prod_sortWord {M : Type*} [CommMonoid M] (w : I → M) {a a' : Fin n → I}
    (h : sortWord a' = a) : ∏ r, w (a r) = ∏ r, w (a' r) := by
  subst h
  exact Equiv.prod_comp (Tuple.sort a') (fun r => w (a' r))

/--
@isnad1 id=eq.0h5v.s7.89c2baae53a9 from=translated src=- shape=b94557e9 vocab=b3b91a21
-/
theorem wordCount_coe {S : Finset I} (f : Fin n → S) (j : S) :
    wordCount (fun r => (f r : I)) (j : I) = wordCount f j := by
  apply Fin.ext
  simp only [wordCount_val, Subtype.coe_inj]

/--
@isnad1 id=eq.1h4v.s6.e68dfa14b65e from=translated src=- shape=1c34523e vocab=7d57b879
-/
theorem wordCount_eq_zero {a : Fin n → I} {j : I} (h : ∀ r, a r ≠ j) : wordCount a j = 0 := by
  apply Fin.ext
  simp [wordCount_val, h]

variable {Z : Type*} [AddCommMonoid Z]

/-- The symmetrized coefficient at `a`: the sum of `B a'` over all words `a'` whose sorted
rearrangement is `a` (all such words take values in the range of `a`).-/
def coeff (B : (Fin n → I) → Z) (a : Fin n → I) : Z :=
  ∑ a' ∈ (Fintype.piFinset fun _ => univ.image a).filter (fun a' => sortWord a' = a), B a'

/-- Regrouping a finite expansion according to sorted rearrangements.
@isnad1 id=eq.0h7v.s7.ef215be4e938 from=translated src=- shape=4db783f2 vocab=efdc450b
-/
theorem sum_smul_coeff {R : Type*} [CommSemiring R] [Module R Z] (x : I → R)
    (B : (Fin n → I) → Z) (s : Finset I) :
    ∑ a ∈ Fintype.piFinset (fun _ => s), (∏ r, x (a r)) • coeff B a =
      ∑ a' ∈ Fintype.piFinset (fun _ => s), (∏ r, x (a' r)) • B a' := by
  have hmaps : ∀ a' ∈ Fintype.piFinset (fun _ : Fin n => s),
      sortWord a' ∈ Fintype.piFinset (fun _ : Fin n => s) := by
    intro a' ha'
    rw [Fintype.mem_piFinset] at ha' ⊢
    exact fun r => ha' _
  conv_rhs => rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [coeff, Finset.smul_sum]
  have hset : (Fintype.piFinset fun _ => univ.image a).filter (fun a' => sortWord a' = a) =
      (Fintype.piFinset fun _ => s).filter (fun a' => sortWord a' = a) := by
    ext a'
    simp only [mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun r => ?_, h2⟩
      obtain ⟨r', -, hr'⟩ := mem_image.mp (h1 r)
      rw [← hr']
      exact (Fintype.mem_piFinset.mp ha) r'
    · rintro ⟨-, h2⟩
      exact ⟨sortWord_mem_image h2, h2⟩
  rw [hset]
  refine Finset.sum_congr rfl fun a' ha' => ?_
  rw [prod_sortWord x (mem_filter.mp ha').2]

/-- For a sorted word `a`, the coefficient is the multiplicity-filtered sum over words in the
range of `a`, written with the range as a subtype.
@isnad1 id=eq.1h5v.s10.8a72338b1239 from=translated src=- shape=7b24dba2 vocab=d099e289
-/
theorem sum_filter_wordCount_eq_coeff (B : (Fin n → I) → Z) {a : Fin n → I} (ha : Monotone a) :
    ∑ f ∈ univ.filter (fun f : Fin n → (univ.image a : Finset I) =>
        ∀ j, wordCount f j = wordCount a (j : I)), B (fun r => (f r : I)) = coeff B a := by
  rw [coeff]
  refine Finset.sum_bij (fun f _ => fun r => (f r : I)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro f hf
    have hf' := (mem_filter.mp hf).2
    simp only [mem_filter, Fintype.mem_piFinset]
    refine ⟨fun r => (f r).2, sortWord_eq_of_wordCount ha fun j => ?_⟩
    by_cases hj : j ∈ univ.image a
    · rw [show j = ((⟨j, hj⟩ : (univ.image a : Finset I)) : I) from rfl, wordCount_coe, hf']
    · have h1 : ∀ r, (f r : I) ≠ j := fun r h => hj (h ▸ (f r).2)
      have h2 : ∀ r, a r ≠ j := fun r h => hj (h ▸ mem_image_of_mem a (mem_univ r))
      rw [wordCount_eq_zero h1, wordCount_eq_zero h2]
  · intro f₁ _ f₂ _ h
    funext r
    exact Subtype.ext (congrFun h r)
  · intro a' ha'
    have h2 := (mem_filter.mp ha').2
    refine ⟨fun r => ⟨a' r, sortWord_mem_image h2 r⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    intro j
    rw [← wordCount_coe]
    change wordCount a' (j : I) = _
    rw [← wordCount_sortWord a', h2]

end AlgebraicPolynomialCZero
