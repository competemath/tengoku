import Tengoku.DgLean.DG.Compact.Triangulated
import Tengoku.Seed.CategoryTheory.Functor.OfSequence
import Tengoku.Seed.CategoryTheory.Limits.Shapes.Countable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Homotopy colimits of sequences in a pretriangulated category

Let `C` be a pretriangulated category, `X : ℕ → C` a sequence of objects and
`f n : X n ⟶ X (n + 1)` morphisms, and assume that the coproduct `∐ X` exists. The
*homotopy colimit* of the sequence (M. Bökstedt and A. Neeman, *Homotopy limits in
triangulated categories*, Compositio Math. 86 (1993); see also A. Neeman, *Triangulated
categories*, Ann. Math. Studies 148, §1.6, and [Stacks, Section 13.33]) is the third object of a
distinguished triangle

  `∐ X ⟶ ∐ X ⟶ hocolim X f ⟶ (∐ X)⟦1⟧`,

whose first morphism is `1 - shift`, where `shift : ∐ X ⟶ ∐ X` restricts to
`f n ≫ Sigma.ι X (n + 1)` on the summand `X n` (`DG.hocolimShift`, `DG.hocolimDiff`). The
triangle is chosen with `distinguished_cocone_triangle`, so `DG.hocolim X f` is well defined
up to non-unique isomorphism. It comes with morphisms `DG.hocolimι X f n : X n ⟶ hocolim X f`
compatible with the `f n` (`DG.f_comp_hocolimι`), and it is a weak colimit: every compatible
family of morphisms `X n ⟶ Y` extends (non-uniquely) to `hocolim X f ⟶ Y`
(`DG.hocolim_exists_desc`).

## Main results

For an object `K` which is compact with respect to countable coproducts (`DG.IsCompact.{0} K`,
coproducts indexed by `Type`), the functor `Hom(K, -)` takes the homotopy colimit to the
colimit of abelian groups `colim_n Hom(K, X n)` ([Stacks, Lemma 13.33.9, Tag 094A]); that is,
the canonical map `colim_n Hom(K, X n) ⟶ Hom(K, hocolim X f)` is surjective and injective:

* `DG.hocolim_exists_factor`: every morphism `K ⟶ hocolim X f` factors through `hocolimι X f n`
  for some `n`;
* `DG.hocolim_exists_eq_of_comp_eq`: if `u v : K ⟶ X n` agree after composition with
  `hocolimι X f n`, they agree after composition with the transition map `X n ⟶ X m` for some
  `m ≥ n`.

The proof: by compactness, `Hom(K, ∐ X) = ⨁ₙ Hom(K, X n)`, and on this direct sum `1 - shift`
becomes `(aₙ)ₙ ↦ (aₙ - aₙ₋₁ ≫ fₙ₋₁)ₙ` (`DG.directSumShift`), which is injective with the
colimit as cokernel. The long exact sequence of `Hom(K, -)` for the defining triangle (and for
its shift, using that `⟦1⟧` commutes with coproducts) then gives the two statements.

The transition maps `X n ⟶ X m` are `(Functor.ofSequence f).map (homOfLE h)`.
-/

universe v u

namespace DG

open CategoryTheory Limits Pretriangulated

variable {C : Type u} [Category.{v} C] [Preadditive C]

section Shift

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The morphism `shift : ∐ X ⟶ ∐ X` whose restriction to `X n` is `f n ≫ Sigma.ι X (n + 1)`.-/
noncomputable def hocolimShift : ∐ X ⟶ ∐ X :=
  Sigma.desc fun n => f n ≫ Sigma.ι X (n + 1)

/-- The morphism `1 - shift : ∐ X ⟶ ∐ X` whose cone is the homotopy colimit.-/
noncomputable def hocolimDiff : ∐ X ⟶ ∐ X :=
  𝟙 _ - hocolimShift X f

end Shift

section DirectSum

variable {K : C} {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

/-- The shift on `⨁ n, (K ⟶ X n)`, sending `a ∈ (K ⟶ X n)` to `a ≫ f n ∈ (K ⟶ X (n + 1))`.
Under the comparison with `K ⟶ ∐ X` it corresponds to composition with `hocolimShift X f`.-/
noncomputable def directSumShift :
    (DirectSum ℕ fun n => (K ⟶ X n)) →+ DirectSum ℕ fun n => (K ⟶ X n) :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (fun n => (K ⟶ X n)) (n + 1)).comp (Preadditive.rightComp K (f n))

/--
@isnad1 id=eq.0h6v.s11.f998678b3ed5 from=translated src=- shape=a8ce57cd vocab=73d2f5ef
-/
@[simp]
theorem directSumShift_of (n : ℕ) (a : K ⟶ X n) :
    directSumShift f (DirectSum.of _ n a) = DirectSum.of (fun n => (K ⟶ X n)) (n + 1) (a ≫ f n) :=
  DirectSum.toAddMonoid_of _ _ _

/--
@isnad1 id=eq.0h5v.s10.2f74f87b8876 from=translated src=- shape=3706faac vocab=557aa889
-/
theorem directSumShift_apply_zero (a : DirectSum ℕ fun n => (K ⟶ X n)) :
    directSumShift f a 0 = 0 := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of n x => simp [DirectSum.of_apply]
  | add a b ha hb => simp [ha, hb]

/--
@isnad1 id=eq.0h6v.s10.306c0001b62e from=translated src=- shape=9b836e6a vocab=2405ae9a
-/
theorem directSumShift_apply_succ (a : DirectSum ℕ fun n => (K ⟶ X n)) (n : ℕ) :
    directSumShift f a (n + 1) = a n ≫ f n := by
  induction a using DirectSum.induction_on with
  | zero => simp
  | of m x =>
    rw [directSumShift_of]
    by_cases h : m = n
    · subst h; simp
    · rw [DirectSum.of_eq_of_ne _ _ _ (by omega), DirectSum.of_eq_of_ne _ _ _ (Ne.symm h),
        Limits.zero_comp]
  | add a b ha hb => simp [ha, hb, Preadditive.add_comp]

/-- `1 - shift` is injective on `⨁ n, (K ⟶ X n)`.
@isnad1 id=eq.1h5v.s10.4ce0bde82651 from=translated src=- shape=fbbe1964 vocab=4366328c
-/
theorem directSumShift_eq_self {a : DirectSum ℕ fun n => (K ⟶ X n)}
    (h : directSumShift f a = a) : a = 0 := by
  have key : ∀ n, a n = 0 := by
    intro n
    induction n with
    | zero => rw [← h, directSumShift_apply_zero]
    | succ n ih => rw [← h, directSumShift_apply_succ, ih, Limits.zero_comp]
  ext n
  simp [key n]

/-- If `a - shift a` is concentrated in degree `n` with value `w`, then `a` is concentrated in
degrees `≥ n` and `a m = w ≫ (X n ⟶ X m)` for `m ≥ n`.
@isnad1 id=eq.2h8v.s11.a4013e3c907f from=translated src=- shape=f8596a59 vocab=2f47b347
-/
theorem apply_eq_of_sub_directSumShift_eq {a : DirectSum ℕ fun n => (K ⟶ X n)} {n : ℕ}
    {w : K ⟶ X n} (h : a - directSumShift f a = DirectSum.of _ n w) {m : ℕ} (hnm : n ≤ m) :
    a m = w ≫ (Functor.ofSequence f).map (homOfLE hnm) := by
  have h' : ∀ k, a k = directSumShift f a k + DirectSum.of (fun n => (K ⟶ X n)) n w k := by
    intro k
    rw [← h, DirectSum.sub_apply, add_sub_cancel]
  have below : ∀ k, k < n → a k = 0 := by
    intro k hk
    induction k with
    | zero => rw [h', directSumShift_apply_zero, DirectSum.of_eq_of_ne _ _ _ (by omega), add_zero]
    | succ k ih =>
      rw [h', directSumShift_apply_succ, ih (by omega), Limits.zero_comp, zero_add,
        DirectSum.of_eq_of_ne _ _ _ (by omega)]
  induction m, hnm using Nat.le_induction with
  | base =>
    rw [h', DirectSum.of_eq_same]
    rcases n with _ | n
    · simp [directSumShift_apply_zero]
      exact (Category.comp_id w).symm
    · simp [directSumShift_apply_succ, below n (by omega)]
      exact (Category.comp_id w).symm
  | succ m hnm ih =>
    rw [h', directSumShift_apply_succ, ih, DirectSum.of_eq_of_ne _ _ _ (by omega), add_zero,
      ← homOfLE_comp hnm (Nat.le_succ m), Functor.map_comp, Functor.ofSequence_map_homOfLE_succ]
    exact Category.assoc _ _ _

end DirectSum

section Injective

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X] {K : C}

section ShiftFunctor

variable [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [HasCountableCoproducts C]

end ShiftFunctor

end Injective

variable [HasZeroObject C] [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [Pretriangulated C]

section Defs

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X]

/-- The *homotopy colimit* of the sequence `X 0 ⟶ X 1 ⟶ ⋯`: a chosen cone of
`1 - shift : ∐ X ⟶ ∐ X`.-/
noncomputable def hocolim : C :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose

/-- The morphism `∐ X ⟶ hocolim X f` of the defining triangle.-/
noncomputable def hocolimπ : ∐ X ⟶ hocolim X f :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose

/-- The morphism `hocolim X f ⟶ (∐ X)⟦1⟧` of the defining triangle.-/
noncomputable def hocolimδ : hocolim X f ⟶ (∐ X)⟦(1 : ℤ)⟧ :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose_spec.choose

/-- The defining triangle `∐ X ⟶ ∐ X ⟶ hocolim X f ⟶ (∐ X)⟦1⟧` of the homotopy colimit.-/
noncomputable def hocolimTriangle : Triangle C :=
  Triangle.mk (hocolimDiff X f) (hocolimπ X f) (hocolimδ X f)

/--
@isnad1 id=mem.0h3v.s6.c313960ec729 from=translated src=- shape=c0e75bf2 vocab=39db832d
-/
theorem hocolimTriangle_distinguished : hocolimTriangle X f ∈ distTriang C :=
  (distinguished_cocone_triangle (hocolimDiff X f)).choose_spec.choose_spec.choose_spec

/--
@isnad1 id=eq.0h3v.s7.705f400cc971 from=translated src=- shape=aa40d0c8 vocab=65ddb966
-/
@[reassoc (attr := simp)]
theorem hocolimDiff_hocolimπ : hocolimDiff X f ≫ hocolimπ X f = 0 :=
  comp_distTriang_mor_zero₁₂ _ (hocolimTriangle_distinguished X f)

/-- The canonical morphism `X n ⟶ hocolim X f`.-/
noncomputable def hocolimι (n : ℕ) : X n ⟶ hocolim X f :=
  Sigma.ι X n ≫ hocolimπ X f

end Defs

section Compact

variable (X : ℕ → C) (f : ∀ n, X n ⟶ X (n + 1)) [HasCoproduct X] {K : C}

variable [HasCountableCoproducts C]

end Compact

end DG
