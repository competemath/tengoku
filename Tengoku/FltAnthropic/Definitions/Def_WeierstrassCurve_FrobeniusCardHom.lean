import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Polynomial

namespace FiniteField

/--
@isnad1 id=iff.0h4v.s6.c91d7a09ef04 from=translated src=- shape=7d98cb71 vocab=43b8823c
-/
theorem mem_range_iff_pow_card_eq_self {F k : Type*} [Field F] [Fintype F] [Field k]
    (f : F →+* k) (x : k) : x ∈ Set.range f ↔ x ^ Fintype.card F = x := by
  classical
  constructor
  · rintro ⟨a, rfl⟩
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have h1 : (1 : ℕ) < Fintype.card F := Fintype.one_lt_card
    have hg0 : (X ^ Fintype.card F - X : k[X]) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k h1
    have hdeg : (X ^ Fintype.card F - X : k[X]).natDegree = Fintype.card F :=
      FiniteField.X_pow_card_sub_X_natDegree_eq k h1
    have hSroots : Finset.univ.image f ⊆ (X ^ Fintype.card F - X : k[X]).roots.toFinset := by
      intro a ha
      rw [Finset.mem_image] at ha
      obtain ⟨b, -, rfl⟩ := ha
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [← map_pow, FiniteField.pow_card, sub_self]
    have hScard : (Finset.univ.image f).card = Fintype.card F := by
      rw [Finset.card_image_of_injective _ f.injective, Finset.card_univ]
    have hcardroots : (X ^ Fintype.card F - X : k[X]).roots.toFinset.card ≤ Fintype.card F :=
      le_trans (Multiset.toFinset_card_le _) (le_trans (Polynomial.card_roots' _) hdeg.le)
    have hSeq : Finset.univ.image f = (X ^ Fintype.card F - X : k[X]).roots.toFinset :=
      Finset.eq_of_subset_of_card_le hSroots (hcardroots.trans hScard.symm.le)
    have hxroot : x ∈ (X ^ Fintype.card F - X : k[X]).roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg0]
      simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [hx, sub_self]
    rw [← hSeq, Finset.mem_image] at hxroot
    obtain ⟨a, -, ha⟩ := hxroot
    exact ⟨a, ha⟩

end FiniteField

namespace WeierstrassCurve

open WeierstrassCurve.Affine

section FrobPoint

variable {k : Type*} [Field k] {V : WeierstrassCurve k}

def frobPoint (q : ℕ)
    (hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)) :
    V.toAffine.Point → V.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (x ^ q) (y ^ q) (hfrob h)

variable {q : ℕ}
  {hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)}

/--
@isnad1 id=eq.1h3v.s7.59c6846508d3 from=translated src=- shape=6f74e99b vocab=b658007a
-/
@[simp]
lemma frobPoint_zero : frobPoint q hfrob (0 : V.toAffine.Point) = 0 :=
  rfl

/--
@isnad1 id=eq.2h5v.s7.142cc3f6e0e2 from=translated src=- shape=3c7cc027 vocab=d64ca11f
-/
lemma frobPoint_some {x y : k} (h : V.toAffine.Nonsingular x y) :
    frobPoint q hfrob (.some x y h) = .some (x ^ q) (y ^ q) (hfrob h) :=
  rfl

/--
@isnad1 id=eq.1h3v.s6.dc3f83f2dee0 from=translated src=- shape=fa799a11 vocab=6c83dbf6
-/
lemma frobPoint_zero' :
    frobPoint q hfrob (Affine.Point.zero : V.toAffine.Point) = Affine.Point.zero :=
  rfl

end FrobPoint

section PowHelpers

variable {k : Type*} [Field k] {V : WeierstrassCurve k} {q : ℕ} {φ : k →+* k}

private lemma some_congr {R : Type*} [CommRing R] {V' : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V'.Nonsingular x₁ y₁) (h₂ : V'.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

/--
@isnad1 id=eq.2h5v.s7.b24e85faa5af from=translated src=- shape=f648bd08 vocab=790c5123
-/
lemma pow_injective_of_ringHom (hφ : ∀ a : k, φ a = a ^ q) {a b : k} (hab : a ^ q = b ^ q) :
    a = b :=
  φ.injective (by rw [hφ, hφ]; exact hab)

/--
@isnad1 id=eq.2h6v.s7.69ea4b409b46 from=translated src=- shape=1c67e815 vocab=d19523bc
-/
lemma negY_pow (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V) (x y : k) :
    V.toAffine.negY (x ^ q) (y ^ q) = V.toAffine.negY x y ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_negY (W' := V.toAffine) φ x y
  rw [hfix'] at h
  simpa only [hφ] using h

/--
@isnad1 id=eq.2h8v.s8.2c86d68d1c3c from=translated src=- shape=7d676bb8 vocab=1a841609
-/
lemma slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q)
      = V.toAffine.slope x₁ x₂ y₁ y₂ ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_slope (W := V.toAffine) φ x₁ x₂ y₁ y₂
  rw [hfix'] at h
  simpa only [hφ] using h

/--
@isnad1 id=eq.2h8v.s8.5a6190cb2ad0 from=translated src=- shape=626cf65f vocab=59c423db
-/
lemma addX_slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.addX (x₁ ^ q) (x₂ ^ q) (V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q))
      = V.toAffine.addX x₁ x₂ (V.toAffine.slope x₁ x₂ y₁ y₂) ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_addX (W' := V.toAffine) φ x₁ x₂ (V.toAffine.slope x₁ x₂ y₁ y₂)
  rw [hfix'] at h
  rw [slope_pow hφ hfix x₁ x₂ y₁ y₂]
  simpa only [hφ] using h

/--
@isnad1 id=eq.2h8v.s8.1e415659bb15 from=translated src=- shape=b32e4557 vocab=29188421
-/
lemma addY_slope_pow [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (x₁ x₂ y₁ y₂ : k) :
    V.toAffine.addY (x₁ ^ q) (x₂ ^ q) (y₁ ^ q)
        (V.toAffine.slope (x₁ ^ q) (x₂ ^ q) (y₁ ^ q) (y₂ ^ q))
      = V.toAffine.addY x₁ x₂ y₁ (V.toAffine.slope x₁ x₂ y₁ y₂) ^ q := by
  have hfix' : V.toAffine.map φ = V.toAffine := hfix
  have h := Affine.map_addY (W' := V.toAffine) (f := φ) (x₁ := x₁) (x₂ := x₂) (y₁ := y₁)
    (ℓ := V.toAffine.slope x₁ x₂ y₁ y₂)
  rw [hfix'] at h
  rw [slope_pow hφ hfix x₁ x₂ y₁ y₂]
  simpa only [hφ] using h

variable {hfrob : ∀ {x y : k}, V.toAffine.Nonsingular x y → V.toAffine.Nonsingular (x ^ q) (y ^ q)}

/--
@isnad1 id=eq.3h5v.s8.421ce097c2de from=translated src=- shape=6ebe2b7f vocab=67c2d783
-/
theorem frobPoint_neg (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (P : V.toAffine.Point) :
    frobPoint q hfrob (-P) = -frobPoint q hfrob P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · simp only [Affine.Point.neg_some, frobPoint_some]
    exact some_congr rfl (negY_pow hφ hfix x y).symm _ _

/--
@isnad1 id=eq.3h6v.s8.d28fbce0f672 from=translated src=- shape=aa9f19a6 vocab=f5bb4c97
-/
theorem frobPoint_add [DecidableEq k] (hφ : ∀ a : k, φ a = a ^ q) (hfix : V.map φ = V)
    (P Q : V.toAffine.Point) :
    frobPoint q hfrob (P + Q) = frobPoint q hfrob P + frobPoint q hfrob Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = V.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2, frobPoint_zero, frobPoint_some, frobPoint_some,
      Affine.Point.add_of_Y_eq (by rw [hxy.1]) (by rw [hxy.2, negY_pow hφ hfix])]
  · have hxy' : ¬(x₁ ^ q = x₂ ^ q ∧ y₁ ^ q = V.toAffine.negY (x₂ ^ q) (y₂ ^ q)) := by
      rintro ⟨hx, hy⟩
      rw [negY_pow hφ hfix] at hy
      exact hxy ⟨pow_injective_of_ringHom hφ hx, pow_injective_of_ringHom hφ hy⟩
    rw [Affine.Point.add_some hxy]
    simp only [frobPoint_some]
    rw [Affine.Point.add_some hxy']
    exact some_congr (addX_slope_pow hφ hfix x₁ x₂ y₁ y₂).symm
      (addY_slope_pow hφ hfix x₁ x₂ y₁ y₂).symm _ _

end PowHelpers

section FrobCardHom

variable {F : Type*} [Field F] [Fintype F] {k : Type*} [Field k] (f : F →+* k)
variable {W₀ : WeierstrassCurve F}

/--
@isnad1 id=nonsingu.1h6v.s7.f68d3bac0e7f from=translated src=- shape=0fffc236 vocab=2badf2c9
-/
theorem nonsingular_pow_card_map {x y : k} (h : (W₀.map f).toAffine.Nonsingular x y) :
    (W₀.map f).toAffine.Nonsingular (x ^ Fintype.card F) (y ^ Fintype.card F) := by
  obtain ⟨p, hcharF, n, hp, hcard⟩ := FiniteField.card' (K := F)
  haveI : CharP F p := hcharF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := charP_of_injective_ringHom f.injective p
  haveI : ExpChar k p := ExpChar.prime hp
  have hfix : (W₀.map f).map (iterateFrobenius k p n) = W₀.map f := by
    rw [map_map]
    congr 1
    ext a
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← map_pow, ← hcard, FiniteField.pow_card]
  have hmap : ((W₀.map f).map (iterateFrobenius k p n)).toAffine.Nonsingular
      (iterateFrobenius k p n x) (iterateFrobenius k p n y) :=
    ((W₀.map f).toAffine.map_nonsingular (iterateFrobenius k p n).injective x y).mpr h
  rw [hfix] at hmap
  simpa only [iterateFrobenius_def, hcard] using hmap

/--
@isnad1 id=ex.0h4v.s7.c38afd2c3e46 from=translated src=- shape=185b77c2 vocab=56605520
-/
theorem exists_ringHom_pow_card_fixing :
    ∃ φ : k →+* k, (∀ a : k, φ a = a ^ Fintype.card F) ∧ (W₀.map f).map φ = W₀.map f := by
  obtain ⟨p, hcharF, n, hp, hcard⟩ := FiniteField.card' (K := F)
  haveI : CharP F p := hcharF
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP k p := charP_of_injective_ringHom f.injective p
  haveI : ExpChar k p := ExpChar.prime hp
  refine ⟨iterateFrobenius k p n, fun a => by rw [iterateFrobenius_def, hcard], ?_⟩
  rw [map_map]
  congr 1
  ext a
  simp only [RingHom.comp_apply, iterateFrobenius_def]
  rw [← map_pow, ← hcard, FiniteField.pow_card]

variable [DecidableEq k]

/--
@isnad1 id=eq.0h6v.s8.14337006474a from=translated src=- shape=f7ae5242 vocab=3318fe12
-/
theorem frobPoint_card_add (P Q : (W₀.map f).toAffine.Point) :
    frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) (P + Q)
      = frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) P
        + frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) Q := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  exact frobPoint_add hφ hfix P Q

noncomputable def frobCardHom :
    (W₀.map f).toAffine.Point →+ (W₀.map f).toAffine.Point where
  toFun := frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h)
  map_zero' := rfl
  map_add' := frobPoint_card_add f

/--
@isnad1 id=eq.0h5v.s8.d214f9bb95af from=translated src=- shape=5dddd3ed vocab=3b42a0fd
-/
@[simp]
lemma frobCardHom_apply (P : (W₀.map f).toAffine.Point) :
    frobCardHom f P
      = frobPoint (Fintype.card F) (fun {_ _} h => nonsingular_pow_card_map f h) P :=
  rfl

/--
@isnad1 id=injectiv.0h4v.s8.f4a785a7187b from=translated src=- shape=7a51c5ea vocab=5155136b
-/
theorem frobCardHom_injective :
    Function.Injective (frobCardHom f (W₀ := W₀)) := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  intro P Q hPQ
  simp only [frobCardHom_apply] at hPQ
  cases P with
  | zero =>
    cases Q with
    | zero => rfl
    | some x y h =>
      rw [frobPoint_zero', frobPoint_some] at hPQ
      simp at hPQ
  | some x y h =>
    cases Q with
    | zero =>
      rw [frobPoint_zero', frobPoint_some] at hPQ
      simp at hPQ
    | some x' y' h' =>
      rw [frobPoint_some, frobPoint_some, Affine.Point.some.injEq] at hPQ
      exact some_congr (pow_injective_of_ringHom hφ hPQ.1) (pow_injective_of_ringHom hφ hPQ.2)
        h h'

/--
@isnad1 id=surjecti.0h4v.s8.eb07ed38e376 from=translated src=- shape=7f081127 vocab=674ab8c3
-/
theorem frobCardHom_surjective [IsAlgClosed k] :
    Function.Surjective (frobCardHom f (W₀ := W₀)) := by
  obtain ⟨φ, hφ, hfix⟩ := exists_ringHom_pow_card_fixing f (W₀ := W₀)
  intro P
  cases P with
  | zero => exact ⟨0, map_zero _⟩
  | some x' y' h' =>
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq x' (n := Fintype.card F) Fintype.card_pos
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq y' (n := Fintype.card F) Fintype.card_pos
    have hns : (W₀.map f).toAffine.Nonsingular x y := by
      have hmap : ((W₀.map f).map φ).toAffine.Nonsingular (φ x) (φ y) := by
        rw [hfix, hφ x, hφ y, hx, hy]
        exact h'
      exact ((W₀.map f).toAffine.map_nonsingular φ.injective x y).mp hmap
    refine ⟨.some x y hns, ?_⟩
    rw [frobCardHom_apply, frobPoint_some]
    exact some_congr hx hy _ h'

/--
@isnad1 id=bijectiv.0h4v.s8.cb9ce0c5251c from=translated src=- shape=7f081127 vocab=60dacb64
-/
theorem frobCardHom_bijective [IsAlgClosed k] :
    Function.Bijective (frobCardHom f (W₀ := W₀)) :=
  ⟨frobCardHom_injective f, frobCardHom_surjective f⟩

end FrobCardHom

end WeierstrassCurve
