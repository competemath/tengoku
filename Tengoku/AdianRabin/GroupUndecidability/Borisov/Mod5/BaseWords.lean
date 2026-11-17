import Tengoku.AdianRabin.GroupUndecidability.Borisov.Mod5.Quotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Free-product syllables in the mod-five Borisov quotient

This file computes the base coordinate of a positive displayed rank-five
word in `BorisovModFiveQuotient.QuotientGroup`.  Every rule letter contributes
one nontrivial `d` syllable followed by one nontrivial `e` syllable.  Stable
letters change only the inversion parity and hence never remove a syllable.
-/

namespace Undecidability
namespace BorisovModFiveBaseWords

open Monoid
open BorisovHNNModel
open BorisovCStage
open BorisovModFiveQuotient

noncomputable section

abbrev Basis := BorisovCStage.RuleBasis
abbrev Factor5 (_ : Fin 2) := C5
abbrev BaseLetter := Σ i : Fin 2, Factor5 i

/-- Inversion of the cyclic factor, as an automorphism.-/
def invertC5 : MulAut C5 where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := by simp [mul_comm]

/--
@isnad1 id=eq.0h3v.s11.aab281718494 from=translated src=- shape=abfdc507 vocab=879f64af
-/
@[simp] theorem invertFactors_pow_of (n : ℕ) (i : Fin 2) (x : C5) :
    (invertFactors ^ n) (CoprodI.of (M := Factor5) (i := i) x) =
      CoprodI.of (M := Factor5) (i := i) ((invertC5 ^ n) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      change (invertFactors ^ n)
          (invertFactors (CoprodI.of (M := Factor5) (i := i) x)) =
        CoprodI.of (M := Factor5) (i := i) ((invertC5 ^ n) (invertC5 x))
      rw [show invertFactors (CoprodI.of (M := Factor5) (i := i) x) =
        CoprodI.of (M := Factor5) (i := i) x⁻¹ by simp [invertFactors]]
      rw [ih (x⁻¹)]
      rfl

/-- Apply the parity accumulated in `n` stable letters to one base syllable.-/
def twistLetter (n : ℕ) : BaseLetter → BaseLetter
  | ⟨i, x⟩ => ⟨i, (invertC5 ^ n) x⟩

/--
@isnad1 id=eq.0h2v.s5.633ad50eb455 from=translated src=- shape=6b0ba5cd vocab=c002621e
-/
@[simp] theorem twistLetter_fst (n : ℕ) (x : BaseLetter) :
    (twistLetter n x).1 = x.1 := by cases x; rfl

/--
@isnad1 id=ne.1h2v.s7.03f90f61b567 from=translated src=- shape=94db4ca7 vocab=8f3ed562
-/
theorem twistLetter_ne_one (n : ℕ) (x : BaseLetter) (hx : x.2 ≠ 1) :
    (twistLetter n x).2 ≠ 1 := by
  rcases x with ⟨i, x⟩
  change (invertC5 ^ n) x ≠ 1
  intro h
  apply hx
  apply (invertC5 ^ n).injective
  simpa using h

/-- Product of a list of free-product letters.-/
def letterProd (letters : List BaseLetter) : ModFiveBase :=
  (letters.map fun x => CoprodI.of (M := Factor5) (i := x.1) x.2).prod

/--
@isnad1 id=eq.0h2v.s10.21f62fec37c7 from=translated src=- shape=97e58296 vocab=b8a7b0a7
-/
@[simp] theorem letterProd_cons (x : BaseLetter) (xs : List BaseLetter) :
    letterProd (x :: xs) =
      CoprodI.of (M := Factor5) (i := x.1) x.2 * letterProd xs := by
  simp [letterProd]

/--
@isnad1 id=eq.0h2v.s6.6b571fce69c6 from=translated src=- shape=31b9e54f vocab=b539b116
-/
@[simp] theorem letterProd_append (xs ys : List BaseLetter) :
    letterProd (xs ++ ys) = letterProd xs * letterProd ys := by
  simp [letterProd, List.map_append]

/--
@isnad1 id=eq.0h2v.s10.50efc1c6bbec from=translated src=- shape=2d64a2d4 vocab=f3fa3324
-/
@[simp] theorem invertFactors_pow_letterProd (n : ℕ)
    (letters : List BaseLetter) :
    (invertFactors ^ n) (letterProd letters) =
      letterProd (letters.map (twistLetter n)) := by
  induction letters with
  | nil => simp [letterProd]
  | cons x xs ih =>
      rcases x with ⟨i, x⟩
      rw [letterProd_cons, map_mul, invertFactors_pow_of, ih]
      simp [letterProd]
      rfl

/-- Stable-letter weight of a displayed basis letter in the source or target
system determined by `rules`.-/
def stableWeight (rules : Fin 3 → List (Fin 2)) : Basis → ℕ
  | .inl _ => 1
  | .inr i => (rules i).length

/-- Number of rule letters in a positive displayed word.-/
def basisRuleCount : List Basis → ℕ
  | [] => 0
  | .inl _ :: rest => basisRuleCount rest
  | .inr _ :: rest => basisRuleCount rest + 1

/-- The two alternating base syllables contributed by one rule letter.-/
def rulePair (rules : Fin 3 → List (Fin 2)) (i : Fin 3) :
    List BaseLetter :=
  [⟨0, c5Generator ^ (i.val + 1)⟩,
    ⟨1, (invertC5 ^ (rules i).length) (c5Generator ^ (i.val + 1))⟩]

/-- Reduced base-syllable trace of the evaluation of a positive displayed
word.  The tail is twisted by the stable weight of its head.-/
def baseLetters (rules : Fin 3 → List (Fin 2)) : List Basis → List BaseLetter
  | [] => []
  | .inl _ :: rest =>
      (baseLetters rules rest).map (twistLetter 1)
  | .inr i :: rest =>
      rulePair rules i ++
        (baseLetters rules rest).map (twistLetter (rules i).length)

/--
@isnad1 id=eq.0h2v.s5.2da5866169fe from=translated src=- shape=12bd7451 vocab=c11fa98d
-/
@[simp] theorem baseLetters_length (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) :
    (baseLetters rules letters).length = 2 * basisRuleCount letters := by
  induction letters with
  | nil => rfl
  | cons q rest ih =>
      cases q with
      | inl beta => simp [baseLetters, basisRuleCount, ih]
      | inr i => simp [baseLetters, basisRuleCount, rulePair, ih, Nat.mul_add]

/-- Image in the quotient of one positive displayed basis letter.-/
def quotientBasis (rules : Fin 3 → List (Fin 2)) : Basis → QuotientGroup
  | .inl _ => quotientStable
  | .inr i =>
      quotientBase (modD ^ (i.val + 1)) *
        quotientStable ^ (rules i).length *
        quotientBase (modE ^ (i.val + 1))

def quotientEval (rules : Fin 3 → List (Fin 2))
    (letters : List Basis) : QuotientGroup :=
  (letters.map (quotientBasis rules)).prod

/--
@isnad1 id=eq.0h1v.s7.753950b4d84a from=translated src=- shape=c721731a vocab=6f3f909d
-/
@[simp] theorem quotientStable_pow_left (n : ℕ) :
    (quotientStable ^ n).left = 1 := by
  let g : Multiplicative ℤ := Multiplicative.ofAdd 1
  have hp : (SemidirectProduct.inr g : QuotientGroup) ^ n =
      SemidirectProduct.inr (g ^ n) :=
    (map_pow (SemidirectProduct.inr : Multiplicative ℤ →* QuotientGroup) g n).symm
  change ((SemidirectProduct.inr g : QuotientGroup) ^ n).left = 1
  rw [hp]
  rfl

/--
@isnad1 id=eq.0h1v.s7.8c32538e8fca from=translated src=- shape=ecdb181a vocab=f40417ec
-/
@[simp] theorem quotientStable_pow_right (n : ℕ) :
    (quotientStable ^ n).right = Multiplicative.ofAdd (n : ℤ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, SemidirectProduct.mul_right, ih]
      apply Multiplicative.toAdd.injective
      simp [quotientStable]

/--
@isnad1 id=eq.0h1v.s8.6507b2576365 from=translated src=- shape=27fc582a vocab=e9750f3e
-/
@[simp] theorem quotientBase_left (x : ModFiveBase) :
    (quotientBase x).left = x := rfl

/--
@isnad1 id=eq.0h1v.s8.865d4cacfe3f from=translated src=- shape=b11ccfac vocab=26063bea
-/
@[simp] theorem quotientBase_right (x : ModFiveBase) :
    (quotientBase x).right = 1 := rfl

/--
@isnad1 id=eq.0h2v.s8.a2edc44258e4 from=translated src=- shape=0e231d13 vocab=7c5dff3d
-/
@[simp] theorem quotientBase_pow_right (x : ModFiveBase) (n : ℕ) :
    (quotientBase x ^ n).right = 1 := by
  have hp : (SemidirectProduct.inl x : QuotientGroup) ^ n =
      SemidirectProduct.inl (x ^ n) :=
    (map_pow (SemidirectProduct.inl : ModFiveBase →* QuotientGroup) x n).symm
  change ((SemidirectProduct.inl x : QuotientGroup) ^ n).right = _
  rw [hp]
  rfl

/--
@isnad1 id=eq.0h1v.s10.03c7225eacb6 from=translated src=- shape=204fdc4d vocab=a14b5191
-/
@[simp] theorem inversionAction_nat (n : ℕ) :
    inversionAction (Multiplicative.ofAdd (n : ℤ)) = invertFactors ^ n := by
  simp [inversionAction]

/--
@isnad1 id=eq.0h1v.s11.3569a1cc3530 from=translated src=- shape=4704e5bb vocab=9eb2651e
-/
@[simp] theorem invertFactors_pow_modE (n : ℕ) :
    (invertFactors ^ n) modE =
      CoprodI.of (M := Factor5) (i := (1 : Fin 2))
        ((invertC5 ^ n) c5Generator) := by
  simp [modE]

/--
@isnad1 id=eq.0h2v.s6.ad0e8f51b90d from=translated src=- shape=0c819ad1 vocab=b77b421e
-/
@[simp] theorem quotientBasis_right
    (rules : Fin 3 → List (Fin 2)) (q : Basis) :
    (quotientBasis rules q).right =
      Multiplicative.ofAdd (stableWeight rules q : ℤ) := by
  cases q with
  | inl beta => simp [quotientBasis, stableWeight, quotientStable]
  | inr i =>
      simp only [quotientBasis, SemidirectProduct.mul_right,
        quotientBase_right, quotientStable_pow_right,
        one_mul, mul_one, stableWeight]

/--
@isnad1 id=eq.0h2v.s7.f50320a06dcc from=translated src=- shape=54a646a4 vocab=0742ae60
-/
@[simp] theorem quotientBasis_left_stable
    (rules : Fin 3 → List (Fin 2)) (beta : Fin 2) :
    (quotientBasis rules (.inl beta)).left = 1 := by
  simp [quotientBasis, quotientStable]

/--
@isnad1 id=eq.0h2v.s6.fa3f3bc91b6c from=translated src=- shape=8502cc15 vocab=0f544df1
-/
@[simp] theorem quotientBasis_left_rule
    (rules : Fin 3 → List (Fin 2)) (i : Fin 3) :
    (quotientBasis rules (.inr i)).left = letterProd (rulePair rules i) := by
  simp only [quotientBasis, SemidirectProduct.mul_left,
    quotientBase_left, quotientBase_right,
    quotientStable_pow_left]
  simp [rulePair, letterProd, invertFactors_pow_modE, modD, map_pow]

/-- Exact base-coordinate evaluation formula.
@isnad1 id=eq.0h2v.s6.29366119114a from=translated src=- shape=8152ef7e vocab=c793351f
-/
@[simp] theorem quotientEval_left
    (rules : Fin 3 → List (Fin 2)) (letters : List Basis) :
    (quotientEval rules letters).left = letterProd (baseLetters rules letters) := by
  induction letters with
  | nil => rfl
  | cons q rest ih =>
      cases q with
      | inl beta =>
          change (quotientBasis rules (.inl beta) *
            quotientEval rules rest).left = _
          rw [SemidirectProduct.mul_left, quotientBasis_left_stable,
            quotientBasis_right, ih, one_mul]
          simp only [stableWeight, baseLetters]
          simpa using (invertFactors_pow_letterProd 1 (baseLetters rules rest))
      | inr i =>
          change (quotientBasis rules (.inr i) *
            quotientEval rules rest).left = _
          rw [SemidirectProduct.mul_left, quotientBasis_left_rule,
            quotientBasis_right, ih]
          simp only [stableWeight, inversionAction_nat,
            baseLetters, letterProd_append]
          rw [invertFactors_pow_letterProd]

end

end BorisovModFiveBaseWords
end Undecidability
