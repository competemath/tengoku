import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Polynomial

namespace WeierstrassCurve.Affine.Point

universe u

section XCoord

variable {R : Type u} [CommRing R] {W : WeierstrassCurve.Affine R}

def xOrZero : W.Point → R
  | .zero => 0
  | .some x _ _ => x

/--
@isnad1 id=eq.0h2v.s5.d2ce69becba8 from=translated src=- shape=350315ba vocab=c7408c49
-/
@[simp] lemma xOrZero_zero : (0 : W.Point).xOrZero = 0 := rfl

/--
@isnad1 id=eq.1h4v.s5.5d88c4bf5c89 from=translated src=- shape=81bddcde vocab=f0690b17
-/
@[simp] lemma xOrZero_some {x y : R} (h : W.Nonsingular x y) :
    (Point.some x y h).xOrZero = x := rfl

end XCoord

variable {F : Type u} [Field F] {W : WeierstrassCurve.Affine F}

def netW20 : W.Point → F
  | .zero => 0
  | .some x y _ => y - W.negY x y

/--
@isnad1 id=eq.0h2v.s5.9adb41f326e3 from=translated src=- shape=350315ba vocab=e8493184
-/
@[simp] lemma netW20_zero : (0 : W.Point).netW20 = 0 := rfl

/--
@isnad1 id=eq.1h4v.s6.cf1b7a2d40da from=translated src=- shape=9e8187c2 vocab=674f946c
-/
@[simp] lemma netW20_some {x y : F} (h : W.Nonsingular x y) :
    (Point.some x y h).netW20 = y - W.negY x y := rfl

variable [DecidableEq F]

variable (P Q : W.Point)

noncomputable def netW21 : F := P.xOrZero - (P + Q).xOrZero

noncomputable def netW12 : F := Q.xOrZero - (P + Q).xOrZero

noncomputable def netW1m1 : F := Q.xOrZero - P.xOrZero

noncomputable def netW2m1 : F := (Q.xOrZero - P.xOrZero) ^ 2 * ((P - Q).xOrZero - P.xOrZero)

variable {P Q}

noncomputable def netCol (A B : W.Point) : ℕ → F
  | 0 => 1
  | 1 => 1
  | m + 2 =>
      netCol A B (m + 1) ^ 2 * (A.xOrZero - ((m + 1) • A + B).xOrZero) / netCol A B m

/--
@isnad1 id=eq.0h4v.s5.eaf66c8b9712 from=translated src=- shape=0c30c165 vocab=1e0ab4bb
-/
@[simp] lemma netCol_zero : netCol P Q 0 = 1 := rfl
/--
@isnad1 id=eq.0h4v.s5.1f288b5b2501 from=translated src=- shape=0c30c165 vocab=1e0ab4bb
-/
@[simp] lemma netCol_one : netCol P Q 1 = 1 := rfl

noncomputable def netPsi (P : W.Point) (n : ℕ) : F :=
  (W.preΨ (n : ℤ)).eval P.xOrZero * (if Even n then P.netW20 else 1)

noncomputable def netTau (p : ℕ) (P Q : W.Point) : F :=
  netCol P Q (p + 1) / P.netPsi (p + 1)

open scoped Classical in

noncomputable def netPairing (p : ℕ) (P Q : W.Point) : F :=
  if P ≠ 0 ∧ ∀ k : ℤ, Q ≠ k • P then netTau p P Q / netTau p Q P else 1

/--
@isnad1 id=eq.0h4v.s6.e301d1402fee from=translated src=- shape=527b6127 vocab=8bd1542a
-/
@[simp] lemma netPairing_zero_left (p : ℕ) (Q : W.Point) :
    netPairing p (0 : W.Point) Q = 1 := by
  unfold netPairing; rw [ite_eq_right]; simp

/--
@isnad1 id=eq.0h4v.s6.3508fe7278e5 from=translated src=- shape=72bb5189 vocab=8bd1542a
-/
@[simp] lemma netPairing_zero_right (p : ℕ) (P : W.Point) :
    netPairing p P (0 : W.Point) = 1 := by
  unfold netPairing
  by_cases hP : P = 0
  · rw [ite_eq_right]; simp [hP]
  · rw [ite_eq_right]; rintro ⟨_, h⟩; exact h 0 (by rw [zero_zsmul])

variable (W) in

def NetShearLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    netPairing p P (Q + P) = netPairing p P Q

variable (W) in

def NetScaleLaw (p : ℕ) : Prop :=
  ∀ ⦃P Q : W.Point⦄, p • P = 0 → p • Q = 0 → P ≠ 0 → (∀ k : ℤ, Q ≠ k • P) →
    ∀ a : ℕ, netPairing p P (a • Q) = netPairing p P Q ^ a

variable (W) in

def NetPairingNondegenerate (p : ℕ) : Prop :=
  ∃ P Q : W.Point, p • P = 0 ∧ p • Q = 0 ∧ netPairing p P Q ≠ 1

end WeierstrassCurve.Affine.Point
