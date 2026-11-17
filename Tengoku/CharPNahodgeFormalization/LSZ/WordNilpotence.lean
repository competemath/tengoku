import Tengoku.CharPNahodgeFormalization.LSZ.Objects
import Tengoku.Seed.Data.List.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Consequences of the LSZ word-nilpotence convention

The project uses the strong convention that every word of **exactly**
length `p` in arbitrary tangent-vector contractions is zero.  This file
connects that definition to the mixed monomial identities used by the
truncated exponential.
-/

namespace LSZ

universe u₁ u₂ u₃

/-- `wordApply` is right-folding the corresponding finite list.
@isnad1 id=eq.0h5v.s5.d44b7c45731e from=translated src=- shape=66554e51 vocab=908a4974
-/
lemma wordApply_list {T : Type u₁} {M : Type u₂}
    (act : T → M → M) (l : List T) (m : M) :
    wordApply act l.length (fun i ↦ l.get i) m = l.foldr act m := by
  induction l with
  | nil => rfl
  | cons x l ih =>
      change act x
          (wordApply act l.length (fun i ↦ l.get i) m) =
        act x (l.foldr act m)
      rw [ih]

/-- The defining length-`n` vanishing applies to any list of that length.
@isnad1 id=eq.2h6v.s5.c4c3dd7e53ba from=translated src=- shape=7dd1621e vocab=4af56321
-/
lemma IsWordNilpotent.foldr_eq_zero {T : Type u₁} {M : Type u₂} [Zero M]
    {n : ℕ} {act : T → M → M} (h : IsWordNilpotent n act)
    (l : List T) (hl : l.length = n) (m : M) :
    l.foldr act m = 0 := by
  subst n
  rw [← wordApply_list]
  exact h (fun i ↦ l.get i) m

/-- Folding a constant block is iteration of its operator.
@isnad1 id=eq.0h6v.s5.a4ab9df93540 from=translated src=- shape=079562f0 vocab=9e346199
-/
lemma foldr_replicate {T : Type u₁} {M : Type u₂}
    (act : T → M → M) (t : T) (n : ℕ) (m : M) :
    (List.replicate n t).foldr act m = (act t)^[n] m := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.foldr_cons, ih,
        Function.iterate_succ_apply']

/-- A word consisting of `i` copies of `x` followed by `j` copies of `y`
is zero whenever its total length is exactly the nilpotence level.
@isnad1 id=eq.2h9v.s8.d1ea5ec0e3c7 from=translated src=- shape=34247802 vocab=67360e8c
-/
lemma IsWordNilpotent.twoBlock_exact
    {R : Type u₁} {T : Type u₂} {M : Type u₃}
    [Semiring R] [AddCommMonoid M] [Module R M]
    {n i j : ℕ} (A : T → Module.End R M)
    (h : IsWordNilpotent n (fun t m ↦ A t m))
    (x y : T) (hij : i + j = n) :
    (A x) ^ i * (A y) ^ j = 0 := by
  apply LinearMap.ext
  intro m
  change ((A x) ^ i * (A y) ^ j) m = 0
  have hz := h.foldr_eq_zero
    (List.replicate i x ++ List.replicate j y) (by simp [hij]) m
  rw [List.foldr_append, foldr_replicate, foldr_replicate] at hz
  simpa only [Module.End.mul_apply, Module.End.pow_apply] using hz

/-- The exact length-`n` convention implies vanishing of every two-block
mixed monomial of total degree at least `n`.
@isnad1 id=eq.2h9v.s8.ecb81ff746e3 from=translated src=- shape=6d3d97a7 vocab=ce0264af
-/
lemma IsWordNilpotent.twoBlock_of_le
    {R : Type u₁} {T : Type u₂} {M : Type u₃}
    [Semiring R] [AddCommMonoid M] [Module R M]
    {n : ℕ} (A : T → Module.End R M)
    (h : IsWordNilpotent n (fun t m ↦ A t m))
    (x y : T) (i j : ℕ) (hij : n ≤ i + j) :
    (A x) ^ i * (A y) ^ j = 0 := by
  by_cases hi : n ≤ i
  · have hpow : (A x) ^ n = 0 := by
      simpa using h.twoBlock_exact A x y (i := n) (j := 0) (by simp)
    rw [pow_eq_zero_of_le hi hpow, zero_mul]
  · have hin : i ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hi)
    have hnj : n - i ≤ j := by omega
    have hexact : (A x) ^ i * (A y) ^ (n - i) = 0 := by
      apply h.twoBlock_exact A x y
      omega
    conv_lhs =>
      rhs
      rw [show j = (n - i) + (j - (n - i)) by omega, pow_add]
    rw [← mul_assoc, hexact, zero_mul]

/-- For a linear Higgs-contraction map, word nilpotence supplies the first
mixed inverse hypothesis for `exp_p(a)`.
@isnad1 id=eq.2h8v.s10.0eddb61aa026 from=translated src=- shape=adf863e8 vocab=e1802417
-/
lemma IsWordNilpotent.linear_positive_negative
    {R : Type u₁} {T : Type u₂} {M : Type u₃}
    [CommRing R] [AddCommGroup T] [Module R T]
    [AddCommGroup M] [Module R M]
    {n : ℕ} (A : T →ₗ[R] Module.End R M)
    (h : IsWordNilpotent n (fun t m ↦ A t m))
    (x : T) (i j : ℕ) (hij : n ≤ i + j) :
    (A x) ^ i * (-(A x)) ^ j = 0 := by
  simpa using h.twoBlock_of_le (fun t ↦ A t) x (-x) i j hij

/-- The second mixed inverse hypothesis, with the negative block first.
@isnad1 id=eq.2h8v.s10.8f41ff89658b from=translated src=- shape=6e23b481 vocab=e1802417
-/
lemma IsWordNilpotent.linear_negative_positive
    {R : Type u₁} {T : Type u₂} {M : Type u₃}
    [CommRing R] [AddCommGroup T] [Module R T]
    [AddCommGroup M] [Module R M]
    {n : ℕ} (A : T →ₗ[R] Module.End R M)
    (h : IsWordNilpotent n (fun t m ↦ A t m))
    (x : T) (i j : ℕ) (hij : n ≤ i + j) :
    (-(A x)) ^ i * (A x) ^ j = 0 := by
  simpa using h.twoBlock_of_le (fun t ↦ A t) (-x) x i j hij

/-- Two arbitrary contractions satisfy the joint nilpotence hypothesis in
the truncated exponential addition formula.
@isnad1 id=eq.2h9v.s10.b46796b3aa91 from=translated src=- shape=7299bb84 vocab=ead9f7d0
-/
lemma IsWordNilpotent.linear_joint
    {R : Type u₁} {T : Type u₂} {M : Type u₃}
    [CommRing R] [AddCommGroup T] [Module R T]
    [AddCommGroup M] [Module R M]
    {n : ℕ} (A : T →ₗ[R] Module.End R M)
    (h : IsWordNilpotent n (fun t m ↦ A t m))
    (x y : T) (i j : ℕ) (hij : n ≤ i + j) :
    (A x) ^ i * (A y) ^ j = 0 :=
  h.twoBlock_of_le (fun t ↦ A t) x y i j hij

end LSZ
