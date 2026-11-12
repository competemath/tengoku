/-
# Koszul signs in the endomorphism operad

A **super module** is a module `V` with an involution `ε`, the sign `(-1)^|x|` on homogeneous
elements. A multilinear operation `β` of `V` is homogeneous of parity `q` when
`β (ε x₁, …, ε xₙ) = (-1)^q ε (β (x₁, …, xₙ))` (`End.IsHomog`). Inserting `β` into the slot `i`
of `α` moves it across the inputs before the slot, which costs the Koszul sign: the Koszul
composition `α ∘ᵏᵢ β` applies `ε^q` to the inputs before `i` and composes (`End.kcompFin`).

* **Sequential associativity holds on the nose**, the parities adding
  (`End.kcompFin_assoc_seq`), and **parallel associativity holds up to the Koszul sign**
  `(-1)^(|β| |γ|)` (`End.kcompFin_assoc_par`).
* So the Koszul circle product `α ⋆ β = ∑ᵢ α ∘ᵏᵢ β` (`End.kstar`) satisfies **the graded pre-Lie
  identity** (`End.kstar_assoc_symm`): its associator is graded symmetric in the last two
  arguments; for an odd `β` the two orders of insertion cancel outright
  (`End.kstar_kstar_odd`): `(α ⋆ β) ⋆ β = α ⋆ (β ⋆ β)`, with no division by two.

This is the sign calculus of the Gerstenhaber bracket and of `A∞`-structures in the bar
convention, where every structure map is odd (`Operad.AInfinity`).
-/
import Tengoku.LeanOperads.Operad.PreLie
import Tengoku.LeanOperads.Operad.Associativity
import Tengoku.LeanOperads.Operad.Endomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

universe u v

namespace Operad

open NSOperad Finset

namespace End

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-! ## Evaluating compositions -/

/-- The inputs of `α` in `compFin i α β`, evaluated at `v`.-/
def cfTuple {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V) (s : Fin m) : V :=
  if h : (s : ℕ) < i then v ⟨s, by have := s.isLt; have := i.isLt; omega⟩
  else if h' : (s : ℕ) = i then
    β (fun t => v ⟨i + t, by have := t.isLt; have := i.isLt; omega⟩)
  else v ⟨s + n - 1, by have := s.isLt; have := i.isLt; omega⟩

lemma cfTuple_of_lt {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (s : ℕ) < i) :
    cfTuple i β v s = v ⟨s, by have := s.isLt; have := i.isLt; omega⟩ := by
  rw [cfTuple, dite_eq_left h]

lemma cfTuple_of_eq {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (s : ℕ) = i) :
    cfTuple i β v s = β (fun t => v ⟨i + t, by have := t.isLt; have := i.isLt; omega⟩) := by
  rw [cfTuple, dite_eq_right (by omega), dite_eq_left h]

lemma cfTuple_of_gt {m n : ℕ} (i : Fin m) (β : End R V n) (v : Fin (m - 1 + n) → V)
    (s : Fin m) (h : (i : ℕ) < s) :
    cfTuple i β v s = v ⟨s + n - 1, by have := s.isLt; have := i.isLt; omega⟩ := by
  rw [cfTuple, dite_eq_right (by omega), dite_eq_right (by omega)]

/-- **`compFin` evaluated**: the inputs before the slot, then `β` of the next `n` inputs, then the
rest.-/
lemma compFin_apply {m n : ℕ} (i : Fin m) (α : End R V m) (β : End R V n)
    (v : Fin (m - 1 + n) → V) : compFin (R := R) i α β v = α (cfTuple i β v) := by
  unfold compFin
  rw [reindex_apply, operad_comp_apply, reindex_apply]
  rfl

/-! ## Twists -/

variable (ε : V →ₗ[R] V)

/-- `ε^q` on the inputs before position `i`.-/
def twistFn (q i : ℕ) {n : ℕ} (t : Fin n) : V →ₗ[R] V :=
  if (t : ℕ) < i then ε ^ q else LinearMap.id

/-- **The twist** `α ↦ α ∘ (ε^q ⊗ ⋯ ⊗ ε^q ⊗ 1 ⊗ ⋯ ⊗ 1)`, with `ε^q` on the inputs before `i`.-/
def twist (q i : ℕ) {n : ℕ} : End R V n →ₗ[R] End R V n :=
  MultilinearMap.compLinearMapₗ (twistFn ε q i)

@[simp] lemma twist_apply (q i : ℕ) {n : ℕ} (α : End R V n) (v : Fin n → V) :
    twist ε q i α v = α (fun t => twistFn ε q i t (v t)) := rfl

lemma twistFn_of_lt (q i : ℕ) {n : ℕ} (t : Fin n) (h : (t : ℕ) < i) :
    twistFn ε q i t = ε ^ q := ite_eq_left h

lemma twistFn_of_ge (q i : ℕ) {n : ℕ} (t : Fin n) (h : i ≤ (t : ℕ)) :
    twistFn ε q i t = LinearMap.id := ite_eq_right (by omega)

/-- Twisting the same inputs twice adds the exponents.-/
lemma twist_twist (q r i : ℕ) {n : ℕ} (α : End R V n) :
    twist ε r i (twist ε q i α) = twist ε (q + r) i α := by
  ext v
  simp only [twist_apply]
  congr 1
  funext t
  by_cases h : (t : ℕ) < i
  · simp only [twistFn_of_lt ε _ _ t h, pow_add, Module.End.mul_apply]
  · simp only [twistFn_of_ge ε _ _ t (not_lt.mp h), LinearMap.id_apply]

/-- Twists commute.-/
lemma twist_comm (q r i i' : ℕ) {n : ℕ} (α : End R V n) :
    twist ε r i' (twist ε q i α) = twist ε q i (twist ε r i' α) := by
  ext v
  simp only [twist_apply]
  congr 1
  funext t
  simp only [twistFn]
  split_ifs <;> simp only [← Module.End.mul_apply, ← pow_add, add_comm, ← Module.End.one_eq_id,
    one_mul, mul_one]

lemma reindex_twist {m m' : ℕ} (h : m = m') (q i : ℕ) (α : End R V m) :
    reindex R (End R V) h (twist ε q i α) = twist ε q i (reindex R (End R V) h α) := by
  subst h
  rfl

/-- **Twisting before the slot commutes with composition.**-/
lemma compFin_twist_left (q i' : ℕ) {m n : ℕ} (i : Fin m) (hi : i' ≤ (i : ℕ)) (α : End R V m)
    (β : End R V n) :
    compFin (R := R) i (twist ε q i' α) β = twist ε q i' (compFin (R := R) i α β) := by
  ext v
  rw [compFin_apply, twist_apply, twist_apply, compFin_apply]
  congr 1
  funext s
  have hs := s.isLt
  have hm := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt i β _ s h, cfTuple_of_lt i β _ s h]
    simp only [twistFn]
  · rw [cfTuple_of_eq i β _ s h, cfTuple_of_eq i β _ s h,
      twistFn_of_ge ε _ _ s (by omega), LinearMap.id_apply]
    congr 1
    funext t
    rw [twistFn_of_ge ε _ _ _ (by simp; omega), LinearMap.id_apply]
  · rw [cfTuple_of_gt i β _ s h, cfTuple_of_gt i β _ s h, twistFn_of_ge ε _ _ s (by omega),
      twistFn_of_ge ε _ _ _ (by simp; omega)]

/-- **Twisting across a nested slot**: twisting the first `i + j` inputs of `α ∘ᵢ β` twists the
inputs of `α` before `i` and the first `j` inputs of `β`.-/
lemma twist_compFin_nested (r : ℕ) {m n : ℕ} (i : Fin m) (j : ℕ) (hj : j ≤ n) (α : End R V m)
    (β : End R V n) :
    twist ε r (i + j) (compFin (R := R) i α β)
      = compFin (R := R) i (twist ε r i α) (twist ε r j β) := by
  ext v
  rw [compFin_apply, twist_apply, twist_apply, compFin_apply]
  congr 1
  funext s
  have hs := s.isLt
  have hm := i.isLt
  rcases lt_trichotomy (s : ℕ) i with h | h | h
  · rw [cfTuple_of_lt i β _ s h, cfTuple_of_lt i _ _ s h, twistFn_of_lt ε _ _ s h,
      twistFn_of_lt ε _ _ _ (by simp; omega)]
  · rw [cfTuple_of_eq i β _ s h, cfTuple_of_eq i _ _ s h, twistFn_of_ge ε _ _ s (by omega),
      LinearMap.id_apply, twist_apply]
    congr 1
    funext t
    simp only [twistFn]
    split_ifs <;> first | rfl | omega
  · rw [cfTuple_of_gt i β _ s h, cfTuple_of_gt i _ _ s h, twistFn_of_ge ε _ _ s (by omega),
      twistFn_of_ge ε _ _ _ (by simp; omega)]

variable {ε}

/-! ## Homogeneous operations -/

variable (ε) in
/-- **A homogeneous operation of parity `q`**: `β (ε x₁, …, ε xₙ) = (-1)^q ε (β (x₁, …, xₙ))`.-/
def IsHomog (q : ℕ) {n : ℕ} (β : End R V n) : Prop :=
  ∀ v : Fin n → V, β (fun t => ε (v t)) = (-1 : R) ^ q • ε (β v)

/-! ## Koszul compositions -/

variable (ε) in
/-- **The Koszul composition** of an operation `β` of parity `q` into the slot `i` of `α`: the
inputs before the slot are twisted by `ε^q`.-/
def kcompFin (q : ℕ) {m n : ℕ} (i : Fin m) (α : End R V m) (β : End R V n) :
    End R V (m - 1 + n) :=
  compFin (R := R) i (twist ε q i α) β

/-- **Sequential associativity of Koszul compositions**, with no sign.-/
theorem kcompFin_assoc_seq (q r : ℕ) {m n p : ℕ} (i : Fin m) (j : Fin n) (α : End R V m)
    (β : End R V n) (γ : End R V p) :
    reindex R (End R V) (by have := i.isLt; have := j.isLt; omega)
        (kcompFin ε r
          (⟨(i : ℕ) + (j : ℕ), by have := i.isLt; have := j.isLt; omega⟩ : Fin (m - 1 + n))
          (kcompFin ε q i α β) γ)
      = kcompFin ε (q + r) i α (kcompFin ε r j β γ) := by
  unfold kcompFin
  rw [show twist ε r ((i : ℕ) + (j : ℕ)) (compFin (R := R) i (twist ε q i α) β)
      = compFin (R := R) i (twist ε r i (twist ε q i α)) (twist ε r j β) from
    twist_compFin_nested ε r i j j.isLt.le _ β, compFin_assoc_seq, twist_twist]

/-! ## The Koszul circle product -/

lemma kcompFin_sum_left (q : ℕ) {m n : ℕ} {ι : Type*} (s : Finset ι) (i : Fin m)
    (f : ι → End R V m) (β : End R V n) :
    kcompFin ε q i (∑ x ∈ s, f x) β = ∑ x ∈ s, kcompFin ε q i (f x) β := by
  unfold kcompFin
  rw [map_sum, compFin_sum_left]

lemma kcompFin_sum_right (q : ℕ) {m n : ℕ} {ι : Type*} (s : Finset ι) (i : Fin m)
    (α : End R V m) (g : ι → End R V n) :
    kcompFin ε q i α (∑ x ∈ s, g x) = ∑ x ∈ s, kcompFin ε q i α (g x) :=
  compFin_sum_right _ _ _ _

variable (ε) in
/-- **The Koszul circle product** `α ⋆ β = ∑ᵢ α ∘ᵏᵢ β`, for `β` of parity `q`.-/
def kstar (q : ℕ) {j k : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1)) : End R V (j + k + 1) :=
  ∑ i : Fin (j + 1), kcompFin ε q i α β

lemma kstar_kstar_left (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε r (kstar ε q α β) γ
      = ∑ i' : Fin (j + k + 1), ∑ i : Fin (j + 1), kcompFin ε r i' (kcompFin ε q i α β) γ := by
  unfold kstar
  exact Finset.sum_congr rfl fun i' _ => kcompFin_sum_left _ _ _ _ _

lemma kstar_kstar_right (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε (q + r) α (kstar ε r β γ)
      = ∑ i : Fin (j + 1), ∑ i'' : Fin (k + 1),
          kcompFin ε (q + r) i α (kcompFin ε r i'' β γ) := by
  unfold kstar
  exact Finset.sum_congr rfl fun i _ => kcompFin_sum_right _ _ _ _ _

variable (ε) in
/-- The part of the associator of `⋆` that survives: the pairs of disjoint slots.-/
def kdisjointPart (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ (nested (k := k) i)ᶜ, kcompFin ε r i' (kcompFin ε q i α β) γ

lemma sum_nested_k (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) (i : Fin (j + 1)) :
    reindex R (End R V) (by omega)
        (∑ i' ∈ nested (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ)
      = ∑ i'' : Fin (k + 1), kcompFin ε (q + r) i α (kcompFin ε r i'' β γ) := by
  rw [nested, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun i'' _ => kcompFin_assoc_seq q r i i'' α β γ

/-- **The associator of `⋆`, isolated**: `(α ⋆ β) ⋆ γ` is `α ⋆ (β ⋆ γ)` plus the disjoint
part.-/
lemma kstar_kstar_left_split (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kstar ε r (kstar ε q α β) γ
      = reindex R (End R V) (by omega) (kstar ε (q + r) α (kstar ε r β γ))
        + kdisjointPart ε q r α β γ := by
  have key : ∀ i : Fin (j + 1),
      (∑ i' : Fin (j + k + 1), kcompFin ε r i' (kcompFin ε q i α β) γ)
        = reindex R (End R V) (by omega)
            (∑ i'' : Fin (k + 1), kcompFin ε (q + r) i α (kcompFin ε r i'' β γ))
          + ∑ i' ∈ (nested (k := k) i)ᶜ, kcompFin ε r i' (kcompFin ε q i α β) γ := by
    intro i
    rw [← Finset.sum_add_sum_compl (nested (k := k) i)]
    congr 1
    rw [← sum_nested_k q r α β γ i, reindex_reindex, reindex_self]
  rw [kstar_kstar_left, Finset.sum_comm, kdisjointPart,
    Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib]
  congr 1
  rw [kstar_kstar_right]
  exact (map_sum _ _ _).symm

variable (ε) in
/-- The pairs of disjoint slots with the second insertion before the first.-/
def kbefore (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ before (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ

variable (ε) in
/-- The pairs of disjoint slots with the second insertion after the first.-/
def kafter (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) : End R V (j + k + l + 1) :=
  ∑ i : Fin (j + 1), ∑ i' ∈ after (k := k) i, kcompFin ε r i' (kcompFin ε q i α β) γ

lemma kdisjointPart_eq (q r : ℕ) {j k l : ℕ} (α : End R V (j + 1)) (β : End R V (k + 1))
    (γ : End R V (l + 1)) :
    kdisjointPart ε q r α β γ = kbefore ε q r α β γ + kafter ε q r α β γ := by
  unfold kdisjointPart kbefore kafter
  rw [Finset.sum_congr rfl fun i _ => sum_compl_nested i _, Finset.sum_add_distrib]

variable (hε : ∀ x, ε (ε x) = x)
include hε

end End

end Operad
