import Tengoku.Seed.Algebra.Group.Int.Defs
import Tengoku.Seed.Algebra.Group.Hom.Defs
import Tengoku.Seed.Algebra.Group.Equiv.Defs
import Tengoku.Seed.Algebra.Group.Pi.Basic
import Tengoku.Seed.Data.Set.Image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract factor-ladder recursion

This file formalizes the coefficientwise-positive recursion used in the
paper, independently of the later Auslander--Reiten construction of its
two additive operators.
-/

namespace QuotientSubmoduleEquidistribution.FactorLadder

universe u v

/-- The free finite-rank integer-vector model used by a factor ladder.
Finiteness of `D` is imposed only when enumerating supports.-/
abbrev IntVector (D : Type u) := D → ℤ

/-- Coefficientwise positive part.-/
def positivePart {D : Type u} (v : IntVector D) : IntVector D :=
  fun d ↦ max (v d) 0

/--
@isnad1 id=eq.0h3v.s4.e1694492409b from=translated src=- shape=f39c23db vocab=77467c82
-/
@[simp]
theorem positivePart_apply {D : Type u}
    (v : IntVector D) (d : D) :
    positivePart v d = max (v d) 0 :=
  rfl

/--
@isnad1 id=le.0h3v.s4.02c1640838eb from=translated src=- shape=2826fe40 vocab=f738aea5
-/
theorem positivePart_nonneg {D : Type u}
    (v : IntVector D) (d : D) :
    0 ≤ positivePart v d :=
  le_max_right _ _

/--
@isnad1 id=iff.0h2v.s4.e10294e3c38d from=translated src=- shape=efb2a32a vocab=f738aea5
-/
theorem positivePart_eq_self_iff {D : Type u}
    (v : IntVector D) :
    positivePart v = v ↔ ∀ d, 0 ≤ v d := by
  constructor
  · intro h d
    rw [← h]
    exact positivePart_nonneg v d
  · intro h
    funext d
    exact max_eq_left (h d)

/-- The basis vector attached to one deleted label.-/
noncomputable def basis {D : Type u} (x : D) : IntVector D :=
  by
    classical
    exact fun d ↦ if d = x then 1 else 0

/--
@isnad1 id=eq.0h2v.s3.7cbd57728aea from=translated src=- shape=878d164f vocab=8b6b6f47
-/
@[simp]
theorem basis_apply_self {D : Type u} (x : D) :
    basis x x = 1 := by
  simp [basis]

/--
@isnad1 id=eq.1h3v.s4.b91769006e1e from=translated src=- shape=cc0d58fe vocab=8b6b6f47
-/
@[simp]
theorem basis_apply_of_ne {D : Type u}
    {x d : D} (h : d ≠ x) :
    basis x d = 0 := by
  simp [basis, h]

/-- The two additive operators entering the factor-ladder recursion.-/
structure Data (D : Type u) where
  theta : IntVector D →+ IntVector D
  tau : IntVector D →+ IntVector D

namespace Data

/-- The factor ladder starting at `x`.-/
noncomputable def ladder {D : Type u}
    (A : Data D) (x : D) : ℕ → IntVector D
  | 0 => basis x
  | 1 => A.theta (basis x)
  | n + 2 =>
      positivePart
        (A.theta (ladder A x (n + 1)) -
          A.tau (ladder A x n))

/--
@isnad1 id=eq.0h3v.s4.f6b8624bbadf from=translated src=- shape=2c0554d8 vocab=08043b61
-/
@[simp]
theorem ladder_zero {D : Type u}
    (A : Data D) (x : D) :
    A.ladder x 0 = basis x :=
  rfl

/--
@isnad1 id=eq.0h3v.s6.8d6041165d4f from=translated src=- shape=325498ad vocab=5fb865dd
-/
@[simp]
theorem ladder_one {D : Type u}
    (A : Data D) (x : D) :
    A.ladder x 1 = A.theta (basis x) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.cbeda2a0c167 from=translated src=- shape=c59c21d3 vocab=c9af27b2
-/
@[simp]
theorem ladder_add_two {D : Type u}
    (A : Data D) (x : D) (n : ℕ) :
    A.ladder x (n + 2) =
      positivePart
        (A.theta (A.ladder x (n + 1)) -
          A.tau (A.ladder x n)) :=
  rfl

/-- Every ladder term from the second recursive step onward is
coefficientwise nonnegative.
@isnad1 id=le.1h5v.s5.22b115129067 from=translated src=- shape=327d9ddb vocab=07b8751e
-/
theorem ladder_nonneg_of_two_le {D : Type u}
    (A : Data D) (x : D) {n : ℕ} (hn : 2 ≤ n) (d : D) :
    0 ≤ A.ladder x n d := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  simp [Nat.add_comm, positivePart]

/-- If both operators vanish on the initial basis vector, then the ladder
dies after its zeroth term.
@isnad1 id=eq.3h4v.s7.c797342e6c40 from=translated src=- shape=723e5194 vocab=b6eaead3
-/
theorem ladder_eq_zero_of_theta_basis_eq_zero_of_tau_basis_eq_zero
    {D : Type u} (A : Data D) (x : D)
    (hθ : A.theta (basis x) = 0)
    (hτ : A.tau (basis x) = 0) :
    ∀ n, 1 ≤ n → A.ladder x n = 0 := by
  have h'all : ∀ n, n = 0 ∨ A.ladder x n = 0 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact Or.inl rfl
    | one => exact Or.inr hθ
    | more n hn hn1 =>
        right
        rw [ladder_add_two]
        have hnext : A.ladder x (n + 1) = 0 := by
          rcases hn1 with hzero | hzero
          · omega
          · exact hzero
        by_cases hnzero : n = 0
        · subst n
          rw [hnext, map_zero, ladder_zero, hτ, sub_self]
          funext d
          simp [positivePart]
        · have hprev : A.ladder x n = 0 := hn.resolve_left hnzero
          rw [hnext, hprev, map_zero, map_zero, sub_self]
          funext d
          simp [positivePart]
  intro n hn
  exact (h'all n).resolve_left (by omega)

/-- Once two consecutive ladder terms vanish, every later term vanishes.
@isnad1 id=eq.3h5v.s6.b381bf6db353 from=translated src=- shape=c432f781 vocab=c28d23d2
-/
theorem ladder_eq_zero_of_consecutive
    {D : Type u} (A : Data D) (x : D) (n : ℕ)
    (hn : A.ladder x n = 0)
    (hn1 : A.ladder x (n + 1) = 0) :
    ∀ m, n ≤ m → A.ladder x m = 0 := by
  intro m hm
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hm
  induction r using Nat.twoStepInduction with
  | zero => simpa using hn
  | one => simpa using hn1
  | more r hr hr1 =>
      rw [show n + (r + 2) = (n + r) + 2 by omega,
        ladder_add_two]
      rw [show n + r + 1 = n + (r + 1) by omega,
        hr1 (by omega), hr (by omega),
        map_zero, map_zero, sub_self]
      funext d
      simp [positivePart]

/-- A boundary label occurs in some term of the ladder.-/
def ReachesBoundary {D : Type u}
    (A : Data D) (P : Set D) (x : D) : Prop :=
  ∃ n p, p ∈ P ∧ 0 < A.ladder x n p

/-- Reindex integer vectors along an equivalence.-/
def reindex (e : D ≃ E) :
    IntVector D ≃+ IntVector E where
  toFun v y := v (e.symm y)
  invFun w x := w (e x)
  left_inv v := by
    funext x
    simp
  right_inv w := by
    funext y
    simp
  map_add' _ _ := rfl

/--
@isnad1 id=eq.0h5v.s6.4992d77e78b5 from=translated src=- shape=357cf20d vocab=fb9169a7
-/
@[simp]
theorem reindex_apply (e : D ≃ E)
    (v : IntVector D) (y : E) :
    reindex e v y = v (e.symm y) :=
  rfl

/--
@isnad1 id=eq.0h5v.s7.8cc0db8e2cf9 from=translated src=- shape=6daac358 vocab=036d3a7f
-/
@[simp]
theorem reindex_symm_apply (e : D ≃ E)
    (w : IntVector E) (x : D) :
    (reindex e).symm w x = w (e x) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.bc992b72e2fa from=translated src=- shape=09fda735 vocab=2ff9f1ef
-/
theorem reindex_positivePart (e : D ≃ E)
    (v : IntVector D) :
    reindex e (positivePart v) =
      positivePart (reindex e v) :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.aaceb5ee86e6 from=translated src=- shape=ef7011a1 vocab=db3f908f
-/
theorem reindex_basis (e : D ≃ E) (x : D) :
    reindex e (basis x) = basis (e x) := by
  classical
  funext y
  simp only [reindex_apply, basis]
  rw [e.symm_apply_eq]

/-- Pull a factor-ladder datum back along an equivalence of its labels.-/
def pullback {D : Type u} {E : Type v}
    (B : Data E) (e : D ≃ E) : Data D where
  theta :=
    { toFun := fun v ↦ (reindex e).symm (B.theta (reindex e v))
      map_zero' := by simp
      map_add' := by simp }
  tau :=
    { toFun := fun v ↦ (reindex e).symm (B.tau (reindex e v))
      map_zero' := by simp
      map_add' := by simp }

/--
@isnad1 id=eq.0h5v.s8.5459307d8d7f from=translated src=- shape=da3e2914 vocab=0daff6dd
-/
@[simp]
theorem pullback_theta {D : Type u} {E : Type v}
    (B : Data E) (e : D ≃ E) (v : IntVector D) :
    (pullback B e).theta v =
      (reindex e).symm (B.theta (reindex e v)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s8.1bfb57e17983 from=translated src=- shape=da3e2914 vocab=269ad11c
-/
@[simp]
theorem pullback_tau {D : Type u} {E : Type v}
    (B : Data E) (e : D ≃ E) (v : IntVector D) :
    (pullback B e).tau v =
      (reindex e).symm (B.tau (reindex e v)) :=
  rfl

/-- An equivalence of labels intertwines the two ladder operators.-/
structure Relabeling {D : Type u} {E : Type v}
    (A : Data D) (B : Data E) (e : D ≃ E) : Prop where
  theta (v : IntVector D) :
    reindex e (A.theta v) = B.theta (reindex e v)
  tau (v : IntVector D) :
    reindex e (A.tau v) = B.tau (reindex e v)

namespace Relabeling

/-- Pullback is tautologically intertwined with the original datum.
@isnad1 id=relabeli.0h4v.s4.531cc4f21328 from=translated src=- shape=abe27f17 vocab=380b8fc9
-/
theorem pullback {D : Type u} {E : Type v}
    (B : Data E) (e : D ≃ E) :
    Relabeling (Data.pullback B e) B e where
  theta v := by simp
  tau v := by simp

/-- Factor ladders are functorial under an intertwining relabeling.
@isnad1 id=eq.1h7v.s7.7e26a201bfed from=translated src=- shape=b9e43e5e vocab=e6f04c02
-/
theorem reindex_ladder
    {D : Type u} {E : Type v}
    {A : Data D} {B : Data E} {e : D ≃ E}
    (h : Relabeling A B e) (x : D) :
    ∀ n, reindex e (A.ladder x n) =
      B.ladder (e x) n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simp [reindex_basis]
  | one =>
      simp [h.theta, reindex_basis]
  | more n hn hn1 =>
      rw [ladder_add_two, ladder_add_two,
        reindex_positivePart]
      apply congrArg positivePart
      rw [map_sub, h.theta, h.tau, hn1, hn]

/-- Reaching a selected boundary is invariant under relabeling.
@isnad1 id=iff.1h7v.s6.15324bfd0188 from=translated src=- shape=76b2995e vocab=67c553e3
-/
theorem reachesBoundary_image_iff
    {D : Type u} {E : Type v}
    {A : Data D} {B : Data E} {e : D ≃ E}
    (h : Relabeling A B e) (P : Set D) (x : D) :
    B.ReachesBoundary (e '' P) (e x) ↔
      A.ReachesBoundary P x := by
  constructor
  · rintro ⟨n, q, ⟨p, hp, rfl⟩, hpos⟩
    refine ⟨n, p, hp, ?_⟩
    have hl : A.ladder x n p =
        B.ladder (e x) n (e p) := by
      simpa using congrFun (h.reindex_ladder x n) (e p)
    simpa [hl] using hpos
  · rintro ⟨n, p, hp, hpos⟩
    refine ⟨n, e p, ⟨p, hp, rfl⟩, ?_⟩
    have hl : A.ladder x n p =
        B.ladder (e x) n (e p) := by
      simpa using congrFun (h.reindex_ladder x n) (e p)
    simpa [← hl] using hpos

end Relabeling

end Data

end QuotientSubmoduleEquidistribution.FactorLadder
