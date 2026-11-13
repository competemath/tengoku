import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Pi
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Piecewise
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Hermite occupation indices

The degree cutoff is on total occupation. Coordinate raising and lowering
remain concrete functions on finite indices, including at the cutoff.
Supports `gaussian-series-partial-transpose-norm`.
-/

noncomputable section
open Finset
namespace NLAlib

/-- Multiindices of total degree at most `p`. The zero multiindex is included
even when the coordinate type is empty.-/
def HermiteIndex (ι : Type*) [Fintype ι] (p : ℕ) :=
  {a : ι → ℕ // ∑ i, a i ≤ p}

namespace HermiteIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ}

/-- The occupation number at one coordinate is at most the total cutoff.
@isnad1 id=le.0h4v.s5.83324209d625 from=translated src=- shape=fe47d9ac vocab=e7ac3051
-/
theorem coordinate_le (a : HermiteIndex ι p) (i : ι) : a.val i ≤ p :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans a.property

/-- The degree-bounded multiindex space is finite, by embedding it into a
finite coordinate cube.-/
instance instFintype : Fintype (HermiteIndex ι p) :=
  Fintype.ofInjective
    (fun a : HermiteIndex ι p => fun i : ι => (⟨a.val i, Nat.lt_succ_of_le (coordinate_le a i)⟩ : Fin (p + 1)))
    (by
      intro a b h
      apply Subtype.ext
      funext i
      exact congrArg Fin.val (congrFun h i))

/-- Equality of bounded multiindices is decidable.-/
instance instDecidableEq : DecidableEq (HermiteIndex ι p) :=
  inferInstanceAs (DecidableEq {a : ι → ℕ // ∑ i, a i ≤ p})

/-- The total occupation degree.-/
def degree (a : HermiteIndex ι p) : ℕ := ∑ i, a.val i

/-- The vacuum is the zero occupation multiindex.-/
def vacuum : HermiteIndex ι p := ⟨0, by simp⟩

/-- Every coordinate of the vacuum occupation is zero.
@isnad1 id=eq.0h3v.s5.6ed61a09704c from=translated src=- shape=28b59d7a vocab=85b84147
-/
@[simp] theorem vacuum_val (i : ι) : (vacuum : HermiteIndex ι p).val i = 0 := rfl

/-- The vacuum has degree zero.
@isnad1 id=eq.0h2v.s4.b45245c380ee from=translated src=- shape=ab578c89 vocab=58d71452
-/
@[simp] theorem degree_vacuum : (vacuum : HermiteIndex ι p).degree = 0 := by
  simp [degree, vacuum]

/-- Lowering one coordinate never leaves the degree cutoff.-/
def lower (a : HermiteIndex ι p) (i : ι) : HermiteIndex ι p :=
  ⟨Function.update a.val i (a.val i - 1), by
    refine (Finset.sum_le_sum fun j _ => ?_).trans a.property
    by_cases h : j = i
    · subst j; simp
    · simp [Function.update_of_ne h]⟩

/-- Lowering changes only the selected coordinate.
@isnad1 id=eq.0h5v.s6.c9f9e2d0b634 from=translated src=- shape=7a39c3f7 vocab=ffb62f6a
-/
@[simp] theorem lower_val (a : HermiteIndex ι p) (i j : ι) :
    (lower a i).val j = if j = i then a.val i - 1 else a.val j := by
  simp [lower, Function.update_apply]

/-- The lowering degree identity is valid when the coordinate is occupied.
@isnad1 id=eq.1h4v.s6.ae20c1b79079 from=translated src=- shape=fd6ad1d5 vocab=3219a7cc
-/
theorem degree_lower (a : HermiteIndex ι p) (i : ι) (hi : 0 < a.val i) :
    (lower a i).degree + 1 = a.degree := by
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) a.val (a.val i - 1)
  change (∑ j, Function.update a.val i (a.val i - 1) j) + 1 = ∑ j, a.val j
  rw [hsum]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  omega

/-- Raising a coordinate is defined below the total cutoff only.-/
def raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) : HermiteIndex ι p :=
  ⟨Function.update a.val i (a.val i + 1), by
    rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (a.val j)) (Finset.mem_univ i)
    change (∑ j, a.val j) < p at h
    rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)] at h
    omega⟩

/-- Raising changes only the selected coordinate.
@isnad1 id=eq.1h5v.s7.b2a54e0c3236 from=translated src=- shape=e91a40c3 vocab=fc9490b7
-/
@[simp] theorem raise_val (a : HermiteIndex ι p) (i j : ι) (h : a.degree < p) :
    (raise a i h).val j = if j = i then a.val i + 1 else a.val j := by
  simp [raise, Function.update_apply]

/-- Raising increases total degree by exactly one.
@isnad1 id=eq.1h4v.s5.4220143bed1b from=translated src=- shape=cabe8a93 vocab=19cf8569
-/
@[simp] theorem degree_raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) :
    (raise a i h).degree = a.degree + 1 := by
  change (∑ j, Function.update a.val i (a.val i + 1) j) = (∑ j, a.val j) + 1
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ i)]
  have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (a.val j)) (Finset.mem_univ i)
  omega

/-- Lowering reverses a permitted raising step.
@isnad1 id=eq.1h4v.s5.025a25b28585 from=translated src=- shape=dbc90a10 vocab=3e7dce11
-/
@[simp] theorem lower_raise (a : HermiteIndex ι p) (i : ι) (h : a.degree < p) :
    lower (raise a i h) i = a := by
  apply Subtype.ext
  funext j
  by_cases hij : j = i <;> simp [hij]

/-- Raising reverses an occupied lowering step, with its cutoff condition
deduced from the original degree bound.
@isnad1 id=eq.2h4v.s6.a36ef861629d from=translated src=- shape=14a712cc vocab=bcc806b5
-/
theorem raise_lower (a : HermiteIndex ι p) (i : ι) (hi : 0 < a.val i)
    (h : (lower a i).degree < p) : raise (lower a i) i h = a := by
  apply Subtype.ext
  funext j
  by_cases hij : j = i
  · subst j
    simp only [raise_val, lower_val, ite_true]
    omega
  · simp [hij]

/-- Lowering weakly decreases degree, whether or not the coordinate is
occupied.
@isnad1 id=le.0h4v.s5.39a249b5e7bd from=translated src=- shape=9bea8481 vocab=1f13ba3a
-/
theorem degree_lower_le (a : HermiteIndex ι p) (i : ι) : (a.lower i).degree ≤ a.degree := by
  apply Finset.sum_le_sum
  intro j _
  by_cases h : j = i
  · subst j; simp
  · simp [h]

/-- Inclusion into a larger total-degree cutoff.-/
def embed {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) : HermiteIndex ι q :=
  ⟨a.val, a.property.trans h⟩

/-- Cutoff inclusion preserves coordinate values.
@isnad1 id=eq.1h5v.s6.ad7071402d1c from=translated src=- shape=30a1cde3 vocab=7aecff4e
-/
@[simp] theorem embed_val {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) (i : ι) :
    (a.embed h).val i = a.val i := rfl

/-- Cutoff inclusion preserves total degree.
@isnad1 id=eq.1h4v.s5.1549eeaa5208 from=translated src=- shape=84c2d6d9 vocab=71d46675
-/
@[simp] theorem degree_embed {q : ℕ} (a : HermiteIndex ι p) (h : p ≤ q) :
    (a.embed h).degree = a.degree := rfl

/-- Cutoff inclusion is injective.
@isnad1 id=injectiv.1h3v.s5.f3e0ebd583eb from=translated src=- shape=3f92d83c vocab=44e98f15
-/
theorem embed_injective {q : ℕ} (h : p ≤ q) :
    Function.Injective (fun a : HermiteIndex ι p => a.embed h) := by
  intro a b he
  apply Subtype.ext
  exact congrArg (fun c : HermiteIndex ι q => c.val) he

/-- Raising a bounded occupation into the next cutoff is always permitted.-/
def raiseNext (a : HermiteIndex ι p) (i : ι) : HermiteIndex ι (p + 1) :=
  (a.embed (Nat.le_succ p)).raise i (by
    change (∑ i, a.val i) < p + 1
    exact Nat.lt_succ_of_le a.property)

/-- The next-cutoff raising step has the literal coordinate update.
@isnad1 id=eq.0h5v.s7.a52694a4531a from=translated src=- shape=1abb9e30 vocab=5ff747c8
-/
@[simp] theorem raiseNext_val (a : HermiteIndex ι p) (i j : ι) :
    (a.raiseNext i).val j = if j = i then a.val i + 1 else a.val j := by
  simp [raiseNext]

/-- Raising into the next cutoff increases degree by one.
@isnad1 id=eq.0h4v.s5.6837a842c615 from=translated src=- shape=bcc651fd vocab=ceeb1e35
-/
@[simp] theorem degree_raiseNext (a : HermiteIndex ι p) (i : ι) :
    (a.raiseNext i).degree = a.degree + 1 := by
  simp [raiseNext]

/-- Lowering at a distinct coordinate commutes with an interior raising
step, including a zero occupation at the lowered coordinate.
@isnad1 id=eq.3h5v.s6.c0537d621786 from=translated src=- shape=e090c7b8 vocab=3e7dce11
-/
theorem lower_raise_of_ne (a : HermiteIndex ι p) {i j : ι} (hij : i ≠ j)
    (h : a.degree < p) (h' : (a.lower i).degree < p) :
    (a.raise j h).lower i = (a.lower i).raise j h' := by
  apply Subtype.ext
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki, hkj]

end HermiteIndex
end NLAlib
