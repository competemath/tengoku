import Tengoku.Seed.GroupTheory.PGroup
import Tengoku.Brauerinduction.BrauerInduction.Background.Group.Conjugacy

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# `p`-regular and `p`-singular elements

This file introduces `p`-regular and `p`-singular elements in a group `G`,
and formalizes the `p`-decomposition for elements of finite order.

An element is `p`-regular if its order is coprime to `p`, and `p`-singular if
its order is a power of `p`.

Every element `x` of finite order can be uniquely decomposed as

`x = s * r = r * s`,

where `s` is `p`-singular and `r` is `p`-regular.

## Main definitions

* `IsPRegular p a`: A predicate stating that the order of `a` is coprime to `p`.
* `IsPSingular p a`: A predicate stating that the order of `a` is a power of `p`.
* `Group.pRegular p a`: The canonical `p`-regular factor of `a`.
* `Group.pSingular p a`: The canonical `p`-singular factor of `a`.

## Main results

* `Group.pDecomp`: the decomposition theorem `pSingular p a * pRegular p a = a`.
* `Group.pDecomp'`: the reversed version `pRegular p a * pSingular p a = a`.
* `Group.pDecomp_commute`: the `p`-singular and `p`-regular factors commute.
* `Group.pSingular_pRegular_unique`: uniqueness of the `p`-decomposition.
* `Group.pDecomp_mul_of_commute`: the `p`-decomposition of a commuting product.

-/
namespace Tengoku.Brauerinduction end Tengoku.Brauerinduction open Tengoku.Brauerinduction
universe u

variable {G : Type u} [Group G]
variable (p : ℕ)

/--
@isnad1 id=other.1h2v.s6.a6696aee12c5 from=translated src=- shape=83ea4fcf vocab=8e4084ed
-/
lemma Nat.ordProj_ordCompl_coprime {n : ℕ} [Fact p.Prime] (h : n ≠ 0) :
    let a := ordProj[p] n
    let b := ordCompl[p] n
    Nat.Coprime a b := by
  have hcop : Nat.Coprime p (ordCompl[p] n) :=
     Nat.coprime_ordCompl (Fact.out : Nat.Prime p) h
  exact Nat.gcd_pow_left_of_gcd_eq_one hcop

/-- An element of a group is `p`-regular if its order is coprime to `p`.-/
def _root_.Tengoku.Brauerinduction.IsPRegular (a : G) : Prop := Nat.Coprime (orderOf a) p

namespace Tengoku.Brauerinduction.IsPRegular

/--
@isnad1 id=ispregul.0h2v.s4.677cf533ba84 from=translated src=- shape=182f3df2 vocab=9657be24
-/
@[simp]
lemma one : IsPRegular p (1 : G) := by simp [IsPRegular]

/--
@isnad1 id=coprime.1h3v.s4.edcbafd403b2 from=translated src=- shape=a74bc715 vocab=3dd5c895
-/
lemma order_coprime {a : G} (h : IsPRegular p a) :
    Nat.Coprime (orderOf a) p := h

/-- An element is `p`-regular iff its inverse is `p`-regular.
@isnad1 id=iff.0h3v.s4.165ee7f850b5 from=translated src=- shape=672253ef vocab=50ffcaba
-/
lemma inv_iff (a : G) : IsPRegular p a⁻¹ ↔ IsPRegular p a := by
    simp only [IsPRegular, orderOf_inv]

/--
The product of commuting `p`-regular elements is `p`-regular.
@isnad1 id=ispregul.3h4v.s5.e80b20966579 from=translated src=- shape=3e8adeb0 vocab=92f9eb4c
-/
lemma mul {a b : G} (ha : IsPRegular p a) (hb : IsPRegular p b)
    (hcomm : Commute a b) : IsPRegular p (a * b) := by
  have h_dvd : orderOf (a * b) ∣ orderOf a * orderOf b :=
    Commute.orderOf_mul_dvd_mul_orderOf hcomm
  exact Nat.Coprime.coprime_dvd_left h_dvd (Nat.Coprime.mul_left ha hb)

/--
The image of a `p`-regular element under a group homomorphism is `p`-regular.
@isnad1 id=ispregul.1h5v.s6.e34f03fdd0d3 from=translated src=- shape=3380ef29 vocab=d55b6cb1
-/
lemma map {H : Type v} [Group H] (f : G →* H) {a : G}
    (h : IsPRegular p a) : IsPRegular p (f a) := by
  have h_dvd : orderOf (f a) ∣ orderOf a := orderOf_map_dvd f a
  exact Nat.Coprime.coprime_dvd_left h_dvd h

/--
@isnad1 id=ispregul.2h4v.s5.97cf1956da88 from=translated src=- shape=6c8abe68 vocab=035c9ab3
-/
lemma isConj {a b : G} (ha : IsPRegular p a) (h : IsConj a b) :
    IsPRegular p b := by
  simpa only [IsPRegular, IsConj.orderOf_eq h] using ha

/--
@isnad1 id=ispregul.1h4v.s6.f1c217fc5a2a from=translated src=- shape=c4efadc8 vocab=16bdeb18
-/
lemma conj {a : G} (h : IsPRegular p a) (b : G) :
    IsPRegular p (b * a * b⁻¹) :=
      IsPRegular.isConj p h (isConj_iff.mpr ⟨b, rfl⟩)

/--
@isnad1 id=ispregul.1h4v.s6.23d122d77669 from=translated src=- shape=b0d671e7 vocab=16bdeb18
-/
lemma conj' {a : G} (h : IsPRegular p a) (b : G) :
    IsPRegular p (b⁻¹ * a * b) :=
      IsPRegular.isConj p h (isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩)

/-- p-regularity is invariant under conjugacy.
@isnad1 id=iff.1h4v.s5.90bc909908e5 from=translated src=- shape=ae8266b1 vocab=035c9ab3
-/
lemma iff_isConj {a b : G} (h : IsConj a b) :
    IsPRegular p a ↔ IsPRegular p b :=
  ⟨fun ha ↦ isConj p ha h, fun hb ↦ isConj p hb h.symm⟩

/--
@isnad1 id=not.1h3v.s5.6b2248be7aed from=translated src=- shape=fe6319a6 vocab=288cc45f
-/
lemma not_dvd_orderOf [Fact p.Prime] {a : G} (h : IsPRegular p a) :
    ¬ p ∣ orderOf a := (Nat.Prime.coprime_iff_not_dvd Fact.out).mp h.symm

/--
A `p`-regular element has finite order, provided `p` is prime.
@isnad1 id=isoffino.1h3v.s4.f7bc62722ef1 from=translated src=- shape=5d1e4b94 vocab=73f77297
-/
lemma isOfFinOrder [Fact p.Prime] {a : G}
    (h : IsPRegular p a) :
    IsOfFinOrder a := by
  rw [← orderOf_ne_zero_iff]
  intro hzero
  have hp_dvd : p ∣ orderOf a := by
    rw [hzero]
    exact dvd_zero p
  exact h.not_dvd_orderOf p hp_dvd

/-- A `p`-regular element has nonzero order.
@isnad1 id=nezero.1h3v.s5.93da74863044 from=translated src=- shape=1d5b6093 vocab=a9fbd099
-/
lemma neZero_orderOf
    [Fact p.Prime] {a : G} (ha : IsPRegular p a) :
    NeZero (orderOf a) :=
  ⟨(orderOf_ne_zero_iff).2 (IsPRegular.isOfFinOrder p ha)⟩

/--
@isnad1 id=dvd.2h4v.s6.6fe72ea9050c from=translated src=- shape=1a4ad4a9 vocab=5365d5ec
-/
lemma orderOf_dvd_ordCompl [Fact p.Prime] {a : G} (h : IsPRegular p a) {n : ℕ}
    (hd : orderOf a ∣ n) : orderOf a ∣ ordCompl[p] n :=
  Nat.dvd_ordCompl_of_dvd_not_dvd hd h.not_dvd_orderOf

/--
@isnad1 id=ispregul.2h4v.s5.7d4c918453a3 from=translated src=- shape=985dd3cf vocab=33f70fb4
-/
lemma of_mem_zpowers {a b : G} (ha : a ∈ Subgroup.zpowers b) (hb : IsPRegular p b) :
    IsPRegular p a := by
  have h_dvd : orderOf a ∣ orderOf b := orderOf_dvd_of_mem_zpowers ha
  exact Nat.Coprime.coprime_dvd_left h_dvd hb

/--
A power of a `p`-regular element is `p`-regular.
@isnad1 id=ispregul.1h4v.s5.75e6d96031a0 from=translated src=- shape=6d5538b3 vocab=1e33e04c
-/
lemma pow (a : G) (h : IsPRegular p a) (n : ℕ) :
    IsPRegular p (a ^ n) :=
  h.coprime_dvd_left (orderOf_pow_dvd n)

/--
@isnad1 id=ispregul.1h3v.s6.ae74d6748133 from=translated src=- shape=42d9aed2 vocab=a88c355c
-/
lemma pow_ordProj [Fact p.Prime] {a : G} (ha : IsOfFinOrder a) :
    IsPRegular p (a ^ ordProj[p] (orderOf a)) := by
  let n : ℕ := orderOf a
  have hn0 : n ≠ 0 := orderOf_ne_zero_iff.mpr ha
  -- ordCompl[p] n is coprime to p
  have hcop : Nat.Coprime (ordCompl[p] n) p := by
    simpa [Nat.coprime_comm, n] using Nat.coprime_ordCompl Fact.out hn0
  have hpow1 :
      (a ^ ordProj[p] n) ^ ordCompl[p] n = 1 := by
    calc
      (a ^ ordProj[p] n) ^ ordCompl[p] n
          = a ^ (ordProj[p] n * ordCompl[p] n) := by
              rw [pow_mul]
      _ = a ^ n := by
              rw [Nat.ordProj_mul_ordCompl_eq_self]
      _ = 1 := by
              simp only [pow_orderOf_eq_one a, n]
  have hdvd : orderOf (a ^ ordProj[p] n) ∣ ordCompl[p] n :=
    orderOf_dvd_of_pow_eq_one hpow1
  exact hcop.of_dvd_left hdvd

/--
@isnad1 id=iff.0h4v.s6.1364777fd28a from=translated src=- shape=0eaf49a6 vocab=80bf6f17
-/
@[simp]
lemma subtype_iff
    {H : Subgroup G} (x : H) :
    IsPRegular p ((x : H) : G) ↔ IsPRegular p x := by
  simp only [IsPRegular, orderOf_submonoid]

end Tengoku.Brauerinduction.IsPRegular

/-- An element of a group is `p`-singular if its order is a power of `p`.-/
def _root_.Tengoku.Brauerinduction.IsPSingular (a : G) : Prop := ∃ n, orderOf a = p ^ n

namespace Tengoku.Brauerinduction.IsPSingular

/--
@isnad1 id=ispsingu.0h2v.s4.1a76a77801fe from=translated src=- shape=182f3df2 vocab=9362e082
-/
@[simp]
lemma one : IsPSingular p (1 : G) := ⟨0, by simp⟩

/-- An element is `p`-singular iff its inverse is `p`-singular.
@isnad1 id=iff.0h3v.s4.9ab35bb3b940 from=translated src=- shape=672253ef vocab=0ba57570
-/
lemma inv_iff (a : G) : IsPSingular p a⁻¹ ↔ IsPSingular p a := by
    simp only [IsPSingular, orderOf_inv]

/--
The product of commuting `p`-singular elements is `p`-singular.
@isnad1 id=ispsingu.3h4v.s6.05aa95fdfdbc from=translated src=- shape=9e7f83ef vocab=c0857eed
-/
lemma mul [Fact p.Prime] {a b : G} (ha : IsPSingular p a)
    (hb : IsPSingular p b) (hcomm : Commute a b) : IsPSingular p (a * b) := by
  rcases ha with ⟨n, ha⟩
  rcases hb with ⟨m, hb⟩
  have h_dvd : orderOf (a * b) ∣ orderOf a * orderOf b :=
    Commute.orderOf_mul_dvd_mul_orderOf hcomm
  rw [ha, hb, ← pow_add] at h_dvd
  obtain ⟨k, -, heq⟩ := (Nat.dvd_prime_pow Fact.out).mp h_dvd
  exact ⟨k, heq⟩

/--
@isnad1 id=ispsingu.1h5v.s6.779010472062 from=translated src=- shape=bb8bfab2 vocab=faec7439
-/
lemma map [Fact p.Prime] {H : Type v} [Group H] (f : G →* H) {a : G}
    (ha : IsPSingular p a) : IsPSingular p (f a) := by
  rcases ha with ⟨n, hn⟩
  have h_dvd : orderOf (f a) ∣ orderOf a := orderOf_map_dvd f a
  rw [hn] at h_dvd
  obtain ⟨k, -, heq⟩ := (Nat.dvd_prime_pow Fact.out).mp h_dvd
  exact ⟨k, heq⟩

/--
@isnad1 id=ispsingu.2h4v.s5.3c069d58b812 from=translated src=- shape=6c8abe68 vocab=d3986d1f
-/
lemma isConj {a b : G} (ha : IsPSingular p a) (h : IsConj a b) :
    IsPSingular p b := by
  obtain ⟨n,hn⟩ := ha
  use n
  rw [← hn]
  exact IsConj.orderOf_eq (IsConj.symm h)

/--
@isnad1 id=ispsingu.1h4v.s6.796c354e663b from=translated src=- shape=c4efadc8 vocab=0c04f4d5
-/
lemma conj {a : G} (h : IsPSingular p a) (b : G) :
    IsPSingular p (b * a * b⁻¹) :=
      IsPSingular.isConj p h (isConj_iff.mpr ⟨b, rfl⟩)

/--
@isnad1 id=ispsingu.1h4v.s6.be634027d2ed from=translated src=- shape=b0d671e7 vocab=0c04f4d5
-/
lemma conj' {a : G} (h : IsPSingular p a) (b : G) :
    IsPSingular p (b⁻¹ * a * b) :=
      IsPSingular.isConj p h (isConj_iff.mpr ⟨b⁻¹, by rw [inv_inv]⟩)

/--
A `p`-singular element has finite order, provided `p` is prime.
@isnad1 id=isoffino.1h3v.s4.4e9f349f1070 from=translated src=- shape=5d1e4b94 vocab=10e14cfe
-/
lemma isOfFinOrder [Fact p.Prime] {a : G}
    (h : IsPSingular p a) :
    IsOfFinOrder a := by
  rcases h with ⟨n, hn⟩
  rw [← orderOf_ne_zero_iff]
  rw [hn]
  exact pow_ne_zero n (Nat.Prime.ne_zero Fact.out)

/-- A `p`-regular element has nonzero order.
@isnad1 id=nezero.1h3v.s5.8e1d1c4199d3 from=translated src=- shape=1d5b6093 vocab=60fee946
-/
lemma neZero_orderOf
    [Fact p.Prime] {a : G} (h : IsPSingular p a) :
    NeZero (orderOf a) :=
  ⟨(orderOf_ne_zero_iff).2 (IsPSingular.isOfFinOrder p h)⟩

/--
@isnad1 id=dvd.3h4v.s6.9dd5a14aed5d from=translated src=- shape=8b1d51a9 vocab=8a35e090
-/
lemma orderOf_dvd_ordProj [Fact p.Prime] {a : G} (h : IsPSingular p a) {n : ℕ}
    (hd : orderOf a ∣ n) (hn : n ≠ 0) :
    orderOf a ∣ ordProj[p] n := by
  rcases h with ⟨a, ha⟩
  rw [ha] at hd ⊢
  exact (Nat.Prime.pow_dvd_iff_dvd_ordProj (Fact.out : Nat.Prime p) hn).mp hd

/--
An element is `p`-singular iff the cyclic subgroup it generates is a
`p`-group.
@isnad1 id=iff.0h3v.s5.91657c2a2e0b from=translated src=- shape=ae5da24c vocab=3353a37e
-/
lemma iff_zpowers_isPGroup [Fact p.Prime] (a : G) :
    IsPSingular p a ↔ IsPGroup p (Subgroup.zpowers a) := by
  unfold IsPSingular
  rw [IsPGroup.iff_orderOf]
  constructor
  · rintro ⟨n, hn⟩ ⟨b, hb⟩
    rcases hb with ⟨m, rfl⟩
    have h_dvd : orderOf (a ^ m) ∣ p ^ n := by
      rw [← hn]
      apply orderOf_dvd_of_mem_zpowers
      simp only [Subgroup.zpow_mem_zpowers]
    rcases (Nat.dvd_prime_pow (Fact.out : Nat.Prime p)).1 h_dvd with ⟨m, _, heq⟩
    use m
    simp [← heq, ← Subgroup.orderOf_coe]
  · intro hg
    rcases hg ⟨a, Subgroup.mem_zpowers a⟩ with ⟨n, hn⟩
    use n
    simp [← hn, ← Subgroup.orderOf_coe]

/--
@isnad1 id=eq.2h3v.s5.29b8c15be845 from=translated src=- shape=964b437a vocab=2f713292
-/
lemma isPRegular_eq_one [Fact p.Prime]
    (a : G) (hs : IsPSingular p a) (hr : IsPRegular p a) :
    a = 1 := by
  simp only [IsPSingular, IsPRegular] at *
  obtain ⟨n, hn⟩ := hs
  rw [hn] at hr
  have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
  cases n with
  | zero => exact orderOf_eq_one_iff.mp hn
  | succ k =>
    rw [Nat.coprime_pow_left_iff] at hr
    · rw [Nat.coprime_self] at hr
      simp only [hr, lt_self_iff_false] at hp
    · simp

/--
@isnad1 id=iff.0h4v.s6.a633459a3ffc from=translated src=- shape=0eaf49a6 vocab=ecfee329
-/
@[simp]
lemma subtype_iff
    {H : Subgroup G} (x : H) :
    IsPSingular p ((x : H) : G) ↔ IsPSingular p x := by
  simp only [IsPSingular, orderOf_submonoid]

end Tengoku.Brauerinduction.IsPSingular

namespace Group

section pRegular

/--
The canonical `p`-regular factor of an element of finite order.

It is defined as a Bezout power of the element, using the decomposition of
`orderOf a` into its `p`-part and prime-to-`p` part.-/
noncomputable def pRegular (a : G) : G :=
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  a ^ (Nat.gcdA n m * n)

/--
@isnad1 id=eq.0h2v.s5.336f576e3987 from=translated src=- shape=c42f8cb7 vocab=89f81f2e
-/
@[simp]
lemma pRegular_one : pRegular p (1 : G) = 1 := by simp [pRegular]

/-- The inverse of a `p`-regular element is `p`-regular.
@isnad1 id=eq.0h3v.s5.e58bfc136212 from=translated src=- shape=c9765324 vocab=cc3085d2
-/
lemma pRegular_inv [Fact p.Prime] {a : G} :
    pRegular p (a⁻¹) = (pRegular p a)⁻¹ := by
  have h_ord : orderOf (a⁻¹) = orderOf a := orderOf_inv a
  simp only [pRegular, h_ord, Nat.cast_pow, inv_zpow', zpow_neg]

/--
@isnad1 id=eq.1h5v.s7.bc31414f4d25 from=translated src=- shape=edf82b05 vocab=e8ddea1d
-/
lemma pRegular_map {H : Type v} [Group H] (f : G →* H) (hf : Function.Injective f)
    (a : G) : pRegular p (f a) = f (pRegular p a) := by
  have h_ord : orderOf (f a) = orderOf a := orderOf_injective f hf a
  simp only [pRegular, h_ord, Nat.cast_pow, map_zpow]

/--
@isnad1 id=dvd.0h3v.s6.87bd52fadee3 from=translated src=- shape=271e6726 vocab=729f6f10
-/
theorem orderOf_pRegular_dvd (a : G) :
    orderOf (pRegular p a) ∣ ordCompl[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  let k : ℤ := Nat.gcdA n m
  have: n * m = orderOf a := Nat.ordProj_mul_ordCompl_eq_self (orderOf a) p
  have hpow : (pRegular p a) ^ m = 1 := by
    calc
      (pRegular p a) ^ m
          = (a ^ (k * n)) ^ m := by
                simp only [pRegular, Nat.cast_pow, m, k, n]
      _   = a ^ ((k * n) * m) := by
                simp only [zpow_mul, zpow_natCast]
      _   = a ^ (k * (n * m)) := by
                rw [mul_assoc]
      _   = a ^ (k * (orderOf a : ℤ)) := by
                simp only [← this, Nat.cast_mul]
      _   = 1 := by
                simp only [zpow_mul, zpow_natCast, zpow_pow_orderOf]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- `pRegular p x` is p-regular: its order is coprime to `p`.
@isnad1 id=ispregul.1h3v.s4.6294fc062c20 from=translated src=- shape=0a83807d vocab=966613f1
-/
@[simp]
lemma isPRegular_pRegular [Fact p.Prime] {a : G} (h : IsOfFinOrder a) :
    IsPRegular p (pRegular p a) := by
  have hdiv : orderOf (pRegular p a) ∣ ordCompl[p] (orderOf a) :=
    orderOf_pRegular_dvd p a
  have hcop : Nat.Coprime p (ordCompl[p] (orderOf a)) :=
    Nat.coprime_ordCompl (Fact.out : Nat.Prime p) (orderOf_ne_zero_iff.mpr h)
  exact (hcop.symm).coprime_dvd_left hdiv

end pRegular

section pSingular

/--
The canonical `p`-singular factor of an element of finite order.

It is defined as a Bezout power of the element, using the decomposition of
`orderOf a` into its `p`-part and prime-to-`p` part.-/
noncomputable def pSingular (a : G) : G :=
  let m := ordProj[p] (orderOf a)
  let n := ordCompl[p] (orderOf a)
  a ^ (Nat.gcdB m n * n)

/--
@isnad1 id=eq.0h2v.s5.edb292d0c202 from=translated src=- shape=c42f8cb7 vocab=2ecceba0
-/
@[simp]
lemma pSingular_one : pSingular p (1 : G) = 1 := by simp [pSingular]

/--
@isnad1 id=eq.0h3v.s5.23d82eba7519 from=translated src=- shape=c9765324 vocab=2531e475
-/
lemma pSingular_inv [Fact p.Prime] {a : G} :
    pSingular p (a⁻¹) = (pSingular p a)⁻¹ := by
  have h_ord : orderOf (a⁻¹) = orderOf a := orderOf_inv a
  simp only [pSingular, h_ord, Int.natCast_ediv, Nat.cast_pow, inv_zpow', zpow_neg]

/--
@isnad1 id=eq.1h5v.s7.2d31fc9d3428 from=translated src=- shape=edf82b05 vocab=6a7bc20e
-/
lemma pSingular_map {H : Type v} [Group H] (f : G →* H) (h : Function.Injective f)
    (a : G) : pSingular p (f a) = f (pSingular p a) := by
  have h_ord : orderOf (f a) = orderOf a := orderOf_injective f h a
  simp only [pSingular, h_ord, Int.natCast_ediv, Nat.cast_pow, map_zpow]

/--
@isnad1 id=dvd.0h3v.s6.4f50fa39b734 from=translated src=- shape=83154039 vocab=ece48501
-/
theorem orderOf_pSingular_dvd (a : G) :
    orderOf (pSingular p a) ∣ ordProj[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  let k : ℤ := Nat.gcdB n m
  have : n * m = orderOf a := Nat.ordProj_mul_ordCompl_eq_self (orderOf a) p
  have hpow : (pSingular p a) ^ n = 1 := by
    calc
      (pSingular p a) ^ n
          = (a ^ (k * m)) ^ n := by
                simp only [pSingular, Int.natCast_ediv, Nat.cast_pow, n, k, m]
      _   = a ^ ((k * m) * n) := by
                simp only [zpow_mul, zpow_natCast]
      _   = a ^ (k * (m * n)) := by
                rw [mul_assoc]
      _   = a ^ (k * (n * m)) := by
                simp only [mul_comm (n : ℤ) m]
      _   = a ^ (k * (orderOf a : ℤ)) := by
                simp only [← this, Nat.cast_mul]
      _   = 1 := by
                simp only [zpow_mul, zpow_natCast, zpow_pow_orderOf]
  exact orderOf_dvd_iff_pow_eq_one.mpr hpow

/-- `pSingular p a` is p-singular: its order is a power of `p`.
@isnad1 id=ispsingu.0h3v.s4.c039472836a5 from=translated src=- shape=59171bb4 vocab=4561eb79
-/
lemma isPSingular_pSingular (a : G) [Fact p.Prime] :
    IsPSingular p (pSingular p a) := by
  let n := ordProj[p] (orderOf a)
  obtain ⟨k, hk⟩ : ∃ k, n = p ^ k := ⟨(orderOf a).factorization p, rfl⟩
  rcases orderOf_pSingular_dvd p a with ⟨m, hm⟩
  have h₁ : orderOf (pSingular p a) ∣ n := orderOf_pSingular_dvd p a
  have h₂ : orderOf (pSingular p a) ∣ p ^ k := by rw [← hk]; exact h₁
  cases k with
  | zero =>
      have : orderOf (pSingular p a) = 1 :=
          Nat.dvd_one.mp ((Nat.ModEq.dvd_iff rfl h₁).mp h₂)
      exact ⟨0, by simp [this]⟩
  | succ k =>
      set n := orderOf (pSingular p a) with hn
      by_cases h : n = 1
      · exact ⟨0, by simp [n, h]⟩
      · have hppk : IsPrimePow (p ^ (k+1)) :=
          ⟨p, k+1, Nat.prime_iff.mp Fact.out, Nat.succ_pos _, rfl⟩
        have hppn : IsPrimePow n := by
          rw [hn]
          apply IsPrimePow.dvd hppk
          · exact (Nat.ModEq.dvd_iff rfl h₁).mp h₂
          · exact Ne.symm (Ne.intro fun a ↦ h (id (Eq.symm a)))
        rcases hppn with ⟨q, e, hqprime, hepos, hpow⟩
        have hqe : q ^ e ∣ p ^ (k+1) := by rw [hpow]; simp only [h₂]
        have hq : q ∣ p ^ (k+1) := Nat.dvd_of_pow_dvd (Nat.succ_le_of_lt hepos) hqe
        have h_eq : q = p :=
          Nat.prime_eq_prime_of_dvd_pow (Nat.prime_iff.mpr hqprime) Fact.out hq
        subst h_eq
        exact ⟨e, by simp [hn, hpow]⟩

end pSingular

section pDecomposition

/--
@isnad1 id=coprime.2h4v.s5.277bcc18c986 from=translated src=- shape=951068a0 vocab=b054286e
-/
lemma isPSingular_isPRegular_orders_coprime
    {a b : G} (ha : IsPSingular p a) (hb : IsPRegular p b) :
    Nat.Coprime (orderOf a) (orderOf b) := by
  rcases ha with ⟨n, hn⟩
  rw [hn]
  exact hb.symm.pow_left n

/-- Powers of `a` commute, hence the canonical factors commute.
@isnad1 id=commute.0h3v.s5.5b53da7ba44b from=translated src=- shape=c0d9a0e9 vocab=34d11023
-/
lemma pDecomp_commute (a : G) :
    Commute (pSingular p a) (pRegular p a) := by simp [pSingular, pRegular]

/--
@isnad1 id=eq.1h3v.s5.4410d95de029 from=translated src=- shape=88f393a2 vocab=db7b800a
-/
theorem pDecomp [Fact p.Prime] {a : G} (hf : IsOfFinOrder a) :
    pSingular p a * pRegular p a = a := by
  let m := ordProj[p] (orderOf a)
  let n := ordCompl[p] (orderOf a)
  let r : ℤ := Nat.gcdA m n
  let s : ℤ := Nat.gcdB m n
  have hs : pSingular p a = a ^ (s * n) := rfl
  have hr : pRegular p a = a ^ (r * m) := rfl
  -- apply Bézout
  have hbez : m * r + n * s = 1 := by
    have hcop : Nat.Coprime m n :=
      Nat.ordProj_ordCompl_coprime p (orderOf_ne_zero_iff.mpr hf)
    rw [← Nat.gcd_eq_gcd_ab m n, hcop.gcd_eq_one]
    rfl
  rw [hs, hr, zpow_mul_comm a (s * ↑n) (r * ↑m)]
  have := congrArg (fun t : ℤ => a ^ t) hbez
  simp only [zpow_add, zpow_one, mul_comm _ r, mul_comm _ s] at this
  exact this

/--
@isnad1 id=eq.1h3v.s5.c81268b672d7 from=translated src=- shape=88f393a2 vocab=db7b800a
-/
theorem pDecomp' [Fact p.Prime] {a : G} (h : IsOfFinOrder a) :
    pRegular p a * pSingular p a = a := by
  rw [← (pDecomp_commute p a).eq, pDecomp p h]

/--
Uniqueness of the `p`-decomposition.

If `a = b * c = c * b`, where `b` is `p`-singular and `c` is `p`-regular,
then `b` and `c` are respectively the canonical `p`-singular and `p`-regular
factors of `a`.
@isnad1 id=and.5h5v.s6.f1d5c482d4ee from=translated src=- shape=ebd7325d vocab=f9de4d52
-/
theorem pSingular_pRegular_unique [Fact p.Prime]
    {a b c : G}
    (ha : IsOfFinOrder a)
    (h₁ : b * c = a) (h₂ : c * b = a)
    (hb : IsPSingular p b)
    (hc : IsPRegular p c) :
    b = pSingular p a ∧ c = pRegular p a := by
  have hcomm : Commute b c := by
    have : b * c = c * b := h₁.trans h₂.symm
    exact (commute_iff_eq b c).mpr this
  have horder : orderOf a = orderOf b * orderOf c := by
    rw [← h₁]
    exact Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcomm
      (isPSingular_isPRegular_orders_coprime p hb hc)
  let n := ordProj[p] (orderOf a)
  let m := ordCompl[p] (orderOf a)
  have hn : b ^ n = 1 := orderOf_dvd_iff_pow_eq_one.mp <|
    IsPSingular.orderOf_dvd_ordProj p hb (by rw [horder]; exact dvd_mul_right _ _)
      (orderOf_ne_zero_iff.mpr ha)
  have hm : c ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp <|
    IsPRegular.orderOf_dvd_ordCompl p hc (by rw [horder]; exact dvd_mul_left _ _)
  let r : ℤ := Nat.gcdA n m
  let s : ℤ := Nat.gcdB n m
  have hbez : n * r + m * s = 1 := by
    have hcop : Nat.Coprime n m := Nat.ordProj_ordCompl_coprime p (orderOf_ne_zero_iff.mpr ha)
    rw [← Nat.gcd_eq_gcd_ab n m, hcop.gcd_eq_one]; rfl
  have hms : c ^ (m * s) = 1 := by rw [zpow_mul, zpow_natCast, hm, one_zpow]
  have hs_eq : b = pSingular p a := by
    calc b
      _ = b * c ^ (m * s) := by rw [hms, mul_one]
      _ = b ^ (n * r + m * s) * c ^ (m * s) := by rw [hbez, zpow_one]
      _ = b ^ (n * r) * b ^ (m * s) * c ^ (m * s) := by rw [zpow_add]
      _ = b ^ (m * s) * 1 := by rw [zpow_mul, zpow_natCast, hn, one_zpow, hms, one_mul]
      _ = (b * c) ^ (s * m) := by rw [← hms, ← hcomm.mul_zpow, mul_comm (m : ℤ) s]
      _ = pSingular p a := by rw [h₁]; rfl
  have hv_eq : c = pRegular p a := by
    calc c
      _ = b ^ (n * r) * c := by rw [zpow_mul, zpow_natCast, hn, one_zpow, one_mul]
      _ = b ^ (n * r) * c ^ (n * r + m * s) := by rw [hbez, zpow_one]
      _ = b ^ (n * r) * (c ^ (n * r) * c ^ (m * s)) := by rw [zpow_add]
      _ = (b * c) ^ (r * n) := by rw [hms, mul_one, ← hcomm.mul_zpow, mul_comm (n : ℤ) r]
      _ = pRegular p a := by rw [h₁]; rfl
  exact ⟨hs_eq, hv_eq⟩

/--
@isnad1 id=eq.2h3v.s5.dfd6392543e7 from=translated src=- shape=fd53cddf vocab=966613f1
-/
lemma pRegular_eq_self_of_isPRegular [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hr : IsPRegular p a) :
    pRegular p a = a := by
  have hs : IsPSingular p (1 : G) := IsPSingular.one p
  obtain ⟨_, hr_eq⟩ := pSingular_pRegular_unique p hf (one_mul a) (mul_one a) hs hr
  exact hr_eq.symm

/--
@isnad1 id=eq.2h3v.s5.1cfcfd012eb6 from=translated src=- shape=fd53cddf vocab=083f5403
-/
lemma pSingular_eq_self_of_isPSingular [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hs : IsPSingular p a) :
    pSingular p a = a := by
  have hr : IsPRegular p (1 : G) := IsPRegular.one p
  obtain ⟨hs_eq, _⟩ := pSingular_pRegular_unique p hf (mul_one a) (one_mul a) hs hr
  exact hs_eq.symm

/--
@isnad1 id=eq.2h3v.s5.e296d203159b from=translated src=- shape=f16bc490 vocab=3d6b0b9c
-/
lemma isPSingular_pRegular_eq_one [Fact p.Prime]
    {a : G} (hf : IsOfFinOrder a) (hs : IsPSingular p a) :
    pRegular p a = 1 := by
  have hr : IsPRegular p (1 : G) := by simp
  obtain ⟨_, hv_eq⟩ := pSingular_pRegular_unique p hf (mul_one a) (one_mul a) hs hr
  exact hv_eq.symm

/--
@isnad1 id=eq.2h3v.s5.860668b01b59 from=translated src=- shape=f16bc490 vocab=41f2df26
-/
lemma isPRegular_pSingular_eq_one [Fact p.Prime]
     {a : G} (hf : IsOfFinOrder a) (hr : IsPRegular p a) :
    pSingular p a = 1 := by
  have hs : IsPSingular p (1 : G) := by simp
  obtain ⟨hs_eq, _⟩ := pSingular_pRegular_unique p hf (one_mul a) (mul_one a) hs hr
  exact hs_eq.symm

/-- Conjugation carries the `p`-elementary/`p`-regular factors
    to those of the conjugate element.
@isnad1 id=and.1h5v.s6.464aa073add5 from=translated src=- shape=72a8653a vocab=b31461c2
-/
lemma pDecomp_SemiconjBy [Fact p.Prime] {a b c : G} (h : SemiconjBy a b c) :
    SemiconjBy a (pSingular p b) (pSingular p c) ∧
    SemiconjBy a (pRegular p b) (pRegular p c) := by
  have h_ord : orderOf b = orderOf c := h.orderOf_eq
  constructor
  · simp only [pSingular, h_ord]
    exact h.zpow_right _
  · simp only [pRegular, h_ord]
    exact h.zpow_right _

/--
@isnad1 id=eq.0h4v.s6.09e45a6614de from=translated src=- shape=0aa221bb vocab=371e3e9f
-/
@[simp]
lemma pRegular_conj [Fact p.Prime] (a b : G) :
    Group.pRegular p (a * b * a⁻¹) = a * Group.pRegular p b * a⁻¹ := by
  have h_semi : SemiconjBy a b (a * b * a⁻¹) := by
    rw [SemiconjBy, inv_mul_cancel_right]
  have h_reg := (pDecomp_SemiconjBy p h_semi).right
  exact eq_mul_inv_of_mul_eq h_reg.eq.symm

/--
@isnad1 id=eq.0h4v.s6.ca58682553dc from=translated src=- shape=2ebffb68 vocab=371e3e9f
-/
@[simp]
lemma pRegular_conj' [Fact p.Prime] (a b : G) :
    Group.pRegular p (a⁻¹ * b * a)  = a⁻¹ * Group.pRegular p b * a := by
  have h := pRegular_conj p (a⁻¹) b
  rw [inv_inv] at h
  exact h

/--
@isnad1 id=eq.0h4v.s6.4912b44eff6b from=translated src=- shape=0aa221bb vocab=d266244e
-/
@[simp]
lemma pSingular_conj [Fact p.Prime] (a b : G) :
    Group.pSingular p (a * b * a⁻¹) = a * Group.pSingular p b * a⁻¹ := by
  have h_semi : SemiconjBy a b (a * b * a⁻¹) := by
    rw [SemiconjBy, inv_mul_cancel_right]
  have h_sing := (pDecomp_SemiconjBy p h_semi).left
  exact eq_mul_inv_of_mul_eq h_sing.eq.symm

/--
If h is p-regular and s is p-singular and they commute, then the p-regular part
of (h * s) is just h.
@isnad1 id=eq.4h4v.s6.f4408bd9bc3d from=translated src=- shape=5def4e8d vocab=3fa66c2a
-/
lemma pRegular_mul_eq_self_of_pSingular_commute [Fact p.Prime]
      {a b : G} (hf : IsOfFinOrder (a * b))
      (ha : IsPRegular p a) (hb : IsPSingular p b)
      (hcomm : Commute a b) :
    Group.pRegular p (a * b) = a := by
  have h_mul : b * a = a * b := hcomm.symm.eq
  obtain ⟨_, h_reg_eq⟩ :=
    pSingular_pRegular_unique p (a := a * b) (b := b) (c := a) hf h_mul rfl hb ha
  exact h_reg_eq.symm

/--
@isnad1 id=eq.3h4v.s6.9e495e749240 from=translated src=- shape=abd6a6c4 vocab=731cd483
-/
lemma isPRegular_eq_one_of_mem_pGroup [Fact p.Prime]
    {a : G} {P : Subgroup G} (hP : IsPGroup p P)
    (haP : a ∈ P) (hr : IsPRegular p a) : a = 1 := by
  -- 1. Extract the fact that a is p-singular from the p-group property
  have hs : IsPSingular p a := by
    rcases (IsPGroup.iff_orderOf).mp hP ⟨a, haP⟩ with ⟨k, hk⟩
    use k
    simp only [← hk, Subgroup.orderOf_mk]
  -- 2. A sinngular and regular element is 1
  exact IsPSingular.isPRegular_eq_one p a hs hr

/-- Two p-regular parts commute if the elements commute.
@isnad1 id=commute.1h4v.s5.a282495cafe8 from=translated src=- shape=4b333b1e vocab=3e72d6dd
-/
lemma pRegular.commute {a b : G} (h : Commute a b) :
    Commute (pRegular p a) (pRegular p b) := Commute.zpow_zpow h _ _

/-- Two p-singular parts commute if the elements commute.
@isnad1 id=commute.1h4v.s5.9d876eb9402b from=translated src=- shape=4b333b1e vocab=054886b4
-/
lemma pSingular.commute {a b : G} (h : Commute a b) :
    Commute (pSingular p a) (pSingular p b) := Commute.zpow_zpow h _ _

/-- If a and b commute, then the p-regular part of a commutes with the p-singular part of b.
@isnad1 id=commute.1h4v.s5.4e197f2e9d58 from=translated src=- shape=4b333b1e vocab=34d11023
-/
lemma pRegular_pSingular_commute {a b : G} (h : Commute a b) :
    Commute (Group.pRegular p a) (Group.pSingular p b) := Commute.zpow_zpow h _ _

/-- If a and b commute, then the p-singular part of a commutes with the
  p-regular part of b.
@isnad1 id=commute.1h4v.s5.269bc4f52d12 from=translated src=- shape=4b333b1e vocab=34d11023
-/
lemma pSingular_pRegular_commute {a b : G} (h : Commute a b) :
    Commute (Group.pSingular p a) (Group.pRegular p b) := Commute.zpow_zpow h _ _

/--
The `p`-decomposition of a commuting product is the product of the
corresponding `p`-singular and `p`-regular factors.
@isnad1 id=and.3h4v.s7.84da05e7537a from=translated src=- shape=398609f1 vocab=0661e433
-/
lemma pDecomp_mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b)
    (hcomm : Commute a b) :
    Group.pSingular p (a * b) = Group.pSingular p a * Group.pSingular p b ∧
    Group.pRegular p (a * b) = Group.pRegular p a * Group.pRegular p b := by
  let ar := Group.pRegular p a
  let as := Group.pSingular p a
  let br := Group.pRegular p b
  let bs := Group.pSingular p b
  let cr := ar * br
  let cs := as * bs
  -- 1 & 2. Use IsPRegular.mul and IsPSingular.mul lemmas
  have hcr : IsPRegular p cr :=
    (isPRegular_pRegular p ha).mul p (isPRegular_pRegular p hb) (pRegular.commute p hcomm)
  have hcs : IsPSingular p cs :=
    (isPSingular_pSingular p a).mul p (isPSingular_pSingular p b) (pSingular.commute p hcomm)
  -- 3. Show cu * cr = a * b
  have h_prod : cs * cr = a * b := by
    rw [mul_assoc, ← mul_assoc bs]
    have: Commute bs ar := Commute.zpow_zpow hcomm.symm _ _
    rw [this, mul_assoc, ← mul_assoc as]
    have hcomm_a : Commute as ar := pDecomp_commute p a
    have hcomm_b : Commute bs br := pDecomp_commute p b
    rw [hcomm_a.eq, hcomm_b.eq, pDecomp' p hb, pDecomp' p ha]
  -- 4. Show cr and cu commute
  have hcomm_c : Commute cs cr := by
    apply Commute.mul_left
    · apply Commute.mul_right
      · exact pDecomp_commute p a
      · exact Commute.zpow_zpow hcomm _ _
    · apply Commute.mul_right
      · exact Commute.zpow_zpow hcomm.symm _ _
      · exact pDecomp_commute p b
  -- 5. Apply uniqueness to get both equalities
  have h_prod_rev : cr * cs = a * b := by
    rw [← hcomm_c.eq, h_prod]
  have hfab : IsOfFinOrder (a * b) := Commute.isOfFinOrder_mul hcomm ha hb
  obtain ⟨hs_eq, hr_eq⟩ := pSingular_pRegular_unique p hfab h_prod h_prod_rev hcs hcr
  exact ⟨hs_eq.symm, hr_eq.symm⟩

/-- Two p-regular parts multiply together if the original elements commute.
@isnad1 id=eq.3h4v.s6.866f01a5a340 from=translated src=- shape=8b67d304 vocab=b379846f
-/
lemma pRegular.mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) (hcomm : Commute a b) :
    Group.pRegular p (a * b) = Group.pRegular p a * Group.pRegular p b :=
  (pDecomp_mul_of_commute p ha hb hcomm).right

/-- Two p-singular parts multiply together if the original elements commute.
@isnad1 id=eq.3h4v.s6.a14526913486 from=translated src=- shape=8b67d304 vocab=cb11ce19
-/
lemma pSingular.mul_of_commute [Fact p.Prime]
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b)
    (hcomm : Commute a b) :
    Group.pSingular p (a * b) = Group.pSingular p a * Group.pSingular p b :=
  (pDecomp_mul_of_commute p ha hb hcomm).left

/-- If `s` is p-singular and commutes with `a`, then `pRegular (a * s) = pRegular a`.
@isnad1 id=eq.4h4v.s6.b5e2d92e4975 from=translated src=- shape=f5f2d5ff vocab=900a9414
-/
lemma pRegular_mul_eq_left_of_right_pSingular_commute [Fact p.Prime]
    {a s : G} (ha_fin : IsOfFinOrder s) (hb_fin : IsOfFinOrder a)
    (hs : IsPSingular p s) (hcomm : Commute s a) :
    Group.pRegular p (a * s) = Group.pRegular p a := by
  calc
    Group.pRegular p (a * s)
        = Group.pRegular p a * Group.pRegular p s := by
          rw [Group.pRegular.mul_of_commute p hb_fin ha_fin hcomm.symm]
    _   = Group.pRegular p a := by
          simp only [Group.isPSingular_pRegular_eq_one p ha_fin hs, mul_one]

/--
Raising an element to the `p`-part of its order only depends on its
`p`-regular factor.
@isnad1 id=eq.1h3v.s7.80371f0bf06d from=translated src=- shape=0a0e4d05 vocab=0d71d8e3
-/
lemma pow_ordProj_eq_pRegular_pow_ordProj [Fact p.Prime]
    {a : G} (h : IsOfFinOrder a) :
    a ^ ordProj[p] (orderOf a) = Group.pRegular p a ^ ordProj[p] (orderOf a) := by
  let n := ordProj[p] (orderOf a)
  let r := Group.pRegular p a
  let s := Group.pSingular p a
  have hdecomp : s * r = a := pDecomp p h
  have hcomm : Commute s r := pDecomp_commute p a
  have : s ^ n = 1 := by
    have hdvd : orderOf s ∣ n := Group.orderOf_pSingular_dvd p a
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd
  calc
    a ^ n = (s * r) ^ n := by rw [hdecomp]
    _     = s ^ n * r ^ n := hcomm.mul_pow n
    _     = 1 * r ^ n := by rw [this]
    _     = r ^ n := by rw [one_mul]

end pDecomposition

end Group
-- Tengoku: root names of this library moved to Tengoku.Brauerinduction so they do not collide with other libraries (generated)
