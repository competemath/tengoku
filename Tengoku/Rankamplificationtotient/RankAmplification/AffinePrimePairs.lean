import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.NumberTheory.PrimeCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Two affine prime forms: finite sieve setup Finite and local algebra for the special `A r + 1`, `B r + 1` instance of Lemma 9.5. -/

namespace RankAmplification

noncomputable section

/-- Parameters for the two positive affine forms used by the diagonal.-/
structure AffinePrimePair where
  /-- Slope of the first affine form.-/
  leftSlope : ℕ
  /-- Slope of the second affine form.-/
  rightSlope : ℕ
  left_pos : 0 < leftSlope
  right_pos : 0 < rightSlope
  slopes_ne : leftSlope ≠ rightSlope

namespace AffinePrimePair

variable (L : AffinePrimePair)

/-- Value of the first affine form at `r`.-/
def leftValue (r : ℕ) : ℕ := L.leftSlope * r + 1

/-- Value of the second affine form at `r`.-/
def rightValue (r : ℕ) : ℕ := L.rightSlope * r + 1

/-- Parameters up to `R` for which both affine values are prime.-/
def primePairSet (R : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter fun r ↦ (L.leftValue r).Prime ∧ (L.rightValue r).Prime

/-- Parameters up to `R` whose affine-value product has no prime divisor at most `z`.-/
def siftedPairSet (R z : ℕ) : Finset ℕ :=
  (Finset.Icc 1 R).filter fun r ↦
    ∀ p ∈ Nat.primesLE z, ¬p ∣ L.leftValue r * L.rightValue r

/--
@isnad1 id=iff.0h3v.s5.0133197fa625 from=translated src=- shape=47d1bc62 vocab=f87e52a0
-/
@[simp]
theorem mem_primePairSet {R r : ℕ} :
    r ∈ L.primePairSet R ↔
      1 ≤ r ∧ r ≤ R ∧ (L.leftValue r).Prime ∧ (L.rightValue r).Prime := by
  simp [primePairSet, and_assoc]

/--
@isnad1 id=iff.0h4v.s6.0877f567ebd8 from=translated src=- shape=806a090e vocab=80500173
-/
@[simp]
theorem mem_siftedPairSet {R z r : ℕ} :
    r ∈ L.siftedPairSet R z ↔
      1 ≤ r ∧ r ≤ R ∧
        ∀ p ∈ Nat.primesLE z, ¬p ∣ L.leftValue r * L.rightValue r := by
  simp [siftedPairSet, and_assoc]

/--
@isnad1 id=and.0h2v.s4.931ed9769f1f from=translated src=- shape=5009d9f3 vocab=25ec599b
-/
theorem value_pos (r : ℕ) : 0 < L.leftValue r ∧ 0 < L.rightValue r := by
  constructor
  · simp only [leftValue]
    omega
  · simp only [rightValue]
    omega

/--
@isnad1 id=strictmo.0h1v.s3.b068be548730 from=translated src=- shape=8735051e vocab=6138f040
-/
theorem value_strictMono_left : StrictMono L.leftValue := by
  intro a b hab
  unfold leftValue
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hab L.left_pos) 1

/--
@isnad1 id=strictmo.0h1v.s3.5aa48dbb2f81 from=translated src=- shape=8735051e vocab=015a0cec
-/
theorem value_strictMono_right : StrictMono L.rightValue := by
  intro a b hab
  unfold rightValue
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hab L.right_pos) 1

/-- Prime pairs whose two values exceed the sifting level survive the finite sieve.
@isnad1 id=mem.3h4v.s5.26c201ddff20 from=translated src=- shape=f7d05666 vocab=ad734ead
-/
theorem mem_siftedPairSet_of_prime_values_gt {R z r : ℕ} (hr : r ∈ L.primePairSet R)
    (hleft : z < L.leftValue r) (hright : z < L.rightValue r) :
    r ∈ L.siftedPairSet R z := by
  have hp := L.mem_primePairSet.mp hr
  apply L.mem_siftedPairSet.mpr
  refine ⟨hp.1, hp.2.1, ?_⟩
  intro p hpz hpdvd
  have pp : p.Prime := Nat.prime_of_mem_primesLE hpz
  rcases pp.dvd_mul.mp hpdvd with hpLeft | hpRight
  · have heq : p = L.leftValue r := (Nat.prime_dvd_prime_iff_eq pp hp.2.2.1).mp hpLeft
    have hple : p ≤ z := Nat.le_of_mem_primesLE hpz
    omega
  · have heq : p = L.rightValue r := (Nat.prime_dvd_prime_iff_eq pp hp.2.2.2).mp hpRight
    have hple : p ≤ z := Nat.le_of_mem_primesLE hpz
    omega

/-- A single affine form can take a prescribed value at most once.
@isnad1 id=le.0h3v.s5.588d2a4aa91c from=translated src=- shape=3dd0464c vocab=d5177019
-/
theorem card_filter_leftValue_le_one (R q : ℕ) :
    ((Finset.Icc 1 R).filter fun r ↦ L.leftValue r = q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have haEq := (Finset.mem_filter.mp ha).2
  have hbEq := (Finset.mem_filter.mp hb).2
  exact L.value_strictMono_left.injective (haEq.trans hbEq.symm)

/--
@isnad1 id=le.0h3v.s5.e187078c9567 from=translated src=- shape=3dd0464c vocab=648119a1
-/
theorem card_filter_rightValue_le_one (R q : ℕ) :
    ((Finset.Icc 1 R).filter fun r ↦ L.rightValue r = q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have haEq := (Finset.mem_filter.mp ha).2
  have hbEq := (Finset.mem_filter.mp hb).2
  exact L.value_strictMono_right.injective (haEq.trans hbEq.symm)

/-- Residues modulo a prime `p` on which one affine form vanishes.-/
def affineRootSet (p A : ℕ) (hp : p.Prime) : Finset (ZMod p) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact Finset.univ.filter fun r ↦ (A : ZMod p) * r + 1 = 0

/--
@isnad1 id=iff.1h3v.s7.905733f70e8e from=translated src=- shape=5f3a73c5 vocab=05f40415
-/
@[simp]
theorem mem_affineRootSet {p A : ℕ} (hp : p.Prime) {r : ZMod p} :
    r ∈ affineRootSet p A hp ↔ (A : ZMod p) * r + 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [affineRootSet]

/-- A nonconstant affine congruence has one root; a constant-one congruence has none.
@isnad1 id=le.1h2v.s4.d71a6170d76f from=translated src=- shape=21024356 vocab=e2c63576
-/
theorem card_affineRootSet_le_one {p A : ℕ} (hp : p.Prime) :
    (affineRootSet p A hp).card ≤ 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hxEq := (mem_affineRootSet hp).mp hx
  have hyEq := (mem_affineRootSet hp).mp hy
  by_cases hA : (A : ZMod p) = 0
  · rw [hA, zero_mul, zero_add] at hxEq
    exact False.elim (one_ne_zero hxEq)
  · have hmul : (A : ZMod p) * (x - y) = 0 := by
      calc
        (A : ZMod p) * (x - y) = ((A : ZMod p) * x + 1) - ((A : ZMod p) * y + 1) := by ring
        _ = 0 := by rw [hxEq, hyEq]; ring
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hA)

/-- The local bad residues for the product of the two affine forms.-/
def badResidueSet (p : ℕ) (hp : p.Prime) : Finset (ZMod p) :=
  affineRootSet p L.leftSlope hp ∪ affineRootSet p L.rightSlope hp

/--
@isnad1 id=iff.1h3v.s8.9849318df830 from=translated src=- shape=c729d6aa vocab=c6528362
-/
@[simp]
theorem mem_badResidueSet_iff {p : ℕ} (hp : p.Prime) {r : ZMod p} :
    r ∈ L.badResidueSet p hp ↔
      ((L.leftSlope : ZMod p) * r + 1) * ((L.rightSlope : ZMod p) * r + 1) = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  simp [badResidueSet, mul_eq_zero]

/-- Dimension at most two: every prime modulus excludes at most two residue classes.
@isnad1 id=le.1h2v.s4.420a3de8ee1a from=translated src=- shape=e1254190 vocab=800b319d
-/
theorem card_badResidueSet_le_two {p : ℕ} (hp : p.Prime) :
    (L.badResidueSet p hp).card ≤ 2 := by
  unfold badResidueSet
  calc
    (affineRootSet p L.leftSlope hp ∪ affineRootSet p L.rightSlope hp).card ≤
        (affineRootSet p L.leftSlope hp).card + (affineRootSet p L.rightSlope hp).card :=
      Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add (card_affineRootSet_le_one hp) (card_affineRootSet_le_one hp)
    _ = 2 := rfl

end AffinePrimePair

end

end RankAmplification
