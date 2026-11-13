import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_NormTheta_Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Algebraic Theorems

Theorems 1-4, 6, 8 from the norm theta series paper.
All proofs are checked by Lean 4.30.0 and Mathlib.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Foundational lemmas for triZ

triZ's `/` is opened exactly once, inside `two_mul_triZ`.
Everything downstream uses `linear_combination` or passes through `two_mul_E` + `omega`.
-/

/--
@isnad1 id=dvd.0h1v.s4.37105c7fe37b from=translated src=- shape=bd967a0d vocab=a56bc09a
-/
lemma two_dvd_mul_succ (r : Int) : 2 ∣ r * (r + 1) :=
  (Int.even_mul_succ_self r).two_dvd

/--
@isnad1 id=eq.0h1v.s5.c2419f11f229 from=translated src=- shape=e492614d vocab=b148211c
-/
lemma two_mul_triZ (r : Int) : 2 * triZ r = r * (r + 1) := by
  unfold triZ
  exact Int.mul_ediv_cancel' (two_dvd_mul_succ r)

/-! ## Theorem 1: Q(k,r) is always even -/

/--
@isnad1 id=dvd.0h2v.s3.36186b4b0eff from=translated src=- shape=a120b2a8 vocab=b81f0d74
-/
theorem Q_even (k r : Int) : 2 ∣ Q k r := by
  unfold Q
  have h1 : 2 ∣ 2 * (2 * k ^ 2 + k + 3 * k * r) := dvd_mul_right 2 _
  have h2 : 2 ∣ r * (r + 1) := two_dvd_mul_succ r
  have hsum : 2 ∣ 2 * (2 * k ^ 2 + k + 3 * k * r) + r * (r + 1) := dvd_add h1 h2
  convert hsum using 1
  ring

/-! ## Spec lemma: Q = 2E (and reverse) -/

/--
@isnad1 id=eq.0h2v.s4.88a0c17c47b7 from=translated src=- shape=82180317 vocab=17beeb82
-/
theorem Q_eq_two_mul_E (k r : Int) : Q k r = 2 * E k r := by
  unfold E Q
  linear_combination -two_mul_triZ r

/--
@isnad1 id=eq.0h2v.s4.1e7e931f6247 from=translated src=- shape=c69a7ce1 vocab=17beeb82
-/
theorem two_mul_E (k r : Int) : 2 * E k r = Q k r := by
  linarith [Q_eq_two_mul_E k r]

/-! ## Theorem 2: beta maps into L, and surjects onto L -/

/--
@isnad1 id=inl.0h2v.s3.039692933b07 from=translated src=- shape=b794339c vocab=3b21a377
-/
theorem beta_mem_L (k r : Int) : InL (beta k r) := by
  unfold InL beta
  use k
  ring

/--
@isnad1 id=ex.1h1v.s4.72ec5f849d52 from=translated src=- shape=3f62e438 vocab=852d38fc
-/
theorem exists_beta_of_mem_L (x : PhiInt) (hx : InL x) :
    ∃ k r : Int, beta k r = x := by
  rcases hx with ⟨k, hk⟩
  refine ⟨k, x.a + 2 * k, ?_⟩
  ext <;> simp only [beta] <;> omega

/-! ## Theorem 3: norm identity -N(β(k,r)) = 10E(k,r) + 1 -/

/-! ## Theorem 4: sign simplification (-1)^r = (-1)^(r-2k) -/

/--
@isnad1 id=eq.0h2v.s4.6a7987adcdb8 from=translated src=- shape=f77113c8 vocab=5f3019fa
-/
theorem parity_beta_a (k r : Int) :
    negOnePowInt r = negOnePowInt (r - 2 * k) := by
  unfold negOnePowInt
  have h : r % 2 = (r - 2 * k) % 2 := by omega
  simp only [h]

/-! ## Theorem 6: Coset stability under unit powers

The stabilizer of L in ⟨ε⟩ is ⟨ε⁶⟩:
- k=1,3,5 (odd): ε^k·L ∩ L = ∅ (strong disjointness)
- k=2,4 (even, not 6): ε^k·L ∩ L ≠ ∅ but ε^k·L ≠ L (partial intersection)
- k=6: ε⁶·L = L (complete stabilization)
-/

def eps2Mul (x : PhiInt) : PhiInt :=
  ⟨2 * x.a + 3 * x.b, 3 * x.a + 5 * x.b⟩

def eps3Mul (x : PhiInt) : PhiInt :=
  ⟨5 * x.a + 8 * x.b, 8 * x.a + 13 * x.b⟩

def eps4Mul (x : PhiInt) : PhiInt :=
  ⟨13 * x.a + 21 * x.b, 21 * x.a + 34 * x.b⟩

def eps5Mul (x : PhiInt) : PhiInt :=
  ⟨34 * x.a + 55 * x.b, 55 * x.a + 89 * x.b⟩

-- Consistency: epskMul = k-fold epsMul composition
/--
@isnad1 id=eq.0h1v.s3.1cc205ddff49 from=translated src=- shape=5dad4736 vocab=3fb2da03
-/
theorem eps2Mul_eq (x : PhiInt) : eps2Mul x = epsMul (epsMul x) := by
  simp only [eps2Mul, epsMul, PhiInt.mk.injEq]; omega

-- Part (a): Odd powers — strong disjointness

/--
@isnad1 id=not.1h1v.s3.6061b057cae7 from=translated src=- shape=26344a34 vocab=826c372a
-/
theorem epsMul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (epsMul x) := by
  simp only [InL, epsMul] at hx ⊢; omega

/--
@isnad1 id=not.1h1v.s3.ffa0eb6dfa60 from=translated src=- shape=26344a34 vocab=8225fb8f
-/
theorem eps3Mul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (eps3Mul x) := by
  simp only [InL, eps3Mul] at hx ⊢; omega

/--
@isnad1 id=not.1h1v.s3.6ef9feaad8ec from=translated src=- shape=26344a34 vocab=78ac04e9
-/
theorem eps5Mul_not_preserve_L (x : PhiInt) (hx : InL x) :
    ¬ InL (eps5Mul x) := by
  simp only [InL, eps5Mul] at hx ⊢; omega

-- Part (b): Even powers — not set-preserving (witness-based)

/--
@isnad1 id=ex.0h0v.s3.9b4c1c75aee2 from=translated src=- shape=c52680f0 vocab=c68c2ee1
-/
theorem eps2Mul_not_setPreserve_L :
    ∃ x : PhiInt, InL x ∧ ¬ InL (eps2Mul x) :=
  ⟨⟨0, 1⟩, by simp [InL, eps2Mul]⟩

/--
@isnad1 id=ex.0h0v.s3.38a8d2d4fbbe from=translated src=- shape=c52680f0 vocab=11158869
-/
theorem eps4Mul_not_setPreserve_L :
    ∃ x : PhiInt, InL x ∧ ¬ InL (eps4Mul x) :=
  ⟨⟨1, 4⟩, by simp [InL, eps4Mul]⟩

-- Part (c): ε⁶ preserves L completely

/--
@isnad1 id=inl.1h1v.s3.3443f3891277 from=translated src=- shape=2c86d966 vocab=6595b265
-/
theorem eps6Mul_preserves_L (x : PhiInt) (hx : InL x) :
    InL (eps6Mul x) := by
  simp only [InL, eps6Mul] at hx ⊢
  obtain ⟨m, hm⟩ := hx
  exact ⟨m - 12 * x.a - 20 * x.b, by omega⟩

/-! ## E is nonneg on both cones (justifies Nat indexing) -/

/-! ## Theorem 7: Order of ε modulo 2√5 is exactly 6

ε⁶ ≡ 1 (mod 2√5), i.e., c_2sqrt5 divides (ε⁶ - 1) as a PhiInt element.
For k=1..5, εᵏ ≢ 1 (mod 2√5) — witnessed on the basis element ⟨1,0⟩.
-/

-- Divisibility in ℤ[φ]: c ∣ x iff ∃ y, x = c * y
def PhiInt.phiDvd (c x : PhiInt) : Prop := ∃ y : PhiInt, x = c * y

-- ε⁶ - 1 applied to basis: eps6Mul(1,0) - (1,0) = ⟨88, 144⟩
/--
@isnad1 id=phidvd.0h0v.s5.a9e9884d7123 from=translated src=- shape=a3d26746 vocab=c57509aa
-/
theorem eps6_congOne_basis1 :
    PhiInt.phiDvd c_2sqrt5 (eps6Mul ⟨1, 0⟩ - ⟨1, 0⟩) :=
  ⟨⟨20, 32⟩, by ext <;> simp [c_2sqrt5, eps6Mul]⟩

-- eps6Mul(0,1) - (0,1) = ⟨144, 232⟩
/--
@isnad1 id=phidvd.0h0v.s5.438766ea9bc6 from=translated src=- shape=a3d26746 vocab=c57509aa
-/
theorem eps6_congOne_basis2 :
    PhiInt.phiDvd c_2sqrt5 (eps6Mul ⟨0, 1⟩ - ⟨0, 1⟩) :=
  ⟨⟨32, 52⟩, by ext <;> simp [c_2sqrt5, eps6Mul]⟩

-- ε¹ ≢ 1: epsMul(1,0) - (1,0) = ⟨0,1⟩, not divisible by ⟨-2,4⟩
/--
@isnad1 id=not.0h0v.s5.6e268a661419 from=translated src=- shape=4518d3c7 vocab=bee097f7
-/
theorem eps1_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (epsMul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, epsMul, PhiInt.ext_iff] at h
  omega

/--
@isnad1 id=not.0h0v.s5.5f785d112bc9 from=translated src=- shape=4518d3c7 vocab=b40ec501
-/
theorem eps2_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps2Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps2Mul, PhiInt.ext_iff] at h
  omega

/--
@isnad1 id=not.0h0v.s5.419ac2066eac from=translated src=- shape=4518d3c7 vocab=fbc453b0
-/
theorem eps3_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps3Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps3Mul, PhiInt.ext_iff] at h
  omega

/--
@isnad1 id=not.0h0v.s5.ffb254c674a8 from=translated src=- shape=4518d3c7 vocab=2420c324
-/
theorem eps4_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps4Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps4Mul, PhiInt.ext_iff] at h
  omega

/--
@isnad1 id=not.0h0v.s5.5b1ce7e091c3 from=translated src=- shape=4518d3c7 vocab=0213e842
-/
theorem eps5_notCongOne :
    ¬ PhiInt.phiDvd c_2sqrt5 (eps5Mul ⟨1, 0⟩ - ⟨1, 0⟩) := by
  intro ⟨⟨a, b⟩, h⟩
  simp [c_2sqrt5, eps5Mul, PhiInt.ext_iff] at h
  omega

/-! ## Theorem 8: HM exponent matches E -/

end Ch10
end QseriesFormalization
