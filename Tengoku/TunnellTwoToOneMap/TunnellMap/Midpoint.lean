import Tengoku.TunnellTwoToOneMap.TunnellMap.QuarterTurns

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Midpoint coordinates

This file formalizes the parity content of Lemma 2.2 in the paper.  The two
Tunnell forms are lifted to the quadratic form `2 X₁² + X₂² + 2 X₃²`.
For every odd source and target, explicit integral half-sum and half-difference
vectors exist, and both have odd third coordinate.
-/

namespace TunnellMap

def qForm (p : Triple) : ℤ :=
  2 * p.x ^ 2 + p.y ^ 2 + 2 * p.z ^ 2

def bLift {n : ℤ} (p : BOddRep n) : Triple :=
  ⟨p.1.x, p.1.y, 2 * p.1.z⟩

def aLift {n : ℤ} (p : ARep n) : Triple :=
  ⟨p.1.x, p.1.y, 4 * p.1.z⟩

/--
@isnad1 id=eq.0h2v.s3.b058109a8315 from=translated src=- shape=93f5b8f2 vocab=59a2e7ae
-/
@[simp] theorem qForm_bLift {n : ℤ} (p : BOddRep n) : qForm (bLift p) = n := by
  have h := p.2.1
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 8 * p.1.z ^ 2 = n at h
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 2 * (2 * p.1.z) ^ 2 = n
  nlinarith

/--
@isnad1 id=eq.0h2v.s3.181325790bf3 from=translated src=- shape=93f5b8f2 vocab=ba0f5862
-/
@[simp] theorem qForm_aLift {n : ℤ} (p : ARep n) : qForm (aLift p) = n := by
  have h := p.2
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 32 * p.1.z ^ 2 = n at h
  change 2 * p.1.x ^ 2 + p.1.y ^ 2 + 2 * (4 * p.1.z) ^ 2 = n
  nlinarith

/--
@isnad1 id=ex.1h1v.s5.6e432b829d76 from=translated src=- shape=f25dc932 vocab=533e4da7
-/
theorem odd_sq_eq_one_add_eight_mul {x : ℤ} (hx : Odd x) :
    ∃ k : ℤ, x ^ 2 = 1 + 8 * k := by
  rcases hx with ⟨a, ha⟩
  rcases Int.even_mul_succ_self a with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  calc
    x ^ 2 = (2 * a + 1) ^ 2 := by rw [ha]
    _ = 1 + 4 * (a * (a + 1)) := by ring
    _ = 1 + 8 * k := by rw [hk]; ring

/--
@isnad1 id=ex.1h1v.s5.c07389aff690 from=translated src=- shape=992dd6d0 vocab=82cc1cb2
-/
theorem even_sq_eq_four_mul {x : ℤ} (hx : Even x) :
    ∃ k : ℤ, x ^ 2 = 4 * k := by
  rcases hx with ⟨a, ha⟩
  refine ⟨a ^ 2, ?_⟩
  rw [ha]
  ring

/--
@isnad1 id=or.1h3v.s6.689252d84e65 from=translated src=- shape=293e05b9 vocab=5fbe2ae5
-/
theorem lifted_first_coordinates_same_parity {n : ℤ} (hn : Odd n)
    (s : BOddRep n) (t : ARep n) :
    (Even s.1.x ∧ Even t.1.x) ∨ (Odd s.1.x ∧ Odd t.1.x) := by
  have hsy := odd_y_of_bOdd hn s
  have hty := odd_y_of_aRep hn t
  rcases Int.even_or_odd s.1.x with hsx | hsx
  · rcases Int.even_or_odd t.1.x with htx | htx
    · exact Or.inl ⟨hsx, htx⟩
    · exfalso
      obtain ⟨ksx, hsx₂⟩ := even_sq_eq_four_mul hsx
      obtain ⟨ktx, htx₂⟩ := odd_sq_eq_one_add_eight_mul htx
      obtain ⟨ksy, hsy₂⟩ := odd_sq_eq_one_add_eight_mul hsy
      obtain ⟨kty, hty₂⟩ := odd_sq_eq_one_add_eight_mul hty
      have hsform := s.2.1
      have htform := t.2
      change 2 * s.1.x ^ 2 + s.1.y ^ 2 + 8 * s.1.z ^ 2 = n at hsform
      change 2 * t.1.x ^ 2 + t.1.y ^ 2 + 32 * t.1.z ^ 2 = n at htform
      rw [hsx₂, hsy₂] at hsform
      rw [htx₂, hty₂] at htform
      omega
  · rcases Int.even_or_odd t.1.x with htx | htx
    · exfalso
      obtain ⟨ksx, hsx₂⟩ := odd_sq_eq_one_add_eight_mul hsx
      obtain ⟨ktx, htx₂⟩ := even_sq_eq_four_mul htx
      obtain ⟨ksy, hsy₂⟩ := odd_sq_eq_one_add_eight_mul hsy
      obtain ⟨kty, hty₂⟩ := odd_sq_eq_one_add_eight_mul hty
      have hsform := s.2.1
      have htform := t.2
      change 2 * s.1.x ^ 2 + s.1.y ^ 2 + 8 * s.1.z ^ 2 = n at hsform
      change 2 * t.1.x ^ 2 + t.1.y ^ 2 + 32 * t.1.z ^ 2 = n at htform
      rw [hsx₂, hsy₂] at hsform
      rw [htx₂, hty₂] at htform
      omega
    · exact Or.inr ⟨hsx, htx⟩

/-- Coordinatewise statement that `2h = E + F`.-/
def IsHalfSum (h E F : Triple) : Prop :=
  2 * h.x = E.x + F.x ∧
    2 * h.y = E.y + F.y ∧
    2 * h.z = E.z + F.z

/-- Coordinatewise statement that `2h = E - F`.-/
def IsHalfDiff (h E F : Triple) : Prop :=
  2 * h.x = E.x - F.x ∧
    2 * h.y = E.y - F.y ∧
    2 * h.z = E.z - F.z

/-- Lemma 2.2: both lifted midpoint halves are integral and have odd third
coordinate.
@isnad1 id=ex.1h3v.s5.a766498d9012 from=translated src=- shape=b87f401f vocab=e1a6caa2
-/
theorem midpoint_parity {n : ℤ} (hn : Odd n) (s : BOddRep n) (t : ARep n) :
    ∃ hPlus hMinus : Triple,
      IsHalfSum hPlus (bLift s) (aLift t) ∧ Odd hPlus.z ∧
      IsHalfDiff hMinus (bLift s) (aLift t) ∧ Odd hMinus.z := by
  obtain ⟨sy, hsy⟩ := odd_y_of_bOdd hn s
  obtain ⟨ty, hty⟩ := odd_y_of_aRep hn t
  obtain ⟨sz, hsz⟩ := s.2.2
  rcases lifted_first_coordinates_same_parity hn s t with hEven | hOdd
  · obtain ⟨⟨sx, hsx⟩, ⟨tx, htx⟩⟩ := hEven
    refine ⟨⟨sx + tx, sy + ty + 1, s.1.z + 2 * t.1.z⟩,
      ⟨sx - tx, sy - ty, s.1.z - 2 * t.1.z⟩, ?_, ?_, ?_, ?_⟩
    · constructor
      · dsimp [IsHalfSum, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz + t.1.z, ?_⟩
      dsimp
      omega
    · constructor
      · dsimp [IsHalfDiff, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz - t.1.z, ?_⟩
      dsimp
      omega
  · obtain ⟨⟨sx, hsx⟩, ⟨tx, htx⟩⟩ := hOdd
    refine ⟨⟨sx + tx + 1, sy + ty + 1, s.1.z + 2 * t.1.z⟩,
      ⟨sx - tx, sy - ty, s.1.z - 2 * t.1.z⟩, ?_, ?_, ?_, ?_⟩
    · constructor
      · dsimp [IsHalfSum, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz + t.1.z, ?_⟩
      dsimp
      omega
    · constructor
      · dsimp [IsHalfDiff, bLift, aLift]
        omega
      · constructor <;> dsimp [bLift, aLift] <;> omega
    · refine ⟨sz - t.1.z, ?_⟩
      dsimp
      omega

/--
@isnad1 id=ne.1h1v.s4.f2773565ae88 from=translated src=- shape=b6f7e32d vocab=2e5522ae
-/
theorem odd_third_ne_zero {p : Triple} (hp : Odd p.z) : p ≠ ⟨0, 0, 0⟩ := by
  intro h
  have hz : p.z = 0 := congrArg Triple.z h
  rw [hz] at hp
  exact Int.not_odd_zero hp

end TunnellMap
