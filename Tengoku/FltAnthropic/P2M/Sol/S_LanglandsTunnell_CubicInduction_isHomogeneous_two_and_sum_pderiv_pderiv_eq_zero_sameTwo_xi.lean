import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_two_and_sum_pderiv_pderiv_eq_zero_sameTwo_xi

set_option autoImplicit false

namespace WsC
namespace S2H

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ

/--
@isnad1 id=ne.0h0v.s5.a12388f0aca2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
/--
@isnad1 id=ne.0h0v.s5.9556c64377c8 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.93abf1c8e128 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.d0ddbab9dc92 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.1e882522a86f from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.7b05c920c4d2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

def Lap (q : R3) : R3 := ∑ i : Fin 3, pderiv i (pderiv i q)

/--
@isnad1 id=eq.0h1v.s11.bf09aeb20cb7 from=translated src=- shape=a14e4ad4 vocab=1ac781a2
-/
theorem Lap_eq (q : R3) :
    Lap q = pderiv 0 (pderiv 0 q) + pderiv 1 (pderiv 1 q) + pderiv 2 (pderiv 2 q) := by
  simp [Lap, Fin.sum_univ_three]

/--
@isnad1 id=eq.0h2v.s6.14da9f710579 from=translated src=- shape=a13ca989 vocab=cc089af1
-/
theorem Lap_sub (q r : R3) : Lap (q - r) = Lap q - Lap r := by
  simp only [Lap_eq, map_sub]; ring

/--
@isnad1 id=eq.0h2v.s8.1593ae585938 from=translated src=- shape=16d38daa vocab=d27a3bde
-/
theorem Lap_C_mul (k : ℂ) (q : R3) : Lap (C k * q) = C k * Lap q := by
  simp only [Lap_eq, pderiv_mul, pderiv_C, zero_mul, zero_add]; ring

def rsq : R3 := ∑ i : Fin 3, MvPolynomial.X i ^ 2

/--
@isnad1 id=eq.0h0v.s6.9b781f65cf69 from=translated src=- shape=a51ea84e vocab=6faf209d
-/
theorem Lap_rsq : Lap rsq = C 6 := by
  simp only [rsq, Lap_eq, Fin.sum_univ_three, pow_two, map_add, pderiv_mul, pderiv_X_self,
    pderiv_X_of_ne ne01, pderiv_X_of_ne ne10, pderiv_X_of_ne ne02, pderiv_X_of_ne ne20,
    pderiv_X_of_ne ne12, pderiv_X_of_ne ne21, pderiv_one, Derivation.map_one_eq_zero,
    mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, map_ofNat]
  norm_num

/--
@isnad1 id=ishomoge.0h0v.s3.c94ebd548cdd from=translated src=- shape=8067f6a0 vocab=a5fc8339
-/
theorem rsq_isHomogeneous : rsq.IsHomogeneous 2 := by
  unfold rsq
  refine IsHomogeneous.sum _ _ _ (fun i _ => ?_)
  exact (isHomogeneous_X ℂ i).pow 2

def Xi (ν : Fin 3 → ℂ) (p : R3) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

def E (M : Matrix (Fin 3) (Fin 3) R3) : R3 :=
  ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)

def same2 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
    (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
        (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))

/--
@isnad1 id=eq.0h1v.s8.702691648b57 from=translated src=- shape=808bc8d1 vocab=139a9003
-/
theorem same2_eq (M : Matrix (Fin 3) (Fin 3) R3) :
    same2 M = C 6 * E M - rsq * Lap (E M) := rfl

/--
@isnad1 id=ishomoge.1h4v.s8.d7b9255e06b4 from=translated src=- shape=b7e5395a vocab=8e0d2502
-/
theorem X_mul_pderiv_isHomogeneous {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (a b : Fin 3) :
    (X a * pderiv b p).IsHomogeneous ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with h | h
  · subst h
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hp
    rw [hp, pderiv_C, mul_zero]
    apply isHomogeneous_zero
  · have := (isHomogeneous_X ℂ a).mul (hp.pderiv (i := b))
    rwa [show 1 + (ℓ - 1) = ℓ by omega] at this

/--
@isnad1 id=ishomoge.1h5v.s5.7ea918f0ec4d from=translated src=- shape=c81d1217 vocab=51c5e0cb
-/
theorem Xi_isHomogeneous (ν : Fin 3 → ℂ) {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (c d : Fin 3) :
    (Xi ν p c d).IsHomogeneous ℓ := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · exact hp.C_mul _
  · exact ((X_mul_pderiv_isHomogeneous hp _ _).sub (X_mul_pderiv_isHomogeneous hp _ _)).neg

/--
@isnad1 id=ishomoge.1h2v.s5.1e393777ca20 from=translated src=- shape=f4815470 vocab=b5726904
-/
theorem E_isHomogeneous {M : Matrix (Fin 3) (Fin 3) R3} {ℓ : ℕ}
    (hM : ∀ c d, (M c d).IsHomogeneous ℓ) : (E M).IsHomogeneous ℓ := by
  unfold E
  refine IsHomogeneous.sum _ _ _ (fun c _ => IsHomogeneous.sum _ _ _ (fun d _ => ?_))
  exact X_mul_pderiv_isHomogeneous (hM c d) c d

/--
@isnad1 id=ishomoge.1h2v.s5.1cf8c2ba6bc4 from=translated src=- shape=641aecfa vocab=9de1e686
-/
theorem Lap_isHomogeneous {q : R3} {n : ℕ} (hq : q.IsHomogeneous n) :
    (Lap q).IsHomogeneous (n - 2) := by
  unfold Lap
  refine IsHomogeneous.sum _ _ _ (fun i _ => ?_)
  rw [show n - 2 = n - 1 - 1 by omega]
  exact (hq.pderiv (i := i)).pderiv (i := i)

/--
@isnad1 id=and.1h1v.s6.19c0687871ff from=translated src=- shape=051e5371 vocab=ed9ff1c0
-/
theorem same2_main (M : Matrix (Fin 3) (Fin 3) R3) (hM : ∀ c d, (M c d).IsHomogeneous 2) :
    (same2 M).IsHomogeneous 2 ∧ Lap (same2 M) = 0 := by
  have hE : (E M).IsHomogeneous 2 := E_isHomogeneous hM
  have hL0 : (Lap (E M)).IsHomogeneous 0 := Lap_isHomogeneous hE
  have hL : Lap (E M) = C ((Lap (E M)).coeff 0) := by
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at hL0
    exact hL0
  refine ⟨?_, ?_⟩
  · rw [same2_eq]
    refine (hE.C_mul _).sub ?_
    have := rsq_isHomogeneous.mul hL0
    exact this
  · rw [same2_eq, Lap_sub, Lap_C_mul, hL, mul_comm rsq, Lap_C_mul, Lap_rsq, mul_comm, sub_self]

/--
@isnad1 id=and.2h2v.s10.6ac1b14d5093 from=translated src=- shape=aa3fb6c4 vocab=a25d0fa1
-/
theorem main (ν : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 2)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    (same2 (Xi ν p)).IsHomogeneous 2 ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (same2 (Xi ν p)))) = 0 :=
  same2_main (Xi ν p) (Xi_isHomogeneous ν hp)

end

end WsC.S2H

open WsC.S2H in
/--
@isnad1 id=other.2h2v.s12.1b2f15f21712 from=translated src=- shape=deddc31f vocab=51de80ee
-/
theorem solution
    (ν : Fin 3 → ℂ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous 2)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let same₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => MvPolynomial.C (6 : ℂ) * (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d)) -
        (∑ i : Fin 3, MvPolynomial.X i ^ 2) *
          (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i
            (∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.X c * MvPolynomial.pderiv d (M c d))))
    (same₂ (Ξ ν p)).IsHomogeneous 2 ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (same₂ (Ξ ν p)))) = 0 := by
  exact WsC.S2H.main ν p hp hharm
