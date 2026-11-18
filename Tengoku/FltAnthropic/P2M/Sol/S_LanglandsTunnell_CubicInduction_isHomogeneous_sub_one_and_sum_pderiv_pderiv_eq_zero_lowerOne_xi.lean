import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_isHomogeneous_sub_one_and_sum_pderiv_pderiv_eq_zero_lowerOne_xi

set_option autoImplicit false

namespace WsC
namespace L1H

open MvPolynomial

noncomputable section

abbrev R3 := MvPolynomial (Fin 3) ℂ

/--
@isnad1 id=eq.0h3v.s10.75ebde12ccb0 from=translated src=- shape=45deb343 vocab=e550fc87
-/
theorem pderiv_comm (i j : Fin 3) (p : R3) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  have h : ⁅(pderiv i : Derivation ℂ R3 R3), (pderiv j : Derivation ℂ R3 R3)⁆ = 0 := by
    refine MvPolynomial.derivation_ext (fun k => ?_)
    rw [Derivation.commutator_apply]
    classical
    simp only [pderiv_X, Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ R3 R3 => D p) h
  simp only [Derivation.commutator_apply] at h2
  have h3 : pderiv i (pderiv j p) - pderiv j (pderiv i p) = 0 := by simpa using h2
  exact sub_eq_zero.mp h3

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
@isnad1 id=eq.0h1v.s11.be92e6dd9241 from=translated src=- shape=a14e4ad4 vocab=f9c71b2d
-/
theorem Lap_eq (q : R3) :
    Lap q = pderiv 0 (pderiv 0 q) + pderiv 1 (pderiv 1 q) + pderiv 2 (pderiv 2 q) := by
  simp [Lap, Fin.sum_univ_three]

/--
@isnad1 id=eq.0h2v.s6.1dda4007b018 from=translated src=- shape=a13ca989 vocab=3d31a6e9
-/
theorem Lap_add (q r : R3) : Lap (q + r) = Lap q + Lap r := by
  simp only [Lap_eq, map_add]; ring

/--
@isnad1 id=eq.0h2v.s6.91a182471d45 from=translated src=- shape=a13ca989 vocab=bd1a6b03
-/
theorem Lap_sub (q r : R3) : Lap (q - r) = Lap q - Lap r := by
  simp only [Lap_eq, map_sub]; ring

/--
@isnad1 id=eq.0h1v.s5.f3b925831ff1 from=translated src=- shape=c7188113 vocab=ac5c6666
-/
theorem Lap_neg (q : R3) : Lap (-q) = -Lap q := by
  simp only [Lap_eq, map_neg]; ring

/--
@isnad1 id=eq.0h0v.s6.193df03ca655 from=translated src=- shape=3c26ae4f vocab=cddf54c0
-/
theorem Lap_zero : Lap 0 = 0 := by
  simp [Lap_eq]

/--
@isnad1 id=eq.0h2v.s8.f9ab23faa659 from=translated src=- shape=16d38daa vocab=b3f10ee9
-/
theorem Lap_C_mul (k : ℂ) (q : R3) : Lap (C k * q) = C k * Lap q := by
  simp only [Lap_eq, pderiv_mul, pderiv_C, zero_mul, zero_add]; ring

/--
@isnad1 id=eq.0h3v.s5.7434eda6f3e5 from=translated src=- shape=e0c2d2cf vocab=013ec776
-/
theorem Lap_sum {ι : Type} (s : Finset ι) (f : ι → R3) :
    Lap (∑ i ∈ s, f i) = ∑ i ∈ s, Lap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lap_add, ih]

/--
@isnad1 id=eq.0h2v.s9.22449deab8d9 from=translated src=- shape=0e1f1900 vocab=52a7f07f
-/
theorem Lap_pderiv (j : Fin 3) (q : R3) : Lap (pderiv j q) = pderiv j (Lap q) := by
  simp only [Lap_eq, map_add]
  rw [pderiv_comm 0 j, pderiv_comm 0 j, pderiv_comm 1 j, pderiv_comm 1 j, pderiv_comm 2 j,
    pderiv_comm 2 j]

/--
@isnad1 id=eq.0h2v.s9.e20f3262d62c from=translated src=- shape=550fa07f vocab=2fe9b15d
-/
theorem Lap_X_mul (c : Fin 3) (q : R3) : Lap (X c * q) = X c * Lap q + C 2 * pderiv c q := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  rcases hc with rfl | rfl | rfl <;>
  · simp only [Lap_eq, pderiv_mul, pderiv_X_self, pderiv_X_of_ne ne01, pderiv_X_of_ne ne10,
      pderiv_X_of_ne ne02, pderiv_X_of_ne ne20, pderiv_X_of_ne ne12, pderiv_X_of_ne ne21,
      map_add, map_zero, Derivation.map_one_eq_zero, pderiv_one, zero_mul, one_mul, zero_add,
      add_zero, map_ofNat]
    ring

/--
@isnad1 id=eq.1h3v.s10.c1cb188d3bc6 from=translated src=- shape=16ca2df0 vocab=9197f575
-/
theorem Lap_rot (i j : Fin 3) (p : R3) (hp : Lap p = 0) :
    Lap (X i * pderiv j p - X j * pderiv i p) = 0 := by
  rw [Lap_sub, Lap_X_mul, Lap_X_mul, Lap_pderiv, Lap_pderiv, hp, map_zero, map_zero, mul_zero,
    mul_zero, zero_add, zero_add, pderiv_comm i j, sub_self]

def Xi (ν : Fin 3 → ℂ) (p : R3) : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
  Matrix.of fun c d =>
    if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
    else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
      MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)

def eps (a c d : Fin 3) : ℂ :=
  (((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
    (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2

/--
@isnad1 id=eq.0h3v.s5.f1ac4cc97880 from=translated src=- shape=bad0fcb8 vocab=9821b92f
-/
theorem eps_swap (a c d : Fin 3) : eps a d c = -eps a c d := by
  unfold eps; ring

def lower1 (M : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ)) : MvPolynomial (Fin 3) ℂ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
    MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
      (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
      (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))

/--
@isnad1 id=eq.0h1v.s10.612fdac94129 from=translated src=- shape=ff4953e7 vocab=0fcf0b8d
-/
theorem lower1_eq (M : Matrix (Fin 3) (Fin 3) R3) :
    lower1 M = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
      C (eps a c d) * (X c * pderiv b (pderiv d (M a b))) := rfl

/--
@isnad1 id=eq.1h4v.s6.888fdebe2cb8 from=translated src=- shape=fa580ca7 vocab=08ba88ff
-/
theorem Xi_harm (ν : Fin 3 → ℂ) (p : R3) (hp : Lap p = 0) (c d : Fin 3) :
    Lap (Xi ν p c d) = 0 := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · rw [Lap_C_mul, hp, mul_zero]
  · rw [Lap_neg, Lap_rot _ _ _ hp, neg_zero]

/--
@isnad1 id=eq.1h5v.s11.93381f3c5fa3 from=translated src=- shape=e48915bb vocab=1fa51089
-/
theorem Lap_term (e : ℂ) (c b d : Fin 3) (m : R3) (hm : Lap m = 0) :
    Lap (C e * (X c * pderiv b (pderiv d m))) = C e * (C 2 * pderiv c (pderiv b (pderiv d m))) := by
  rw [Lap_C_mul, Lap_X_mul, Lap_pderiv, Lap_pderiv, hm, map_zero, map_zero, mul_zero, zero_add]

/--
@isnad1 id=eq.0h4v.s11.ca163563d2d7 from=translated src=- shape=a281f262 vocab=e550fc87
-/
theorem T_symm (c b d : Fin 3) (m : R3) :
    pderiv c (pderiv b (pderiv d m)) = pderiv d (pderiv b (pderiv c m)) := by
  rw [pderiv_comm b d, pderiv_comm c d, pderiv_comm c b]

/--
@isnad1 id=eq.1h1v.s6.088250c32fcc from=translated src=- shape=40a0812c vocab=2b774b56
-/
theorem lower1_harm (M : Matrix (Fin 3) (Fin 3) R3) (hM : ∀ a b, Lap (M a b) = 0) :
    Lap (lower1 M) = 0 := by
  rw [lower1_eq, Lap_sum]
  apply Finset.sum_eq_zero
  intro a _
  rw [Lap_sum]
  apply Finset.sum_eq_zero
  intro b _
  rw [Lap_sum]
  simp_rw [Lap_sum, Lap_term _ _ _ _ _ (hM a b)]

  set S := ∑ c : Fin 3, ∑ d : Fin 3, C (eps a c d) * (C 2 * pderiv c (pderiv b (pderiv d (M a b))))
    with hS
  have hneg : S = -S := by
    conv_lhs => rw [hS, Finset.sum_comm]
    rw [hS, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [eps_swap a d c, T_symm c b d, map_neg, neg_mul]
  have h2 : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    nth_rewrite 2 [hneg]
    exact add_neg_cancel S
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

/--
@isnad1 id=ishomoge.1h5v.s9.acf2e6ee7a6c from=translated src=- shape=0091f3aa vocab=e1789483
-/
theorem X_mul_pderiv_pderiv_isHomogeneous {q : R3} {n : ℕ} (hq : q.IsHomogeneous n)
    (c b d : Fin 3) : (X c * pderiv b (pderiv d q)).IsHomogeneous (n - 1) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : (pderiv d q).IsHomogeneous 0 := by
      have := hq.pderiv (i := d)
      rwa [show n - 1 = 0 by omega] at this
    rw [← totalDegree_zero_iff_isHomogeneous, totalDegree_eq_zero_iff_eq_C] at h1
    rw [h1, pderiv_C, mul_zero]
    apply isHomogeneous_zero
  · have := (isHomogeneous_X ℂ c).mul ((hq.pderiv (i := d)).pderiv (i := b))
    rwa [show 1 + (n - 1 - 1) = n - 1 by omega] at this

/--
@isnad1 id=ishomoge.1h4v.s8.c42c7a704a14 from=translated src=- shape=b7e5395a vocab=4853d3b9
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
@isnad1 id=ishomoge.1h5v.s5.7b22d43a67c4 from=translated src=- shape=c81d1217 vocab=9dc4e5f3
-/
theorem Xi_isHomogeneous (ν : Fin 3 → ℂ) {p : R3} {ℓ : ℕ} (hp : p.IsHomogeneous ℓ) (c d : Fin 3) :
    (Xi ν p c d).IsHomogeneous ℓ := by
  unfold Xi
  rw [Matrix.of_apply]
  split_ifs with h
  · exact hp.C_mul _
  · exact ((X_mul_pderiv_isHomogeneous hp _ _).sub (X_mul_pderiv_isHomogeneous hp _ _)).neg

/--
@isnad1 id=and.2h3v.s10.d5d79100e2ff from=translated src=- shape=11f383f0 vocab=f1d75723
-/
theorem main (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    (lower1 (Xi ν p)).IsHomogeneous (ℓ - 1) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower1 (Xi ν p)))) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [lower1_eq]
    refine IsHomogeneous.sum _ _ _ (fun a _ => IsHomogeneous.sum _ _ _ (fun b _ =>
      IsHomogeneous.sum _ _ _ (fun c _ => IsHomogeneous.sum _ _ _ (fun d _ => ?_))))
    exact (X_mul_pderiv_pderiv_isHomogeneous (Xi_isHomogeneous ν hp a b) c b d).C_mul _
  · have hp0 : Lap p = 0 := hharm
    have := lower1_harm (Xi ν p) (Xi_harm ν p hp0)
    exact this

end

end WsC.L1H

open WsC.L1H in
/--
@isnad1 id=other.2h3v.s12.a88fb03222ea from=translated src=- shape=5659b2e5 vocab=e4514247
-/
theorem solution
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₁ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ∑ d : Fin 3,
        MvPolynomial.C ((((a : ℕ) : ℂ) - ((c : ℕ) : ℂ)) * (((c : ℕ) : ℂ) - ((d : ℕ) : ℂ)) *
          (((d : ℕ) : ℂ) - ((a : ℕ) : ℂ)) / 2) *
          (MvPolynomial.X c * MvPolynomial.pderiv b (MvPolynomial.pderiv d (M a b)))
    (lower₁ (Ξ ν p)).IsHomogeneous (ℓ - 1) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower₁ (Ξ ν p)))) = 0 := by
  exact WsC.L1H.main ν ℓ p hp hharm
