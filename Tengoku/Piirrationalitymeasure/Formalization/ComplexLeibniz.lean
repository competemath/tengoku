import Tengoku.Piirrationalitymeasure.Formalization.ComplexDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Normalized Leibniz derivatives indexed by nonnegative tuples. -/

namespace PiIrrationality

theorem normalizedComplexDeriv_mul {n : ℕ} {f g : ℂ → ℂ} {x : ℂ}
    (hf : ContDiffAt ℂ n f x) (hg : ContDiffAt ℂ n g x) :
    normalizedComplexDeriv n (fun y => f y * g y) x =
      ∑ i ∈ Finset.range (n + 1),
        normalizedComplexDeriv i f x * normalizedComplexDeriv (n - i) g x := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_fun_mul hf hg]
  apply (div_eq_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))).2
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hchoose : (n.choose i : ℂ) * (i.factorial : ℂ) *
      ((n - i).factorial : ℂ) = (n.factorial : ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi'
  have hi0 : (i.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr i.factorial_ne_zero
  have hni0 : ((n - i).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - i).factorial_ne_zero
  field_simp [hi0, hni0]
  linear_combination iteratedDeriv i f x * iteratedDeriv (n - i) g x * hchoose

theorem sum_antidiagonalTuple_succ {A : Type*} [AddCommMonoid A]
    (r n : ℕ) (F : (Fin (r + 1) → ℕ) → A) :
    ∑ m ∈ Finset.Nat.antidiagonalTuple (r + 1) n, F m =
      ∑ i ∈ Finset.range (n + 1),
        ∑ m ∈ Finset.Nat.antidiagonalTuple r (n - i), F (Fin.cons i m) := by
  classical
  rw [← Finset.sum_sigma (Finset.range (n + 1))
    (fun i => Finset.Nat.antidiagonalTuple r (n - i))
    (fun p => F (Fin.cons p.1 p.2))]
  symm
  refine Finset.sum_bij (fun p _ => Fin.cons p.1 p.2) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp, hm⟩ := Finset.mem_sigma.mp hp
    have hi : p.1 ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
    rw [Finset.Nat.mem_antidiagonalTuple, Fin.sum_cons,
      Finset.Nat.mem_antidiagonalTuple.mp hm, Nat.add_sub_of_le hi]
  · intro p hp q hq he
    have hhead := congrFun he 0
    have htail : p.2 = q.2 := by
      funext i
      exact congrFun he i.succ
    have hfirst : p.1 = q.1 := hhead
    exact Sigma.ext hfirst (heq_of_eq htail)
  · intro m hm
    have hs := Finset.Nat.mem_antidiagonalTuple.mp hm
    rw [Fin.sum_univ_succ] at hs
    refine ⟨⟨m 0, Fin.tail m⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma, Finset.mem_range, Finset.Nat.mem_antidiagonalTuple]
      dsimp [Fin.tail]
      constructor <;> omega
    · exact Fin.cons_self_tail m
  · intro p hp
    rfl

theorem normalizedComplexDeriv_fin_prod (r n : ℕ) (f : Fin r → ℂ → ℂ) (x : ℂ)
    (hf : ∀ i, ContDiffAt ℂ n (f i) x) :
    normalizedComplexDeriv n (fun y => ∏ i, f i y) x =
      ∑ m ∈ Finset.Nat.antidiagonalTuple r n,
        ∏ i, normalizedComplexDeriv (m i) (f i) x := by
  induction r generalizing n with
  | zero =>
      cases n <;> simp [normalizedComplexDeriv, iteratedDeriv_const,
        Finset.Nat.antidiagonalTuple_zero_zero,
        Finset.Nat.antidiagonalTuple_zero_succ]
  | succ r ih =>
      simp_rw [Fin.prod_univ_succ]
      rw [normalizedComplexDeriv_mul (hf 0) (by fun_prop),
        sum_antidiagonalTuple_succ]
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih (n - i) (fun j => f j.succ)
        (fun j => (hf j.succ).of_le (by exact_mod_cast Nat.sub_le n i)),
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      simp

theorem normalizedComplexDeriv_add_power (k m : ℕ) (a x : ℂ) :
    normalizedComplexDeriv k (fun t : ℂ => (t + a) ^ m) x =
      (m.choose k : ℂ) * (x + a) ^ (m - k) := by
  unfold normalizedComplexDeriv
  rw [iteratedDeriv_comp_add_const k (fun t : ℂ => t ^ m) a]
  dsimp only
  rw [iteratedDeriv_pow, Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr k.factorial_ne_zero]

end PiIrrationality
