import Tengoku.Hellingerrepolean4.Hellinger.QuadraticDual
import Tengoku.Seed.Algebra.MvPolynomial.NoZeroDivisors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms walsh_family` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms family_bent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms family_mean` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms anf_eval` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms anf_totalDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms anf_multilinear` (it only prints; the queue checks the axioms of every declaration). -/

/-! The explicit Maiorana–McFarland family in the unbounded-degree remark.
Its Walsh transform is the actual normalized transform on a 2k-dimensional
Boolean cube, and its phase is a multilinear polynomial over F₂. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.MaioranaMcFarland

open Fourier F2Model ChannelSections

def halves (k : ℕ) : Fourier.Cube (k + k) ≃ Fourier.Cube k × Fourier.Cube k :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) Bool)

def highSign {k : ℕ} (y : Fourier.Cube k) : ℝ := sign (∏ i, bitEquiv (y i))

def pairFunction {k : ℕ} (p : Fourier.Cube k × Fourier.Cube k) : ℝ :=
  Fourier.phase p.1 p.2 * highSign p.2

def family (k : ℕ) : Fourier.Cube (k + k) → ℝ := pairFunction ∘ halves k

/--
@isnad1 id=eq.0h3v.s8.837b6bc2d917 from=translated src=- shape=69faefc2 vocab=c15d9d0d
-/
theorem phase_halves {k : ℕ} (s x : Fourier.Cube (k + k)) :
    Fourier.phase s x = Fourier.phase (halves k s).1 (halves k x).1 *
      Fourier.phase (halves k s).2 (halves k x).2 := by
  unfold Fourier.phase
  rw [← finSumFinEquiv.prod_comp (fun i : Fin (k + k) => boolSign (s i && x i))]
  rw [Fintype.prod_sum_type]
  rfl

/--
@isnad1 id=eq.0h3v.s7.a69ec40ee635 from=translated src=- shape=de76ba00 vocab=ea0f3189
-/
theorem pair_walsh {k : ℕ} (s t : Fourier.Cube k) :
    mean (fun p : Fourier.Cube k × Fourier.Cube k =>
      pairFunction p * Fourier.phase s p.1 * Fourier.phase t p.2) =
        ((2 : ℝ) ^ k)⁻¹ * highSign s * Fourier.phase t s := by
  rw [mean_prod_swap]
  have hinner (y : Fourier.Cube k) :
      mean (fun x => pairFunction (x, y) * Fourier.phase s x * Fourier.phase t y) =
        (if y = s then 1 else 0) * (highSign y * Fourier.phase t y) := by
    have heq (x : Fourier.Cube k) :
        pairFunction (x, y) * Fourier.phase s x * Fourier.phase t y =
          (Fourier.phase y x * Fourier.phase s x) * (highSign y * Fourier.phase t y) := by
      rw [pairFunction, Fourier.phase_symm x y]
      ring
    simp_rw [heq]
    rw [Fourier.mean_mul_const, Fourier.orthogonality]
  simp_rw [hinner]
  simp [mean, mul_assoc]

/--
@isnad1 id=eq.0h2v.s8.4a2c080e28cd from=translated src=- shape=cd6c606c vocab=b287c44b
-/
theorem walsh_family (k : ℕ) (v : Fourier.Cube (k + k)) :
    Fourier.walsh (family k) v = ((2 : ℝ) ^ k)⁻¹ *
      highSign (halves k v).1 * Fourier.phase (halves k v).2 (halves k v).1 := by
  unfold Fourier.walsh
  rw [← mean_comp_equiv (halves k).symm]
  change mean (fun p => family k ((halves k).symm p) *
    Fourier.phase v ((halves k).symm p)) = _
  have heq (p : Fourier.Cube k × Fourier.Cube k) :
      family k ((halves k).symm p) * Fourier.phase v ((halves k).symm p) =
        pairFunction p * Fourier.phase (halves k v).1 p.1 * Fourier.phase (halves k v).2 p.2 := by
    rw [phase_halves]
    simp only [family, Function.comp_apply, Equiv.apply_symm_apply]
    ring
  simp_rw [heq]
  exact pair_walsh _ _

/--
@isnad1 id=or.0h2v.s5.3a4020d6f05d from=translated src=- shape=6b35fc0f vocab=5a978cdf
-/
theorem family_boolean (k : ℕ) (x : Fourier.Cube (k + k)) :
    family k x = -1 ∨ family k x = 1 := by
  have hp := Fourier.phase_sq (halves k x).1 (halves k x).2
  have hs := QuadraticRadical.sign_sq (∏ i, bitEquiv ((halves k x).2 i))
  have h : family k x ^ 2 = 1 := by
    simp only [family, Function.comp_apply, pairFunction, highSign, mul_pow, hp, hs, one_mul]
  rcases sq_eq_one_iff.mp h with hx | hx
  · exact Or.inr hx
  · exact Or.inl hx

/--
@isnad1 id=isbent.0h1v.s3.f9c4fa3e2414 from=translated src=- shape=26a36036 vocab=c393f662
-/
theorem family_bent (k : ℕ) : Flatness.IsBent (family k) := by
  intro v
  rw [walsh_family, mul_pow, mul_pow, Fourier.phase_sq,
    show highSign (halves k v).1 ^ 2 = 1 from QuadraticRadical.sign_sq _]
  simp [pow_add, pow_two, mul_inv_rev]

/--
@isnad1 id=eq.1h1v.s6.cc6986ff678b from=translated src=- shape=72674841 vocab=0e101d06
-/
theorem family_mean (k : ℕ) (hk : 0 < k) : mean (family k) = ((2 : ℝ) ^ k)⁻¹ := by
  rw [← Fourier.walsh_zero, walsh_family]
  have hh : halves k (fun _ => false) = ((fun _ => false), (fun _ => false)) := rfl
  rw [hh]
  simp [highSign, Fourier.phase, boolSign, sign, Nat.ne_of_gt hk]

abbrev Variables (k : ℕ) := Fin k ⊕ Fin k

def quadraticPart (k : ℕ) : MvPolynomial (Variables k) F2 :=
  ∑ i, MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i)

def highPart (k : ℕ) : MvPolynomial (Variables k) F2 :=
  ∏ i, MvPolynomial.X (Sum.inr i)

def anf (k : ℕ) : MvPolynomial (Variables k) F2 := quadraticPart k + highPart k

/--
@isnad1 id=eq.0h3v.s8.1b59e0484ca1 from=translated src=- shape=eedce224 vocab=94fc6278
-/
theorem anf_eval (k : ℕ) (x y : Fourier.Cube k) :
    sign (MvPolynomial.eval (Sum.elim (fun i => bitEquiv (x i)) (fun i => bitEquiv (y i)))
      (anf k)) = pairFunction (x, y) := by
  simp only [anf, quadraticPart, highPart, map_add, map_sum, map_mul, map_prod,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, sign_add]
  rw [QuadraticDual.sign_sum]
  have hprod : (∏ i, sign (bitEquiv (x i) * bitEquiv (y i))) = Fourier.phase x y := by
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> cases y i <;> norm_num [sign, boolSign]
  exact congrArg (· * highSign y) hprod

/--
@isnad1 id=le.0h1v.s4.519ef7c1f0c9 from=translated src=- shape=dd8d1055 vocab=6233a5e8
-/
theorem quadraticPart_totalDegree (k : ℕ) : (quadraticPart k).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/--
@isnad1 id=eq.0h4v.s6.ef70bab3b52f from=translated src=- shape=43f09e87 vocab=61e099b5
-/
theorem prod_X_totalDegree {σ β : Type*} (s : Finset β) (j : β → σ) :
    (∏ i ∈ s, (MvPolynomial.X (j i) : MvPolynomial σ F2)).totalDegree = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr (fun _ _ => MvPolynomial.X_ne_zero _)),
      MvPolynomial.totalDegree_X, ih]
    omega

/--
@isnad1 id=eq.0h1v.s4.d5b3996c63e3 from=translated src=- shape=115f156b vocab=1734b602
-/
theorem highPart_totalDegree (k : ℕ) : (highPart k).totalDegree = k := by
  simpa [highPart] using prod_X_totalDegree (Finset.univ : Finset (Fin k)) Sum.inr

/--
@isnad1 id=eq.1h1v.s5.861ed6893fdb from=translated src=- shape=da261d76 vocab=e0678b96
-/
theorem anf_totalDegree (k : ℕ) (hk : 3 ≤ k) : (anf k).totalDegree = k := by
  rw [anf, MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt, highPart_totalDegree]
  rw [highPart_totalDegree]
  exact lt_of_le_of_lt (quadraticPart_totalDegree k) (by omega)

/-- Every exponent is at most one, so this is the multilinear algebraic normal form.
@isnad1 id=le.0h2v.s4.3af6bb19bb23 from=translated src=- shape=8b510f90 vocab=61a567c3
-/
theorem anf_multilinear (k : ℕ) (v : Variables k) : (anf k).degreeOf v ≤ 1 := by
  apply (MvPolynomial.degreeOf_add_le v _ _).trans
  apply max_le
  · apply (MvPolynomial.degreeOf_sum_le v Finset.univ _).trans
    apply Finset.sup_le
    intro i _
    apply (MvPolynomial.degreeOf_mul_le v _ _).trans
    cases v with
    | inl j => simp [MvPolynomial.degreeOf_X]; split_ifs <;> omega
    | inr j => simp [MvPolynomial.degreeOf_X]; split_ifs <;> omega
  · apply (MvPolynomial.degreeOf_prod_le v Finset.univ _).trans
    cases v with
    | inl j => simp [MvPolynomial.degreeOf_X]
    | inr j => simp [MvPolynomial.degreeOf_X]

end Hellinger.MaioranaMcFarland
