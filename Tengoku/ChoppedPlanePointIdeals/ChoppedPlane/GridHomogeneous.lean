module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Grid
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Points
public import Tengoku.Seed.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Tengoku.Seed.RingTheory.MvPolynomial.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

noncomputable section
set_option maxHeartbeats 800000

namespace ChoppedPlane.Grid

open MvPolynomial
variable {K : Type*} [Field K]

/-- The homogeneous product of the grid's vertical-line equations.-/
def planeFirst {d : ℕ} (α : Fin d → K) : Poly K 3 :=
  ∏ i, (X 0 - C (α i) * X 2)

/-- The homogeneous product of the grid's horizontal-line equations.-/
def planeSecond {d : ℕ} (β : Fin d → K) : Poly K 3 :=
  ∏ i, (X 1 - C (β i) * X 2)

/--
@isnad1 id=ishomoge.0h3v.s4.2d2334e65bf4 from=translated src=- shape=9fcc3f6a vocab=84e859e2
-/
theorem planeFirst_homogeneous {d : ℕ} (α : Fin d → K) :
    (planeFirst α).IsHomogeneous d := by
  classical
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, planeFirst] using
    IsHomogeneous.prod (Finset.univ : Finset (Fin d))
      (fun i => X 0 - C (α i) * X 2) (fun _ => 1)
      (fun i _ => (isHomogeneous_X K 0).sub (isHomogeneous_C_mul_X (α i) 2))

/--
@isnad1 id=ishomoge.0h3v.s4.6068c5ced96a from=translated src=- shape=9fcc3f6a vocab=6186f5c4
-/
theorem planeSecond_homogeneous {d : ℕ} (β : Fin d → K) :
    (planeSecond β).IsHomogeneous d := by
  classical
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one, planeSecond] using
    IsHomogeneous.prod (Finset.univ : Finset (Fin d))
      (fun i => X 1 - C (β i) * X 2) (fun _ => 1)
      (fun i _ => (isHomogeneous_X K 1).sub (isHomogeneous_C_mul_X (β i) 2))

/-- The degree-`d` first equation, in the genuine homogeneous space.-/
def firstForm {d : ℕ} (α : Fin d → K) : Forms K 3 d :=
  ⟨planeFirst α, planeFirst_homogeneous α⟩

/-- The degree-`d` second equation, in the genuine homogeneous space.-/
def secondForm {d : ℕ} (β : Fin d → K) : Forms K 3 d :=
  ⟨planeSecond β, planeSecond_homogeneous β⟩

/--
@isnad1 id=eq.0h5v.s8.62f1e7e90dac from=translated src=- shape=7c36319c vocab=4eac49eb
-/
@[simp] theorem planeFirst_eval {d : ℕ} (α : Fin d → K) (a b : K) :
    eval ![a,b,1] (planeFirst α) = (coordinatePolynomial α).eval a := by
  classical
  simp [planeFirst, coordinatePolynomial, Polynomial.eval_prod]

/--
@isnad1 id=eq.0h5v.s8.28875d8103fc from=translated src=- shape=bdce0c84 vocab=432a376f
-/
@[simp] theorem planeSecond_eval {d : ℕ} (β : Fin d → K) (a b : K) :
    eval ![a,b,1] (planeSecond β) = (coordinatePolynomial β).eval b := by
  classical
  simp [planeSecond, coordinatePolynomial, Polynomial.eval_prod]

/--
@isnad1 id=eq.0h3v.s8.0f4f3da036ab from=translated src=- shape=19500868 vocab=24074547
-/
@[simp] theorem planeFirst_eval_infinity {d : ℕ} (α : Fin d → K) :
    eval ![1,0,0] (planeFirst α) = 1 := by
  classical
  simp [planeFirst]

/--
@isnad1 id=eq.0h3v.s8.39ea86815091 from=translated src=- shape=19500868 vocab=72f372cb
-/
@[simp] theorem planeSecond_eval_infinity {d : ℕ} (β : Fin d → K) :
    eval ![0,1,0] (planeSecond β) = 1 := by
  classical
  simp [planeSecond]

/-- Neither grid equation is the zero polynomial.
@isnad1 id=ne.0h3v.s6.2924f4ea0643 from=translated src=- shape=7e073886 vocab=43922c30
-/
theorem planeFirst_ne_zero {d : ℕ} (α : Fin d → K) : planeFirst α ≠ 0 := by
  intro h
  have := planeFirst_eval_infinity α
  simp [h] at this

/--
@isnad1 id=ne.0h3v.s6.5cb6dad29034 from=translated src=- shape=7e073886 vocab=84c30010
-/
theorem planeSecond_ne_zero {d : ℕ} (β : Fin d → K) : planeSecond β ≠ 0 := by
  intro h
  have := planeSecond_eval_infinity β
  simp [h] at this

/-- Every vertical-line factor is irreducible, including when its scalar is zero.
@isnad1 id=irreduci.0h2v.s8.a0df2182b8e0 from=translated src=- shape=7d0bc0f3 vocab=e84608e2
-/
theorem first_linear_irreducible (a : K) :
    Irreducible (X 0 - C a * X 2 : Poly K 3) := by
  have h := irreducible_mul_X_add (1 : Poly K 3) (-C a * X 2) (0 : Fin 3)
    one_ne_zero (by simp) (by
      simp only [neg_mul, vars_neg]
      intro hz
      have hsub := vars_mul (C a : Poly K 3) (X 2) hz
      simp at hsub) isRelPrime_one_left
  simpa only [one_mul, sub_eq_add_neg, neg_mul] using h

/-- The first and second grid equations have no common nonunit factor.
@isnad1 id=isrelpri.0h4v.s6.2919703f865b from=translated src=- shape=8e9ed0ae vocab=aa6b5668
-/
theorem plane_equations_relPrime {d : ℕ} (α β : Fin d → K) :
    IsRelPrime (planeFirst α) (planeSecond β) := by
  classical
  apply IsRelPrime.prod_left
  intro i _
  apply (first_linear_irreducible (α i)).isRelPrime_iff_not_dvd.mpr
  intro h
  have he := map_dvd (eval ![0,1,0]) h
  simp only [map_sub, map_mul, eval_X, eval_C] at he
  simp at he

/-- Divisibility expresses that the second equation acts injectively modulo the
    principal ideal generated by the first.
@isnad1 id=dvd.1h5v.s8.50e1d0b3b0ed from=translated src=- shape=b30f4238 vocab=7dd09111
-/
theorem plane_regular_mod_first {d : ℕ} (α β : Fin d → K) (P : Poly K 3)
    (h : planeFirst α ∣ planeSecond β * P) : planeFirst α ∣ P :=
  (plane_equations_relPrime α β).dvd_of_dvd_mul_left h

end ChoppedPlane.Grid

namespace ChoppedPlane.Grid

open scoped Polynomial.Bivariate
variable {K : Type*} [Field K]

/-- Set the third homogeneous coordinate to one.-/
def dehom : Poly K 3 →+* K[X][Y] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.C Polynomial.X, Polynomial.X, 1]

/--
@isnad1 id=eq.0h4v.s8.e3f2e82dadbe from=translated src=- shape=e6e7aeff vocab=befbdeea
-/
@[simp] theorem dehom_eval (P : Poly K 3) (a b : K) :
    (dehom P).evalEval a b = MvPolynomial.eval ![a,b,1] P := by
  change (Polynomial.evalEvalRingHom a b) (dehom P) = _
  rw [dehom, MvPolynomial.map_eval₂Hom]
  have hcoeff : (Polynomial.evalEvalRingHom a b).comp
      (Polynomial.C.comp Polynomial.C) = RingHom.id K := by
    ext r
    simp
  rw [hcoeff]
  have hvar : (fun i : Fin 3 => (Polynomial.evalEvalRingHom a b)
      (![Polynomial.C Polynomial.X, Polynomial.X, 1] i)) = ![a,b,1] := by
    funext i
    fin_cases i <;> simp
  rw [hvar]
  rfl

/--
@isnad1 id=eq.0h3v.s8.d4ab82c9124f from=translated src=- shape=b452ad6e vocab=570e51fe
-/
@[simp] theorem dehom_first {d : ℕ} (α : Fin d → K) :
    dehom (planeFirst α) = firstEquation α := by
  classical
  simp [planeFirst, dehom, firstEquation, coordinatePolynomial]

/--
@isnad1 id=eq.0h3v.s8.c412f6434c9f from=translated src=- shape=b452ad6e vocab=6d22fde2
-/
@[simp] theorem dehom_second {d : ℕ} (β : Fin d → K) :
    dehom (planeSecond β) = secondEquation β := by
  classical
  simp [planeSecond, dehom, secondEquation, coordinatePolynomial, Polynomial.map_prod]

/-- Setting `z = 1` loses no information at a fixed homogeneous degree.
@isnad1 id=injectiv.0h2v.s10.123b8d92bb60 from=translated src=- shape=4bc43336 vocab=dcf0f75c
-/
theorem dehom_injective [Infinite K] {d : ℕ} :
    Function.Injective (fun f : Forms K 3 d => dehom f.val) := by
  intro f g hfg
  have hzero : f - g = 0 := by
    apply homogeneous_eq_zero_of_chart_evaluations
    intro a b
    have h := congrArg (fun P : K[X][Y] => P.evalEval a b) hfg
    simpa only [dehom_eval, Submodule.coe_sub, map_sub,
      sub_eq_zero] using h
  exact sub_eq_zero.mp hzero

/--
@isnad1 id=eq.0h5v.s9.e8d041c41a1a from=translated src=- shape=689f298c vocab=fdf09703
-/
@[simp] theorem dehom_monomial_coeff (e : Fin 3 →₀ ℕ) (r : K) (i j : ℕ) :
    ((dehom (MvPolynomial.monomial e r)).coeff j).coeff i =
      if j = e 1 ∧ i = e 0 then r else 0 := by
  classical
  have heq : dehom (MvPolynomial.monomial e r) =
      Polynomial.C (Polynomial.C r * Polynomial.X ^ e 0) * Polynomial.X ^ e 1 := by
    simp [dehom, MvPolynomial.eval₂Hom_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three, mul_assoc]
  rw [heq, Polynomial.coeff_C_mul_X_pow]
  by_cases hj : j = e 1
  · simp [hj]
  · simp [hj]

/-- Every homogeneous degree-`d` polynomial dehomogenizes to total degree at most `d`.
@isnad1 id=totaldeg.1h3v.s8.0a90e0339217 from=translated src=- shape=3adcad97 vocab=d83e527e
-/
theorem dehom_totalDegreeLE_aux {d : ℕ} (P : Poly K 3)
    (hP : P.IsHomogeneous d) : TotalDegreeLE d (dehom P) := by
  induction hP using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero =>
    intro i j hij
    simp
  | add p q hp hq ihp ihq =>
    intro i j hij
    simp only [map_add, Polynomial.coeff_add, ihp i j hij, ihq i j hij, zero_add]
  | monomial e r he =>
    intro i j hij
    rw [dehom_monomial_coeff]
    split_ifs with hij'
    · have hdeg : e 0 + e 1 + e 2 = d := by
        have he' : e.sum (fun _ c => c) = d := by
          simpa [Finsupp.weight_apply, smul_eq_mul] using he
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at he'
        simpa only [Fin.sum_univ_three] using he'
      omega
    · rfl

/-- The total-degree bound, specialized to the actual homogeneous subspace.
@isnad1 id=totaldeg.0h3v.s9.dc0a81f7719a from=translated src=- shape=05354ae5 vocab=1d1f685a
-/
theorem dehom_totalDegreeLE {d : ℕ} (f : Forms K 3 d) :
    TotalDegreeLE d (dehom f.val) := dehom_totalDegreeLE_aux f.val f.property

end ChoppedPlane.Grid

namespace ChoppedPlane.Grid
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K]

/--
@isnad1 id=eq.0h3v.s9.c851fbe2824d from=translated src=- shape=43989288 vocab=fce6718a
-/
@[simp] theorem dehom_smul (c : K) (P : Poly K 3) :
    dehom (c • P) = c • dehom P := by
  ext j i
  simp [dehom, MvPolynomial.smul_eq_C_mul, Polynomial.coeff_C_mul]

/-- Exact homogeneous form of the full-grid degree-`d` kernel.
@isnad1 id=iff.3h5v.s12.4f107c90bc7e from=translated src=- shape=6653c17c vocab=7545049e
-/
theorem grid_forms_kernel [Infinite K] {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) (f : Forms K 3 d) :
    (∀ i j, MvPolynomial.eval ![α i,β j,1] f.val = 0) ↔
      ∃ a b : K, f = a • firstForm α + b • secondForm β := by
  constructor
  · intro hv
    obtain ⟨a,b,hab⟩ := (grid_kernel hd α β hα hβ (dehom f.val)
      (dehom_totalDegreeLE f)).mp (by simpa only [dehom_eval] using hv)
    refine ⟨a,b,dehom_injective ?_⟩
    simpa only [Submodule.coe_add, Submodule.coe_smul, map_add, dehom_smul,
      firstForm, secondForm, dehom_first, dehom_second] using hab
  · rintro ⟨a,b,rfl⟩ i j
    simp [MvPolynomial.smul_eq_C_mul, firstForm, secondForm]

end ChoppedPlane.Grid
