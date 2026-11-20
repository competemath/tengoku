import Tengoku.CayleyBacharach.CayleyBacharach.Bridge
import Tengoku.CayleyBacharach.CayleyBacharach.CriterionIff
import Tengoku.CayleyBacharach.CayleyBacharach.PascalClean
import Tengoku.CayleyBacharach.CayleyBacharach.PappusClean

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Layer 14: Mathlib-only restatements and witnesses

Every `l14_*` theorem below has a statement mentioning only Mathlib notions: plane cubics,
conics and lines are homogeneous `MvPolynomial (Fin 3) K` of degree 3, 2, 1
(`MvPolynomial.IsHomogeneous`), points of `ℙ²(K)` are vectors `Fin 3 → K`, "distinct
projective points" is `LinearIndependent K ![u, v]`, vanishing is `MvPolynomial.eval`, common
components are factorisations `F = ℓ * q`, the space of cubics through points is
`homogeneousSubmodule ⊓ ⨅ ker (aeval Pᵢ)` and its dimension is `Module.finrank`, the field-size
hypotheses are stated with `Finset`/`Fintype.card`. Collinearity of three projective points
is `Matrix.det = 0` and the Pascal/Pappus points are Mathlib cross products `⨯₃`.
The `l14b_*` lemmas are the bridges to the library's coefficient-vector encodings; the
`l14w_*` theorems are explicit witnesses (non-vacuity).
-/
namespace Tengoku.CayleyBacharach end Tengoku.CayleyBacharach open Tengoku.CayleyBacharach
open MvPolynomial Matrix

namespace CBL14

variable {K : Type*} [Field K]

/-- Exponent of `X 0 ^ a * X 1 ^ b * X 2 ^ c`.-/
noncomputable def ex (a b c : ℕ) : Fin 3 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![a, b, c]

/--
@isnad1 id=eq.0h4v.s6.f0e4f67382db from=translated src=- shape=9817478f vocab=a7d2253a
-/
@[simp] theorem ex_apply (a b c : ℕ) (i : Fin 3) : ex a b c i = ![a, b, c] i := by
  simp [ex]

/--
@isnad1 id=eq.0h3v.s7.56c3914b048d from=translated src=- shape=10dd35f9 vocab=6f594dad
-/
theorem ex_degree (a b c : ℕ) : (ex a b c).degree = a + b + c := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]; simp

/--
@isnad1 id=iff.0h6v.s5.a645af54aff6 from=translated src=- shape=6fe97741 vocab=af9a8fbf
-/
theorem ex_inj {a b c a' b' c' : ℕ} : ex a b c = ex a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' := by
  constructor
  · intro h
    exact ⟨by simpa using congrArg (· 0) h, by simpa using congrArg (· 1) h,
      by simpa using congrArg (· 2) h⟩
  · rintro ⟨rfl, rfl, rfl⟩; rfl

theorem eq_ex (d : Fin 3 →₀ ℕ) : d = ex (d 0) (d 1) (d 2) := by
  ext i; fin_cases i <;> simp

/--
@isnad1 id=eq.0h1v.s8.13edbc762a2b from=translated src=- shape=768993fb vocab=57dd135f
-/
theorem degree_three (d : Fin 3 →₀ ℕ) : d.degree = d 0 + d 1 + d 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]

theorem eq_ex_of {d : Fin 3 →₀ ℕ} {a b c : ℕ} (h0 : d 0 = a) (h1 : d 1 = b) (h2 : d 2 = c) :
    d = ex a b c := by
  rw [eq_ex d, h0, h1, h2]

/--
@isnad1 id=eq.0h5v.s10.a03b68dce7df from=translated src=- shape=b3d52309 vocab=599fa676
-/
theorem monomial_ex (a b c : ℕ) (r : K) :
    monomial (ex a b c) r = C r * (X 0 ^ a * X 1 ^ b * X 2 ^ c) := by
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_three]
  simp [mul_assoc]

/-! Generic coefficient-vector ↔ polynomial map for an exponent table `E`. -/

section Generic

variable {n : ℕ} (E : Fin n → Fin 3 →₀ ℕ)

noncomputable def toP (c : Fin n → K) : MvPolynomial (Fin 3) K := ∑ i, monomial (E i) (c i)

/--
@isnad1 id=eq.1h5v.s6.d0570e433bbd from=translated src=- shape=96ffde76 vocab=92587240
-/
theorem coeff_toP (hE : Function.Injective E) (c : Fin n → K) (i : Fin n) :
    coeff (E i) (toP E c) = c i := by
  classical
  rw [toP, coeff_sum, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [coeff_monomial, ite_eq_right (fun h => hj (hE h))]
  · simp

/--
@isnad1 id=eq.0h5v.s7.1bc4b44dbe16 from=translated src=- shape=dc1e2fc1 vocab=a190c128
-/
theorem toP_add (c c' : Fin n → K) : toP E (c + c') = toP E c + toP E c' := by
  simp [toP, map_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h5v.s7.4dbc89eb175d from=translated src=- shape=035387f7 vocab=de953741
-/
theorem toP_smul (a : K) (c : Fin n → K) : toP E (a • c) = a • toP E c := by
  simp [toP, Finset.smul_sum, smul_monomial]

noncomputable def toPₗ : (Fin n → K) →ₗ[K] MvPolynomial (Fin 3) K where
  toFun := toP E
  map_add' := toP_add E
  map_smul' := toP_smul E

/--
@isnad1 id=injectiv.1h3v.s5.acf477d3e702 from=translated src=- shape=d09e39f3 vocab=3db60608
-/
theorem toP_injective (hE : Function.Injective E) : Function.Injective (toP (K := K) E) := by
  intro c c' h; funext i; rw [← coeff_toP E hE c i, ← coeff_toP E hE c' i, h]

/--
@isnad1 id=ishomoge.1h5v.s7.bf3e52a654af from=translated src=- shape=09dfabba vocab=b50c1c52
-/
theorem toP_isHomogeneous {k : ℕ} (hk : ∀ i, (E i).degree = k) (c : Fin n → K) :
    (toP E c).IsHomogeneous k :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_monomial _ (hk i)

theorem eq_toP {k : ℕ} (hE : Function.Injective E) (hk : ∀ i, (E i).degree = k)
    (hsurj : ∀ d : Fin 3 →₀ ℕ, d.degree = k → ∃ i, E i = d)
    {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous k) :
    p = toP E (fun i => coeff (E i) p) := by
  ext d
  by_cases hd : d.degree = k
  · obtain ⟨i, rfl⟩ := hsurj d hd
    rw [coeff_toP E hE]
  · rw [hp.coeff_eq_zero hd, (toP_isHomogeneous E hk _).coeff_eq_zero hd]

end Generic

/-! The three exponent tables, in the library's monomial orders. -/

noncomputable def E3 : Fin 10 → Fin 3 →₀ ℕ :=
  ![ex 3 0 0, ex 2 1 0, ex 2 0 1, ex 1 2 0, ex 1 1 1, ex 1 0 2, ex 0 3 0, ex 0 2 1, ex 0 1 2,
    ex 0 0 3]

noncomputable def E2 : Fin 6 → Fin 3 →₀ ℕ :=
  ![ex 2 0 0, ex 1 1 0, ex 1 0 1, ex 0 2 0, ex 0 1 1, ex 0 0 2]

noncomputable def E1 : Fin 3 → Fin 3 →₀ ℕ := ![ex 1 0 0, ex 0 1 0, ex 0 0 1]

/--
@isnad1 id=injectiv.0h0v.s4.19977f226d80 from=translated src=- shape=a6eb7227 vocab=e7a7aefd
-/
theorem E3_inj : Function.Injective E3 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [E3, ex_inj]

/--
@isnad1 id=injectiv.0h0v.s4.907c436a59ec from=translated src=- shape=a6eb7227 vocab=91fdd29e
-/
theorem E2_inj : Function.Injective E2 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [E2, ex_inj]

/--
@isnad1 id=injectiv.0h0v.s4.46a08137e49d from=translated src=- shape=a6eb7227 vocab=ee328f1a
-/
theorem E1_inj : Function.Injective E1 := by
  intro i j h; fin_cases i <;> fin_cases j <;> simp_all [E1, ex_inj]

/--
@isnad1 id=eq.0h1v.s7.f8c55c938e2a from=translated src=- shape=e7b23608 vocab=0c923c36
-/
theorem E3_deg (i : Fin 10) : (E3 i).degree = 3 := by
  fin_cases i <;> simp [E3, ex_degree]

/--
@isnad1 id=eq.0h1v.s7.8d6e5f9de816 from=translated src=- shape=e7b23608 vocab=60657e52
-/
theorem E2_deg (i : Fin 6) : (E2 i).degree = 2 := by
  fin_cases i <;> simp [E2, ex_degree]

/--
@isnad1 id=eq.0h1v.s7.c387761ebc0f from=translated src=- shape=e7b23608 vocab=221e8591
-/
theorem E1_deg (i : Fin 3) : (E1 i).degree = 1 := by
  fin_cases i <;> simp [E1, ex_degree]

/--
@isnad1 id=ex.1h1v.s7.65049468dada from=translated src=- shape=771e433d vocab=0c923c36
-/
theorem E3_surj (d : Fin 3 →₀ ℕ) (h : d.degree = 3) : ∃ i, E3 i = d := by
  rw [degree_three] at h
  rw [eq_ex d]
  generalize d 0 = a at *
  generalize d 1 = b at *
  generalize d 2 = c at *
  obtain rfl : c = 3 - a - b := by omega
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 - a := by omega
  interval_cases a <;> interval_cases b
  exacts [⟨9, rfl⟩, ⟨8, rfl⟩, ⟨7, rfl⟩, ⟨6, rfl⟩, ⟨5, rfl⟩, ⟨4, rfl⟩, ⟨3, rfl⟩, ⟨2, rfl⟩,
    ⟨1, rfl⟩, ⟨0, rfl⟩]

/--
@isnad1 id=ex.1h1v.s7.19db2fdf8c9c from=translated src=- shape=771e433d vocab=60657e52
-/
theorem E2_surj (d : Fin 3 →₀ ℕ) (h : d.degree = 2) : ∃ i, E2 i = d := by
  rw [degree_three] at h
  have : (d 0 = 2 ∧ d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 1 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 1) ∨ (d 0 = 0 ∧ d 1 = 2 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 1) ∨ (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 2) := by omega
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
    ⟨h0, h1, h2⟩ <;> rw [eq_ex_of h0 h1 h2]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩]

/--
@isnad1 id=ex.1h1v.s7.d286de9ef05b from=translated src=- shape=771e433d vocab=221e8591
-/
theorem E1_surj (d : Fin 3 →₀ ℕ) (h : d.degree = 1) : ∃ i, E1 i = d := by
  rw [degree_three] at h
  have : (d 0 = 1 ∧ d 1 = 0 ∧ d 2 = 0) ∨ (d 0 = 0 ∧ d 1 = 1 ∧ d 2 = 0) ∨
      (d 0 = 0 ∧ d 1 = 0 ∧ d 2 = 1) := by omega
  rcases this with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ <;> rw [eq_ex_of h0 h1 h2]
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]

/-! Explicit forms, evaluation and products. -/

/--
@isnad1 id=eq.0h2v.s12.e41a2cbce3b8 from=translated src=- shape=dfb668cb vocab=318d782c
-/
theorem toP3_eq (F : Fin 10 → K) : toP E3 F =
    C (F 0) * X 0 ^ 3 + C (F 1) * (X 0 ^ 2 * X 1) + C (F 2) * (X 0 ^ 2 * X 2)
      + C (F 3) * (X 0 * X 1 ^ 2) + C (F 4) * (X 0 * X 1 * X 2) + C (F 5) * (X 0 * X 2 ^ 2)
      + C (F 6) * X 1 ^ 3 + C (F 7) * (X 1 ^ 2 * X 2) + C (F 8) * (X 1 * X 2 ^ 2)
      + C (F 9) * X 2 ^ 3 := by
  simp [toP, E3, Fin.sum_univ_succ, monomial_ex]; ring

/--
@isnad1 id=eq.0h2v.s11.2aae931abec1 from=translated src=- shape=fe325d84 vocab=1c8bde95
-/
theorem toP2_eq (q : Fin 6 → K) : toP E2 q =
    C (q 0) * X 0 ^ 2 + C (q 1) * (X 0 * X 1) + C (q 2) * (X 0 * X 2) + C (q 3) * X 1 ^ 2
      + C (q 4) * (X 1 * X 2) + C (q 5) * X 2 ^ 2 := by
  simp [toP, E2, Fin.sum_univ_succ, monomial_ex]; ring

/--
@isnad1 id=eq.0h2v.s10.7d1d7ab195ae from=translated src=- shape=3a8c04c3 vocab=278d02eb
-/
theorem toP1_eq (ℓ : Fin 3 → K) : toP E1 ℓ = C (ℓ 0) * X 0 + C (ℓ 1) * X 1 + C (ℓ 2) * X 2 := by
  simp [toP, E1, Fin.sum_univ_succ, monomial_ex]; ring

/--
@isnad1 id=eq.0h3v.s7.d7f198f1af25 from=translated src=- shape=8117ef58 vocab=4c3da280
-/
theorem eval_toP3 (F : Fin 10 → K) (v : Fin 3 → K) :
    MvPolynomial.eval v (toP E3 F) = PlaneCubic.eval F v := by
  rw [toP3_eq, PlaneCubic.eval_expand]; simp

/--
@isnad1 id=eq.0h3v.s7.f888c11d1cca from=translated src=- shape=8117ef58 vocab=3775e3be
-/
theorem eval_toP2 (q : Fin 6 → K) (v : Fin 3 → K) :
    MvPolynomial.eval v (toP E2 q) = PlaneCubic.evalC q v := by
  rw [toP2_eq, PlaneCubic.evalC_expand]; simp

/--
@isnad1 id=eq.0h3v.s7.d95be90206e0 from=translated src=- shape=6e1582d2 vocab=6d9dcf34
-/
theorem eval_toP1 (ℓ : Fin 3 → K) (v : Fin 3 → K) :
    MvPolynomial.eval v (toP E1 ℓ) = ℓ ⬝ᵥ v := by
  rw [toP1_eq]; simp [dotProduct, Fin.sum_univ_succ]; ring

/--
@isnad1 id=eq.0h3v.s7.4e348cea6add from=translated src=- shape=1e0475b0 vocab=c11c06a2
-/
theorem toP_mulLin (ℓ : Fin 3 → K) (q : Fin 6 → K) :
    toP E3 (PlaneCubic.mulLin ℓ q) = toP E1 ℓ * toP E2 q := by
  rw [toP3_eq, toP1_eq, toP2_eq]; simp [PlaneCubic.mulLin]; ring

/--
@isnad1 id=eq.0h3v.s7.5d9a66ad3a09 from=translated src=- shape=1e0475b0 vocab=e4aaf145
-/
theorem toP_linMul (ℓ m : Fin 3 → K) : toP E2 (PlaneCubic.linMul ℓ m) = toP E1 ℓ * toP E1 m := by
  rw [toP2_eq, toP1_eq, toP1_eq]; simp [PlaneCubic.linMul]; ring

/-! Every homogeneous polynomial of degree 1, 2, 3 is in the image. -/

/--
@isnad1 id=eq.1h2v.s6.c1a32ae80d77 from=translated src=- shape=0ef28535 vocab=40bc99c6
-/
theorem eq3 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 3) :
    p = toP E3 (fun i => coeff (E3 i) p) := eq_toP E3 E3_inj E3_deg E3_surj hp

/--
@isnad1 id=eq.1h2v.s6.a5befc581c0d from=translated src=- shape=0ef28535 vocab=c38fadb7
-/
theorem eq2 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 2) :
    p = toP E2 (fun i => coeff (E2 i) p) := eq_toP E2 E2_inj E2_deg E2_surj hp

/--
@isnad1 id=eq.1h2v.s6.49d41056745b from=translated src=- shape=0ef28535 vocab=3e4515cf
-/
theorem eq1 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 1) :
    p = toP E1 (fun i => coeff (E1 i) p) := eq_toP E1 E1_inj E1_deg E1_surj hp

/--
@isnad1 id=ex.1h2v.s6.30d6af966a9e from=translated src=- shape=389e9c03 vocab=ee410cbc
-/
theorem exists3 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 3) :
    ∃ F : Fin 10 → K, p = toP E3 F := ⟨_, eq3 hp⟩

/--
@isnad1 id=ex.1h2v.s6.b4d733d5387a from=translated src=- shape=389e9c03 vocab=27751bc0
-/
theorem exists2 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 2) :
    ∃ q : Fin 6 → K, p = toP E2 q := ⟨_, eq2 hp⟩

/--
@isnad1 id=ex.1h2v.s6.87e20274281a from=translated src=- shape=389e9c03 vocab=ac0df937
-/
theorem exists1 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 1) :
    ∃ ℓ : Fin 3 → K, p = toP E1 ℓ := ⟨_, eq1 hp⟩

/-! ### Bridges to the library's encodings -/

/-- Coefficient vector of a polynomial w.r.t. an exponent table.-/
noncomputable def cv {n : ℕ} (E : Fin n → Fin 3 →₀ ℕ) (p : MvPolynomial (Fin 3) K) : Fin n → K :=
  fun i => coeff (E i) p

/--
@isnad1 id=eq.1h2v.s6.db7a47564b64 from=translated src=- shape=1661eff5 vocab=99c11179
-/
theorem cv3 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 3) : toP E3 (cv E3 p) = p :=
  (eq3 hp).symm

/--
@isnad1 id=eq.1h2v.s6.1da1f01964a9 from=translated src=- shape=1661eff5 vocab=d6f87c39
-/
theorem cv2 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 2) : toP E2 (cv E2 p) = p :=
  (eq2 hp).symm

/--
@isnad1 id=eq.1h2v.s6.7c12973dcba2 from=translated src=- shape=1661eff5 vocab=a2590c48
-/
theorem cv1 {p : MvPolynomial (Fin 3) K} (hp : p.IsHomogeneous 1) : toP E1 (cv E1 p) = p :=
  (eq1 hp).symm

/--
@isnad1 id=eq.1h3v.s7.2dc469c3166b from=translated src=- shape=d0d5ee8a vocab=b65b1449
-/
theorem l14b_eval3 {F : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3) (v : Fin 3 → K) :
    MvPolynomial.eval v F = PlaneCubic.eval (cv E3 F) v := by
  conv_lhs => rw [eq3 hF]
  rw [eval_toP3]; rfl

/--
@isnad1 id=eq.1h3v.s7.980ce1597a54 from=translated src=- shape=d0d5ee8a vocab=e67a7c11
-/
theorem l14b_eval2 {q : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2) (v : Fin 3 → K) :
    MvPolynomial.eval v q = PlaneCubic.evalC (cv E2 q) v := by
  conv_lhs => rw [eq2 hq]
  rw [eval_toP2]; rfl

/--
@isnad1 id=eq.1h3v.s7.5eac0d0a1456 from=translated src=- shape=6582af96 vocab=1a7c16d0
-/
theorem l14b_eval1 {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (v : Fin 3 → K) :
    MvPolynomial.eval v ℓ = cv E1 ℓ ⬝ᵥ v := by
  conv_lhs => rw [eq1 hℓ]
  rw [eval_toP1]; rfl

/--
@isnad1 id=ne.1h3v.s11.111615779770 from=translated src=- shape=61f7a2ee vocab=ed03066a
-/
theorem l14b_cross {u v : Fin 3 → K} (h : LinearIndependent K ![u, v]) : u ⨯₃ v ≠ 0 :=
  crossProduct_ne_zero_iff_linearIndependent.2 h

/--
@isnad1 id=ne.2h5v.s11.8398bd498dea from=translated src=- shape=00231868 vocab=ed03066a
-/
theorem l14b_pairwise {n : ℕ} {P : Fin n → Fin 3 → K}
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j]) :
    ∀ i j, i ≠ j → P i ⨯₃ P j ≠ 0 := fun i j h => l14b_cross (hP i j h)

/--
@isnad1 id=linearin.3h3v.s8.3fee04f8d892 from=translated src=- shape=42a6f7e9 vocab=b6d658a0
-/
theorem l14b_linIndep {F G : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hG : G.IsHomogeneous 3) (h : LinearIndependent K ![F, G]) :
    LinearIndependent K ![cv E3 F, cv E3 G] := by
  apply LinearIndependent.of_comp (toPₗ E3)
  convert h using 1
  funext i; fin_cases i
  · exact (eq3 hF).symm
  · exact (eq3 hG).symm

/--
@isnad1 id=le.3h6v.s9.d98927f600d2 from=translated src=- shape=5dd3af32 vocab=a6abab82
-/
theorem l14b_h5 {m : ℕ} {P : Fin m → Fin 3 → K} {k : ℕ}
    (h5 : ∀ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin m),
      (∀ i ∈ s, MvPolynomial.eval (P i) ℓ = 0) → s.card ≤ k) :
    ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin m), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) → s.card ≤ k := by
  intro ℓ hℓ s hs
  refine h5 (toP E1 ℓ) (toP_isHomogeneous E1 E1_deg ℓ) ?_ s fun i hi => ?_
  · intro h0; apply hℓ
    exact toP_injective E1 E1_inj (h0.trans (by simp [toP]))
  · rw [eval_toP1]; exact hs i hi

/--
@isnad1 id=eq.2h4v.s8.46bbd1e7f43e from=translated src=- shape=6f42fbc7 vocab=5d2e21e9
-/
theorem l14b_conic {m : ℕ} {P : Fin m → Fin 3 → K}
    (hc : ∀ q : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 →
      (∀ i, MvPolynomial.eval (P i) q = 0) → q = 0) :
    ∀ q : Fin 6 → K, (∀ i, PlaneCubic.evalC q (P i) = 0) → q = 0 := by
  intro q hq
  have := hc (toP E2 q) (toP_isHomogeneous E2 E2_deg q) fun i => by rw [eval_toP2]; exact hq i
  exact toP_injective E2 E2_inj (this.trans (by simp [toP]))

/--
@isnad1 id=ne.1h2v.s7.8077d7059a58 from=translated src=- shape=2742fb02 vocab=5f38ca81
-/
theorem l14b_ne1 {ℓ : Fin 3 → K} (hℓ : ℓ ≠ 0) : toP E1 ℓ ≠ 0 := fun h0 =>
  hℓ (toP_injective E1 E1_inj (h0.trans (by simp [toP])))

/--
@isnad1 id=ne.1h2v.s7.75c6b393cdae from=translated src=- shape=2742fb02 vocab=4ba63f2e
-/
theorem l14b_ne2 {q : Fin 6 → K} (hq : q ≠ 0) : toP E2 q ≠ 0 := fun h0 =>
  hq (toP_injective E2 E2_inj (h0.trans (by simp [toP])))

/--
@isnad1 id=ne.2h2v.s7.433c7126d3f1 from=translated src=- shape=c2741f48 vocab=9f6d688c
-/
theorem l14b_cv1_ne {ℓ : MvPolynomial (Fin 3) K} (hℓ : ℓ.IsHomogeneous 1) (h : ℓ ≠ 0) :
    cv E1 ℓ ≠ 0 := fun h0 => h (by rw [eq1 hℓ]; change toP E1 (cv E1 ℓ) = 0; rw [h0]; simp [toP])

/--
@isnad1 id=ne.2h2v.s7.dbc531b9e366 from=translated src=- shape=c2741f48 vocab=dbea28f0
-/
theorem l14b_cv2_ne {q : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2) (h : q ≠ 0) :
    cv E2 q ≠ 0 := fun h0 => h (by rw [eq2 hq]; change toP E2 (cv E2 q) = 0; rw [h0]; simp [toP])

/-- A homogeneous factorisation `F = ℓ * q` is the library's `mulLin`.
@isnad1 id=iff.3h4v.s7.4bd956453f41 from=translated src=- shape=d947d738 vocab=713ad4bd
-/
theorem l14b_mulLin_iff {F ℓ q : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3)
    (hℓ : ℓ.IsHomogeneous 1) (hq : q.IsHomogeneous 2) :
    F = ℓ * q ↔ cv E3 F = PlaneCubic.mulLin (cv E1 ℓ) (cv E2 q) := by
  constructor
  · intro h; apply toP_injective E3 E3_inj
    rw [toP_mulLin]; change toP E3 (cv E3 F) = toP E1 (cv E1 ℓ) * toP E2 (cv E2 q)
    rw [cv3 hF, cv1 hℓ, cv2 hq, h]
  · intro h; rw [← cv3 hF, ← cv1 hℓ, ← cv2 hq, h, toP_mulLin]

/--
@isnad1 id=iff.2h3v.s9.3ce01556bc23 from=translated src=- shape=17e1641d vocab=837b9dbc
-/
theorem l14b_lin {F G : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3) (hG : G.IsHomogeneous 3) :
    (¬ ∃ ℓ q q' : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 ∧ q.IsHomogeneous 2 ∧
      q'.IsHomogeneous 2 ∧ ℓ ≠ 0 ∧ F = ℓ * q ∧ G = ℓ * q') ↔
    ¬ ∃ ℓ q q', ℓ ≠ 0 ∧ cv E3 F = PlaneCubic.mulLin ℓ q ∧ cv E3 G = PlaneCubic.mulLin ℓ q' := by
  apply not_congr; constructor
  · rintro ⟨ℓ, q, q', hℓ, hq, hq', h0, h1, h2⟩
    exact ⟨_, _, _, l14b_cv1_ne hℓ h0, (l14b_mulLin_iff hF hℓ hq).1 h1,
      (l14b_mulLin_iff hG hℓ hq').1 h2⟩
  · rintro ⟨ℓ, q, q', hℓ, h1, h2⟩
    have e1 := toP_isHomogeneous E1 E1_deg ℓ
    have e2 := toP_isHomogeneous E2 E2_deg q
    have e2' := toP_isHomogeneous E2 E2_deg q'
    refine ⟨_, _, _, e1, e2, e2', l14b_ne1 hℓ, (l14b_mulLin_iff hF e1 e2).2 ?_,
      (l14b_mulLin_iff hG e1 e2').2 ?_⟩
    · rw [h1]; congr 1 <;> funext i <;> exact (coeff_toP _ (by first | exact E1_inj | exact E2_inj) _ i).symm
    · rw [h2]; congr 1 <;> funext i <;> exact (coeff_toP _ (by first | exact E1_inj | exact E2_inj) _ i).symm

/--
@isnad1 id=iff.2h3v.s9.fcc2d8bb53ed from=translated src=- shape=3570e583 vocab=837b9dbc
-/
theorem l14b_con {F G : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3) (hG : G.IsHomogeneous 3) :
    (¬ ∃ q m m' : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 ∧ m.IsHomogeneous 1 ∧
      m'.IsHomogeneous 1 ∧ q ≠ 0 ∧ F = m * q ∧ G = m' * q) ↔
    ¬ ∃ q m m', q ≠ 0 ∧ cv E3 F = PlaneCubic.mulLin m q ∧ cv E3 G = PlaneCubic.mulLin m' q := by
  apply not_congr; constructor
  · rintro ⟨q, m, m', hq, hm, hm', h0, h1, h2⟩
    exact ⟨_, _, _, l14b_cv2_ne hq h0, (l14b_mulLin_iff hF hm hq).1 h1,
      (l14b_mulLin_iff hG hm' hq).1 h2⟩
  · rintro ⟨q, m, m', hq, h1, h2⟩
    have e2 := toP_isHomogeneous E2 E2_deg q
    have e1 := toP_isHomogeneous E1 E1_deg m
    have e1' := toP_isHomogeneous E1 E1_deg m'
    refine ⟨_, _, _, e2, e1, e1', l14b_ne2 hq, (l14b_mulLin_iff hF e1 e2).2 ?_,
      (l14b_mulLin_iff hG e1' e2).2 ?_⟩
    · rw [h1]; congr 1 <;> funext i <;> exact (coeff_toP _ (by first | exact E1_inj | exact E2_inj) _ i).symm
    · rw [h2]; congr 1 <;> funext i <;> exact (coeff_toP _ (by first | exact E1_inj | exact E2_inj) _ i).symm

/--
@isnad1 id=exactlym.5h4v.s10.28c20051fc37 from=translated src=- shape=0cb3bd44 vocab=7faca676
-/
theorem l14b_exact {P : Fin 9 → Fin 3 → K} (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    {F G : MvPolynomial (Fin 3) K} (hF : F.IsHomogeneous 3) (hG : G.IsHomogeneous 3)
    (hZ : ∀ i, MvPolynomial.eval (P i) F = 0 ∧ MvPolynomial.eval (P i) G = 0)
    (hex : ∀ v : Fin 3 → K, v ≠ 0 → MvPolynomial.eval v F = 0 → MvPolynomial.eval v G = 0 →
      ∃ i, ∃ c : K, v = c • P i) :
    PlaneCubic.ExactlyMeetIn (cv E3 F) (cv E3 G) P := by
  rw [PlaneCubic.exactlyMeetIn_iff]
  refine ⟨fun i => ⟨PlaneCubic.ne_zero_of_pairwise (n := 7) (l14b_pairwise hP) i, ?_, ?_⟩,
    fun v hv h1 h2 => hex v hv ?_ ?_⟩
  · rw [← l14b_eval3 hF]; exact (hZ i).1
  · rw [← l14b_eval3 hG]; exact (hZ i).2
  · rw [l14b_eval3 hF]; exact h1
  · rw [l14b_eval3 hG]; exact h2

/-! ### Mathlib-only restatements -/

/-- **Cayley–Bacharach, general position, every field** (`cayley_bacharach_any`).
@isnad1 id=eq.10h5v.s10.d37cbb91dae5 from=translated src=- shape=51c39633 vocab=0d65445e
-/
theorem l14_cayley_bacharach_any (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    (h5 : ∀ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin 8),
      (∀ i ∈ s, MvPolynomial.eval (P (Fin.castSucc i)) ℓ = 0) → s.card ≤ 4)
    (hconic : ∀ q : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 →
      (∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) q = 0) → q = 0)
    (F G : MvPolynomial (Fin 3) K) (hF3 : F.IsHomogeneous 3) (hG3 : G.IsHomogeneous 3)
    (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, MvPolynomial.eval (P i) F = 0) (hG : ∀ i, MvPolynomial.eval (P i) G = 0)
    (H : MvPolynomial (Fin 3) K) (hH3 : H.IsHomogeneous 3)
    (hH : ∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) :
    MvPolynomial.eval (P 8) H = 0 := by
  rw [l14b_eval3 hH3]
  exact PlaneCubic.cayley_bacharach_any P (l14b_pairwise hP)
    (l14b_h5 (P := fun i : Fin 8 => P (Fin.castSucc i)) h5)
    (l14b_conic (P := fun i : Fin 8 => P (Fin.castSucc i)) hconic) _ _
    (l14b_linIndep hF3 hG3 hFG) (fun i => by rw [← l14b_eval3 hF3]; exact hF i)
    (fun i => by rw [← l14b_eval3 hG3]; exact hG i) _
    (fun i => by rw [← l14b_eval3 hH3]; exact hH i)

/-- **Cayley–Bacharach, no common component, every field**
(`cayley_bacharach_of_no_common_factor_any`).
@isnad1 id=eq.10h5v.s10.bcae689c1773 from=translated src=- shape=3c44907c vocab=30107e2d
-/
theorem l14_cayley_bacharach_of_no_common_factor_any (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    (F G : MvPolynomial (Fin 3) K) (hF3 : F.IsHomogeneous 3) (hG3 : G.IsHomogeneous 3)
    (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, MvPolynomial.eval (P i) F = 0) (hG : ∀ i, MvPolynomial.eval (P i) G = 0)
    (hlin : ¬ ∃ ℓ q q' : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 ∧ q.IsHomogeneous 2 ∧
      q'.IsHomogeneous 2 ∧ ℓ ≠ 0 ∧ F = ℓ * q ∧ G = ℓ * q')
    (hcon : ¬ ∃ q m m' : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 ∧ m.IsHomogeneous 1 ∧
      m'.IsHomogeneous 1 ∧ q ≠ 0 ∧ F = m * q ∧ G = m' * q)
    (H : MvPolynomial (Fin 3) K) (hH3 : H.IsHomogeneous 3)
    (hH : ∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) :
    MvPolynomial.eval (P 8) H = 0 := by
  rw [l14b_eval3 hH3]
  exact PlaneCubic.cayley_bacharach_of_no_common_factor_any P (l14b_pairwise hP) _ _
    (l14b_linIndep hF3 hG3 hFG) (fun i => by rw [← l14b_eval3 hF3]; exact hF i)
    (fun i => by rw [← l14b_eval3 hG3]; exact hG i) ((l14b_lin hF3 hG3).1 hlin)
    ((l14b_con hF3 hG3).1 hcon) _ (fun i => by rw [← l14b_eval3 hH3]; exact hH i)

/-- **Cayley–Bacharach, textbook form, infinite field** (`cayley_bacharach_classical`).
@isnad1 id=eq.8h5v.s10.7747f5cf8f02 from=translated src=- shape=7179ecd7 vocab=9275470c
-/
theorem l14_cayley_bacharach_classical [Infinite K] (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    (F G : MvPolynomial (Fin 3) K) (hF3 : F.IsHomogeneous 3) (hG3 : G.IsHomogeneous 3)
    (hFG : LinearIndependent K ![F, G])
    (hZ : ∀ i, MvPolynomial.eval (P i) F = 0 ∧ MvPolynomial.eval (P i) G = 0)
    (hex : ∀ v : Fin 3 → K, v ≠ 0 → MvPolynomial.eval v F = 0 → MvPolynomial.eval v G = 0 →
      ∃ i, ∃ c : K, v = c • P i)
    (H : MvPolynomial (Fin 3) K) (hH3 : H.IsHomogeneous 3)
    (hH : ∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) :
    MvPolynomial.eval (P 8) H = 0 := by
  rw [l14b_eval3 hH3]
  exact PlaneCubic.cayley_bacharach_classical P (l14b_pairwise hP) _ _
    (l14b_linIndep hF3 hG3 hFG) (l14b_exact hP hF3 hG3 hZ hex) _
    (fun i => by rw [← l14b_eval3 hH3]; exact hH i)

/-- **Cayley–Bacharach, textbook form, finite field with `|K| ∉ {4, 5, 7}`**
(`cayley_bacharach_classical_finite`; covers `cayley_bacharach_classical_card8`).
@isnad1 id=eq.11h5v.s10.38595a9713f8 from=translated src=- shape=56ca0d3f vocab=ac0b23cf
-/
theorem l14_cayley_bacharach_classical_finite [Fintype K] (h4 : Fintype.card K ≠ 4)
    (h5 : Fintype.card K ≠ 5) (h7 : Fintype.card K ≠ 7) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    (F G : MvPolynomial (Fin 3) K) (hF3 : F.IsHomogeneous 3) (hG3 : G.IsHomogeneous 3)
    (hFG : LinearIndependent K ![F, G])
    (hZ : ∀ i, MvPolynomial.eval (P i) F = 0 ∧ MvPolynomial.eval (P i) G = 0)
    (hex : ∀ v : Fin 3 → K, v ≠ 0 → MvPolynomial.eval v F = 0 → MvPolynomial.eval v G = 0 →
      ∃ i, ∃ c : K, v = c • P i)
    (H : MvPolynomial (Fin 3) K) (hH3 : H.IsHomogeneous 3)
    (hH : ∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) :
    MvPolynomial.eval (P 8) H = 0 := by
  rw [l14b_eval3 hH3]
  exact PlaneCubic.cayley_bacharach_classical_finite h4 h5 h7 P (l14b_pairwise hP) _ _
    (l14b_linIndep hF3 hG3 hFG) (l14b_exact hP hF3 hG3 hZ hex) _
    (fun i => by rw [← l14b_eval3 hH3]; exact hH i)

/-- **Nine common zeros, `|K| = 3`** (`cayley_bacharach_card3`).
@isnad1 id=eq.9h5v.s10.fd1ebbb8daa6 from=translated src=- shape=6e6f6862 vocab=0be56bb5
-/
theorem l14_cayley_bacharach_card3 [Fintype K] (hK : Fintype.card K = 3) (P : Fin 9 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j])
    (F G : MvPolynomial (Fin 3) K) (hF3 : F.IsHomogeneous 3) (hG3 : G.IsHomogeneous 3)
    (hFG : LinearIndependent K ![F, G])
    (hF : ∀ i, MvPolynomial.eval (P i) F = 0) (hG : ∀ i, MvPolynomial.eval (P i) G = 0)
    (H : MvPolynomial (Fin 3) K) (hH3 : H.IsHomogeneous 3)
    (hH : ∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) :
    MvPolynomial.eval (P 8) H = 0 := by
  rw [l14b_eval3 hH3]
  exact PlaneCubic.cayley_bacharach_card3 hK P (l14b_pairwise hP) _ _
    (l14b_linIndep hF3 hG3 hFG) (fun i => by rw [← l14b_eval3 hF3]; exact hF i)
    (fun i => by rw [← l14b_eval3 hG3]; exact hG i) _
    (fun i => by rw [← l14b_eval3 hH3]; exact hH i)

/-! ### Converse bridges (library hypotheses ⇒ Mathlib hypotheses) -/

/--
@isnad1 id=eq.1h4v.s5.4df210ef2ec4 from=translated src=- shape=c935530f vocab=0f02f6fc
-/
theorem cv_toP {n : ℕ} {E : Fin n → Fin 3 →₀ ℕ} (hE : Function.Injective E) (c : Fin n → K) :
    cv E (toP E c) = c := funext (coeff_toP E hE c)

/--
@isnad1 id=le.4h6v.s9.1c10231d95f2 from=translated src=- shape=8739f7a2 vocab=a6abab82
-/
theorem l14b_h5' {m : ℕ} {P : Fin m → Fin 3 → K} {k : ℕ}
    (h5 : ∀ ℓ : Fin 3 → K, ℓ ≠ 0 → ∀ s : Finset (Fin m), (∀ i ∈ s, ℓ ⬝ᵥ P i = 0) → s.card ≤ k) :
    ∀ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin m),
      (∀ i ∈ s, MvPolynomial.eval (P i) ℓ = 0) → s.card ≤ k := fun ℓ hℓ h0 s hs =>
  h5 _ (l14b_cv1_ne hℓ h0) s fun i hi => by rw [← l14b_eval1 hℓ]; exact hs i hi

/--
@isnad1 id=eq.3h4v.s8.74f3d6d19a0e from=translated src=- shape=98fde687 vocab=5d2e21e9
-/
theorem l14b_conic' {m : ℕ} {P : Fin m → Fin 3 → K}
    (hc : ∀ q : Fin 6 → K, (∀ i, PlaneCubic.evalC q (P i) = 0) → q = 0) :
    ∀ q : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 →
      (∀ i, MvPolynomial.eval (P i) q = 0) → q = 0 := fun q hq h => by
  have := hc (cv E2 q) fun i => by rw [← l14b_eval2 hq]; exact h i
  rw [← cv2 hq, this]; simp [toP]

/--
@isnad1 id=ne.2h4v.s7.bdc43377411c from=translated src=- shape=c07492e3 vocab=da865332
-/
theorem l14b_irr {q : MvPolynomial (Fin 3) K} (hq : q.IsHomogeneous 2)
    (h : ∀ ℓ m : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → q ≠ ℓ * m) :
    ∀ ℓ m : Fin 3 → K, cv E2 q ≠ PlaneCubic.linMul ℓ m := fun ℓ m he =>
  h _ _ (toP_isHomogeneous E1 E1_deg ℓ) (toP_isHomogeneous E1 E1_deg m)
    (by rw [← toP_linMul, ← he, cv2 hq])

/-- The space of plane cubics through the points `P i`, as a Mathlib submodule.
@isnad1 id=eq.0h3v.s9.0bf859f1621f from=translated src=- shape=e97d0db0 vocab=e5df7530
-/
theorem l14b_cubicsThrough {m : ℕ} (P : Fin m → Fin 3 → K) :
    MvPolynomial.homogeneousSubmodule (Fin 3) K 3 ⊓
        ⨅ i, LinearMap.ker (MvPolynomial.aeval (P i)).toLinearMap =
      (LinearMap.ker (PlaneCubic.evalMap P)).map (toPₗ E3) := by
  ext F
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    MvPolynomial.mem_homogeneousSubmodule, Submodule.mem_map, AlgHom.toLinearMap_apply]
  simp only [← LinearMap.mem_ker, PlaneCubic.mem_ker_evalMap]
  constructor
  · rintro ⟨hF, h⟩
    exact ⟨cv E3 F, fun i => by rw [← l14b_eval3 hF]; exact h i, cv3 hF⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨toP_isHomogeneous E3 E3_deg c, fun i => by
      change MvPolynomial.eval (P i) (toP E3 c) = 0; rw [eval_toP3]; exact hc i⟩

/-- **The eight-point criterion, every field** (`finrank_ker_evalMap_eq_two_iff`).
@isnad1 id=iff.1h2v.s11.dbf112db8475 from=translated src=- shape=e7527c3c vocab=af4bb80e
-/
theorem l14_finrank_eq_two_iff (P : Fin 8 → Fin 3 → K)
    (hP : ∀ i j, i ≠ j → LinearIndependent K ![P i, P j]) :
    Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin 3) K 3 ⊓
        ⨅ i, LinearMap.ker (MvPolynomial.aeval (P i)).toLinearMap : Submodule K _) = 2 ↔
      (∀ ℓ : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin 8),
        (∀ i ∈ s, MvPolynomial.eval (P i) ℓ = 0) → s.card ≤ 4) ∧
      (∀ q : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 →
        (∀ i, MvPolynomial.eval (P i) q = 0) → q = 0) := by
  rw [l14b_cubicsThrough, ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
    (toP_injective (K := K) E3 E3_inj) _), PlaneCubic.finrank_ker_evalMap_eq_two_iff P
    (l14b_pairwise hP)]
  exact ⟨fun ⟨a, b⟩ => ⟨l14b_h5' a, l14b_conic' b⟩, fun ⟨a, b⟩ => ⟨l14b_h5 a, l14b_conic b⟩⟩

/-- **Pascal, natural hypotheses, `|K| > 10`** (`pascal_clean`). The six points lie on a
homogeneous quadratic `q` that is not a product of two linear forms.
@isnad1 id=eq.10h8v.s14.70e8961c7ed5 from=translated src=- shape=c6edbd7d vocab=222506bd
-/
theorem l14_pascal (hK : ∃ s : Finset K, 10 < s.card) (A₁ A₂ A₃ A₄ A₅ A₆ : Fin 3 → K)
    (hA : ∀ i j, i ≠ j →
      LinearIndependent K ![![A₁, A₂, A₃, A₄, A₅, A₆] i, ![A₁, A₂, A₃, A₄, A₅, A₆] j])
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 2)
    (hirr : ∀ ℓ m : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → q ≠ ℓ * m)
    (hq₁ : MvPolynomial.eval A₁ q = 0) (hq₂ : MvPolynomial.eval A₂ q = 0)
    (hq₃ : MvPolynomial.eval A₃ q = 0) (hq₄ : MvPolynomial.eval A₄ q = 0)
    (hq₅ : MvPolynomial.eval A₅ q = 0) (hq₆ : MvPolynomial.eval A₆ q = 0) :
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 := by
  have : PlaneCubic.CardGT K 10 := ⟨hK⟩
  rw [l14b_eval2 hq] at hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
  exact PlaneCubic.pascal_clean A₁ A₂ A₃ A₄ A₅ A₆ (l14b_pairwise hA) _ (l14b_irr hq hirr)
    hq₁ hq₂ hq₃ hq₄ hq₅ hq₆

/-- **Pappus, natural hypotheses, `|K| > 10`** (`pappus_clean`).
@isnad1 id=eq.19h9v.s14.d955c953311c from=translated src=- shape=03cb2127 vocab=797391a1
-/
theorem l14_pappus (hK : ∃ s : Finset K, 10 < s.card) (A₁ A₂ A₃ A₄ A₅ A₆ l m : Fin 3 → K)
    (hl₁ : l ⬝ᵥ A₁ = 0) (hl₃ : l ⬝ᵥ A₃ = 0) (hl₅ : l ⬝ᵥ A₅ = 0)
    (hm₂ : m ⬝ᵥ A₂ = 0) (hm₄ : m ⬝ᵥ A₄ = 0) (hm₆ : m ⬝ᵥ A₆ = 0)
    (hm₁ : m ⬝ᵥ A₁ ≠ 0) (hm₃ : m ⬝ᵥ A₃ ≠ 0) (hm₅ : m ⬝ᵥ A₅ ≠ 0)
    (hl₂ : l ⬝ᵥ A₂ ≠ 0) (hl₄ : l ⬝ᵥ A₄ ≠ 0) (hl₆ : l ⬝ᵥ A₆ ≠ 0)
    (a13 : LinearIndependent K ![A₁, A₃]) (a15 : LinearIndependent K ![A₁, A₅])
    (a35 : LinearIndependent K ![A₃, A₅]) (a24 : LinearIndependent K ![A₂, A₄])
    (a26 : LinearIndependent K ![A₂, A₆]) (a46 : LinearIndependent K ![A₄, A₆]) :
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 := by
  have : PlaneCubic.CardGT K 10 := ⟨hK⟩
  exact PlaneCubic.pappus_clean A₁ A₂ A₃ A₄ A₅ A₆ l m hl₁ hl₃ hl₅ hm₂ hm₄ hm₆ hm₁ hm₃ hm₅
    hl₂ hl₄ hl₆ (l14b_cross a13) (l14b_cross a15) (l14b_cross a35) (l14b_cross a24)
    (l14b_cross a26) (l14b_cross a46)

/-- **Line lemma, `|K| ≥ 3`** (`line_lemma`).
@isnad1 id=ex.5h3v.s9.726257750748 from=translated src=- shape=31d7539d vocab=374572a6
-/
theorem l14_line_lemma (hK : ∃ t : K, t ≠ 0 ∧ t ≠ 1) (F ℓ : MvPolynomial (Fin 3) K)
    (hF3 : F.IsHomogeneous 3) (hℓ1 : ℓ.IsHomogeneous 1) (hℓ : ℓ ≠ 0)
    (hF : ∀ v : Fin 3 → K, MvPolynomial.eval v ℓ = 0 → MvPolynomial.eval v F = 0) :
    ∃ q : MvPolynomial (Fin 3) K, q.IsHomogeneous 2 ∧ F = ℓ * q := by
  have : PlaneCubic.AtLeastThree K := ⟨hK⟩
  obtain ⟨q, hq⟩ := PlaneCubic.line_lemma (cv E3 F) (cv E1 ℓ) (l14b_cv1_ne hℓ1 hℓ)
    fun v hv => by rw [← l14b_eval3 hF3]; exact hF v (by rw [l14b_eval1 hℓ1]; exact hv)
  have e2 := toP_isHomogeneous E2 E2_deg q
  exact ⟨_, e2, (l14b_mulLin_iff hF3 hℓ1 e2).2 (by rw [hq, cv_toP E2_inj])⟩

def gridQ : Fin 9 → Fin 3 → ℚ :=
  ![![-1, -1, 1], ![-1, 0, 1], ![-1, 1, 1], ![0, -1, 1], ![0, 0, 1], ![0, 1, 1], ![1, -1, 1],
    ![1, 0, 1], ![1, 1, 1]]

/--
@isnad1 id=linearin.1h2v.s6.cd8fb0163e95 from=translated src=- shape=40371904 vocab=aa650346
-/
theorem gridQ_li : ∀ i j, i ≠ j → LinearIndependent ℚ ![gridQ i, gridQ j] := by
  intro i j hij
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  fin_cases i <;> fin_cases j <;> simp_all [gridQ, cross_apply, funext_iff, Fin.forall_fin_succ] <;>
    norm_num

/--
@isnad1 id=ex.3h1v.s8.dd02152f36b3 from=translated src=- shape=763f71df vocab=768055e8
-/
theorem grid_hex (v : Fin 3 → ℚ) (hv : v ≠ 0)
    (hF : v 0 * (v 0 - v 2) * (v 0 + v 2) = 0) (hG : v 1 * (v 1 - v 2) * (v 1 + v 2) = 0) :
    ∃ i, ∃ c : ℚ, v = c • gridQ i := by
  by_cases h2 : v 2 = 0
  · exfalso; apply hv
    rw [h2] at hF hG; simp at hF hG
    funext k; fin_cases k <;> simp [hF, hG, h2]
  have ha : v 0 = -v 2 ∨ v 0 = 0 ∨ v 0 = v 2 := by
    rcases mul_eq_zero.1 hF with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inl (by linarith)
  have hb : v 1 = -v 2 ∨ v 1 = 0 ∨ v 1 = v 2 := by
    rcases mul_eq_zero.1 hG with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by linarith))
    · exact Or.inl (by linarith)
  have key : ∀ i : Fin 9, gridQ i 0 * v 2 = v 0 → gridQ i 1 * v 2 = v 1 →
      ∃ i, ∃ c : ℚ, v = c • gridQ i := fun i h0 h1 => ⟨i, v 2, by
    funext k; fin_cases k
    · simp; rw [← h0, mul_comm]
    · simp; rw [← h1, mul_comm]
    · have : gridQ i 2 = 1 := by fin_cases i <;> rfl
      simp [this]⟩
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb
  · exact key 0 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 1 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 2 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 3 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 4 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 5 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 6 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 7 (by simp [gridQ, ha]) (by simp [gridQ, hb])
  · exact key 8 (by simp [gridQ, ha]) (by simp [gridQ, hb])

/-! ### Witnesses -/

/-- `F = x (x - z) (x + z)`.-/
noncomputable def Fw (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R :=
  X 0 * (X 0 - X 2) * (X 0 + X 2)

/-- `G = y (y - z) (y + z)`.-/
noncomputable def Gw (R : Type*) [CommRing R] : MvPolynomial (Fin 3) R :=
  X 1 * (X 1 - X 2) * (X 1 + X 2)

/--
@isnad1 id=ishomoge.0h1v.s4.0459c5158a13 from=translated src=- shape=15c54c9f vocab=b9bef8bc
-/
theorem Fw_hom (R : Type*) [CommRing R] : (Fw R).IsHomogeneous 3 :=
  ((isHomogeneous_X R 0).mul ((isHomogeneous_X R 0).sub (isHomogeneous_X R 2))).mul
    ((isHomogeneous_X R 0).add (isHomogeneous_X R 2))

/--
@isnad1 id=ishomoge.0h1v.s4.27f52d894453 from=translated src=- shape=15c54c9f vocab=6935fe02
-/
theorem Gw_hom (R : Type*) [CommRing R] : (Gw R).IsHomogeneous 3 :=
  ((isHomogeneous_X R 1).mul ((isHomogeneous_X R 1).sub (isHomogeneous_X R 2))).mul
    ((isHomogeneous_X R 1).add (isHomogeneous_X R 2))

/--
@isnad1 id=linearin.0h1v.s7.50b2610c2865 from=translated src=- shape=ea105cce vocab=f55725c7
-/
theorem FGw_li (R : Type*) [Field R] : LinearIndependent R ![Fw R, Gw R] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have h1 := congrArg (MvPolynomial.eval ![1, 0, 0]) h
  have h2 := congrArg (MvPolynomial.eval ![0, 1, 0]) h
  simp [Fw, Gw] at h1 h2
  exact ⟨h1, h2⟩

/--
@isnad1 id=eq.0h1v.s7.176e2026e3fd from=translated src=- shape=08c3b03e vocab=678cc14a
-/
theorem Fw_gridQ (i : Fin 9) : MvPolynomial.eval (gridQ i) (Fw ℚ) = 0 := by
  fin_cases i <;> simp [Fw, gridQ]

/--
@isnad1 id=eq.0h1v.s7.1081ab6e372a from=translated src=- shape=08c3b03e vocab=97ba595d
-/
theorem Gw_gridQ (i : Fin 9) : MvPolynomial.eval (gridQ i) (Gw ℚ) = 0 := by
  fin_cases i <;> simp [Gw, gridQ]

/--
@isnad1 id=ex.3h1v.s8.4c181f6ffffd from=translated src=- shape=564b30bd vocab=494f004f
-/
theorem hexQ (v : Fin 3 → ℚ) (hv : v ≠ 0) (hF : MvPolynomial.eval v (Fw ℚ) = 0)
    (hG : MvPolynomial.eval v (Gw ℚ) = 0) : ∃ i, ∃ c : ℚ, v = c • gridQ i :=
  grid_hex v hv (by simpa [Fw] using hF) (by simpa [Gw] using hG)

/--
@isnad1 id=ex.0h0v.s4.38e6ef3bff9e from=translated src=- shape=c4cb3c08 vocab=efcbffa4
-/
theorem cardQ : ∃ s : Finset ℚ, 10 < s.card :=
  ⟨(Finset.range 11).image (fun n : ℕ => (n : ℚ)), by
    rw [Finset.card_image_of_injective _ Nat.cast_injective]; simp⟩

/-- The eight-point general-position hypotheses hold for the first eight grid points
(derived from exactness via the library).
@isnad1 id=and.0h0v.s9.5dea6cb6602e from=translated src=- shape=40dbc700 vocab=c77352a1
-/
theorem gridQ_gp :
    (∀ ℓ : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin 8),
      (∀ i ∈ s, MvPolynomial.eval (gridQ (Fin.castSucc i)) ℓ = 0) → s.card ≤ 4) ∧
    (∀ q : MvPolynomial (Fin 3) ℚ, q.IsHomogeneous 2 →
      (∀ i : Fin 8, MvPolynomial.eval (gridQ (Fin.castSucc i)) q = 0) → q = 0) := by
  have hex := l14b_exact gridQ_li (Fw_hom ℚ) (Gw_hom ℚ) (fun i => ⟨Fw_gridQ i, Gw_gridQ i⟩) hexQ
  obtain ⟨hPZ, hZ⟩ := hex
  have hF : ∀ i, PlaneCubic.eval (cv E3 (Fw ℚ)) (gridQ i) = 0 := fun i => (hPZ i).2.1
  have hG : ∀ i, PlaneCubic.eval (cv E3 (Gw ℚ)) (gridQ i) = 0 := fun i => (hPZ i).2.2
  have hex' : ∀ v, v ≠ 0 → PlaneCubic.eval (cv E3 (Fw ℚ)) v = 0 →
      PlaneCubic.eval (cv E3 (Gw ℚ)) v = 0 → ∃ i, v ⨯₃ gridQ i = 0 :=
    fun v hv h1 h2 => hZ v ⟨hv, h1, h2⟩
  have hP := l14b_pairwise gridQ_li
  have hP' : ∀ i j : Fin 8, i ≠ j → gridQ (Fin.castSucc i) ⨯₃ gridQ (Fin.castSucc j) ≠ 0 :=
    fun i j hij => hP _ _ (fun h => hij (Fin.castSucc_injective _ h))
  obtain ⟨h4, hc⟩ := PlaneCubic.general_position_of_no_common_factor
    (fun i => gridQ (Fin.castSucc i)) hP' _ _ (fun i => hF _) (fun i => hG _)
    (PlaneCubic.no_common_line_of_exact (fun i => (hPZ i).1) _ _ hex')
    (PlaneCubic.no_common_conic_of_exact (n := 6) hP _ _ hF hG hex')
  exact ⟨l14b_h5' (P := fun i : Fin 8 => gridQ (Fin.castSucc i))
    (fun ℓ hℓ s hs => (h4 ℓ hℓ s hs).trans (by norm_num)), l14b_conic' hc⟩

/-- `F` and `G` have no common linear or conic component (derived from exactness).
@isnad1 id=and.0h0v.s9.cb8ac32e5f07 from=translated src=- shape=519d4e4e vocab=7fec61f0
-/
theorem gridQ_ncf :
    (¬ ∃ ℓ q q' : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 ∧ q.IsHomogeneous 2 ∧
      q'.IsHomogeneous 2 ∧ ℓ ≠ 0 ∧ Fw ℚ = ℓ * q ∧ Gw ℚ = ℓ * q') ∧
    (¬ ∃ q m m' : MvPolynomial (Fin 3) ℚ, q.IsHomogeneous 2 ∧ m.IsHomogeneous 1 ∧
      m'.IsHomogeneous 1 ∧ q ≠ 0 ∧ Fw ℚ = m * q ∧ Gw ℚ = m' * q) := by
  obtain ⟨hPZ, hZ⟩ :=
    l14b_exact gridQ_li (Fw_hom ℚ) (Gw_hom ℚ) (fun i => ⟨Fw_gridQ i, Gw_gridQ i⟩) hexQ
  have hex' : ∀ v, v ≠ 0 → PlaneCubic.eval (cv E3 (Fw ℚ)) v = 0 →
      PlaneCubic.eval (cv E3 (Gw ℚ)) v = 0 → ∃ i, v ⨯₃ gridQ i = 0 :=
    fun v hv h1 h2 => hZ v ⟨hv, h1, h2⟩
  exact ⟨(l14b_lin (Fw_hom ℚ) (Gw_hom ℚ)).2
      (PlaneCubic.no_common_line_of_exact (fun i => (hPZ i).1) _ _ hex'),
    (l14b_con (Fw_hom ℚ) (Gw_hom ℚ)).2 (PlaneCubic.no_common_conic_of_exact (n := 6)
      (l14b_pairwise gridQ_li) _ _ (fun i => (hPZ i).2.1) (fun i => (hPZ i).2.2) hex')⟩

/-- **Witness (Cayley–Bacharach, all three forms over `ℚ`).** The nine points of the grid
`{-1,0,1}²` are the exact common zeros of `x(x-z)(x+z)` and `y(y-z)(y+z)`; all hypotheses of
`l14_cayley_bacharach_any`, `l14_cayley_bacharach_of_no_common_factor_any` and
`l14_cayley_bacharach_classical` hold, and `H = F + G` is a cubic through the first eight that
is neither a multiple of `F` nor of `G`.
@isnad1 id=ex.0h0v.s11.033065573f05 from=translated src=- shape=d05886b0 vocab=8dc9c09b
-/
theorem l14w_cayley_bacharach :
    ∃ (P : Fin 9 → Fin 3 → ℚ) (F G H : MvPolynomial (Fin 3) ℚ),
      (∀ i j, i ≠ j → LinearIndependent ℚ ![P i, P j]) ∧
      F.IsHomogeneous 3 ∧ G.IsHomogeneous 3 ∧ H.IsHomogeneous 3 ∧
      LinearIndependent ℚ ![F, G] ∧
      (∀ i, MvPolynomial.eval (P i) F = 0 ∧ MvPolynomial.eval (P i) G = 0) ∧
      (∀ v : Fin 3 → ℚ, v ≠ 0 → MvPolynomial.eval v F = 0 → MvPolynomial.eval v G = 0 →
        ∃ i, ∃ c : ℚ, v = c • P i) ∧
      (∀ ℓ : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 → ℓ ≠ 0 → ∀ s : Finset (Fin 8),
        (∀ i ∈ s, MvPolynomial.eval (P (Fin.castSucc i)) ℓ = 0) → s.card ≤ 4) ∧
      (∀ q : MvPolynomial (Fin 3) ℚ, q.IsHomogeneous 2 →
        (∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) q = 0) → q = 0) ∧
      (¬ ∃ ℓ q q' : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 ∧ q.IsHomogeneous 2 ∧
        q'.IsHomogeneous 2 ∧ ℓ ≠ 0 ∧ F = ℓ * q ∧ G = ℓ * q') ∧
      (¬ ∃ q m m' : MvPolynomial (Fin 3) ℚ, q.IsHomogeneous 2 ∧ m.IsHomogeneous 1 ∧
        m'.IsHomogeneous 1 ∧ q ≠ 0 ∧ F = m * q ∧ G = m' * q) ∧
      (∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) ∧
      (∀ c : ℚ, H ≠ c • F) ∧ (∀ c : ℚ, H ≠ c • G) ∧
      MvPolynomial.eval (P 8) H = 0 := by
  refine ⟨gridQ, Fw ℚ, Gw ℚ, Fw ℚ + Gw ℚ, gridQ_li, Fw_hom ℚ, Gw_hom ℚ,
    (Fw_hom ℚ).add (Gw_hom ℚ), FGw_li ℚ, fun i => ⟨Fw_gridQ i, Gw_gridQ i⟩, hexQ, gridQ_gp.1,
    gridQ_gp.2, gridQ_ncf.1, gridQ_ncf.2, fun i => by simp [Fw_gridQ, Gw_gridQ], ?_, ?_, ?_⟩
  · intro c h
    have := congrArg (MvPolynomial.eval ![0, 2, 1]) h
    simp [Fw, Gw] at this; norm_num at this
  · intro c h
    have := congrArg (MvPolynomial.eval ![2, 0, 1]) h
    simp [Fw, Gw] at this; norm_num at this
  · exact l14_cayley_bacharach_classical gridQ gridQ_li _ _ (Fw_hom ℚ) (Gw_hom ℚ) (FGw_li ℚ)
      (fun i => ⟨Fw_gridQ i, Gw_gridQ i⟩) hexQ _ ((Fw_hom ℚ).add (Gw_hom ℚ))
      (fun i => by simp [Fw_gridQ, Gw_gridQ])

/-! ### Witness over `𝔽₃` (`|K| = 3`): the same two cubics meet in exactly all nine affine points -/

def gridZ : Fin 9 → Fin 3 → ZMod 3 :=
  ![![-1, -1, 1], ![-1, 0, 1], ![-1, 1, 1], ![0, -1, 1], ![0, 0, 1], ![0, 1, 1], ![1, -1, 1],
    ![1, 0, 1], ![1, 1, 1]]

/--
@isnad1 id=linearin.1h2v.s8.e28b1626d8a0 from=translated src=- shape=76823791 vocab=58936a3d
-/
theorem gridZ_li : ∀ i j, i ≠ j → LinearIndependent (ZMod 3) ![gridZ i, gridZ j] := by
  intro i j hij
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  fin_cases i <;> fin_cases j <;> simp_all [gridZ, cross_apply, funext_iff, Fin.forall_fin_succ] <;>
    decide

/--
@isnad1 id=ex.0h2v.s7.c12cc994f6c3 from=translated src=- shape=38aac00a vocab=dca666d1
-/
theorem gridZ_surj (a b : ZMod 3) : ∃ i, gridZ i 0 = a ∧ gridZ i 1 = b ∧ gridZ i 2 = 1 := by
  revert a b; decide

/--
@isnad1 id=eq.0h1v.s8.4e3e17370465 from=translated src=- shape=b8fc3ac6 vocab=8750b980
-/
theorem Fw_gridZ (i : Fin 9) : MvPolynomial.eval (gridZ i) (Fw (ZMod 3)) = 0 := by
  fin_cases i <;> (simp [Fw, gridZ]; try decide)

/--
@isnad1 id=eq.0h1v.s8.ff2d8fbedaa9 from=translated src=- shape=b8fc3ac6 vocab=8476e29b
-/
theorem Gw_gridZ (i : Fin 9) : MvPolynomial.eval (gridZ i) (Gw (ZMod 3)) = 0 := by
  fin_cases i <;> (simp [Gw, gridZ]; try decide)

/--
@isnad1 id=ex.3h1v.s10.90e9333ba7ea from=translated src=- shape=1879f398 vocab=8649abe2
-/
theorem hexZ (v : Fin 3 → ZMod 3) (hv : v ≠ 0) (hF : MvPolynomial.eval v (Fw (ZMod 3)) = 0)
    (hG : MvPolynomial.eval v (Gw (ZMod 3)) = 0) : ∃ i, ∃ c : ZMod 3, v = c • gridZ i := by
  simp only [Fw, Gw, map_mul, map_sub, map_add, MvPolynomial.eval_X] at hF hG
  by_cases h2 : v 2 = 0
  · exfalso; apply hv
    rw [h2] at hF hG
    have h0 : v 0 = 0 := by
      generalize v 0 = a at hF; revert a; decide
    have h1 : v 1 = 0 := by
      generalize v 1 = a at hG; revert a; decide
    funext k; fin_cases k <;> simp [h0, h1, h2]
  obtain ⟨i, h0, h1, h2'⟩ := gridZ_surj (v 0 * (v 2)⁻¹) (v 1 * (v 2)⁻¹)
  refine ⟨i, v 2, ?_⟩
  funext k; fin_cases k
  · simp [h0]; field_simp
  · simp [h1]; field_simp
  · simp [h2']

/-- **Witness (`|K| = 3`).** Over `ZMod 3` the cubics `x(x-z)(x+z)` and `y(y-z)(y+z)` are
linearly independent and their common zeros are exactly the nine points of `𝔽₃²`; this is a
configuration satisfying all hypotheses of `l14_cayley_bacharach_card3` and
`l14_cayley_bacharach_classical_finite`, with `H = F + G` not a multiple of `F` or `G`.
@isnad1 id=ex.0h0v.s12.54c0bfdcd0b3 from=translated src=- shape=d77a8cd9 vocab=3ed21120
-/
theorem l14w_cayley_bacharach_zmod3 :
    ∃ (P : Fin 9 → Fin 3 → ZMod 3) (F G H : MvPolynomial (Fin 3) (ZMod 3)),
      (∀ i j, i ≠ j → LinearIndependent (ZMod 3) ![P i, P j]) ∧
      F.IsHomogeneous 3 ∧ G.IsHomogeneous 3 ∧ H.IsHomogeneous 3 ∧
      LinearIndependent (ZMod 3) ![F, G] ∧
      (∀ i, MvPolynomial.eval (P i) F = 0 ∧ MvPolynomial.eval (P i) G = 0) ∧
      (∀ v : Fin 3 → ZMod 3, v ≠ 0 → MvPolynomial.eval v F = 0 → MvPolynomial.eval v G = 0 →
        ∃ i, ∃ c : ZMod 3, v = c • P i) ∧
      (∀ i : Fin 8, MvPolynomial.eval (P (Fin.castSucc i)) H = 0) ∧
      (∀ c : ZMod 3, H ≠ c • F) ∧ (∀ c : ZMod 3, H ≠ c • G) ∧
      MvPolynomial.eval (P 8) H = 0 := by
  refine ⟨gridZ, Fw _, Gw _, Fw _ + Gw _, gridZ_li, Fw_hom _, Gw_hom _, (Fw_hom _).add (Gw_hom _),
    FGw_li _, fun i => ⟨Fw_gridZ i, Gw_gridZ i⟩, hexZ, fun i => by simp [Fw_gridZ, Gw_gridZ],
    ?_, ?_, ?_⟩
  · intro c h
    have := congrArg (MvPolynomial.eval ![0, 1, 0]) h
    simp [Fw, Gw] at this
  · intro c h
    have := congrArg (MvPolynomial.eval ![1, 0, 0]) h
    simp [Fw, Gw] at this
  · exact l14_cayley_bacharach_card3 (ZMod.card 3) gridZ gridZ_li _ _ (Fw_hom _) (Gw_hom _)
      (FGw_li _) (fun i => Fw_gridZ i) (fun i => Gw_gridZ i) _ ((Fw_hom _).add (Gw_hom _))
      (fun i => by simp [Fw_gridZ, Gw_gridZ])

/-! ### Witness for the eight-point criterion (both directions) -/

/-- Five points on `y = 0` and three more: the criterion fails.-/
def five : Fin 8 → Fin 3 → ℚ :=
  ![![0, 0, 1], ![1, 0, 1], ![2, 0, 1], ![3, 0, 1], ![4, 0, 1], ![0, 1, 1], ![1, 1, 1],
    ![0, 2, 1]]

/--
@isnad1 id=linearin.1h2v.s6.7d0f4c8b989b from=translated src=- shape=40371904 vocab=2acc2607
-/
theorem five_li : ∀ i j, i ≠ j → LinearIndependent ℚ ![five i, five j] := by
  intro i j hij
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  fin_cases i <;> fin_cases j <;> simp_all [five, cross_apply, funext_iff, Fin.forall_fin_succ] <;>
    norm_num

/--
@isnad1 id=and.0h0v.s11.bc7504d108b2 from=translated src=- shape=a926b141 vocab=efb7ad16
-/
theorem w_finrank_core :
    (∀ i j : Fin 8, i ≠ j →
        LinearIndependent ℚ ![gridQ (Fin.castSucc i), gridQ (Fin.castSucc j)]) ∧
      Module.finrank ℚ (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ 3 ⊓
        ⨅ i : Fin 8, LinearMap.ker (MvPolynomial.aeval (gridQ (Fin.castSucc i))).toLinearMap :
          Submodule ℚ _) = 2 ∧
    (∀ i j, i ≠ j → LinearIndependent ℚ ![five i, five j]) ∧
      Module.finrank ℚ (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ 3 ⊓
        ⨅ i, LinearMap.ker (MvPolynomial.aeval (five i)).toLinearMap : Submodule ℚ _) ≠ 2 := by
  have hl : ∀ i j : Fin 8, i ≠ j →
      LinearIndependent ℚ ![gridQ (Fin.castSucc i), gridQ (Fin.castSucc j)] :=
    fun i j h => gridQ_li _ _ (fun e => h (Fin.castSucc_injective _ e))
  refine ⟨hl, (l14_finrank_eq_two_iff _ hl).2 gridQ_gp, five_li, fun h => ?_⟩
  have := ((l14_finrank_eq_two_iff _ five_li).1 h).1 (X 1) (isHomogeneous_X ℚ 1) (X_ne_zero 1)
    {0, 1, 2, 3, 4} (by intro i hi; fin_cases hi <;> simp [five])
  simp at this

/-- **Witness (criterion).** For the first eight grid points the space of cubics through
them has dimension exactly `2`; for eight points with five on the line `y = 0` it does not.
@isnad1 id=other.0h0v.s12.71f7e38d8859 from=translated src=- shape=991da269 vocab=1f01a3a6
-/
theorem l14w_finrank_eq_two_iff :
    let P : Fin 9 → Fin 3 → ℚ :=
      ![![-1, -1, 1], ![-1, 0, 1], ![-1, 1, 1], ![0, -1, 1], ![0, 0, 1], ![0, 1, 1],
        ![1, -1, 1], ![1, 0, 1], ![1, 1, 1]]
    let Q : Fin 8 → Fin 3 → ℚ :=
      ![![0, 0, 1], ![1, 0, 1], ![2, 0, 1], ![3, 0, 1], ![4, 0, 1],
        ![0, 1, 1], ![1, 1, 1], ![0, 2, 1]]
    (∀ i j : Fin 8, i ≠ j →
        LinearIndependent ℚ ![(P (Fin.castSucc i)), (P (Fin.castSucc j))]) ∧
      Module.finrank ℚ (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ 3 ⊓
        ⨅ i : Fin 8, LinearMap.ker (MvPolynomial.aeval ((P (Fin.castSucc i)))).toLinearMap :
          Submodule ℚ _) = 2 ∧
    (∀ i j, i ≠ j → LinearIndependent ℚ ![(Q i), (Q j)]) ∧
      Module.finrank ℚ (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ 3 ⊓
        ⨅ i, LinearMap.ker (MvPolynomial.aeval ((Q i))).toLinearMap : Submodule ℚ _) ≠ 2 :=
  w_finrank_core

/-! ### Witnesses for Pascal and Pappus -/

/-- Six points on the conic `x² + y² = z²`.-/
def hexagon : Fin 6 → Fin 3 → ℚ :=
  ![![1, 0, 1], ![0, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 4, 5], ![-4, 3, 5]]

noncomputable def circleQ : MvPolynomial (Fin 3) ℚ := X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2

/--
@isnad1 id=ishomoge.0h0v.s3.67f653c7145c from=translated src=- shape=8067f6a0 vocab=19448c23
-/
theorem circleQ_hom : circleQ.IsHomogeneous 2 :=
  ((isHomogeneous_X_pow 0 2).add (isHomogeneous_X_pow 1 2)).sub (isHomogeneous_X_pow 2 2)

/--
@isnad1 id=ne.2h2v.s7.a16fbf325e99 from=translated src=- shape=81e40d04 vocab=2a897a57
-/
theorem circleQ_irr : ∀ ℓ m : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 →
    circleQ ≠ ℓ * m := by
  intro ℓ m hℓ hm h
  have e : cv E2 circleQ = PlaneCubic.linMul (cv E1 ℓ) (cv E1 m) := by
    apply toP_injective E2 E2_inj
    rw [cv2 circleQ_hom, toP_linMul, cv1 hℓ, cv1 hm, h]
  have hd := PlaneCubic.det_gram_linMul (K := ℚ) two_ne_zero (cv E1 ℓ) (cv E1 m)
  rw [← e] at hd
  have c : cv E2 circleQ = ![1, 0, 0, 1, 0, -1] := by
    apply toP_injective E2 E2_inj
    rw [cv2 circleQ_hom, toP2_eq]; simp [circleQ]; ring
  rw [c] at hd
  simp [PlaneCubic.gram, Matrix.det_fin_three] at hd

/--
@isnad1 id=linearin.1h2v.s9.6a37fbebbc61 from=translated src=- shape=3206e9d8 vocab=21f2dfdd
-/
theorem hexagon_li : ∀ i j, i ≠ j → LinearIndependent ℚ
    ![![hexagon 0, hexagon 1, hexagon 2, hexagon 3, hexagon 4, hexagon 5] i,
      ![hexagon 0, hexagon 1, hexagon 2, hexagon 3, hexagon 4, hexagon 5] j] := by
  intro i j hij
  rw [← crossProduct_ne_zero_iff_linearIndependent]
  fin_cases i <;> fin_cases j <;>
    simp_all [hexagon, cross_apply, funext_iff, Fin.forall_fin_succ] <;> norm_num

/--
@isnad1 id=other.0h0v.s15.4d1fa2cd7ae7 from=translated src=- shape=a4bec468 vocab=31ee9332
-/
theorem w_pascal_core :
    let A := hexagon
    (∀ i j, i ≠ j → LinearIndependent ℚ
      ![![A 0, A 1, A 2, A 3, A 4, A 5] i, ![A 0, A 1, A 2, A 3, A 4, A 5] j]) ∧
    circleQ.IsHomogeneous 2 ∧
    (∀ ℓ m : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → circleQ ≠ ℓ * m) ∧
    (∀ i, MvPolynomial.eval (A i) circleQ = 0) ∧
    LinearIndependent ℚ ![A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4), A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5)] ∧
    LinearIndependent ℚ ![A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5), A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0)] ∧
    LinearIndependent ℚ ![A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0), A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4)] ∧
    Matrix.det ![A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4), A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5),
      A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0)] = 0 := by
  intro A
  have hz : ∀ i, MvPolynomial.eval (A i) circleQ = 0 := by
    intro i; fin_cases i <;> simp [A, hexagon, circleQ] <;> norm_num
  refine ⟨hexagon_li, circleQ_hom, circleQ_irr, hz, ?_, ?_, ?_,
    l14_pascal cardQ _ _ _ _ _ _ hexagon_li _ circleQ_hom circleQ_irr
      (hz 0) (hz 1) (hz 2) (hz 3) (hz 4) (hz 5)⟩ <;>
  · rw [← crossProduct_ne_zero_iff_linearIndependent]
    simp [A, hexagon, cross_apply, funext_iff, Fin.forall_fin_succ]; norm_num

/-- **Witness (Pascal).** Six distinct points on the irreducible conic `x² + y² = z²` over `ℚ`;
the three Pascal points are pairwise distinct projective points and are collinear.
@isnad1 id=other.0h0v.s15.7d00bbf53e0d from=translated src=- shape=abe4b72f vocab=12206f90
-/
theorem l14w_pascal :
    let A : Fin 6 → Fin 3 → ℚ :=
      ![![1, 0, 1], ![0, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, 4, 5], ![-4, 3, 5]]
    let q : MvPolynomial (Fin 3) ℚ := X 0 ^ 2 + X 1 ^ 2 - X 2 ^ 2
    (∀ i j, i ≠ j → LinearIndependent ℚ
      ![![A 0, A 1, A 2, A 3, A 4, A 5] i, ![A 0, A 1, A 2, A 3, A 4, A 5] j]) ∧
    q.IsHomogeneous 2 ∧
    (∀ ℓ m : MvPolynomial (Fin 3) ℚ, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → q ≠ ℓ * m) ∧
    (∀ i, MvPolynomial.eval (A i) q = 0) ∧
    LinearIndependent ℚ ![A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4), A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5)] ∧
    LinearIndependent ℚ ![A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5), A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0)] ∧
    LinearIndependent ℚ ![A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0), A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4)] ∧
    Matrix.det ![A 0 ⨯₃ A 1 ⨯₃ (A 3 ⨯₃ A 4), A 1 ⨯₃ A 2 ⨯₃ (A 4 ⨯₃ A 5),
      A 2 ⨯₃ A 3 ⨯₃ (A 5 ⨯₃ A 0)] = 0 :=
  w_pascal_core

/-- **Witness (Pappus).** `A₁, A₃, A₅ = (1,0), (2,0), (4,0)` on `y = 0`, `A₂, A₄, A₆ = (0,1),
(1,1), (3,1)` on `y = z`; the three Pappus points are pairwise distinct and collinear.
@isnad1 id=other.0h0v.s15.28c98a2ef20a from=translated src=- shape=f1bb43e4 vocab=8273043c
-/
theorem l14w_pappus :
    let A₁ : Fin 3 → ℚ := ![1, 0, 1]; let A₂ : Fin 3 → ℚ := ![0, 1, 1]
    let A₃ : Fin 3 → ℚ := ![2, 0, 1]; let A₄ : Fin 3 → ℚ := ![1, 1, 1]
    let A₅ : Fin 3 → ℚ := ![4, 0, 1]; let A₆ : Fin 3 → ℚ := ![3, 1, 1]
    let l : Fin 3 → ℚ := ![0, 1, 0]; let m : Fin 3 → ℚ := ![0, 1, -1]
    (l ⬝ᵥ A₁ = 0 ∧ l ⬝ᵥ A₃ = 0 ∧ l ⬝ᵥ A₅ = 0 ∧ m ⬝ᵥ A₂ = 0 ∧ m ⬝ᵥ A₄ = 0 ∧ m ⬝ᵥ A₆ = 0) ∧
    (m ⬝ᵥ A₁ ≠ 0 ∧ m ⬝ᵥ A₃ ≠ 0 ∧ m ⬝ᵥ A₅ ≠ 0 ∧ l ⬝ᵥ A₂ ≠ 0 ∧ l ⬝ᵥ A₄ ≠ 0 ∧ l ⬝ᵥ A₆ ≠ 0) ∧
    (LinearIndependent ℚ ![A₁, A₃] ∧ LinearIndependent ℚ ![A₁, A₅] ∧
      LinearIndependent ℚ ![A₃, A₅] ∧ LinearIndependent ℚ ![A₂, A₄] ∧
      LinearIndependent ℚ ![A₂, A₆] ∧ LinearIndependent ℚ ![A₄, A₆]) ∧
    LinearIndependent ℚ ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆)] ∧
    LinearIndependent ℚ ![A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆), A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] ∧
    LinearIndependent ℚ ![A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁), A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅)] ∧
    Matrix.det ![A₁ ⨯₃ A₂ ⨯₃ (A₄ ⨯₃ A₅), A₂ ⨯₃ A₃ ⨯₃ (A₅ ⨯₃ A₆),
      A₃ ⨯₃ A₄ ⨯₃ (A₆ ⨯₃ A₁)] = 0 := by
  intro A₁ A₂ A₃ A₄ A₅ A₆ l m
  have hli : ∀ u v : Fin 3 → ℚ, u ⨯₃ v ≠ 0 → LinearIndependent ℚ ![u, v] :=
    fun u v h => crossProduct_ne_zero_iff_linearIndependent.1 h
  have h1 : l ⬝ᵥ A₁ = 0 ∧ l ⬝ᵥ A₃ = 0 ∧ l ⬝ᵥ A₅ = 0 ∧ m ⬝ᵥ A₂ = 0 ∧ m ⬝ᵥ A₄ = 0 ∧
      m ⬝ᵥ A₆ = 0 := by
    simp [A₁, A₂, A₃, A₄, A₅, A₆, l, m, dotProduct, Fin.sum_univ_succ]
  have h2 : m ⬝ᵥ A₁ ≠ 0 ∧ m ⬝ᵥ A₃ ≠ 0 ∧ m ⬝ᵥ A₅ ≠ 0 ∧ l ⬝ᵥ A₂ ≠ 0 ∧ l ⬝ᵥ A₄ ≠ 0 ∧
      l ⬝ᵥ A₆ ≠ 0 := by
    simp [A₁, A₂, A₃, A₄, A₅, A₆, l, m, dotProduct, Fin.sum_univ_succ]
  have h3 : LinearIndependent ℚ ![A₁, A₃] ∧ LinearIndependent ℚ ![A₁, A₅] ∧
      LinearIndependent ℚ ![A₃, A₅] ∧ LinearIndependent ℚ ![A₂, A₄] ∧
      LinearIndependent ℚ ![A₂, A₆] ∧ LinearIndependent ℚ ![A₄, A₆] := by
    refine ⟨hli _ _ ?_, hli _ _ ?_, hli _ _ ?_, hli _ _ ?_, hli _ _ ?_, hli _ _ ?_⟩ <;>
      simp [A₁, A₂, A₃, A₄, A₅, A₆, cross_apply, funext_iff, Fin.forall_fin_succ] <;> norm_num
  refine ⟨h1, h2, h3, hli _ _ ?_, hli _ _ ?_, hli _ _ ?_, l14_pappus cardQ A₁ A₂ A₃ A₄ A₅ A₆ l m
    h1.1 h1.2.1 h1.2.2.1 h1.2.2.2.1 h1.2.2.2.2.1 h1.2.2.2.2.2 h2.1 h2.2.1 h2.2.2.1 h2.2.2.2.1
    h2.2.2.2.2.1 h2.2.2.2.2.2 h3.1 h3.2.1 h3.2.2.1 h3.2.2.2.1 h3.2.2.2.2.1 h3.2.2.2.2.2⟩ <;>
    simp [A₁, A₂, A₃, A₄, A₅, A₆, cross_apply, funext_iff, Fin.forall_fin_succ] <;> norm_num

/-! ### Line lemma: witness and the `𝔽₂` sharpness, Mathlib-only -/

/-- **Witness (line lemma).** Over `ℚ`, `F = z (x² + y² + z²)` vanishes on the line `z = 0`;
it is nonzero and the lemma produces the nonzero conic factor.
@isnad1 id=other.0h0v.s10.5c86eeec35db from=translated src=- shape=05fbce8e vocab=5b323c00
-/
theorem l14w_line_lemma :
    let F : MvPolynomial (Fin 3) ℚ := X 2 * (X 0 ^ 2 + X 1 ^ 2 + X 2 ^ 2)
    F.IsHomogeneous 3 ∧ F ≠ 0 ∧ (∀ v : Fin 3 → ℚ, MvPolynomial.eval v (X 2) = 0 →
      MvPolynomial.eval v F = 0) ∧
    ∃ q : MvPolynomial (Fin 3) ℚ, q.IsHomogeneous 2 ∧ q ≠ 0 ∧ F = X 2 * q := by
  intro F
  have hF : F.IsHomogeneous 3 := (isHomogeneous_X ℚ 2).mul
    (((isHomogeneous_X_pow 0 2).add (isHomogeneous_X_pow 1 2)).add (isHomogeneous_X_pow 2 2))
  have hF0 : F ≠ 0 := fun h => by
    have := congrArg (MvPolynomial.eval ![0, 0, 1]) h; simp [F] at this
  have hv : ∀ v : Fin 3 → ℚ, MvPolynomial.eval v (X 2) = 0 → MvPolynomial.eval v F = 0 :=
    fun v h => by simp only [F, map_mul]; rw [h, zero_mul]
  obtain ⟨q, hq, he⟩ := l14_line_lemma ⟨2, two_ne_zero, by norm_num⟩ F (X 2) hF
    (isHomogeneous_X ℚ 2) (X_ne_zero 2) hv
  exact ⟨hF, hF0, hv, q, hq, fun h => hF0 (by rw [he, h, mul_zero]), he⟩

/-- **Line lemma fails over `𝔽₂`** (`line_lemma_false_zmod_two`), Mathlib-only: `x²y + xy²`
vanishes at every point of `z = 0` over `ZMod 2` but is not divisible by `z`.
@isnad1 id=and.0h0v.s12.5b6454a5b5a6 from=translated src=- shape=562c1252 vocab=2a484c12
-/
theorem l14_line_lemma_false_zmod_two :
    (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)).IsHomogeneous 3 ∧
    (∀ v : Fin 3 → ZMod 2, MvPolynomial.eval v (X 2) = 0 →
      MvPolynomial.eval v (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = 0) ∧
    ¬ ∃ q : MvPolynomial (Fin 3) (ZMod 2),
      (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = X 2 * q := by
  refine ⟨((isHomogeneous_X_pow 0 2).mul (isHomogeneous_X _ 1)).add
    ((isHomogeneous_X _ 0).mul (isHomogeneous_X_pow 1 2)), fun v _ => ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow, MvPolynomial.eval_X]
    generalize v 0 = a; generalize v 1 = b; revert a b; decide
  · rintro ⟨q, hq⟩
    classical
    have := congrArg (coeff (ex 2 1 0)) hq
    rw [coeff_X_mul', ite_eq_right (by simp)] at this
    have e : (X 0 ^ 2 * X 1 + X 0 * X 1 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) =
        monomial (ex 2 1 0) 1 + monomial (ex 1 2 0) 1 := by
      rw [monomial_ex, monomial_ex]; simp
    rw [e, coeff_add, coeff_monomial, coeff_monomial, ite_eq_left rfl, ite_eq_right (by simp [ex_inj])]
      at this
    simp at this

/-! ### Pascal and Pappus with the three points given by their defining property -/

/--
@isnad1 id=ex.3h4v.s11.6d3c8d0e010a from=translated src=- shape=f6558401 vocab=ec07f610
-/
theorem l14b_on_two {u v X : Fin 3 → K} (huv : u ⨯₃ v ≠ 0) (hu : X ⬝ᵥ u = 0)
    (hv : X ⬝ᵥ v = 0) : ∃ c : K, X = c • (u ⨯₃ v) := by
  obtain ⟨c, hc⟩ := PlaneCubic.lin_two huv hu hv
  exact ⟨c, hc⟩

/--
@isnad1 id=eq.4h10v.s8.c733abe7b9c5 from=translated src=- shape=7f1fd400 vocab=aba55e84
-/
theorem l14b_det_smul {X Y Z X₀ Y₀ Z₀ : Fin 3 → K} {a b c : K} (hX : X = a • X₀)
    (hY : Y = b • Y₀) (hZ : Z = c • Z₀) (h : Matrix.det ![X₀, Y₀, Z₀] = 0) :
    Matrix.det ![X, Y, Z] = 0 := by
  rw [← triple_product_eq_det] at h ⊢
  rw [hX, hY, hZ]
  simp [smul_dotProduct, h]

/--
@isnad1 id=ex.3h6v.s14.4efe7ea370a6 from=translated src=- shape=28a3f7d6 vocab=8abb27a4
-/
theorem l14b_meet {A B C D X : Fin 3 → K} (h : A ⨯₃ B ⨯₃ (C ⨯₃ D) ≠ 0 ∨ C ⨯₃ D ⨯₃ (A ⨯₃ B) ≠ 0)
    (h1 : Matrix.det ![X, A, B] = 0) (h2 : Matrix.det ![X, C, D] = 0) :
    ∃ c : K, X = c • (A ⨯₃ B ⨯₃ (C ⨯₃ D)) := by
  rw [← triple_product_eq_det] at h1 h2
  have h' : A ⨯₃ B ⨯₃ (C ⨯₃ D) ≠ 0 := by
    rcases h with h | h
    · exact h
    · rwa [← cross_anticomm, neg_ne_zero] at h
  exact l14b_on_two h' h1 h2

/-- **Pascal, intersection points by their defining property** (`pascal_clean` +
`pascal_generic`). Any `X` on the lines `A₁A₂` and `A₄A₅`, `Y` on `A₂A₃` and `A₅A₆`, `Z` on
`A₃A₄` and `A₆A₁` (incidence of projective points as `det = 0`) are collinear.
@isnad1 id=eq.16h11v.s11.2a43c4b0bcfd from=translated src=- shape=a4338937 vocab=14f5c580
-/
theorem l14_pascal_points (hK : ∃ s : Finset K, 10 < s.card) (A₁ A₂ A₃ A₄ A₅ A₆ : Fin 3 → K)
    (hA : ∀ i j, i ≠ j →
      LinearIndependent K ![![A₁, A₂, A₃, A₄, A₅, A₆] i, ![A₁, A₂, A₃, A₄, A₅, A₆] j])
    (q : MvPolynomial (Fin 3) K) (hq : q.IsHomogeneous 2)
    (hirr : ∀ ℓ m : MvPolynomial (Fin 3) K, ℓ.IsHomogeneous 1 → m.IsHomogeneous 1 → q ≠ ℓ * m)
    (hq₁ : MvPolynomial.eval A₁ q = 0) (hq₂ : MvPolynomial.eval A₂ q = 0)
    (hq₃ : MvPolynomial.eval A₃ q = 0) (hq₄ : MvPolynomial.eval A₄ q = 0)
    (hq₅ : MvPolynomial.eval A₅ q = 0) (hq₆ : MvPolynomial.eval A₆ q = 0)
    (X Y Z : Fin 3 → K)
    (hX₁ : Matrix.det ![X, A₁, A₂] = 0) (hX₂ : Matrix.det ![X, A₄, A₅] = 0)
    (hY₁ : Matrix.det ![Y, A₂, A₃] = 0) (hY₂ : Matrix.det ![Y, A₅, A₆] = 0)
    (hZ₁ : Matrix.det ![Z, A₃, A₄] = 0) (hZ₂ : Matrix.det ![Z, A₆, A₁] = 0) :
    Matrix.det ![X, Y, Z] = 0 := by
  have h := l14_pascal hK A₁ A₂ A₃ A₄ A₅ A₆ hA q hq hirr hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
  rw [l14b_eval2 hq] at hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
  obtain ⟨-, hL⟩ := PlaneCubic.pascal_generic A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ (l14b_pairwise hA) _
    (l14b_irr hq hirr) hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ rfl rfl rfl
  obtain ⟨a, ha⟩ := l14b_meet (Or.inl (hL 0 1)) hX₁ hX₂
  obtain ⟨b, hb⟩ := l14b_meet (C := A₅) (D := A₆) (Or.inr (hL 2 0)) hY₁ hY₂
  obtain ⟨c, hc⟩ := l14b_meet (Or.inl (hL 1 2)) hZ₁ hZ₂
  exact l14b_det_smul ha hb hc h

/-- **Pappus, intersection points by their defining property** (`pappus_clean` +
`pappus_generic`).
@isnad1 id=eq.25h12v.s11.acf193989c13 from=translated src=- shape=8249e77f vocab=9d3fcd6b
-/
theorem l14_pappus_points (hK : ∃ s : Finset K, 10 < s.card) (A₁ A₂ A₃ A₄ A₅ A₆ l m : Fin 3 → K)
    (hl₁ : l ⬝ᵥ A₁ = 0) (hl₃ : l ⬝ᵥ A₃ = 0) (hl₅ : l ⬝ᵥ A₅ = 0)
    (hm₂ : m ⬝ᵥ A₂ = 0) (hm₄ : m ⬝ᵥ A₄ = 0) (hm₆ : m ⬝ᵥ A₆ = 0)
    (hm₁ : m ⬝ᵥ A₁ ≠ 0) (hm₃ : m ⬝ᵥ A₃ ≠ 0) (hm₅ : m ⬝ᵥ A₅ ≠ 0)
    (hl₂ : l ⬝ᵥ A₂ ≠ 0) (hl₄ : l ⬝ᵥ A₄ ≠ 0) (hl₆ : l ⬝ᵥ A₆ ≠ 0)
    (a13 : LinearIndependent K ![A₁, A₃]) (a15 : LinearIndependent K ![A₁, A₅])
    (a35 : LinearIndependent K ![A₃, A₅]) (a24 : LinearIndependent K ![A₂, A₄])
    (a26 : LinearIndependent K ![A₂, A₆]) (a46 : LinearIndependent K ![A₄, A₆])
    (X Y Z : Fin 3 → K)
    (hX₁ : Matrix.det ![X, A₁, A₂] = 0) (hX₂ : Matrix.det ![X, A₄, A₅] = 0)
    (hY₁ : Matrix.det ![Y, A₂, A₃] = 0) (hY₂ : Matrix.det ![Y, A₅, A₆] = 0)
    (hZ₁ : Matrix.det ![Z, A₃, A₄] = 0) (hZ₂ : Matrix.det ![Z, A₆, A₁] = 0) :
    Matrix.det ![X, Y, Z] = 0 := by
  have h := l14_pappus hK A₁ A₂ A₃ A₄ A₅ A₆ l m hl₁ hl₃ hl₅ hm₂ hm₄ hm₆ hm₁ hm₃ hm₅ hl₂ hl₄
    hl₆ a13 a15 a35 a24 a26 a46
  obtain ⟨-, hL, -⟩ := PlaneCubic.pappus_generic A₁ A₂ A₃ A₄ A₅ A₆ _ _ _ l m hl₁ hl₃ hl₅
    hm₂ hm₄ hm₆ hm₁ hm₃ hm₅ hl₂ hl₄ hl₆ (l14b_cross a13) (l14b_cross a15) (l14b_cross a35)
    (l14b_cross a24) (l14b_cross a26) (l14b_cross a46) rfl rfl rfl
  obtain ⟨a, ha⟩ := l14b_meet (Or.inl (hL 0 1)) hX₁ hX₂
  obtain ⟨b, hb⟩ := l14b_meet (C := A₅) (D := A₆) (Or.inr (hL 2 0)) hY₁ hY₂
  obtain ⟨c, hc⟩ := l14b_meet (Or.inl (hL 1 2)) hZ₁ hZ₂
  exact l14b_det_smul ha hb hc h

end CBL14
-- Tengoku: root names of this library moved to Tengoku.CayleyBacharach so they do not collide with other libraries (generated)
