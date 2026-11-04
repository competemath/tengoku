import Tengoku.ErdosLean.ErdosLean.Erdos494.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Erdős 494, part D5: Roth's lemma for two variables (Wronskian proof).

A nonzero `P ∈ ℤ[X,Y]` of bidegree `≤ (r1,r2)`, height `≤ H`, with `r2 ≤ η r1`,
`q1^{r1} ≤ q2^{r2}` and `64^{r1} H ≤ q1^{η r1}`, has a nonvanishing Hasse derivative of
weight `< 4√η` at `ξ = (p1/q1, p2/q2)` (reduced fractions).

Proof (Schmidt, *Diophantine Approximation*, LNM 785, Ch. V, case `m = 2`): write
`P = Σ_{k=0}^{l} φ_k(X) ψ_k(Y)` with `l ≤ r2` minimal (so both families are linearly
independent over `ℚ`).  `W = det(D^{(μ,ν)} P)_{μ,ν ≤ l} = U(X) V(Y)` with `U, V` the Wronskians
of `φ`, `ψ`, nonzero by `wronskian_ne_zero`.  Height: `H(W) ≤ (32^{r1} H)^{l+1}`.
Upper bound: by Gauss (`gauss_order_bound`), `q1^{ord_ξ1 U} q2^{ord_ξ2 V} ≤ H(W)`, so the
weighted index of `W` at `ξ` is `≤ (l+1) η`.  Lower bound: if all derivatives of weight
`< Θ = 4√η` vanish, each entry has index `≥ Θ - η - ν/r2`, so the index of `W` is
`≥ Σ_{ν≤l} max(0, Θ - η - ν/r2) ≥ (l+1)(3√η)^2/4 > (l+1) η`.  Contradiction.

Formalization notes: bivariate polynomials live in `R[X][X]` (inner variable `X`, outer `Y`).
We only use the coarser bound `q1^{e1} q2^{e2} ≤ N^2` (with `N` the leading coefficient of the
integer Wronskian), which suffices once `η ≤ 1/4`; for `η > 1/4` the statement is trivial
(every Taylor coefficient has weight `≤ 2 < 4√η`). -/

open Polynomial Finset

namespace Erdos494
namespace RL2

/-- The Wronskian matrix.-/
noncomputable def a2_wr {m : ℕ} (f : Fin m → Polynomial ℚ) : Matrix (Fin m) (Fin m) (Polynomial ℚ) :=
  Matrix.of fun (μ k : Fin m) => Polynomial.derivative^[(μ : ℕ)] (f k)

/--
@isnad1 id=eq.0h3v.s8.27e2fa7d638b from=translated src=- shape=b50efda2 vocab=2ba7cefa
-/
lemma a2_iterate_derivative_add' (p q : Polynomial ℚ) (k : ℕ) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by
  induction k generalizing p q with
  | zero => simp
  | succ k ih => simp [Function.iterate_succ_apply, ih]

/--
@isnad1 id=eq.1h4v.s6.609cefe19dc8 from=translated src=- shape=c4a8f595 vocab=32a923fb
-/
lemma a2_coeff_prod_of_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → Polynomial ℚ)
    (e : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ e i) :
    (∏ i ∈ s, p i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, (p i).coeff (e i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    have h1 : (p a).natDegree ≤ e a := h a (Finset.mem_insert_self a s)
    have h2 : (∏ i ∈ s, p i).natDegree ≤ ∑ i ∈ s, e i :=
      (natDegree_prod_le _ _).trans
        (Finset.sum_le_sum fun i hi => h i (Finset.mem_insert_of_mem hi))
    rw [coeff_mul_add_eq_of_natDegree_le h1 h2, ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/--
@isnad1 id=ne.2h2v.s6.fc8d84e6a044 from=translated src=- shape=bcca700e vocab=690d99a2
-/
lemma a2_det_ne_zero_of_injective {m : ℕ} (f : Fin m → Polynomial ℚ) (hne : ∀ k, f k ≠ 0)
    (hinj : Function.Injective fun k => (f k).natDegree) : (a2_wr f).det ≠ 0 := by
  set d : Fin m → ℕ := fun k => (f k).natDegree with hd
  set N : ℕ := ∑ k, d k - ∑ μ : Fin m, (μ : ℕ) with hN
  have key : ∀ σ : Equiv.Perm (Fin m),
      (∏ k, derivative^[(σ k : ℕ)] (f k)).coeff N
        = ∏ k, ((f k).leadingCoeff * ((d k).descFactorial (σ k) : ℚ)) := by
    intro σ
    by_cases h : ∀ k, (σ k : ℕ) ≤ d k
    · have hN' : N = ∑ k, (d k - σ k) := by
        rw [Finset.sum_tsub_distrib _ (fun k _ => h k), hN]
        congr 1
        exact (Equiv.sum_comp σ (fun μ : Fin m => (μ : ℕ))).symm
      rw [hN', a2_coeff_prod_of_le _ _ _ (fun k _ => by
        have := natDegree_iterate_derivative (f k) (σ k); simpa [hd] using this)]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [coeff_iterate_derivative, Nat.sub_add_cancel (h k), nsmul_eq_mul, mul_comm]
      rfl
    · push Not at h
      obtain ⟨k, hk⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ k) (iterate_derivative_eq_zero hk),
        Finset.prod_eq_zero (Finset.mem_univ k)]
      · simp
      · simp [(Nat.descFactorial_eq_zero_iff_lt).mpr hk]
  -- the coefficient of `X^N` in the Wronskian
  let D : Matrix (Fin m) (Fin m) ℚ := Matrix.of fun (μ k : Fin m) => ((d k).descFactorial μ : ℚ)
  have hcoeff : (a2_wr f).det.coeff N = (∏ k, (f k).leadingCoeff) * D.det := by
    have e1 : (a2_wr f).det.coeff N
        = (Matrix.of fun (μ k : Fin m) => (f k).leadingCoeff * D μ k).det := by
      rw [Matrix.det_apply, Matrix.det_apply, finsetSum_coeff]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [Units.smul_def, Units.smul_def, zsmul_eq_mul, zsmul_eq_mul, ← C_eq_intCast,
        coeff_C_mul]
      simp only [a2_wr, Matrix.of_apply, D]
      rw [key]
    rw [e1, ← Matrix.det_transpose D, ← Matrix.det_mul_column]
    conv_lhs => rw [← Matrix.det_transpose]
    rfl
  have hD : D.det ≠ 0 := by
    have hv := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
      (fun k => (d k : ℚ)) (fun μ => descPochhammer ℚ μ)
      (fun μ => descPochhammer_natDegree ℚ μ) (fun μ => monic_descPochhammer ℚ μ)
    have hDt : D = (Matrix.of fun (i j : Fin m) =>
        (descPochhammer ℚ (j : ℕ)).eval ((d i : ℕ) : ℚ)).transpose := by
      ext μ k
      simp [D, descPochhammer_eval_eq_descFactorial]
    rw [hDt, Matrix.det_transpose, ← hv, Matrix.det_vandermonde_ne_zero_iff]
    intro a b hab
    exact hinj (Nat.cast_injective hab)
  intro h0
  have : (a2_wr f).det.coeff N = 0 := by rw [h0]; simp
  rw [hcoeff] at this
  refine (mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => ?_) hD) this
  exact leadingCoeff_ne_zero.mpr (hne k)

/--
@isnad1 id=ne.2h3v.s6.1acd995622a7 from=translated src=- shape=01c5eedb vocab=ab00d39a
-/
lemma a2_wmain {m : ℕ} (n : ℕ) : ∀ f : Fin m → Polynomial ℚ, (∑ k, (f k).natDegree) = n →
    LinearIndependent ℚ f → (a2_wr f).det ≠ 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro f hn hf
  by_cases hinj : Function.Injective fun k => (f k).natDegree
  · exact a2_det_ne_zero_of_injective f (fun k => hf.ne_zero k) hinj
  simp only [Function.Injective, not_forall] at hinj
  obtain ⟨a, b, hdeg, hab⟩ := hinj
  have hfa : f a ≠ 0 := hf.ne_zero a
  have hla : (f a).leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hfa
  set c : ℚ := -((f b).leadingCoeff / (f a).leadingCoeff) with hc
  set g : Fin m → Polynomial ℚ := Function.update f b (f b + c • f a) with hg
  have hba : b ≠ a := fun h => hab h.symm
  have hgli : LinearIndependent ℚ g := by
    refine hf.update b _ ⟨1, one_mem _, Finsupp.single b 1 + Finsupp.single a c, ?_, ?_⟩
    · simp [hab]
    · simp [Finsupp.linearCombination_single, map_add]
  have hwr : a2_wr g = Matrix.updateCol (a2_wr f) b (fun k => a2_wr f k b + C c • a2_wr f k a) := by
    ext μ k : 1
    by_cases hk : k = b
    · subst hk
      simp [a2_wr, hg, smul_eq_C_mul]
    · simp [a2_wr, hg, hk]
  have hdet : (a2_wr g).det = (a2_wr f).det := by
    rw [hwr]; exact Matrix.det_updateCol_add_smul_self (a2_wr f) hba (C c)
  have hgb : g b = f b + c • f a := by simp [hg]
  have hgb0 : g b ≠ 0 := hgli.ne_zero b
  have hle : (g b).natDegree ≤ (f b).natDegree := by
    rw [hgb]
    refine (natDegree_add_le _ _).trans (max_le le_rfl ?_)
    exact (natDegree_smul_le _ _).trans (le_of_eq hdeg)
  have hcoef : (g b).coeff (f b).natDegree = 0 := by
    have hA : (f a).coeff (f b).natDegree = (f a).leadingCoeff := by rw [← hdeg]; rfl
    rw [hgb, coeff_add, coeff_smul, hA, smul_eq_mul]
    change (f b).leadingCoeff + c * (f a).leadingCoeff = 0
    rw [hc]; field_simp; ring
  have hlt : (g b).natDegree < (f b).natDegree := by
    refine lt_of_le_of_ne hle fun h => ?_
    have : (g b).leadingCoeff = 0 := by rw [leadingCoeff, h]; exact hcoef
    exact hgb0 (leadingCoeff_eq_zero.mp this)
  have hsum : ∑ k, (g k).natDegree < n := by
    rw [← hn]
    refine Finset.sum_lt_sum (fun k _ => ?_) ⟨b, Finset.mem_univ _, hlt⟩
    by_cases hk : k = b
    · subst hk; exact hle
    · simp [hg, hk]
  rw [← hdet]
  exact ih _ hsum g rfl hgli

/--
@isnad1 id=ne.1h2v.s8.17a39d10271a from=translated src=- shape=7cda5acc vocab=8eee557b
-/
theorem wronskian_ne_zero {m : ℕ} (f : Fin m → Polynomial ℚ) (hf : LinearIndependent ℚ f) :
    (Matrix.of fun (μ k : Fin m) => Polynomial.derivative^[(μ : ℕ)] (f k)).det ≠ 0 :=
  a2_wmain _ f rfl hf

/--
@isnad1 id=dvd.3h4v.s7.13ea75757c2a from=translated src=- shape=28866b7c vocab=f84fe7b1
-/
theorem gauss_order_bound (U : Polynomial ℤ) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : IsCoprime p (q : ℤ)) (e : ℕ)
    (hdvd : (Polynomial.X - Polynomial.C ((p : ℚ) / q)) ^ e ∣ U.map (Int.castRingHom ℚ)) :
    (q : ℤ) ^ e ∣ U.leadingCoeff := by
  set V : ℤ[X] := C (q : ℤ) * X + C (-p) with hV
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
  have hVcoeff1 : V.coeff 1 = q := by
    rw [hV, coeff_add, coeff_C_mul, coeff_X_one, coeff_C]; simp
  have hVcoeff0 : V.coeff 0 = -p := by
    rw [hV, coeff_add, coeff_C_mul, coeff_X_zero, coeff_C_zero]; simp
  have hVlc : V.leadingCoeff = q := leadingCoeff_linear hq0
  have hVprim : V.IsPrimitive := by
    intro r hr
    rw [C_dvd_iff_dvd_coeff] at hr
    have h1 := hr 1
    have h0 := hr 0
    rw [hVcoeff1] at h1
    rw [hVcoeff0, dvd_neg] at h0
    exact hcop.isUnit_of_dvd' h0 h1
  have hVpow : ∀ n : ℕ, (V ^ n).IsPrimitive := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ]; exact ih.mul hVprim
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have hmapV : V.map (Int.castRingHom ℚ) = C ((q : ℚ)) * (X - C ((p : ℚ) / q)) := by
    rw [hV, Polynomial.map_add, Polynomial.map_mul, map_C, map_C, map_X, mul_sub, ← C_mul,
      mul_div_cancel₀ _ hq', sub_eq_add_neg, ← C_neg]
    simp
  have hdiv : V ^ e ∣ U := by
    rw [IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast _ _ (hVpow e), Polynomial.map_pow, hmapV,
      mul_pow, ← C_pow]
    have hu : IsUnit (C ((q : ℚ) ^ e)) :=
      isUnit_C.mpr (IsUnit.pow _ (isUnit_iff_ne_zero.mpr hq'))
    exact hu.mul_left_dvd.mpr hdvd
  obtain ⟨W, hW⟩ := hdiv
  rw [hW, leadingCoeff_mul, leadingCoeff_pow, hVlc]
  exact dvd_mul_right _ _

/-! ### An `ℓ¹`-type norm on polynomials -/

/-- Norm-like functions on a ring.-/
structure NormLike {R : Type*} [Ring R] (ν : R → ℝ) : Prop where
  zero : ν 0 = 0
  nonneg : ∀ a, 0 ≤ ν a
  add : ∀ a b, ν (a + b) ≤ ν a + ν b
  mul : ∀ a b, ν (a * b) ≤ ν a * ν b
  neg : ∀ a, ν (-a) = ν a
  one : ν 1 ≤ 1

/-- `ℓ¹` norm of the coefficients, measured by `ν`.-/
noncomputable def L1 {R : Type*} [Semiring R] (ν : R → ℝ) (p : R[X]) : ℝ :=
  p.sum fun _ a => ν a

/--
@isnad1 id=eq.2h4v.s6.b7593039e9a1 from=translated src=- shape=db6c0e40 vocab=63654055
-/
lemma L1_eq_sum {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) (p : R[X]) (s : Finset ℕ)
    (hs : p.support ⊆ s) : L1 ν p = ∑ i ∈ s, ν (p.coeff i) := by
  unfold L1
  rw [Polynomial.sum_def]
  apply Finset.sum_subset hs
  intro i _ hi
  rw [Polynomial.notMem_support_iff.mp hi, hν.zero]

/--
@isnad1 id=eq.1h4v.s7.74aa2e7310cb from=translated src=- shape=bd69954d vocab=8bd725e0
-/
lemma L1_monomial {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) (n : ℕ) (a : R) :
    L1 ν (monomial n a) = ν a := by
  unfold L1
  rw [Polynomial.sum_monomial_index]
  exact hν.zero

/--
@isnad1 id=normlike.1h2v.s4.1ff1f131df0a from=translated src=- shape=35e15fe9 vocab=d539c827
-/
lemma L1_normLike {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) : NormLike (L1 ν) where
  zero := by simp [L1]
  nonneg := fun p => by
    unfold L1; rw [Polynomial.sum_def]; exact Finset.sum_nonneg fun i _ => hν.nonneg _
  add := fun p q => by
    classical
    rw [L1_eq_sum hν (p + q) (p.support ∪ q.support) Polynomial.support_add,
      L1_eq_sum hν p (p.support ∪ q.support) Finset.subset_union_left,
      L1_eq_sum hν q (p.support ∪ q.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact hν.add _ _
  mul := fun p q => by
    classical
    rw [Polynomial.mul_eq_sum_sum]
    have hsub : ∀ (s : Finset ℕ) (g : ℕ → R[X]), L1 ν (∑ i ∈ s, g i) ≤ ∑ i ∈ s, L1 ν (g i) := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp [L1]
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        refine le_trans ?_ (add_le_add le_rfl ih)
        rw [L1_eq_sum hν _ ((g a).support ∪ (∑ i ∈ s, g i).support) Polynomial.support_add,
          L1_eq_sum hν (g a) ((g a).support ∪ (∑ i ∈ s, g i).support) Finset.subset_union_left,
          L1_eq_sum hν (∑ i ∈ s, g i) ((g a).support ∪ (∑ i ∈ s, g i).support)
            Finset.subset_union_right, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => by rw [Polynomial.coeff_add]; exact hν.add _ _
    refine le_trans (hsub _ _) ?_
    rw [L1_eq_sum hν p p.support subset_rfl, L1_eq_sum hν q q.support subset_rfl,
      Finset.sum_mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Polynomial.sum_def]
    refine le_trans (hsub _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    rw [L1_monomial hν]
    exact hν.mul _ _
  neg := fun p => by
    rw [L1_eq_sum hν (-p) p.support (by rw [Polynomial.support_neg]),
      L1_eq_sum hν p p.support subset_rfl]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.coeff_neg, hν.neg]
  one := by
    rw [← Polynomial.C_1, ← Polynomial.monomial_zero_left, L1_monomial hν]
    exact hν.one

/--
@isnad1 id=normlike.0h0v.s3.cec58c4e9ca9 from=translated src=- shape=99abad4d vocab=12b7fdf8
-/
lemma normLike_abs : NormLike (fun a : ℤ => (|a| : ℝ)) where
  zero := by simp
  nonneg := fun a => by positivity
  add := fun a b => by push_cast; exact abs_add_le _ _
  mul := fun a b => by push_cast; rw [abs_mul]
  neg := fun a => by push_cast; rw [abs_neg]
  one := by simp

/--
@isnad1 id=le.1h5v.s5.ad77a04209b0 from=translated src=- shape=f777fd36 vocab=f0c30a65
-/
lemma normLike_prod {R : Type*} [CommRing R] {ν : R → ℝ} (hν : NormLike ν) {ι : Type*}
    (s : Finset ι) (g : ι → R) : ν (∏ i ∈ s, g i) ≤ ∏ i ∈ s, ν (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hν.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact le_trans (hν.mul _ _) (mul_le_mul_of_nonneg_left ih (hν.nonneg _))

/--
@isnad1 id=le.1h5v.s5.2248d27b0d1f from=translated src=- shape=f777fd36 vocab=c1e2221c
-/
lemma normLike_sum {R : Type*} [Ring R] {ν : R → ℝ} (hν : NormLike ν) {ι : Type*}
    (s : Finset ι) (g : ι → R) : ν (∑ i ∈ s, g i) ≤ ∑ i ∈ s, ν (g i) :=
  Finset.le_sum_of_subadditive ν hν.zero.le hν.add s g

/-! ### Auxiliary lemmas -/

/-- Coefficient vector to polynomial.-/
noncomputable def a2_L (n : ℕ) : (Fin n → ℚ) →ₗ[ℚ] ℚ[X] where
  toFun v := ∑ i : Fin n, monomial (i : ℕ) (v i)
  map_add' v w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a v := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_monomial]

/--
@isnad1 id=eq.0h2v.s7.665c034f9fde from=translated src=- shape=27eccc86 vocab=0a4c92ea
-/
lemma a2_L_apply (n : ℕ) (v : Fin n → ℚ) : a2_L n v = ∑ i : Fin n, monomial (i : ℕ) (v i) := rfl

/--
@isnad1 id=eq.0h3v.s7.72faff326286 from=translated src=- shape=b2481773 vocab=7b2d7037
-/
lemma a2_L_coeff (n : ℕ) (v : Fin n → ℚ) (i : Fin n) : (a2_L n v).coeff i = v i := by
  rw [a2_L_apply, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro b _ hb; rw [coeff_monomial, ite_eq_right]; exact fun h => hb (Fin.ext h)
  · simp

/--
@isnad1 id=eq.0h1v.s7.ad39b0fac54e from=translated src=- shape=892155da vocab=2e00b798
-/
lemma a2_L_ker (n : ℕ) : LinearMap.ker (a2_L n) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv; funext i; have := a2_L_coeff n v i; rw [hv] at this; simpa using this.symm

/--
@isnad1 id=lt.0h3v.s8.05fd60a1ee18 from=translated src=- shape=5534171e vocab=f3dcf4c2
-/
lemma a2_L_natDegree (n : ℕ) (v : Fin (n+1) → ℚ) (k : ℕ) :
    (hasseDeriv k (a2_L (n+1) v)).natDegree < n + 1 := by
  refine lt_of_le_of_lt (natDegree_hasseDeriv_le _ _) ?_
  refine lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_succ_of_le ?_)
  rw [a2_L_apply]
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => le_trans (natDegree_monomial_le _) ?_
  exact Nat.lt_succ_iff.mp i.2

/--
@isnad1 id=eq.0h4v.s8.41babe6cfe33 from=translated src=- shape=fa06d2cb vocab=b97ddcee
-/
lemma a2_eval_hD_L (n : ℕ) (v : Fin n → ℚ) (i : ℕ) (x : ℚ) :
    (hasseDeriv i (a2_L n v)).eval x = ∑ j : Fin n, ((j : ℕ).choose i : ℚ) * v j * x ^ ((j : ℕ) - i) := by
  rw [a2_L_apply, map_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_monomial, eval_monomial]

/-- Hasse–Wronskian.-/
noncomputable def a2_HWm {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → R[X]) :
    Matrix (Fin m) (Fin m) R[X] :=
  Matrix.of fun (μ k : Fin m) => hasseDeriv (μ : ℕ) (f k)

noncomputable def a2_HW {R : Type*} [CommRing R] {m : ℕ} (f : Fin m → R[X]) : R[X] :=
  (a2_HWm f).det

/--
@isnad1 id=ne.1h2v.s6.2cbfc5f0c79c from=translated src=- shape=d1044aec vocab=43394d20
-/
lemma a2_HW_ne_zero {m : ℕ} (f : Fin m → ℚ[X]) (hf : LinearIndependent ℚ f) : a2_HW f ≠ 0 := by
  have h := wronskian_ne_zero f hf
  have : (Matrix.of fun (μ k : Fin m) => derivative^[(μ : ℕ)] (f k)) =
      Matrix.of fun (μ k : Fin m) => (((μ : ℕ).factorial : ℚ[X])) * a2_HWm f μ k := by
    ext1 μ k
    simp only [Matrix.of_apply, a2_HWm]
    rw [← factorial_smul_hasseDeriv, LinearMap.smul_apply, nsmul_eq_mul]
  rw [this, Matrix.det_mul_column] at h
  exact right_ne_zero_of_mul h

/--
@isnad1 id=eq.1h5v.s8.8caa3da0ff79 from=translated src=- shape=8b88644a vocab=a994a109
-/
lemma a2_HW_comb {R : Type*} [CommRing R] {m : ℕ} (f h : Fin m → R[X])
    (G : Matrix (Fin m) (Fin m) R) (hf : ∀ k', f k' = ∑ k, G k' k • h k) :
    a2_HW f = C G.det * a2_HW h := by
  unfold a2_HW
  have : a2_HWm f = a2_HWm h * (C.mapMatrix G.transpose) := by
    refine Matrix.ext fun μ k' => ?_
    rw [Matrix.mul_apply]
    simp only [a2_HWm, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.transpose_apply]
    rw [hf, map_sum (hasseDeriv (μ : ℕ))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_C_mul, mul_comm]
  rw [this, Matrix.det_mul, ← RingHom.map_det, Matrix.det_transpose, mul_comm]

/--
@isnad1 id=eq.0h2v.s5.75b625461702 from=translated src=- shape=a35ebecc vocab=b35b00ec
-/
lemma a2_HW_map {m : ℕ} (f : Fin m → ℤ[X]) :
    a2_HW (fun k => (f k).map (Int.castRingHom ℚ)) = (a2_HW f).map (Int.castRingHom ℚ) := by
  unfold a2_HW
  rw [← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext μ k
  simp [a2_HWm, hasseDeriv_map]

/-! #### Integer rows and columns, heights -/

noncomputable def a2_vecZ (n : ℕ) (v : Fin n → ℤ) : ℤ[X] := ∑ i : Fin n, monomial (i : ℕ) (v i)

/--
@isnad1 id=eq.0h2v.s7.4a0f87bad3ae from=translated src=- shape=0cdfa083 vocab=f4bbdc84
-/
lemma a2_vecZ_map (n : ℕ) (v : Fin n → ℤ) :
    (a2_vecZ n v).map (Int.castRingHom ℚ) = a2_L n (fun i => (v i : ℚ)) := by
  simp [a2_vecZ, a2_L_apply, Polynomial.map_sum]

/--
@isnad1 id=le.1h4v.s7.f2b23febb0c1 from=translated src=- shape=67ea81dc vocab=feb6d90c
-/
lemma a2_L1_hD_vecZ (n : ℕ) (v : Fin (n+1) → ℤ) (H : ℝ) (hH : ∀ i, |(v i : ℝ)| ≤ H) (μ : ℕ) :
    L1 (fun a : ℤ => (|a| : ℝ)) (hasseDeriv μ (a2_vecZ (n+1) v)) ≤ (n + 1) * 2 ^ n * H := by
  have hν := L1_normLike normLike_abs
  rw [a2_vecZ, map_sum]
  refine le_trans (normLike_sum hν _ _) ?_
  have : ∀ i : Fin (n+1), L1 (fun a : ℤ => (|a| : ℝ)) (hasseDeriv μ (monomial (i : ℕ) (v i))) ≤
      2 ^ n * H := by
    intro i
    rw [hasseDeriv_monomial, L1_monomial normLike_abs]
    push_cast
    rw [abs_mul]
    have h1 : |((i : ℕ).choose μ : ℝ)| ≤ 2 ^ n := by
      rw [abs_of_nonneg (by positivity)]
      have := Nat.choose_le_two_pow (i : ℕ) μ
      have h2 : 2 ^ (i : ℕ) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.lt_succ_iff.mp i.2)
      exact_mod_cast le_trans this h2
    exact mul_le_mul h1 (hH i) (abs_nonneg _) (by positivity)
  refine le_trans (Finset.sum_le_sum fun i _ => this i) ?_
  simp [mul_assoc]

/-! #### Lower bound machinery -/

/--
@isnad1 id=eq.1h4v.s8.795e0718fb09 from=translated src=- shape=148b9b49 vocab=99f58b5f
-/
lemma a2_comp_expand (f : ℚ[X]) (x : ℚ) (r N : ℕ) (hN : f.natDegree < N) :
    f.comp (C x + X ^ r) = ∑ m ∈ range N, C ((hasseDeriv m f).eval x) * X ^ (r * m) := by
  have h1 : f.comp (C x + X ^ r) = (taylor x f).comp (X ^ r) := by
    rw [taylor_apply, comp_assoc]; congr 1; simp [add_comm]
  rw [h1]
  conv_lhs => rw [as_sum_range' (taylor x f) N (by rwa [natDegree_taylor])]
  rw [← coe_compRingHom_apply, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coe_compRingHom_apply, monomial_comp, taylor_coeff, pow_mul]

/--
@isnad1 id=dvd.1h4v.s8.461f07bbee7b from=translated src=- shape=f3560c61 vocab=c4f9d095
-/
lemma a2_det_dvd {R : Type*} [CommRing R] {l : ℕ} (M : Matrix (Fin l) (Fin l) R[X])
    (d : Fin l → ℕ) (h : ∀ i j, X ^ d j ∣ M i j) : X ^ (∑ j, d j) ∣ M.det := by
  rw [Matrix.det_apply]
  refine Finset.dvd_sum fun σ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum, Units.smul_def, zsmul_eq_mul]
  exact dvd_mul_of_dvd_right (Finset.prod_dvd_prod_of_dvd _ _ fun j _ => h _ _) _

/--
@isnad1 id=dvd.3h12v.s10.262b37c14d82 from=translated src=- shape=41dce0a6 vocab=59461b7a
-/
lemma a2_entry_dvd {l : ℕ} (φ ψ : Fin l → ℚ[X]) (x y : ℚ) (r1 r2 N1 N2 d μ ν : ℕ)
    (h1 : ∀ k, (hasseDeriv μ (φ k)).natDegree < N1)
    (h2 : ∀ k, (hasseDeriv ν (ψ k)).natDegree < N2)
    (hT : ∀ m n, r2 * m + r1 * n < d →
      ∑ k, (hasseDeriv (m + μ) (φ k)).eval x * (hasseDeriv (n + ν) (ψ k)).eval y = 0) :
    X ^ d ∣ ∑ k, (hasseDeriv μ (φ k)).comp (C x + X ^ r2) *
      (hasseDeriv ν (ψ k)).comp (C y + X ^ r1) := by
  simp only [fun k => a2_comp_expand _ x r2 N1 (h1 k), fun k => a2_comp_expand _ y r1 N2 (h2 k),
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun m _ => ?_
  rw [Finset.sum_comm]
  refine Finset.dvd_sum fun n _ => ?_
  have key : ∑ k, C ((hasseDeriv m (hasseDeriv μ (φ k))).eval x) * X ^ (r2 * m) *
      (C ((hasseDeriv n (hasseDeriv ν (ψ k))).eval y) * X ^ (r1 * n)) =
      C (∑ k, (hasseDeriv m (hasseDeriv μ (φ k))).eval x *
        (hasseDeriv n (hasseDeriv ν (ψ k))).eval y) * X ^ (r2 * m + r1 * n) := by
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [C_mul, pow_add]; ring
  rw [key]
  by_cases hd : d ≤ r2 * m + r1 * n
  · exact dvd_mul_of_dvd_right (pow_dvd_pow X hd) _
  · have hz : ∑ k, (hasseDeriv m (hasseDeriv μ (φ k))).eval x *
        (hasseDeriv n (hasseDeriv ν (ψ k))).eval y = 0 := by
      have e1 : ∀ f : ℚ[X], hasseDeriv m (hasseDeriv μ f) = (m + μ).choose m • hasseDeriv (m + μ) f :=
        fun f => LinearMap.congr_fun (hasseDeriv_comp m μ) f
      have e2 : ∀ f : ℚ[X], hasseDeriv n (hasseDeriv ν f) = (n + ν).choose n • hasseDeriv (n + ν) f :=
        fun f => LinearMap.congr_fun (hasseDeriv_comp n ν) f
      simp only [e1, e2, eval_smul, nsmul_eq_mul]
      have := hT m n (not_le.mp hd)
      calc _ = ((m + μ).choose m : ℚ) * ((n + ν).choose n : ℚ) * ∑ k, (hasseDeriv (m + μ) (φ k)).eval x
              * (hasseDeriv (n + ν) (ψ k)).eval y := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by simp only [eval_mul, eval_natCast]; ring
        _ = 0 := by rw [this, mul_zero]
    rw [hz, C_0, zero_mul]
    exact dvd_zero _

/--
@isnad1 id=le.5h7v.s8.c52297dc44eb from=translated src=- shape=1947b365 vocab=90778c2a
-/
lemma a2_ord_le (U V : ℚ[X]) (x y : ℚ) (r1 r2 D : ℕ) (hr1 : 1 ≤ r1) (hr2 : 1 ≤ r2)
    (hU : U ≠ 0) (hV : V ≠ 0)
    (h : X ^ D ∣ U.comp (C x + X ^ r2) * V.comp (C y + X ^ r1)) :
    D ≤ r2 * rootMultiplicity x U + r1 * rootMultiplicity y V := by
  obtain ⟨R1, hU1, hR1⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd U hU x
  obtain ⟨R2, hV1, hR2⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd V hV y
  set e1 := rootMultiplicity x U
  set e2 := rootMultiplicity y V
  have hc1 : (X - C x).comp (C x + X ^ r2) = X ^ r2 := by simp
  have hc2 : (X - C y).comp (C y + X ^ r1) = X ^ r1 := by simp
  rw [hU1, hV1, mul_comp, mul_comp, pow_comp, pow_comp, hc1, hc2] at h
  have hG : (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)).eval 0 ≠ 0 := by
    rw [eval_mul, eval_comp, eval_comp]
    simp only [eval_add, eval_C, eval_pow, eval_X, zero_pow (by omega : r2 ≠ 0),
      zero_pow (by omega : r1 ≠ 0), add_zero]
    rw [dvd_iff_isRoot] at hR1 hR2
    exact mul_ne_zero hR1 hR2
  have hh : (X ^ r2) ^ e1 * R1.comp (C x + X ^ r2) * ((X ^ r1) ^ e2 * R2.comp (C y + X ^ r1)) =
      X ^ (r2 * e1 + r1 * e2) * (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)) := by
    rw [pow_add, pow_mul, pow_mul]; ring
  rw [hh] at h
  by_contra hlt
  push_neg at hlt
  have h' : X ^ (r2 * e1 + r1 * e2) * X ∣
      X ^ (r2 * e1 + r1 * e2) * (R1.comp (C x + X ^ r2) * R2.comp (C y + X ^ r1)) :=
    dvd_trans (by rw [← pow_succ]; exact pow_dvd_pow X hlt) h
  rw [mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero), X_dvd_iff, coeff_zero_eq_eval_zero] at h'
  exact hG h'

/--
@isnad1 id=le.7h10v.s9.d877205f6211 from=translated src=- shape=142aa51c vocab=258b9a37
-/
lemma a2_lower {l : ℕ} (φ ψ : Fin l → ℚ[X]) (x y : ℚ) (r1 r2 N1 N2 : ℕ) (hr1 : 1 ≤ r1)
    (hr2 : 1 ≤ r2) (hU : a2_HW φ ≠ 0) (hV : a2_HW ψ ≠ 0) (d : Fin l → ℕ)
    (h1 : ∀ (μ : ℕ) k, (hasseDeriv μ (φ k)).natDegree < N1)
    (h2 : ∀ (ν : ℕ) k, (hasseDeriv ν (ψ k)).natDegree < N2)
    (hT : ∀ (μ ν : Fin l) (m n : ℕ), r2 * m + r1 * n < d ν →
      ∑ k, (hasseDeriv (m + μ) (φ k)).eval x * (hasseDeriv (n + ν) (ψ k)).eval y = 0) :
    ∑ ν, d ν ≤ r2 * rootMultiplicity x (a2_HW φ) + r1 * rootMultiplicity y (a2_HW ψ) := by
  apply a2_ord_le _ _ x y r1 r2 _ hr1 hr2 hU hV
  let A := (compRingHom (C x + X ^ r2)).mapMatrix (a2_HWm φ)
  let B := ((compRingHom (C y + X ^ r1)).mapMatrix (a2_HWm ψ)).transpose
  have hdet : (A * B).det = (a2_HW φ).comp (C x + X ^ r2) * (a2_HW ψ).comp (C y + X ^ r1) := by
    rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← RingHom.map_det]
    rfl
  rw [← hdet]
  apply a2_det_dvd
  intro μ ν
  have : (A * B) μ ν = ∑ k, (hasseDeriv μ (φ k)).comp (C x + X ^ r2) *
      (hasseDeriv ν (ψ k)).comp (C y + X ^ r1) := by
    simp [A, B, Matrix.mul_apply, a2_HWm]
  rw [this]
  exact a2_entry_dvd φ ψ x y r1 r2 N1 N2 (d ν) μ ν (h1 μ) (h2 ν) (hT μ ν)

/-! #### Rank decomposition -/

/--
@isnad1 id=ex.0h3v.s7.3ecd0729d523 from=translated src=- shape=51fc6270 vocab=404bbf72
-/
lemma a2_basis {n m : ℕ} (M : Matrix (Fin n) (Fin m) ℚ) : ∃ (l : ℕ) (I : Fin l → Fin n),
    LinearIndependent ℚ (fun k => M (I k)) ∧
    (∀ i, M i ∈ Submodule.span ℚ (Set.range fun k => M (I k))) ∧ l = M.transpose.rank := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ M
  haveI : Fintype κ := Fintype.ofInjective a ha
  let e := Fintype.equivFin κ
  have hli' : LinearIndependent ℚ ((M ∘ a) ∘ e.symm) := hli.comp e.symm e.symm.injective
  have hr : Set.range ((M ∘ a) ∘ e.symm) = Set.range (M ∘ a) := e.symm.surjective.range_comp _
  refine ⟨Fintype.card κ, a ∘ e.symm, hli', ?_, ?_⟩
  · intro i
    change M i ∈ Submodule.span ℚ (Set.range ((M ∘ a) ∘ e.symm))
    rw [hr, hspan]; exact Submodule.subset_span ⟨i, rfl⟩
  · rw [Matrix.rank_eq_finrank_span_cols, ← finrank_span_eq_card hli, hspan]
    rfl

/--
@isnad1 id=ex.0h3v.s9.e297e3af550d from=translated src=- shape=122e5248 vocab=fcf24493
-/
lemma a2_decomp (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) : ∃ (l : ℕ) (I : Fin l → Fin (r1+1))
    (J : Fin l → Fin (r2+1)) (g : Fin (r1+1) → Fin l → ℚ),
    LinearIndependent ℚ (fun k => a2_L (r2+1) (fun j => (c (I k) j : ℚ))) ∧
    LinearIndependent ℚ (fun k => a2_L (r1+1) (fun i => (c i (J k) : ℚ))) ∧
    ∀ (i : Fin (r1+1)) (j : Fin (r2+1)), (c i j : ℚ) = ∑ k, g i k * c (I k) j := by
  let M : Matrix (Fin (r1+1)) (Fin (r2+1)) ℚ := Matrix.of fun i j => (c i j : ℚ)
  obtain ⟨l, I, hI, hspan, hl⟩ := a2_basis M
  obtain ⟨l', J, hJ, -, hl'⟩ := a2_basis M.transpose
  have hll : l' = l := by rw [hl, hl', Matrix.transpose_transpose, Matrix.rank_transpose]
  subst hll
  have hex := fun i => (Submodule.mem_span_range_iff_exists_fun ℚ).1 (hspan i)
  refine ⟨l', I, J, fun i => (hex i).choose, ?_, ?_, ?_⟩
  · exact hI.map' (a2_L _) (a2_L_ker _)
  · exact hJ.map' (a2_L _) (a2_L_ker _)
  · intro i j
    have := congr_fun (hex i).choose_spec j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M, Matrix.of_apply] at this
    exact this.symm

/--
@isnad1 id=eq.1h10v.s10.7a6b854d3c31 from=translated src=- shape=ca961217 vocab=220fe90c
-/
lemma a2_hasseEval_eq (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) {l : ℕ} (I : Fin l → Fin (r1+1))
    (g : Fin (r1+1) → Fin l → ℚ)
    (hg : ∀ (i : Fin (r1+1)) (j : Fin (r2+1)), (c i j : ℚ) = ∑ k, g i k * c (I k) j)
    (i1 i2 : ℕ) (x y : ℚ) :
    hasseEval r1 r2 c i1 i2 (x : ℝ) (y : ℝ) =
     ((∑ k, (hasseDeriv i1 (a2_L (r1+1) (fun i => g i k))).eval x *
        (hasseDeriv i2 (a2_L (r2+1) (fun j => (c (I k) j : ℚ)))).eval y : ℚ) : ℝ) := by
  have h0 : hasseEval r1 r2 c i1 i2 (x : ℝ) (y : ℝ) = ((∑ i : Fin (r1+1), ∑ j : Fin (r2+1),
      (c i j : ℚ) * ((i : ℕ).choose i1 : ℚ) * ((j : ℕ).choose i2 : ℚ) * x ^ ((i : ℕ) - i1) *
        y ^ ((j : ℕ) - i2) : ℚ) : ℝ) := by
    unfold hasseEval
    simp_rw [Finset.sum_range]
    push_cast
    rfl
  rw [h0]
  congr 1
  simp only [a2_eval_hD_L, Finset.sum_mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hg i j, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/--
@isnad1 id=eq.1h7v.s5.8908644d180a from=translated src=- shape=f284169d vocab=020d1ae8
-/
lemma a2_hE_zero (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (i1 i2 : ℕ) (x y : ℝ) (h : r1 < i1 ∨ r2 < i2) :
    hasseEval r1 r2 c i1 i2 x y = 0 := by
  unfold hasseEval
  refine Finset.sum_eq_zero fun k1 hk1 => Finset.sum_eq_zero fun k2 hk2 => ?_
  rw [Finset.mem_range] at hk1 hk2
  rcases h with h | h
  · rw [Nat.choose_eq_zero_of_lt (by omega : k1 < i1)]; simp
  · rw [Nat.choose_eq_zero_of_lt (by omega : k2 < i2)]; simp

/--
@isnad1 id=ex.1h5v.s5.8c4e21d5bb23 from=translated src=- shape=0b7f3fcd vocab=9806ae75
-/
lemma a2_trivial (r1 r2 : ℕ) (c : ℕ → ℕ → ℤ) (hc : BoxNonzero r1 r2 c) (x y : ℝ) :
    ∃ i1 ≤ r1, ∃ i2 ≤ r2, hasseEval r1 r2 c i1 i2 x y ≠ 0 := by
  classical
  let S1 := (range (r1+1)).filter (fun k1 => ∃ k2 ≤ r2, c k1 k2 ≠ 0)
  have hS1 : S1.Nonempty := by
    obtain ⟨k1, hk1, k2, hk2, hne⟩ := hc
    exact ⟨k1, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), k2, hk2, hne⟩⟩
  let a := S1.max' hS1
  have ha := Finset.mem_filter.1 (S1.max'_mem hS1)
  have hamax : ∀ k1, k1 ∈ S1 → k1 ≤ a := fun k1 hk => S1.le_max' k1 hk
  let S2 := (range (r2+1)).filter (fun k2 => c a k2 ≠ 0)
  have hS2 : S2.Nonempty := by
    obtain ⟨k2, hk2, hne⟩ := ha.2
    exact ⟨k2, Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hne⟩⟩
  let b := S2.max' hS2
  have hb := Finset.mem_filter.1 (S2.max'_mem hS2)
  have hbmax : ∀ k2, k2 ∈ S2 → k2 ≤ b := fun k2 hk => S2.le_max' k2 hk
  have har := Finset.mem_range.1 ha.1
  have hbr := Finset.mem_range.1 hb.1
  refine ⟨a, by omega, b, by omega, ?_⟩
  unfold hasseEval
  rw [Finset.sum_eq_single a, Finset.sum_eq_single b]
  · simpa using hb.2
  · intro k2 hk2 hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · have : c a k2 = 0 := by
        by_contra hc'
        have := hbmax k2 (Finset.mem_filter.2 ⟨hk2, hc'⟩); omega
      simp [this]
  · intro h; exact absurd hb.1 h
  · intro k1 hk1 hne
    refine Finset.sum_eq_zero fun k2 hk2 => ?_
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · have : c k1 k2 = 0 := by
        by_contra hc'
        have := hamax k1 (Finset.mem_filter.2 ⟨hk1, k2,
          Nat.lt_succ_iff.mp (Finset.mem_range.1 hk2), hc'⟩); omega
      simp [this]
  · intro h; exact absurd ha.1 h

/-! #### Arithmetic -/

/--
@isnad1 id=eq.0h1v.s5.61c9351c7a56 from=translated src=- shape=1f8c6911 vocab=48575070
-/
lemma a2_sum_id (n : ℕ) : (∑ ν ∈ range n, (ν : ℝ)) * 2 = n * (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; push_cast; ring

/--
@isnad1 id=lt.5h3v.s7.9121c49399d9 from=translated src=- shape=4693673c vocab=13f4c6e8
-/
lemma a2_S_big (r2 l : ℕ) (η : ℝ) (hr2 : 1 ≤ r2) (hl : 1 ≤ l) (hl2 : l ≤ r2 + 1) (hη : 0 < η)
    (hη4 : η ≤ 1/4) :
    2 * l * η < ∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2) := by
  have hs0 : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hss : Real.sqrt η * Real.sqrt η = η := Real.mul_self_sqrt hη.le
  set s := Real.sqrt η with hs
  have hs2 : s ≤ 1/2 := by nlinarith
  set T := 4 * s - η with hTdef
  have hT : 7/2 * s ≤ T := by nlinarith
  have hr2' : (0:ℝ) < r2 := by exact_mod_cast hr2
  have hl' : (1:ℝ) ≤ l := by exact_mod_cast hl
  have gen : ∀ n ≤ l, ((n:ℝ) - 1) ≤ T * r2 →
      n * T / 2 ≤ ∑ ν ∈ range l, max 0 (T - ν / r2) := by
    intro n hn hnT
    have hsum : (∑ ν ∈ range n, (ν:ℝ)) = n * (n - 1) / 2 := by linarith [a2_sum_id n]
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg _
    have h2 : (∑ ν ∈ range n, (ν:ℝ)) / r2 ≤ n * T / 2 := by
      rw [div_le_iff₀ hr2', hsum]
      nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hnT)]
    calc (n:ℝ) * T / 2 ≤ ∑ ν ∈ range n, (T - ν / r2) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.sum_div]
          linarith
      _ ≤ ∑ ν ∈ range n, max 0 (T - ν / r2) := Finset.sum_le_sum fun ν _ => le_max_right _ _
      _ ≤ ∑ ν ∈ range l, max 0 (T - ν / r2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn)
            (fun _ _ _ => le_max_left _ _)
  have hTr : 0 ≤ T * r2 := mul_nonneg (by linarith) hr2'.le
  by_cases hA : l ≤ ⌊T * r2⌋₊ + 1
  · have h1 : ((l:ℝ) - 1) ≤ T * r2 := by
      have : ((l:ℝ) - 1) ≤ (⌊T * r2⌋₊ : ℝ) := by
        have : (l:ℝ) ≤ (⌊T * r2⌋₊ : ℝ) + 1 := by exact_mod_cast hA
        linarith
      exact le_trans this (Nat.floor_le hTr)
    have := gen l le_rfl h1
    have h4 : 4 * η < T := by nlinarith
    have := mul_lt_mul_of_pos_left h4 (by linarith : (0:ℝ) < l)
    linarith
  · push_neg at hA
    set n := ⌊T * r2⌋₊ + 1 with hn
    have h1 : ((n:ℝ) - 1) ≤ T * r2 := by rw [hn]; push_cast; linarith [Nat.floor_le hTr]
    have := gen n hA.le h1
    have h2 : T * r2 < n := by rw [hn]; push_cast; exact Nat.lt_floor_add_one _
    have h3 : (l:ℝ) ≤ 2 * r2 := by
      have : (l:ℝ) ≤ r2 + 1 := by exact_mod_cast hl2
      have : (1:ℝ) ≤ r2 := by exact_mod_cast hr2
      linarith
    have hT0 : 0 < T := by linarith
    have h5 : T * r2 * T / 2 ≤ n * T / 2 := by
      have := mul_le_mul_of_nonneg_right h2.le hT0.le
      linarith
    have h6 : 49/4 * η ≤ T * T := by
      have h7 : 7/2 * s * (7/2 * s) ≤ T * T := mul_self_le_mul_self (by positivity) hT
      nlinarith
    have h7 : 49/8 * η * r2 ≤ T * r2 * T / 2 := by
      have := mul_le_mul_of_nonneg_right h6 hr2'.le
      nlinarith
    have h8 : 2 * l * η ≤ 4 * r2 * η := by
      have := mul_le_mul_of_nonneg_right h3 hη.le
      linarith
    have h9 : 0 < η * r2 := mul_pos hη hr2'
    nlinarith

/--
@isnad1 id=false.13h9v.s9.4e217dc6707b from=translated src=- shape=f0edfc83 vocab=3aadf9ef
-/
lemma a2_final (r1 r2 l e1 e2 : ℕ) (H η : ℝ) (q1 q2 : ℕ)
    (hr2 : 1 ≤ r2) (hl : 1 ≤ l) (hl2 : l ≤ r2 + 1) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hr21 : (r2:ℝ) ≤ η * r1) (hH : 1 ≤ H) (hq1 : 0 < q1)
    (hq12 : (q1:ℝ) ^ r1 ≤ (q2:ℝ) ^ r2) (hbig : 64 ^ r1 * H ≤ (q1:ℝ) ^ (η * r1))
    (hu1 : (q1:ℝ) ^ e1 ≤ (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l)
    (hu2 : (q2:ℝ) ^ e2 ≤ (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l)
    (hlow : (r1:ℝ) * r2 * (∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2)) ≤
      r2 * e1 + r1 * e2) : False := by
  set S := ∑ ν ∈ range l, max 0 (4 * Real.sqrt η - η - ν / r2) with hSdef
  have hS := a2_S_big r2 l η hr2 hl hl2 hη hη4
  rw [← hSdef] at hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => le_max_left _ _
  have hr2' : (1:ℝ) ≤ r2 := by exact_mod_cast hr2
  have hr1' : (1:ℝ) ≤ r1 := by
    rcases Nat.eq_zero_or_pos r1 with h | h
    · subst h; simp at hr21; linarith
    · exact_mod_cast h
  have hr1n : 1 ≤ r1 := by exact_mod_cast hr1'
  have h64 : (64:ℝ) ≤ 64 ^ r1 := le_self_pow₀ (by norm_num) (by omega)
  have hq1' : (1:ℝ) < q1 := by
    by_contra h
    push_neg at h
    have : q1 = 1 := by
      have : q1 ≤ 1 := by exact_mod_cast h
      omega
    subst this
    simp at hbig
    have := mul_le_mul h64 hH (by norm_num) (by positivity)
    linarith
  have hq1pos : (0:ℝ) < q1 := by linarith
  have hq2pos : (0:ℝ) < q2 := by
    rcases Nat.eq_zero_or_pos q2 with h | h
    · subst h
      have : (0:ℝ) < (q1:ℝ) ^ r1 := by positivity
      simp [zero_pow (by omega : r2 ≠ 0)] at hq12; linarith
    · exact_mod_cast h
  set B := (l.factorial : ℝ) * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l with hB
  have hBpos : 0 < B := by positivity
  set L := Real.log q1 with hL
  have hLpos : 0 < L := Real.log_pos hq1'
  have he1 : (e1:ℝ) * L ≤ Real.log B := by
    have := Real.log_le_log (by positivity) hu1
    rwa [Real.log_pow] at this
  have he2 : (e2:ℝ) * Real.log q2 ≤ Real.log B := by
    have := Real.log_le_log (by positivity) hu2
    rwa [Real.log_pow] at this
  have hq12L : (r1:ℝ) * L ≤ r2 * Real.log q2 := by
    have := Real.log_le_log (by positivity) hq12
    rwa [Real.log_pow, Real.log_pow] at this
  -- r1 * S * L ≤ 2 log B
  have hchain : (r1:ℝ) * S * L ≤ 2 * Real.log B := by
    have e0 : (0:ℝ) ≤ e2 := Nat.cast_nonneg _
    have k1' : (r1:ℝ) * r2 * S * L ≤ (r2 * e1 + r1 * e2) * L := mul_le_mul_of_nonneg_right hlow hLpos.le
    have k2 : (e2:ℝ) * (r1 * L) ≤ e2 * (r2 * Real.log q2) := mul_le_mul_of_nonneg_left hq12L e0
    have k3 : (r2:ℝ) * (e1 * L) ≤ r2 * Real.log B := mul_le_mul_of_nonneg_left he1 (by linarith)
    have k4 : (r2:ℝ) * (e2 * Real.log q2) ≤ r2 * Real.log B := mul_le_mul_of_nonneg_left he2 (by linarith)
    have : (r1:ℝ) * S * L * r2 ≤ 2 * Real.log B * r2 := by
      calc (r1:ℝ) * S * L * r2 = (r1 * r2 * S) * L := by ring
        _ ≤ (r2 * e1 + r1 * e2) * L := k1'
        _ = r2 * (e1 * L) + e2 * (r1 * L) := by ring
        _ ≤ r2 * Real.log B + e2 * (r2 * Real.log q2) := add_le_add k3 k2
        _ = r2 * Real.log B + r2 * (e2 * Real.log q2) := by ring
        _ ≤ r2 * Real.log B + r2 * Real.log B := add_le_add le_rfl k4
        _ = 2 * Real.log B * r2 := by ring
    exact le_of_mul_le_mul_right this (by linarith)
  -- height comparison
  have hA64 : Real.log (64 ^ r1 * H) ≤ η * r1 * L := by
    have := Real.log_le_log (by positivity) hbig
    rwa [Real.log_rpow hq1pos] at this
  have hB8 : B ≤ (8 ^ r1 * H) ^ l := by
    have hf : (l.factorial : ℝ) ≤ ((r1:ℝ) + 1) ^ l := by
      have h1 : l.factorial ≤ l ^ l := Nat.factorial_le_pow l
      have h2 : l ^ l ≤ (r1 + 1) ^ l := Nat.pow_le_pow_left (by
        have : (r2:ℝ) ≤ r1 := le_trans hr21 (mul_le_of_le_one_left (Nat.cast_nonneg _) (by linarith))
        have : r2 ≤ r1 := by exact_mod_cast this
        omega) l
      exact_mod_cast le_trans h1 h2
    have hr : ((r1:ℝ) + 1) ≤ 2 ^ r1 := by
      have := Nat.lt_two_pow_self (n := r1)
      exact_mod_cast this
    calc B ≤ ((r1:ℝ) + 1) ^ l * (((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l :=
          mul_le_mul_of_nonneg_right hf (by positivity)
      _ = (((r1:ℝ) + 1) * ((r1:ℝ) + 1) * 2 ^ r1 * H) ^ l := by rw [← mul_pow]; ring_nf
      _ ≤ (2 ^ r1 * 2 ^ r1 * 2 ^ r1 * H) ^ l := by
          gcongr
      _ = (8 ^ r1 * H) ^ l := by
          congr 1; rw [show (8:ℝ) = 2 * 2 * 2 by norm_num, mul_pow, mul_pow]
  have hlogB : Real.log B ≤ l * Real.log (8 ^ r1 * H) := by
    have := Real.log_le_log hBpos hB8
    rwa [Real.log_pow] at this
  have hA8pos : 0 < Real.log (8 ^ r1 * H) := Real.log_pos (by
    have : (8:ℝ) ≤ 8 ^ r1 := le_self_pow₀ (by norm_num) (by omega)
    calc (1:ℝ) < 8 := by norm_num
      _ ≤ 8 ^ r1 := this
      _ ≤ 8 ^ r1 * H := le_mul_of_one_le_right (by positivity) hH)
  have hA8 : Real.log (8 ^ r1 * H) < Real.log (64 ^ r1 * H) := by
    apply Real.log_lt_log (by positivity)
    have : (8:ℝ) ^ r1 < 64 ^ r1 := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
    exact mul_lt_mul_of_pos_right this (by linarith)
  -- combine
  have c1 : S * Real.log (64 ^ r1 * H) ≤ S * (η * r1 * L) := mul_le_mul_of_nonneg_left hA64 hS0
  have c2 : S * (η * r1 * L) ≤ η * (2 * Real.log B) := by
    have := mul_le_mul_of_nonneg_left hchain hη.le
    calc S * (η * r1 * L) = η * (r1 * S * L) := by ring
      _ ≤ _ := this
  have c3 : η * (2 * Real.log B) ≤ η * (2 * (l * Real.log (8 ^ r1 * H))) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hl0 : (0:ℝ) < l := by exact_mod_cast hl
  have c4 : 2 * l * η * Real.log (64 ^ r1 * H) < S * Real.log (64 ^ r1 * H) :=
    mul_lt_mul_of_pos_right hS (by linarith)
  have c5 : η * (2 * (l * Real.log (8 ^ r1 * H))) ≤ 2 * l * η * Real.log (64 ^ r1 * H) := by
    have := mul_le_mul_of_nonneg_left hA8.le (by positivity : (0:ℝ) ≤ 2 * l * η)
    calc η * (2 * (l * Real.log (8 ^ r1 * H))) = 2 * l * η * Real.log (8 ^ r1 * H) := by ring
      _ ≤ _ := this
  linarith

end RL2

end Erdos494
