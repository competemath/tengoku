import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

noncomputable section

namespace ActualEisensteinSieve

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

private def lambda : O := omega - 1

private def lambdaIdeal : Ideal O := Ideal.span {lambda}

private theorem lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

/--
@isnad1 id=ismaxima.0h0v.s4.514a9a36e9c3 from=translated src=- shape=25b03439 vocab=39e1cd68
-/
theorem lambda_maximal : lambdaIdeal.IsMaximal := by
  have hp : lambdaIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime lambda_prime
  have hne : lambdaIdeal ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero
  exact hp.isMaximal hne

/--
@isnad1 id=eq.0h0v.s5.9082f6889557 from=translated src=- shape=2221e9d0 vocab=302630ea
-/
theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

private def localQuadratic (P : Ideal O) [P.IsMaximal] (x : O) : ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x)

private theorem localQuadratic_one (P : Ideal O) [P.IsMaximal] :
    localQuadratic P 1 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) 1 = 1
  exact map_one _

private theorem localQuadratic_mul (P : Ideal O) [P.IsMaximal] (x y : O) :
    localQuadratic P (x * y) = localQuadratic P x * localQuadratic P y := by
  simp [localQuadratic, map_mul]

private theorem localQuadratic_zero_iff (P : Ideal O) [P.IsMaximal] (x : O) :
    localQuadratic P x = 0 ↔ x ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [quadraticChar_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem exists_localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O, localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hodd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ?_⟩
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact ha

/--
@isnad1 id=eq.1h1v.s8.8d77507fa63a from=translated src=- shape=5815c0a7 vocab=6350e2a9
-/
theorem localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    localQuadratic P (-1) = ZMod.χ₄ (Nat.card (O ⧸ P)) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (-1) = ZMod.χ₄ (Nat.card (O ⧸ P))
  simpa only [Nat.card_eq_fintype_card] using quadraticChar_neg_one hodd

/--
@isnad1 id=eq.1h2v.s6.954240354282 from=translated src=- shape=4bc89bd1 vocab=14fe8cfa
-/
theorem localQuadratic_cube_root_one (P : Ideal O) [P.IsMaximal]
    (u : O) (hu : u ^ 3 = 1) : localQuadratic P u = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  let v : O ⧸ P := Ideal.Quotient.mk P u
  have hv3 : v ^ 3 = 1 := by
    simpa [v] using congrArg (Ideal.Quotient.mk P) hu
  have hvne : v ≠ 0 := by
    intro hv0
    simp [hv0] at hv3
  have hv4 : v ^ 4 = v := by
    calc
      v ^ 4 = v ^ 3 * v := by ring
      _ = v := by rw [hv3, one_mul]
  have hsq : quadraticChar (O ⧸ P) (v ^ 4) = 1 := by
    simpa only [← pow_mul] using quadraticChar_sq_one' (F := O ⧸ P)
      (a := v ^ 2) (pow_ne_zero _ hvne)
  change quadraticChar (O ⧸ P) v = 1
  rwa [hv4] at hsq

private theorem localQuadratic_trichotomy (P : Ideal O) [P.IsMaximal]
    (x : O) :
    localQuadratic P x = 0 ∨ localQuadratic P x = 1 ∨
      localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 1 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact quadraticChar_isQuadratic (O ⧸ P) _

private instance : lambdaIdeal.IsMaximal := lambda_maximal

/--
@isnad1 id=ne.0h0v.s6.355d51503d70 from=translated src=- shape=2221e9d0 vocab=cf9f00be
-/
theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  let : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  norm_num at hcard

/--
@isnad1 id=eq.0h0v.s5.74dcae3f3445 from=translated src=- shape=65482e97 vocab=4dc945b2
-/
theorem lambdaQuadratic_neg_one : localQuadratic lambdaIdeal (-1) = -1 := by
  rw [localQuadratic_neg_one lambdaIdeal lambda_residue_odd, lambda_card]
  rfl

private theorem finite_prod_trichotomy {ι : Type*} (s : Finset ι)
    (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1 ∨ f i = -1) :
    s.prod f = 0 ∨ s.prod f = 1 ∨ s.prod f = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have ih' := ih hfs
      rcases hfi with h0 | h1 | hm
      · left; simp [Finset.prod_insert his, h0]
      · simpa [Finset.prod_insert his, h1] using ih'
      · rcases ih' with h0 | h1 | hm'
        · left; simp [Finset.prod_insert his, hm, h0]
        · right; right; simp [Finset.prod_insert his, hm, h1]
        · right; left; simp [Finset.prod_insert his, hm, hm']

private theorem crt_pair (I J : Ideal O) (h : IsCoprime I J)
    (a : O ⧸ I) (b : O ⧸ J) :
    ∃ x : O, Ideal.Quotient.mk I x = a ∧ Ideal.Quotient.mk J x = b := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (a, b))
  have he : e (Ideal.Quotient.mk (I * J) x) = (a, b) := by
    rw [hx, e.apply_symm_apply]
  refine ⟨x, ?_, ?_⟩
  · simpa [e] using congrArg Prod.fst he
  · simpa [e] using congrArg Prod.snd he

private theorem localQuadratic_congr (P : Ideal O) [P.IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) :
    localQuadratic P x = localQuadratic P y := by
  simp only [localQuadratic, h]

/--
@isnad1 id=eq.0h0v.s3.0c3ab0d6ead5 from=translated src=- shape=b3c4969c vocab=03e8c876
-/
theorem lambdaQuadratic_omega : localQuadratic lambdaIdeal omega = 1 := by
  apply (localQuadratic_congr lambdaIdeal omega 1 ?_).trans
    (localQuadratic_one lambdaIdeal)
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (by simp [lambda, omega])

private theorem productQuadratic_detects_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O,
      Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q (1 : O) ∧
      localQuadratic P x * localQuadratic Q x = -1 := by
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one P hodd
  obtain ⟨x, hP, hQ⟩ := crt_pair P Q hcop
    (Ideal.Quotient.mk P a) (Ideal.Quotient.mk Q (1 : O))
  refine ⟨x, hQ, ?_⟩
  rw [localQuadratic_congr P x a hP,
    localQuadratic_congr Q x 1 hQ, ha, localQuadratic_one]
  ring

/--
@isnad1 id=not.2h2v.s9.deb92664ccb9 from=translated src=- shape=c33b16b5 vocab=8e8ee3de
-/
theorem productQuadratic_not_factor_right
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ¬ ∃ f : (O ⧸ Q) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk Q x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hQ, hneg⟩ := productQuadratic_detects_left P Q hcop hodd
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hQ] at hx
  rw [localQuadratic_one P, localQuadratic_one Q] at h1
  norm_num at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk Q (1 : O)) := hx
      _ = f 1 := by simp
      _ = 1 := h1.symm
  norm_num at absurd

/--
@isnad1 id=not.2h2v.s9.e70a8c162e27 from=translated src=- shape=3aa07597 vocab=8e8ee3de
-/
theorem productQuadratic_not_factor_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ Q) ≠ 2) :
    ¬ ∃ f : (O ⧸ P) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk P x) := by
  intro h
  apply productQuadratic_not_factor_right Q P hcop.symm hodd
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  intro x
  rw [mul_comm]
  exact hf x

/--
@isnad1 id=ex.2h3v.s9.210d25b40184 from=translated src=- shape=facccf13 vocab=406cb7af
-/
theorem finiteQuadratic_detects_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ∃ x : O,
      (∀ j : ι, j ≠ i₀ → Ideal.Quotient.mk (P j) x = 1) ∧
      (∏ j : ι, localQuadratic (P j) x) = -1 := by
  classical
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one (P i₀) (hodd i₀)
  let target (j : ι) : O ⧸ P j :=
    Ideal.Quotient.mk (P j) (if j = i₀ then a else 1)
  obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective hpair target
  have hlocal (j : ι) :
      localQuadratic (P j) x = if j = i₀ then -1 else 1 := by
    by_cases hj : j = i₀
    · subst j
      have hres : Ideal.Quotient.mk (P i₀) x = Ideal.Quotient.mk (P i₀) a := by
        simpa [target] using hx i₀
      simpa using (localQuadratic_congr (P i₀) x a hres).trans ha
    · have hres : Ideal.Quotient.mk (P j) x = Ideal.Quotient.mk (P j) (1 : O) := by
        simpa [target, hj] using hx j
      simpa [hj] using (localQuadratic_congr (P j) x 1 hres).trans
        (localQuadratic_one (P j))
  refine ⟨x, ?_, ?_⟩
  · intro j hj
    simpa [target, hj] using hx j
  · simp_rw [hlocal]
    simp

private def quadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  ∏ i : ι, localQuadratic (P i) x

private theorem quadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P 1 = 1 := by
  simp [quadraticProduct, localQuadratic_one]

private theorem quadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    quadraticProduct P (x * y) = quadraticProduct P x * quadraticProduct P y := by
  simp [quadraticProduct, localQuadratic_mul, Finset.prod_mul_distrib]

private theorem quadraticProduct_neg_one_square
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P (-1) ^ 2 = 1 := by
  calc
    quadraticProduct P (-1) ^ 2 =
        quadraticProduct P ((-1 : O) * (-1)) := by
          rw [pow_two, quadraticProduct_mul]
    _ = 1 := by simpa using quadraticProduct_one P

def correctedQuadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  if quadraticProduct P (-1) = 1 then quadraticProduct P x
  else quadraticProduct P x * localQuadratic lambdaIdeal x

/--
@isnad1 id=eq.0h2v.s6.66bd1112ddcd from=translated src=- shape=ab784a8e vocab=b59831c7
-/
theorem correctedQuadraticProduct_neg_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P (-1) = 1 := by
  classical
  have hsq := quadraticProduct_neg_one_square P
  have hsign : quadraticProduct P (-1) = 1 ∨
      quadraticProduct P (-1) = -1 :=
    sq_eq_one_iff.mp hsq
  rcases hsign with h | h
  · simp [correctedQuadraticProduct, h]
  · simp [correctedQuadraticProduct, h, lambdaQuadratic_neg_one]

/--
@isnad1 id=eq.0h2v.s5.f94181f8e1f3 from=translated src=- shape=628a3e80 vocab=b3aab284
-/
theorem correctedQuadraticProduct_omega
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P omega = 1 := by
  have hq : quadraticProduct P omega = 1 := by
    simp [quadraticProduct, localQuadratic_cube_root_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one,
      omega]
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, hq]
  · simp [correctedQuadraticProduct, h, hq, lambdaQuadratic_omega]

/--
@isnad1 id=eq.0h2v.s6.a540b25a10d4 from=translated src=- shape=7b1d4073 vocab=c0491579
-/
theorem correctedQuadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P 1 = 1 := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_one]
  · simp [correctedQuadraticProduct, h, quadraticProduct_one,
      localQuadratic_one]

/--
@isnad1 id=eq.0h4v.s6.b3088a80e728 from=translated src=- shape=4785b8e8 vocab=8cd4a142
-/
theorem correctedQuadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    correctedQuadraticProduct P (x * y) =
      correctedQuadraticProduct P x * correctedQuadraticProduct P y := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_mul]
  · simp only [correctedQuadraticProduct, h, ite_false,
      quadraticProduct_mul, localQuadratic_mul]
    ring

private def correctedQuadraticHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : O →* ℤ where
  toFun := correctedQuadraticProduct P
  map_one' := correctedQuadraticProduct_one P
  map_mul' := correctedQuadraticProduct_mul P

/--
@isnad1 id=eq.0h3v.s6.d335f55d342e from=translated src=- shape=6d7b6c10 vocab=0d39c751
-/
theorem correctedQuadraticProduct_units
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (u : Oˣ) :
    correctedQuadraticProduct P (u : O) = 1 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot
    (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · subst u
    simpa using correctedQuadraticProduct_one P
  · subst u
    simpa using correctedQuadraticProduct_neg_one P
  · subst u
    change correctedQuadraticProduct P (η : O) = 1
    rw [hη]
    exact correctedQuadraticProduct_omega P
  · subst u
    change correctedQuadraticProduct P (-(η : O)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P ((η : O) ^ 2) = 1
    rw [pow_two, correctedQuadraticProduct_mul, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P (-((η : O) ^ 2)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one]
    have hpow : correctedQuadraticProduct P ((η : O) ^ 2) = 1 := by
      rw [pow_two, correctedQuadraticProduct_mul, hη,
        correctedQuadraticProduct_omega]
      norm_num
    rw [hpow]
    norm_num

/--
@isnad1 id=eq.1h4v.s12.44812c5ac571 from=translated src=- shape=de34ffe5 vocab=063b1430
-/
theorem correctedQuadraticProduct_congr_mod_conductor
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) y) :
    correctedQuadraticProduct P x = correctedQuadraticProduct P y := by
  classical
  have hmem : x - y ∈ lambdaIdeal * Finset.univ.prod P :=
    Ideal.Quotient.eq.mp h
  have hlambda : Ideal.Quotient.mk lambdaIdeal x =
      Ideal.Quotient.mk lambdaIdeal y :=
    Ideal.Quotient.eq.mpr (Ideal.mul_le_left hmem)
  have hprod : quadraticProduct P x = quadraticProduct P y := by
    unfold quadraticProduct
    apply Finset.prod_congr rfl
    intro j _
    apply localQuadratic_congr
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.mul_le_right.trans
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j)))) hmem
  unfold correctedQuadraticProduct
  split_ifs <;> simp [hprod, localQuadratic_congr lambdaIdeal x y hlambda]

/--
@isnad1 id=eq.1h3v.s8.3f684fac1e8f from=translated src=- shape=7cda693e vocab=5154306b
-/
theorem correctedQuadraticProduct_one_of_congruent
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O)
    (h : x - 1 ∈ lambdaIdeal * Finset.univ.prod P) :
    correctedQuadraticProduct P x = 1 := by
  have hres : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr h
  exact (correctedQuadraticProduct_congr_mod_conductor P x 1 hres).trans
    (correctedQuadraticProduct_one P)

noncomputable def correctedAssociatesHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Associates O →* ℤ where
  toFun := Quotient.lift (correctedQuadraticProduct P) (by
    intro a b hab
    obtain ⟨u, hu⟩ := hab
    rw [← hu, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_units, mul_one])
  map_one' := by
    change correctedQuadraticProduct P 1 = 1
    exact correctedQuadraticProduct_one P
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Associates.mk_surjective x
    obtain ⟨b, rfl⟩ := Associates.mk_surjective y
    change correctedQuadraticProduct P (a * b) =
      correctedQuadraticProduct P a * correctedQuadraticProduct P b
    exact correctedQuadraticProduct_mul P a b

private noncomputable def idealGeneratorClass (I : Ideal O) : Associates O :=
  (Ideal.associatesMulEquivIsPrincipal O).symm
    ⟨I, IsPrincipalIdealRing.principal I⟩

private theorem idealGeneratorClass_one : idealGeneratorClass (1 : Ideal O) = 1 := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]

private theorem idealGeneratorClass_mul (I J : Ideal O) :
    idealGeneratorClass (I * J) = idealGeneratorClass I * idealGeneratorClass J := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl

private theorem idealGeneratorClass_span (x : O) :
    idealGeneratorClass (Ideal.span {x}) = Associates.mk x := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl

noncomputable def correctedIdealHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Ideal O →* ℤ where
  toFun I := correctedAssociatesHom P (idealGeneratorClass I)
  map_one' := by
    rw [idealGeneratorClass_one, map_one]
  map_mul' := by
    intro I J
    rw [idealGeneratorClass_mul, map_mul]

/--
@isnad1 id=eq.0h3v.s8.8cbf8ac2eccd from=translated src=- shape=a46f4303 vocab=f5a7874b
-/
theorem correctedIdealHom_span
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    correctedIdealHom P (Ideal.span {x}) =
      correctedQuadraticProduct P x := by
  simp [correctedIdealHom, idealGeneratorClass_span, correctedAssociatesHom]

/--
@isnad1 id=not.2h3v.s9.3c5a1e51d482 from=translated src=- shape=22c630d1 vocab=3288bb9b
-/
theorem finiteQuadratic_not_factor_without_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : ((j : {j : ι // j ≠ i₀}) → O ⧸ P j.1) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (fun j => Ideal.Quotient.mk (P j.1) x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hsame :
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) x) =
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) (1 : O)) := by
    funext j
    simpa using hres j.1 j.2
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hsame] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := hx.trans h1.symm
  norm_num at absurd

/--
@isnad1 id=not.2h3v.s10.7ba782fafe95 from=translated src=- shape=acaa7976 vocab=b56c34fb
-/
theorem finiteQuadratic_not_factor_omit_prime_ideal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : (O ⧸ (Finset.univ.erase i₀).prod P) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (Ideal.Quotient.mk ((Finset.univ.erase i₀).prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  let s : Finset ι := Finset.univ.erase i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j := by
    exact Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := by simpa [s] using hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := by simpa [s] using h1.symm
  norm_num at absurd

/--
@isnad1 id=eq.1h4v.s11.025745818b43 from=translated src=- shape=95f14ab1 vocab=153e05b7
-/
theorem finiteQuadratic_congr_mod_product
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk (Finset.univ.prod P) x =
      Ideal.Quotient.mk (Finset.univ.prod P) y) :
    (∏ j : ι, localQuadratic (P j) x) =
      ∏ j : ι, localQuadratic (P j) y := by
  classical
  have hmem : x - y ∈ Finset.univ.prod P := Ideal.Quotient.eq.mp h
  apply Finset.prod_congr rfl
  intro j _
  apply localQuadratic_congr
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))) hmem

private def finiteQuadraticOnQuotient
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (z : O ⧸ Finset.univ.prod P) : ℤ :=
  ∏ j : ι, localQuadratic (P j) (Quotient.out z)

/--
@isnad1 id=eq.0h3v.s10.d1f07e437418 from=translated src=- shape=80f3accf vocab=33aca247
-/
theorem finiteQuadraticOnQuotient_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    finiteQuadraticOnQuotient P
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ j : ι, localQuadratic (P j) x := by
  classical
  unfold finiteQuadraticOnQuotient
  apply finiteQuadratic_congr_mod_product P
  exact Quotient.out_eq _

/--
@isnad1 id=not.3h4v.s11.a0b79edfef21 from=translated src=- shape=6eefe492 vocab=8ffb931c
-/
theorem finiteQuadratic_not_factor_subproduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        finiteQuadraticOnQuotient P
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [finiteQuadraticOnQuotient_mk, hneg] at hx
  rw [finiteQuadraticOnQuotient_mk] at h1
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := h1.symm
  norm_num at absurd

private noncomputable def squarefreeCRT
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (O ⧸ Finset.univ.prod P) ≃+* ((i : ι) → O ⧸ P i) := by
  classical
  have hpairU : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime P) := by
    intro i hi j hj hij
    exact hpair hij
  have hprod : Finset.univ.prod P = ⨅ i, P i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairU
  exact (Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient P hpair)

private theorem squarefreeCRT_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeCRT P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      fun i => Ideal.Quotient.mk (P i) x := by
  classical
  funext i
  simp only [squarefreeCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change (Ideal.quotientInfToPiQuotient P
    (Ideal.Quotient.mk (⨅ i, P i) x)) i = Ideal.Quotient.mk (P i) x
  rfl

private noncomputable def localResidueChar (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P)

private theorem localResidueChar_zero_iff (P : Ideal O) [P.IsMaximal]
    (z : O ⧸ P) : localResidueChar P z = 0 ↔ z = 0 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) z = 0 ↔ z = 0
  exact quadraticChar_eq_zero_iff

private noncomputable def squarefreePiChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    MulChar ((i : ι) → O ⧸ P i) ℤ where
  toFun z := ∏ i : ι, localResidueChar (P i) (z i)
  map_one' := by
    classical
    simp
  map_mul' := by
    classical
    intro x y
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    classical
    intro z hz
    by_contra hprod
    have hnonzero (i : ι) : localResidueChar (P i) (z i) ≠ 0 := by
      intro hzero
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    have hunit_i (i : ι) : IsUnit (z i) := by
      let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
      exact isUnit_iff_ne_zero.mpr
        ((localResidueChar_zero_iff (P i) (z i)).not.mp (hnonzero i))
    exact hz (Pi.isUnit_iff.mpr hunit_i)

noncomputable def squarefreeQuotientChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ Finset.univ.prod P) ℤ where
  toFun z := squarefreePiChar P (squarefreeCRT P hpair z)
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp
  map_nonunit' := by
    intro z hz
    apply (squarefreePiChar P).map_nonunit
    intro hu
    have hzunit : IsUnit z := by
      simpa using hu.map (squarefreeCRT P hpair).symm.toRingHom
    exact hz hzunit

/--
@isnad1 id=eq.1h3v.s10.b1f6a1258b4c from=translated src=- shape=efa8c79c vocab=e5ffc5e2
-/
theorem squarefreeQuotientChar_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeQuotientChar P hpair
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ i : ι, localQuadratic (P i) x := by
  classical
  simp only [squarefreeQuotientChar, MulChar.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, squarefreeCRT_mk, squarefreePiChar]
  apply Finset.prod_congr rfl
  intro i _
  rfl

/--
@isnad1 id=not.3h4v.s11.c89d368c8856 from=translated src=- shape=5383b2a3 vocab=cacb0f2f
-/
theorem squarefreeQuotientChar_primitive
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        squarefreeQuotientChar P hpair
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  intro hf
  apply finiteQuadratic_not_factor_subproduct P hpair hodd s i₀ hi₀
  obtain ⟨f, hf⟩ := hf
  refine ⟨f, ?_⟩
  intro x
  simpa only [finiteQuadraticOnQuotient_mk, squarefreeQuotientChar_mk] using hf x

/--
@isnad1 id=isquadra.1h2v.s8.b5b7d9f8e458 from=translated src=- shape=9b8fa593 vocab=9cc8f2f8
-/
theorem squarefreeQuotientChar_isQuadratic
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (squarefreeQuotientChar P hpair).IsQuadratic := by
  classical
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [squarefreeQuotientChar_mk]
  apply finite_prod_trichotomy
  intro i _
  exact localQuadratic_trichotomy (P i) x

/--
@isnad1 id=eq.1h2v.s11.d0daa551a590 from=translated src=- shape=6d32b6e7 vocab=ea55adbc
-/
theorem squarefreeQuotientChar_order_two
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    squarefreeQuotientChar P hpair ^ 2 = 1 :=
  (squarefreeQuotientChar_isQuadratic P hpair).sq_eq_one

/--
@isnad1 id=not.2h2v.s10.33d1cefd1b0b from=translated src=- shape=f0efd598 vocab=958ad5ca
-/
theorem correctedQuadraticProduct_not_factor_without_lambda
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (hneed : quadraticProduct P (-1) ≠ 1) :
    ¬ ∃ f : (O ⧸ Finset.univ.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (Finset.univ.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hlambda, hP⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (-1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O))
  have hraw : quadraticProduct P x = 1 := by
    change (∏ i : ι, localQuadratic (P i) x) = 1
    rw [finiteQuadratic_congr_mod_product P x 1 hP]
    simp [localQuadratic_one]
  have hlocal : localQuadratic lambdaIdeal x = -1 := by
    rw [localQuadratic_congr lambdaIdeal x (-1) hlambda]
    exact lambdaQuadratic_neg_one
  have hx : correctedQuadraticProduct P x = -1 := by
    simp [correctedQuadraticProduct, hneed, hraw, hlocal]
  have h1 : correctedQuadraticProduct P (1 : O) = 1 :=
    correctedQuadraticProduct_one P
  have hEq : f (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) :=
    congrArg f hP
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (Finset.univ.prod P) x) :=
        hx.symm.trans (hf x)
      _ = f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) := hEq
      _ = 1 := (hf 1).symm.trans h1
  norm_num at this

/--
@isnad1 id=eq.1h1v.s6.dfd92ad1beca from=translated src=- shape=f0955683 vocab=dede327b
-/
theorem lambdaQuadratic_sq_one_of_not_mem (x : O)
    (hx : x ∉ lambdaIdeal) :
    localQuadratic lambdaIdeal x ^ 2 = 1 := by
  rcases localQuadratic_trichotomy lambdaIdeal x with hzero | hone | hminus
  · exact False.elim (hx ((localQuadratic_zero_iff lambdaIdeal x).mp hzero))
  · simp [hone]
  · simp [hminus]

/--
@isnad1 id=eq.2h5v.s8.332a859bbaaa from=translated src=- shape=7bf978fa vocab=a1e74265
-/
theorem correctedQuadraticProduct_pair_cancel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) (Q : κ → Ideal O)
    [∀ i, (P i).IsMaximal] [∀ j, (Q j).IsMaximal]
    (hsame : quadraticProduct P (-1) = quadraticProduct Q (-1))
    (x : O) (hx : x ∉ lambdaIdeal) :
    correctedQuadraticProduct P x * correctedQuadraticProduct Q x =
      quadraticProduct P x * quadraticProduct Q x := by
  by_cases hP : quadraticProduct P (-1) = 1
  · have hQ : quadraticProduct Q (-1) = 1 := hsame.symm.trans hP
    simp [correctedQuadraticProduct, hP, hQ]
  · have hQ : quadraticProduct Q (-1) ≠ 1 := by
      intro h
      exact hP (hsame.trans h)
    simp only [correctedQuadraticProduct, hP, hQ, ite_false]
    have hlamSq := lambdaQuadratic_sq_one_of_not_mem x hx
    calc
      quadraticProduct P x * localQuadratic lambdaIdeal x *
          (quadraticProduct Q x * localQuadratic lambdaIdeal x) =
        (quadraticProduct P x * quadraticProduct Q x) *
          localQuadratic lambdaIdeal x ^ 2 := by ring
      _ = quadraticProduct P x * quadraticProduct Q x := by
        rw [hlamSq, mul_one]

/--
@isnad1 id=not.4h4v.s11.1547346f50e6 from=translated src=- shape=3fd7c3a7 vocab=ddf3dda4
-/
theorem correctedQuadraticProduct_not_factor_without_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ lambdaIdeal * s.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  obtain ⟨y, hlam, hfull⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) x)
  have hraw : quadraticProduct P y = -1 := by
    change (∏ j : ι, localQuadratic (P j) y) = -1
    rw [finiteQuadratic_congr_mod_product P y x hfull]
    exact hneg
  have hlocal : localQuadratic lambdaIdeal y = 1 := by
    rw [localQuadratic_congr lambdaIdeal y 1 hlam]
    exact localQuadratic_one lambdaIdeal
  have hy : correctedQuadraticProduct P y = -1 := by
    by_cases hsign : quadraticProduct P (-1) = 1
    · simp [correctedQuadraticProduct, hsign, hraw]
    · simp [correctedQuadraticProduct, hsign, hraw, hlocal]
  have hcopS : IsCoprime lambdaIdeal (s.prod P) := by
    apply IsCoprime.prod_right
    intro j hj
    exact (IsCoprime.prod_right_iff.mp hcop) j (Finset.mem_univ j)
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprodS : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hs : y - 1 ∈ s.prod P := by
    rw [hprodS]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    have hPj : Ideal.Quotient.mk (P j) y =
        Ideal.Quotient.mk (P j) x := by
      apply Ideal.Quotient.eq.mpr
      exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_univ j))) (Ideal.Quotient.eq.mp hfull)
    exact Ideal.Quotient.eq.mp (hPj.trans (hres j hjne))
  have hmod : Ideal.Quotient.mk (lambdaIdeal * s.prod P) y =
      Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O) := by
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.mul_eq_inf_of_isCoprime hcopS]
    exact ⟨Ideal.Quotient.eq.mp hlam, hs⟩
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) y) :=
        hy.symm.trans (hf y)
      _ = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O)) :=
        congrArg f hmod
      _ = 1 := (hf 1).symm.trans (correctedQuadraticProduct_one P)
  norm_num at this

end ActualEisensteinSieve

end

end OAI
