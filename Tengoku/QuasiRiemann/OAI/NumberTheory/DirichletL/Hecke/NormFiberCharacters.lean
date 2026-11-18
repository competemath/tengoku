import Tengoku.QuasiRiemann.OAI.NumberTheory.DirichletL.Arithmetic.NormFiberMellin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology

namespace ShortDraftHeckeBridge

/--
@isnad1 id=eq.0h2v.s4.a2f8a896b4ba from=translated src=- shape=9654c490 vocab=30ba62f2
-/
theorem normFiberCoeff_baseChangeWeight_zero {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 0 = 0 := by
  classical
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 0 := by
    simpa using hI
  have hbot : I = ⊥ := Ideal.absNorm_eq_zero_iff.mp hnorm
  subst I
  rw [baseChangeWeight]
  have hz : UniqueFactorizationMonoid.moebius (⊥ : Ideal O) = 0 := by
    simpa only [Ideal.zero_eq_bot] using
      (UniqueFactorizationMonoid.moebius_zero (α := Ideal O))
  rw [hz]
  simp

noncomputable def baseChangeChar {q : ℕ} (χ : DirichletCharacter ℂ q) :
    DirichletCharacter ℂ (q * 3) :=
  χ.changeLevel (Nat.dvd_mul_right q 3) *
    chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q)

/--
@isnad1 id=ne.1h2v.s7.2fbe6e656189 from=translated src=- shape=a03d63f7 vocab=8059303d
-/
theorem baseChangeChar_ne_one_of_one {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ = 1) :
    baseChangeChar χ ≠ 1 := by
  intro h
  apply not_both_principal χ
  constructor
  · simp [hχ]
  · exact h

end ShortDraftHeckeBridge
namespace ActualEisensteinCubic

open MulChar AddChar

end ActualEisensteinCubic

namespace ShortDraftHeckeBridge

/--
@isnad1 id=isrelpri.1h2v.s9.503639f51d37 from=translated src=- shape=1f37d68b vocab=825ac2cf
-/
theorem ideals_isRelPrime_of_norms_coprime (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    IsRelPrime I J := by
  have hcast : IsCoprime ((Ideal.absNorm I : ℕ) : O)
      ((Ideal.absNorm J : ℕ) : O) := by
    simpa only [map_natCast] using
      (Nat.Coprime.isCoprime h).map (Int.castRingHom O)
  obtain ⟨a, b, hab⟩ := hcast
  apply IsCoprime.isRelPrime
  apply Ideal.isCoprime_iff_exists.mpr
  refine ⟨a * (Ideal.absNorm I : O),
    I.mul_mem_left a (Ideal.absNorm_mem I),
    b * (Ideal.absNorm J : O),
    J.mul_mem_left b (Ideal.absNorm_mem J), hab⟩

/--
@isnad1 id=eq.1h4v.s9.866eb4609306 from=translated src=- shape=b5f3b9b7 vocab=164d0a23
-/
theorem baseChangeWeight_mul_of_coprime_norms {q : ℕ}
    (χ : DirichletCharacter ℂ q) (I J : Ideal O)
    (h : (Ideal.absNorm I).Coprime (Ideal.absNorm J)) :
    baseChangeWeight χ (I * J) =
      baseChangeWeight χ I * baseChangeWeight χ J := by
  have hrel := ideals_isRelPrime_of_norms_coprime I J h
  simp only [baseChangeWeight, map_mul, hrel.moebius_mul, Int.cast_mul, Nat.cast_mul]
  ring

/--
@isnad1 id=eq.1h3v.s8.2e05174fadd5 from=translated src=- shape=db89da36 vocab=690bbdb5
-/
theorem baseChangeChar_apply_of_coprime {q : ℕ}
    (χ : DirichletCharacter ℂ q) (n : ℕ)
    (h : n.Coprime (q * 3)) :
    baseChangeChar χ n = χ n * chiMinusThree n := by
  have hc : IsCoprime (n : ℤ) (q * 3 : ℕ) := by
    simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using h
  rw [baseChangeChar, MulChar.mul_apply]
  have hχ : χ.changeLevel (Nat.dvd_mul_right q 3) n = χ n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' χ
      (Nat.dvd_mul_right q 3) hc)
  have hη : chiMinusThree.changeLevel (Nat.dvd_mul_left 3 q) n =
      chiMinusThree n := by
    simpa using (DirichletCharacter.changeLevel_eq_cast_of_dvd' chiMinusThree
      (Nat.dvd_mul_left 3 q) hc)
  rw [hχ, hη]

/--
@isnad1 id=eq.0h0v.s6.0926eb05eaa9 from=translated src=- shape=6aa72273 vocab=63b66b40
-/
theorem chiMinusThree_three : chiMinusThree (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff chiMinusThree 3).mpr
    (by simp [Int.isCoprime_iff_nat_coprime])

/--
@isnad1 id=eq.0h2v.s7.2b6a159086bf from=translated src=- shape=78a95cbd vocab=c1fc6779
-/
theorem baseChangeChar_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    baseChangeChar χ (3 : ℕ) = 0 := by
  simpa using (DirichletCharacter.apply_eq_zero_iff (baseChangeChar χ) 3).mpr
    (by
      intro hc
      have hn : Nat.Coprime 3 (q * 3) := by
        simpa [Int.isCoprime_iff_nat_coprime, Int.natAbs_mul] using hc
      have hself : Nat.Coprime 3 3 := hn.of_dvd_right (Nat.dvd_mul_left 3 q)
      norm_num at hself)

private abbrev K := CyclotomicField 3 ℚ
private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
private instance : IsGalois ℚ K := IsCyclotomicExtension.isGalois {3} ℚ K

private theorem orderOf_mod3_eq_one {p : ℕ} (h : p % 3 = 1) :
    orderOf (p : ZMod 3) = 1 := by
  have hc : (p : ZMod 3) = 1 :=
    (ZMod.natCast_eq_natCast_iff' p 1 3).2 (by simpa using h)
  simp [hc]

private theorem orderOf_mod3_eq_two {p : ℕ} (h : p % 3 = 2) :
    orderOf (p : ZMod 3) = 2 := by
  have hc : (p : ZMod 3) = 2 :=
    (ZMod.natCast_eq_natCast_iff' p 2 3).2 (by simpa using h)
  rw [hc]
  have hdvd : orderOf (2 : ZMod 3) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by decide : (2 : ZMod 3) ^ 2 = 1)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hdvd with h1 | h2
  · have h21 : (2 : ZMod 3) = 1 := orderOf_eq_one_iff.mp h1
    exact False.elim ((by decide : (2 : ZMod 3) ≠ 1) h21)
  · exact h2

private theorem degree_two : Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 3 K]
  decide

private theorem gal_card_two : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K]
  exact degree_two

private theorem not_dvd_three {p : ℕ} (hp : p.Prime) (hneq : p ≠ 3) : ¬ p ∣ 3 := by
  intro hd
  have h := (Nat.dvd_prime (by decide : Nat.Prime 3)).1 hd
  rcases h with h1 | h3
  · exact hp.ne_one h1
  · exact hneq h3

/--
@isnad1 id=eq.2h1v.s6.d44ff0dd1c17 from=translated src=- shape=5738961f vocab=6a06f0cc
-/
theorem split_count_of_mod_one {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_one hmod, gal_card_two] at hmain
  omega

/--
@isnad1 id=eq.2h1v.s6.94f650225870 from=translated src=- shape=5738961f vocab=6a06f0cc
-/
theorem inert_count_of_mod_two {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    ((Ideal.span {(p : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hmain := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p : ℤ)}) O Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hnd,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
    orderOf_mod3_eq_two hmod, gal_card_two] at hmain
  omega

/--
@isnad1 id=eq.0h0v.s6.6b6004377cc6 from=translated src=- shape=5ba1d7aa vocab=47f75f89
-/
theorem ramified_count :
    ((Ideal.span {(3 : ℤ)}).primesOver O).ncard = 1 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime 3 K

/--
@isnad1 id=eq.2h2v.s8.653b3fdd9143 from=translated src=- shape=cf7ba213 vocab=ad5fe7d2
-/
theorem absNorm_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_one hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf, pow_one]

/--
@isnad1 id=eq.2h2v.s8.9770a2de8f6e from=translated src=- shape=c4336a65 vocab=022e4919
-/
theorem absNorm_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2)
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.absNorm P = p ^ 2 := by
  let : Fact p.Prime := ⟨hp⟩
  have hneq : p ≠ 3 := by
    intro heq
    subst p
    norm_num at hmod
  have hnd := not_dvd_three hp hneq
  have hf : P.inertiaDeg ℤ = 2 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)}) P Gal(K/ℚ),
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hnd,
      orderOf_mod3_eq_two hmod]
  rw [← Ideal.pow_inertiaDeg p P, hf]

/--
@isnad1 id=eq.0h1v.s8.208799758659 from=translated src=- shape=ce0c2305 vocab=c9fb348a
-/
theorem absNorm_ramified
    (P : Ideal O) [P.IsPrime] [P.LiesOver (Ideal.span {(3 : ℤ)})] :
    Ideal.absNorm P = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hfin : (Ideal.span {(3 : ℤ)}).inertiaDegIn O = 1 := by
    simpa using IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime 3 K
  have hf : P.inertiaDeg ℤ = 1 := by
    rw [← Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(3 : ℤ)}) P Gal(K/ℚ)]
    exact hfin
  rw [← Ideal.pow_inertiaDeg 3 P, hf, pow_one]

/--
@isnad1 id=mem.2h2v.s8.fd991ceac670 from=translated src=- shape=95b1d9c3 vocab=2b177ffc
-/
theorem norm_prime_implies_over {p : ℕ} (hp : p.Prime) (I : Ideal O)
    (hI : Ideal.absNorm I = p) :
    I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
  have hprime : I.IsPrime :=
    Ideal.isPrime_of_irreducible_absNorm (by
      rw [hI]
      exact (Nat.irreducible_iff_nat_prime p).2 hp)
  have hover : I.LiesOver (Ideal.span {(p : ℤ)}) := by
    rw [Ideal.liesOver_iff]
    rw [Ideal.under_def, algebraMap_int_eq]
    simpa [hI] using Ideal.span_singleton_absNorm (I := I) (hI ▸ hp)
  exact ⟨hprime, hover⟩

/--
@isnad1 id=eq.2h1v.s8.82332e6e2367 from=translated src=- shape=c345e443 vocab=b5964920
-/
theorem norm_p_fiber_split {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    {I : Ideal O | Ideal.absNorm I = p} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over hp I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_split hp hmod I

/--
@isnad1 id=eq.2h1v.s8.6ec67735b4d8 from=translated src=- shape=9d2bc9a8 vocab=817b61fc
-/
theorem norm_p_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p} = ∅ := by
  ext I
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro hI
  have hOver := norm_prime_implies_over hp I hI
  let : I.IsPrime := hOver.1
  let : I.LiesOver (Ideal.span {(p : ℤ)}) := hOver.2
  have hNorm := absNorm_inert hp hmod I
  have hpge := hp.two_le
  nlinarith

/--
@isnad1 id=eq.0h0v.s8.0b1efaac893a from=translated src=- shape=69b70d7f vocab=78478c7a
-/
theorem norm_three_fiber :
    {I : Ideal O | Ideal.absNorm I = 3} =
      (Ideal.span {(3 : ℤ)}).primesOver O := by
  ext I
  constructor
  · exact norm_prime_implies_over (by decide) I
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(3 : ℤ)}) := hI.2
    exact absNorm_ramified I

/--
@isnad1 id=eq.2h1v.s8.33b22da23008 from=translated src=- shape=709866b1 vocab=0b2a8901
-/
theorem norm_p_sq_fiber_inert {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    {I : Ideal O | Ideal.absNorm I = p ^ 2} =
      (Ideal.span {(p : ℤ)}).primesOver O := by
  ext I
  constructor
  · intro hI
    have hdiv : p ∣ Ideal.absNorm I := by
      rw [hI]
      exact dvd_pow_self p (by decide)
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = p ^ 2 := absNorm_inert hp hmod P
    obtain ⟨J, hIJ⟩ := hPdiv
    have hJN : Ideal.absNorm J = 1 := by
      have heq := congrArg Ideal.absNorm hIJ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nlinarith
    have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJN
    subst J
    simp only [Ideal.mul_top] at hIJ
    subst I
    exact ⟨inferInstance, inferInstance⟩
  · intro hI
    let : I.IsPrime := hI.1
    let : I.LiesOver (Ideal.span {(p : ℤ)}) := hI.2
    exact absNorm_inert hp hmod I

/--
@isnad1 id=ex.3h2v.s9.c55df86386bd from=translated src=- shape=ea39c9ef vocab=c98006ae
-/
theorem norm_p_sq_split_factors {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1)
    (I : Ideal O) (hI : Ideal.absNorm I = p ^ 2) :
    ∃ P Q : Ideal O,
      P ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      Q ∈ (Ideal.span {(p : ℤ)}).primesOver O ∧
      I = P * Q := by
  have hdiv : p ∣ Ideal.absNorm I := by
    rw [hI]
    exact dvd_pow_self p (by decide)
  obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
    Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp I hdiv
  have : P.IsPrime := hPmax.isPrime
  have : P.LiesOver (Ideal.span {(p : ℤ)}) := ⟨hPunder.symm⟩
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  obtain ⟨Q, hIQ⟩ := hPdiv
  have hQN : Ideal.absNorm Q = p := by
    have heq := congrArg Ideal.absNorm hIQ
    simp only [map_mul] at heq
    rw [hI, hPN] at heq
    have hppos := hp.pos
    nlinarith
  exact ⟨P, Q, ⟨inferInstance, inferInstance⟩,
    norm_prime_implies_over hp Q hQN, hIQ⟩

/--
@isnad1 id=eq.0h0v.s9.a2e8d4cc2931 from=translated src=- shape=110d1fd8 vocab=6a62300d
-/
theorem norm_nine_fiber_ramified :
    {I : Ideal O | Ideal.absNorm I = 9} =
      {I : Ideal O | ∃ P : Ideal O,
        P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
  ext I
  constructor
  · intro hI
    have hdiv : 3 ∣ Ideal.absNorm I := by
      rw [hI]
      decide
    obtain ⟨P, hPmax, hPunder, hPdiv⟩ :=
      Ideal.exists_isMaximal_dvd_of_dvd_absNorm' (by decide : Nat.Prime 3) I hdiv
    have : P.IsPrime := hPmax.isPrime
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := ⟨hPunder.symm⟩
    have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
    obtain ⟨Q, hIQ⟩ := hPdiv
    have hQN : Ideal.absNorm Q = 3 := by
      have heq := congrArg Ideal.absNorm hIQ
      simp only [map_mul] at heq
      rw [hI, hPN] at heq
      omega
    have hQover := norm_prime_implies_over (by decide : Nat.Prime 3) Q hQN
    have hPover : P ∈ (Ideal.span {(3 : ℤ)}).primesOver O :=
      ⟨inferInstance, inferInstance⟩
    have hfinite : ((Ideal.span {(3 : ℤ)}).primesOver O).Finite := by
      rw [← norm_three_fiber]
      exact Ideal.finite_setOfPred_absNorm_eq 3
    have hsub : ∀ {A B : Ideal O},
        A ∈ (Ideal.span {(3 : ℤ)}).primesOver O →
        B ∈ (Ideal.span {(3 : ℤ)}).primesOver O → A = B :=
      (Set.ncard_le_one_iff hfinite).mp (by rw [ramified_count])
    have hPQ : P = Q := hsub hPover hQover
    refine ⟨P, hPover, ?_⟩
    rw [hIQ, ← hPQ, pow_two]
  · rintro ⟨P, hP, rfl⟩
    have : P.IsPrime := hP.1
    have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
    change Ideal.absNorm (P ^ 2) = 9
    rw [map_pow, absNorm_ramified P]
    norm_num

/--
@isnad1 id=dirichle.2h0v.s7.7cc628aed229 from=translated src=- shape=398a0241 vocab=543e21f0
-/
theorem dirichletTarget_of_ideal_base_change
    (hcoeff : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (n : ℕ), n ≠ 0 →
        normFiberCoeff (baseChangeWeight χ) n =
          pairInverseCoeff χ (baseChangeChar χ) n)
    (hbound : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q)
      (ρ : ℂ), (23 / 24 : ℝ) < ρ.re → ρ.re < 1 →
        ∃ σ : ℝ, 0 < σ ∧ σ < ρ.re ∧
          (fun D : ℝ => normFiberExpSum (baseChangeWeight χ) D⁻¹) =O[atTop]
            (fun D : ℝ => D ^ σ)) :
    ShortDraft.DirichletTarget := by
  intro q _ χ ρ h23 hprincipal
  by_cases hρ : ρ.re < 1
  · obtain ⟨σ, hσpos, hσρ, htop⟩ := hbound q χ ρ h23 hρ
    have hσone : σ < 1 := lt_trans hσρ hρ
    have hρone : ρ ≠ 1 := by
      intro hh
      subst ρ
      norm_num at hρ
    have hc := hcoeff q χ
    have hz := normFiberCoeff_baseChangeWeight_zero χ
    by_cases hχ : χ = 1
    · have hψ : baseChangeChar χ ≠ 1 :=
        baseChangeChar_ne_one_of_one χ hχ
      have hc' : ∀ n : ℕ, n ≠ 0 →
          normFiberCoeff (baseChangeWeight χ) n =
            pairInverseCoeff (1 : DirichletCharacter ℂ q)
              (baseChangeChar χ) n := by
        intro n hn
        simpa only [hχ] using hc n hn
      have hpair := pair_zero_free_of_normFiber_exp_power_bound_principal_left
        (q := q) (baseChangeChar χ) hψ (baseChangeWeight χ)
        hc' hz σ hσpos hσone htop ρ hσρ hρone
      simpa only [hχ] using hpair.1
    · by_cases hψ : baseChangeChar χ = 1
      · have hc' : ∀ n : ℕ, n ≠ 0 →
            normFiberCoeff (baseChangeWeight χ) n =
              pairInverseCoeff χ (1 : DirichletCharacter ℂ (q * 3)) n := by
          intro n hn
          simpa only [hψ] using hc n hn
        exact (pair_zero_free_of_normFiber_exp_power_bound_principal_right
          χ hχ (baseChangeWeight χ) hc' hz σ hσpos hσone htop ρ hσρ hρone).1
      · exact (pair_zero_free_of_normFiber_exp_power_bound_only
          χ (baseChangeChar χ) hχ hψ (baseChangeWeight χ)
          (fun n hn => hc n hn) hz σ hσpos hσone htop ρ hσρ).1
  · exact ShortDraft.dirichlet_target_of_one_le_re q χ ρ
      (le_of_not_gt hρ) hprincipal

/--
@isnad1 id=eq.2h3v.s5.eab6ab821fe1 from=translated src=- shape=0a2e9f34 vocab=6f3161e6
-/
theorem local_inert_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) p = 0 := by
  have hf := norm_p_fiber_inert hp hmod
  unfold normFiberCoeff
  simp [hf]

/--
@isnad1 id=eq.2h3v.s6.8cb51aab7ad7 from=translated src=- shape=3a8addaa vocab=237afa7e
-/
theorem local_split_p {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) p = -(2 : ℂ) * χ p := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) p
  have hcard : hf.toFinset.card = 2 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p} hf]
    rw [norm_p_fiber_split hp hmod]
    exact split_count_of_mod_one hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) p =
      ∑ I ∈ hf.toFinset, -χ p := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = p := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime p).2 hp))
    rw [baseChangeWeight_prime χ I hprime, hnorm]
  rw [hsum]
  simp [hcard]

/--
@isnad1 id=eq.0h2v.s6.17f99f84a516 from=translated src=- shape=75a04623 vocab=887f6f5a
-/
theorem local_ramified_three {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 3 = -χ 3 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 3
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = 3} hf]
    rw [norm_three_fiber]
    exact ramified_count
  have hsum : normFiberCoeff (baseChangeWeight χ) 3 =
      ∑ I ∈ hf.toFinset, -χ 3 := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hnorm : Ideal.absNorm I = 3 := hf.mem_toFinset.mp hI
    have hprime : Prime I :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp
        (Ideal.irreducible_of_irreducible_absNorm (by
          rw [hnorm]
          exact (Nat.irreducible_iff_nat_prime 3).2 (by decide)))
    simpa only [hnorm, Nat.cast_ofNat] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

/--
@isnad1 id=eq.2h3v.s7.43d47ad52ff9 from=translated src=- shape=dc487338 vocab=9064327b
-/
theorem local_inert_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 2) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = -χ (p ^ 2) := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hcard : hf.toFinset.card = 1 := by
    rw [← Set.ncard_eq_toFinset_card {I : Ideal O | Ideal.absNorm I = p ^ 2} hf]
    rw [norm_p_sq_fiber_inert hp hmod]
    exact inert_count_of_mod_two hp hmod
  have hsum : normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
      ∑ I ∈ hf.toFinset, -χ (p ^ 2) := by
    unfold normFiberCoeff
    apply Finset.sum_congr rfl
    intro I hI
    have hover : I ∈ (Ideal.span {(p : ℤ)}).primesOver O := by
      rw [← norm_p_sq_fiber_inert hp hmod]
      exact hf.mem_toFinset.mp hI
    have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hI
    let : I.IsPrime := hover.1
    have hprime : Prime I := Ideal.prime_of_isPrime (by
      intro hbot
      have : Ideal.absNorm I = 0 := by rw [hbot]; simp
      rw [hnorm] at this
      exact (pow_ne_zero 2 hp.ne_zero) this) inferInstance
    simpa only [hnorm, Nat.cast_pow] using baseChangeWeight_prime χ I hprime
  rw [hsum]
  simp [hcard]

/--
@isnad1 id=eq.0h2v.s4.a22dcad779df from=translated src=- shape=9654c490 vocab=30ba62f2
-/
theorem local_ramified_nine {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 9 = 0 := by
  classical
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) 9
  unfold normFiberCoeff
  apply Finset.sum_eq_zero
  intro I hI
  have hnorm : Ideal.absNorm I = 9 := hf.mem_toFinset.mp hI
  have hfactor : I ∈ {I : Ideal O | ∃ P : Ideal O,
      P ∈ (Ideal.span {(3 : ℤ)}).primesOver O ∧ I = P ^ 2} := by
    rw [← norm_nine_fiber_ramified]
    exact hnorm
  obtain ⟨P, hP, rfl⟩ := hfactor
  have : P.IsPrime := hP.1
  have : P.LiesOver (Ideal.span {(3 : ℤ)}) := hP.2
  have hPN : Ideal.absNorm P = 3 := absNorm_ramified P
  have hnotunit : ¬ IsUnit P := by
    intro hunit
    have htop : P = ⊤ := Ideal.isUnit_iff.mp hunit
    rw [htop, Ideal.absNorm_top] at hPN
    norm_num at hPN
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    apply hnotunit
    exact hsq P (by rw [pow_two])
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

private theorem baseChangeWeight_prime_sq_zero {q : ℕ} (χ : DirichletCharacter ℂ q)
    (P : Ideal O) (hP : Prime P) :
    baseChangeWeight χ (P ^ 2) = 0 := by
  have hnot : ¬ Squarefree (P ^ 2) := by
    intro hsq
    have hunit : IsUnit P := hsq P (by rw [pow_two])
    exact hP.irreducible.not_isUnit hunit
  rw [baseChangeWeight, UniqueFactorizationMonoid.moebius_of_not_squarefree hnot]
  simp

/--
@isnad1 id=eq.2h3v.s7.550e23860ef4 from=translated src=- shape=d7c6916f vocab=e9553691
-/
theorem local_split_p_sq {q : ℕ} (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) = χ (p ^ 2) := by
  classical
  let s : Set (Ideal O) := (Ideal.span {(p : ℤ)}).primesOver O
  obtain ⟨P, Q, hPQ, hset⟩ := Set.ncard_eq_two.mp (split_count_of_mod_one hp hmod)
  have hPover : P ∈ s := by
    change P ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  have hQover : Q ∈ s := by
    change Q ∈ (Ideal.span {(p : ℤ)}).primesOver O
    rw [hset]
    simp
  let : P.IsPrime := hPover.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hPover.2
  let : Q.IsPrime := hQover.1
  let : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQover.2
  have hPN : Ideal.absNorm P = p := absNorm_split hp hmod P
  have hQN : Ideal.absNorm Q = p := absNorm_split hp hmod Q
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hPN
    exact hp.ne_zero hPN.symm
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hQN
    exact hp.ne_zero hQN.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPne inferInstance
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQne inferInstance
  have : P.IsMaximal := (inferInstance : P.IsPrime).isMaximal hPne
  have : Q.IsMaximal := (inferInstance : Q.IsPrime).isMaximal hQne
  have hrel : IsRelPrime P Q := (Ideal.isCoprime_of_isMaximal hPQ).isRelPrime
  have hmu : UniqueFactorizationMonoid.moebius (P * Q) = 1 := by
    rw [hrel.moebius_mul, hPprime.irreducible.moebius_eq,
      hQprime.irreducible.moebius_eq]
    norm_num
  let hf := Ideal.finite_setOfPred_absNorm_eq (S := O) (p ^ 2)
  have hmem : P * Q ∈ hf.toFinset := by
    rw [hf.mem_toFinset]
    change Ideal.absNorm (P * Q) = p ^ 2
    rw [map_mul, hPN, hQN, pow_two]
  calc
    normFiberCoeff (baseChangeWeight χ) (p ^ 2) =
        ∑ I ∈ hf.toFinset, baseChangeWeight χ I := by rfl
    _ = baseChangeWeight χ (P * Q) := by
      apply Finset.sum_eq_single (P * Q)
      · intro I hImem hneq
        have hnorm : Ideal.absNorm I = p ^ 2 := hf.mem_toFinset.mp hImem
        obtain ⟨A, B, hA, hB, rfl⟩ := norm_p_sq_split_factors hp hmod I hnorm
        rw [hset] at hA hB
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
        rcases hA with hAP | hAQ <;> rcases hB with hBP | hBQ
        · rw [hAP, hBP]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ P hPprime
        · exact False.elim (hneq (by rw [hAP, hBQ]))
        · exact False.elim (hneq (by rw [hAQ, hBP, mul_comm]))
        · rw [hAQ, hBQ]
          simpa only [pow_two] using baseChangeWeight_prime_sq_zero χ Q hQprime
      · intro hnot
        exact False.elim (hnot hmem)
    _ = χ (p ^ 2) := by
      rw [baseChangeWeight, hmu]
      have hnorm : Ideal.absNorm (P * Q) = p ^ 2 := by
        rw [map_mul, hPN, hQN, pow_two]
      simp [hnorm, Nat.cast_pow]

/--
@isnad1 id=eq.0h2v.s4.fa029ab3f3d5 from=translated src=- shape=9654c490 vocab=30ba62f2
-/
theorem local_one {q : ℕ} (χ : DirichletCharacter ℂ q) :
    normFiberCoeff (baseChangeWeight χ) 1 = 1 := by
  classical
  have hfinset : (Ideal.finite_setOfPred_absNorm_eq (S := O) 1).toFinset = {⊤} := by
    ext I
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Ideal.absNorm_eq_one_iff
  unfold normFiberCoeff
  rw [hfinset]
  simp only [Finset.sum_singleton]
  change baseChangeWeight χ ⊤ = 1
  have hunit : IsUnit (⊤ : Ideal O) := Ideal.isUnit_iff.mpr rfl
  have hmu : UniqueFactorizationMonoid.moebius (⊤ : Ideal O) = 1 := hunit.moebius_eq
  change (UniqueFactorizationMonoid.moebius (⊤ : Ideal O) : ℂ) *
    χ (Ideal.absNorm (⊤ : Ideal O)) = 1
  rw [hmu, Ideal.absNorm_top]
  simp

end ShortDraftHeckeBridge

end

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
