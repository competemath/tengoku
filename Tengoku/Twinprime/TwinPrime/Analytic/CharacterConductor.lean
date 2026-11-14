import Tengoku.Twinprime.TwinPrime.Analytic.CharacterPrimitiveReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact regrouping by primitive conductor

Each primitive character at a divisor of a positive modulus induces exactly
one character at that modulus. The finite identities below preserve this
multiplicity, including the principal character of conductor one.
-/

noncomputable section

open Finset Classical

namespace TwinPrime.Analytic

/-- A primitive character agrees pointwise with its associated primitive
character, even though their level parameters need transport.
@isnad1 id=eq.1h3v.s7.90736b4119d8 from=translated src=- shape=9c37b2f7 vocab=3e3c48b8
-/
theorem primitiveCharacter_apply_of_primitive {r : ℕ}
    (ψ : DirichletCharacter ℂ r) (hψ : ψ.IsPrimitive) (a : ℤ) :
    ψ.primitiveCharacter a = ψ a := by
  have hc : ψ.conductor = r := hψ
  by_cases ha : IsCoprime a r
  · exact ψ.primitiveCharacter_apply_of_isCoprime ha
  · rw [(ψ.apply_eq_zero_iff a).mpr ha,
      (ψ.primitiveCharacter.apply_eq_zero_iff a).mpr (by simpa only [hc] using ha)]

/-- Inducing a primitive character and then taking its primitive character
does not change its centered endpoint maximum.
@isnad1 id=eq.2h4v.s9.0b3e0681cd93 from=translated src=- shape=322ad536 vocab=3f749b1b
-/
theorem characterMaxError_primitive_changeLevel {r q : ℕ} [NeZero q]
    (hd : r ∣ q) (ψ : DirichletCharacter ℂ r) (hψ : ψ.IsPrimitive) (T : ℕ) :
    characterMaxError T (ψ.changeLevel hd).primitiveCharacter = characterMaxError T ψ := by
  have hsum (t : ℕ) :
      characterPsi t (ψ.changeLevel hd).primitiveCharacter = characterPsi t ψ := by
    unfold characterPsi
    apply sum_congr rfl
    intro n _
    congr 1
    have h := DirichletCharacter.primitiveCharacter_changeLevel_apply hd ψ (n : ℤ)
    rw [primitiveCharacter_apply_of_primitive ψ hψ] at h
    simpa only [Int.cast_natCast] using h
  have hcenter (t : ℕ) :
      centeredCharacterPsi t (ψ.changeLevel hd).primitiveCharacter = centeredCharacterPsi t ψ := by
    simp only [centeredCharacterPsi, hsum, primitiveCharacter_principal_iff,
      DirichletCharacter.changeLevel_eq_one_iff]
  simp only [characterMaxError, hcenter]

/-- The mass at one primitive conductor.-/
def primitiveCharacterMass (T r : ℕ) : ℝ :=
  ∑ ψ ∈ (univ : Finset (DirichletCharacter ℂ r)).filter (fun ψ => ψ.IsPrimitive),
    characterMaxError T ψ

/--
@isnad1 id=le.0h2v.s4.f491cdfbf506 from=translated src=- shape=5ffe46ab vocab=a9f87211
-/
theorem primitiveCharacterMass_nonneg (T r : ℕ) : 0 ≤ primitiveCharacterMass T r :=
  sum_nonneg fun ψ _ => characterMaxError_nonneg T ψ

/-- Exact finite conductor regrouping at a positive modulus.
@isnad1 id=eq.1h2v.s6.d2383f2da8e9 from=translated src=- shape=901ffb8d vocab=96f4a484
-/
theorem sum_characterMaxError_primitiveCharacter_eq (T q : ℕ) (hq : 0 < q) :
    (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) =
      ∑ r ∈ q.divisors, primitiveCharacterMass T r := by
  letI : NeZero q := ⟨hq.ne'⟩
  let s : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
    q.divisors.sigma (fun r => univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive))
  have hmem (p : Σ r : ℕ, DirichletCharacter ℂ r) (hp : p ∈ s) :
      p.1 ∣ q ∧ p.2.IsPrimitive := by
    have hs := mem_sigma.mp hp
    exact ⟨(Nat.mem_divisors.mp hs.1).1, (mem_filter.mp hs.2).2⟩
  have hbij : (∑ p ∈ s, characterMaxError T p.2) =
      ∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter := by
    apply sum_bij (fun p hp => p.2.changeLevel (hmem p hp).1)
    · intro p _
      exact mem_univ _
    · rintro ⟨r, ψ⟩ hp ⟨r', ψ'⟩ hp' heq
      have hψ : ψ.conductor = r := (hmem ⟨r, ψ⟩ hp).2
      have hψ' : ψ'.conductor = r' := (hmem ⟨r', ψ'⟩ hp').2
      have hr : r = r' := by
        have h := congrArg DirichletCharacter.conductor heq
        simpa only [DirichletCharacter.conductor_changeLevel, hψ, hψ'] using h
      subst r'
      have hchar : ψ = ψ' := DirichletCharacter.changeLevel_injective (hmem ⟨r, ψ⟩ hp).1 heq
      cases hchar
      rfl
    · intro χ _
      refine ⟨⟨χ.conductor, χ.primitiveCharacter⟩, ?_, ?_⟩
      · exact mem_sigma.mpr ⟨Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, hq.ne'⟩,
          mem_filter.mpr ⟨mem_univ _, χ.primitiveCharacter_isPrimitive⟩⟩
      · exact χ.changeLevel_primitiveCharacter
    · intro p hp
      exact (characterMaxError_primitive_changeLevel (hmem p hp).1 p.2 (hmem p hp).2 T).symm
  rw [← hbij]
  simp only [s, sum_sigma', primitiveCharacterMass]

/-- Reindex a finite divisor sum by the positive multiplier of each divisor.
@isnad1 id=eq.0h2v.s6.05dc66396287 from=translated src=- shape=5e23488f vocab=4323015c
-/
theorem sum_Ioc_divisors_eq_sum_multiples (Q : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ q ∈ Ioc 0 Q, ∑ r ∈ q.divisors, f r q) =
      ∑ r ∈ Ioc 0 Q, ∑ k ∈ Ioc 0 (Q / r), f r (r * k) := by
  have hdiv (q : ℕ) (hq : q ∈ Ioc 0 Q) :
      q.divisors = (Ioc 0 Q).filter (fun r => r ∣ q) := by
    ext r
    simp only [Nat.mem_divisors, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hrq, _⟩
      have hr0 : 0 < r := Nat.pos_of_dvd_of_pos hrq (mem_Ioc.mp hq).1
      exact ⟨⟨hr0, (Nat.le_of_dvd (mem_Ioc.mp hq).1 hrq).trans (mem_Ioc.mp hq).2⟩, hrq⟩
    · intro hr
      exact ⟨hr.2, (mem_Ioc.mp hq).1.ne'⟩
  calc
    _ = ∑ q ∈ Ioc 0 Q, ∑ r ∈ Ioc 0 Q, if r ∣ q then f r q else 0 := by
      apply sum_congr rfl
      intro q hq
      rw [hdiv q hq, sum_filter]
    _ = ∑ r ∈ Ioc 0 Q, ∑ q ∈ (Ioc 0 Q).filter (fun q => r ∣ q), f r q := by
      rw [sum_comm]
      simp only [sum_filter]
    _ = _ := by
      apply sum_congr rfl
      intro r hr
      have hr0 : 0 < r := (mem_Ioc.mp hr).1
      symm
      apply sum_bij (fun k _ => r * k)
      · intro k hk
        have hk0 : 0 < k := (mem_Ioc.mp hk).1
        have hprod : r * k ≤ Q := by
          simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hr0).mp (mem_Ioc.mp hk).2
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨Nat.mul_pos hr0 hk0, hprod⟩, dvd_mul_right _ _⟩
      · intro k _ l _ hkl
        exact Nat.eq_of_mul_eq_mul_left hr0 hkl
      · intro q hq
        obtain ⟨hqI, hrq⟩ := mem_filter.mp hq
        refine ⟨q / r, mem_Ioc.mpr ⟨?_, ?_⟩, Nat.mul_div_cancel' hrq⟩
        · exact Nat.div_pos (Nat.le_of_dvd (mem_Ioc.mp hqI).1 hrq) hr0
        · exact Nat.div_le_div_right (mem_Ioc.mp hqI).2
      · intro k _
        rfl

/-- The global regrouping retains the exact multiplicity weight from all
original moduli divisible by a primitive conductor.
@isnad1 id=eq.0h2v.s7.55722414a924 from=translated src=- shape=0c4aa912 vocab=f9359d1d
-/
theorem sum_primitiveCharacter_errors_eq_conductor_sum (T Q : ℕ) :
    (∑ q ∈ Icc 1 Q,
      (∑ χ : DirichletCharacter ℂ q, characterMaxError T χ.primitiveCharacter) /
        Nat.totient q) =
      ∑ r ∈ Icc 1 Q, primitiveCharacterMass T r *
        ∑ k ∈ Ioc 0 (Q / r), (1 : ℝ) / Nat.totient (r * k) := by
  have hI : Icc 1 Q = Ioc 0 Q := by ext q; simp only [mem_Icc, mem_Ioc]; omega
  rw [hI]
  calc
    _ = ∑ q ∈ Ioc 0 Q, ∑ r ∈ q.divisors,
        primitiveCharacterMass T r / Nat.totient q := by
      apply sum_congr rfl
      intro q hq
      rw [sum_characterMaxError_primitiveCharacter_eq T q (mem_Ioc.mp hq).1, sum_div]
    _ = ∑ r ∈ Ioc 0 Q, ∑ k ∈ Ioc 0 (Q / r),
        primitiveCharacterMass T r / Nat.totient (r * k) :=
      sum_Ioc_divisors_eq_sum_multiples Q (fun r q => primitiveCharacterMass T r / Nat.totient q)
    _ = _ := by
      apply sum_congr rfl
      intro r _
      rw [mul_sum]
      apply sum_congr rfl
      intro k _
      ring

end TwinPrime.Analytic
