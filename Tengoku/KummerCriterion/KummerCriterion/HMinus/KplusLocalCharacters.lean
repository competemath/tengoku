module

public import Tengoku.KummerCriterion.KummerCriterion.ZetaFactorisation.Basic
import Tengoku.KummerCriterion.KummerCriterion.GaussSum.SignInvariant.BranchChoice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# `K⁺` local even-character data

Residue-degree and local-factor identities for the maximal real subfield side.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators Pointwise

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime]

/-- The residue-degree candidate for `K⁺`: the order of `ℓ mod p` up to sign.-/
noncomputable def localResidueDegreePlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  if Even d then d / 2 else d

/-- The expected number of primes above `ℓ ≠ p` on the `K⁺` side.-/
noncomputable def localPrimeCountPlus (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ℕ :=
  let d := localResidueDegree (p := p) ℓ hℓp
  let c := localPrimeCount (p := p) ℓ hℓp
  if Even d then c else c / 2

/--
@isnad1 id=eq.2h2v.s5.46397252311f from=translated src=- shape=d12e5dc9 vocab=73527589
-/
lemma localResidueDegreePlus_eq_half {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_even : Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp / 2 := by
  simp [localResidueDegreePlus, hd_even]

/--
@isnad1 id=eq.2h2v.s5.fdf3b889cf23 from=translated src=- shape=eecef131 vocab=07ad0503
-/
lemma localResidueDegreePlus_eq_self {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (hd_odd : ¬ Even (localResidueDegree (p := p) ℓ hℓp)) :
    localResidueDegreePlus (p := p) ℓ hℓp = localResidueDegree (p := p) ℓ hℓp := by
  simp [localResidueDegreePlus, hd_odd]

/--
@isnad1 id=or.1h2v.s7.59cd3d74bde4 from=translated src=- shape=3a4b7c53 vocab=2b44a479
-/
lemma unitOfPrimeNe_pow_localResidueDegreePlus_eq_one_or_neg_one
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = 1) ∨
      (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p) ^
        localResidueDegreePlus (p := p) ℓ hℓp = -1) := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hsq : (((u : ZMod p) ^ (d / 2)) ^ 2) = 1 := by
      rw [← pow_mul]
      have : (d / 2) * 2 = d := by omega
      rw [this]
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    have hcases : ((u : ZMod p) ^ (d / 2)) = 1 ∨ ((u : ZMod p) ^ (d / 2)) = -1 :=
      sq_eq_one_iff.mp hsq
    have hnot_one : ((u : ZMod p) ^ (d / 2)) ≠ 1 := by
      intro hpow
      have hpow_units : u ^ (d / 2) = 1 := by
        apply Units.ext
        simpa using hpow
      have hdvd : d ∣ d / 2 := by
        simpa [d, localResidueDegree, u] using
          (orderOf_dvd_iff_pow_eq_one (x := u)).2 hpow_units
      have hk_pos : 0 < k := by
        have hd_pos : 0 < d := by
          dsimp [d, localResidueDegree]
          exact orderOf_pos u
        omega
      have hle : 2 * k ≤ k := by
        have hdvd' : 2 * k ∣ k := by
          rw [hk] at hdvd
          rw [show k + k = 2 * k by omega] at hdvd
          simpa using hdvd
        exact Nat.le_of_dvd hk_pos hdvd'
      omega
    rcases hcases with hpow | hpow
    · exact False.elim (hnot_one hpow)
    · right
      simpa [localResidueDegreePlus, d, hk] using hpow
  · left
    have hpow : (u : ZMod p) ^ d = 1 := by
      dsimp [d, localResidueDegree]
      change (((u ^ orderOf u : (ZMod p)ˣ) : ZMod p)) = 1
      exact congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one u)
    simpa [localResidueDegreePlus, d, hd_even] using hpow

/--
@isnad1 id=eq.1h2v.s7.6ecf101e8c61 from=translated src=- shape=3e877a97 vocab=28439213
-/
lemma orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) =
      localResidueDegreePlus (p := p) ℓ hℓp := by
  let u : (ZMod p)ˣ := unitOfPrimeNe (p := p) ℓ hℓp
  let d : ℕ := localResidueDegree (p := p) ℓ hℓp
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hd_even' : Even (localResidueDegree (p := p) ℓ hℓp) :=
      ⟨k, by simpa [d] using hk⟩
    have hgcd : d.gcd 2 = 2 := by
      apply Nat.dvd_antisymm
      · exact Nat.gcd_dvd_right d 2
      · exact Nat.dvd_gcd ⟨k, by omega⟩ dvd_rfl
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [orderOf_pow], hgcd,
      localResidueDegreePlus_eq_half (p := p) hℓp hd_even']
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    have hgcd : d.gcd 2 = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hd_odd.coprime_two_right
    rw [show orderOf (u ^ 2) = d / d.gcd 2 by
        dsimp [d, localResidueDegree]
        rw [orderOf_pow], hgcd,
      localResidueDegreePlus_eq_self (p := p) hℓp (by simpa [d] using hd_even)]
    simp [d]

attribute [local instance] Classical.decEq Classical.propDecidable

/--
@isnad1 id=eq.1h1v.s6.3bfedb96b7d9 from=translated src=- shape=e827cb13 vocab=b3b84ea0
-/
lemma card_even_characters_kplus (hp_odd' : p ≠ 2) :
    (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
  card_even_characters p hp_odd'

/--
@isnad1 id=eq.1h1v.s5.429431a94eea from=translated src=- shape=6a00d6f6 vocab=4f6e8da9
-/
lemma card_evenNontrivialCharacters (hp_odd' : p ≠ 2) :
    (evenNontrivialCharacters (p := p)).card = (p - 3) / 2 := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  rw [hrewrite, Finset.card_erase_of_mem]
  · have hcard_even :
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card = (p - 1) / 2 :=
      card_even_characters_kplus (p := p) hp_odd'
    omega
  · simp [htriv_even]

/--
@isnad1 id=eq.2h2v.s6.f4ee8f218502 from=translated src=- shape=fb1329b6 vocab=be0401cc
-/
lemma localPrimeCountPlus_mul_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).card := by
  classical
  set d := localResidueDegree (p := p) ℓ hℓp with hd
  set c := localPrimeCount (p := p) ℓ hℓp with hc
  have hprod_card : c * d = Nat.card (DirichletCharacter ℂ p) := by
    simpa [c, d] using (localPrimeCount_mul_localResidueDegree (p := p) hℓp)
  have hprod : c * d = p - 1 := by
    rw [hprod_card, card_dirichletCharacter_complex (p := p)]
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  rw [card_even_characters_kplus (p := p) hp_odd']
  rcases hp_odd_nat with ⟨m, hm⟩
  have hhalf : (p - 1) / 2 = m := by
    omega
  by_cases hd_even : Even d
  · rcases hd_even with ⟨k, hk⟩
    have hkdiv : (k + k) / 2 = k := by
      omega
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp *
            localResidueDegreePlus (p := p) ℓ hℓp =
          c * k := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hkdiv, ← hc]
    have hck : c * k = m := by
      have hdouble : c * k + c * k = m + m := by
        calc
          c * k + c * k = c * (k + k) := by rw [Nat.mul_add]
          _ = p - 1 := by simpa [hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (c * k) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hck]
  · have hd_odd : Odd d := Nat.not_even_iff_odd.mp hd_even
    rcases hd_odd with ⟨k, hk⟩
    have hc_even : Even c := by
      have hprod' : c * (2 * k + 1) = p - 1 := by
        simpa [hk] using hprod
      have h_rhs_even : Even (p - 1) := by
        refine ⟨m, ?_⟩
        rw [hm]
        omega
      by_contra hc_not_even
      have hc_odd : Odd c := Nat.not_even_iff_odd.mp hc_not_even
      have hlhs_odd : Odd (c * (2 * k + 1)) :=
        hc_odd.mul ⟨k, rfl⟩
      have h_lhs_even : Even (c * (2 * k + 1)) := by
        simpa [hprod'] using h_rhs_even
      exact (Nat.not_even_iff_odd.mpr hlhs_odd) h_lhs_even
    rcases hc_even with ⟨j, hj⟩
    have hc_half : localPrimeCount (p := p) ℓ hℓp / 2 = j := by
      rw [← hc, hj]
      simpa [two_mul, Nat.mul_comm] using (Nat.mul_div_right j (by decide : 0 < 2))
    have hlhs :
        localPrimeCountPlus (p := p) ℓ hℓp * localResidueDegreePlus (p := p) ℓ hℓp =
          j * (2 * k + 1) := by
      simp [localPrimeCountPlus, localResidueDegreePlus, d, hk, hc_half]
    have hjk : j * (2 * k + 1) = m := by
      have hdouble : j * (2 * k + 1) + j * (2 * k + 1) = m + m := by
        calc
          j * (2 * k + 1) + j * (2 * k + 1) = (j + j) * (2 * k + 1) := by
            rw [Nat.add_mul]
          _ = p - 1 := by simpa [hj, hk] using hprod
          _ = m + m := by rw [hm]; omega
      have hdouble' : 2 * (j * (2 * k + 1)) = 2 * m := by
        simpa [two_mul] using hdouble
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) hdouble'
    rw [hlhs, hhalf, hjk]

/-- The product over all even characters at `ℓ ≠ p` is a single local factor of
degree `localResidueDegreePlus`, repeated `localPrimeCountPlus` times.
@isnad1 id=eq.2h3v.s7.e7159b7def3e from=translated src=- shape=45a9daa4 vocab=2f2382ff
-/
lemma prod_even_characters_eval_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (T : ℂ) :
    Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ => (1 - χ (ℓ : ZMod p) * T)) =
      (1 - T ^ localResidueDegreePlus (p := p) ℓ hℓp) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  let E : Finset (DirichletCharacter ℂ p) :=
    Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even
  set n := Nat.card (DirichletCharacter ℂ p) with hn_def
  have hn_units : Fintype.card (ZMod p)ˣ = n := by
    rw [hn_def, card_dirichletCharacter_complex (p := p), ZMod.card_units]
  have hn_units' : Nat.card (ZMod p)ˣ = n := by
    rw [Nat.card_eq_fintype_card, hn_units]
  have hn_pos : 0 < n := by
    rw [← hn_units]
    exact Fintype.card_pos
  have hp_odd_nat : Odd p := hp.out.odd_of_ne_two hp_odd'
  have hn_even : Even n := by
    rcases hp_odd_nat with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hn_def, card_dirichletCharacter_complex (p := p), hm]
    omega
  rcases hn_even with ⟨n2, hn2⟩
  have hn2' : n = 2 * n2 := by
    omega
  have hn2_pos : 0 < n2 := by
    omega
  have hnp1 : n = p - 1 := by
    rw [hn_def, card_dirichletCharacter_complex (p := p)]
  obtain ⟨g, hg_mon⟩ : ∃ g : (ZMod p)ˣ, ∀ x : (ZMod p)ˣ, x ∈ Submonoid.powers g :=
    IsCyclic.exists_monoid_generator
  have hg_mon' : ∀ x : (ZMod p)ˣ, ∃ m : ℕ, g ^ m = x := fun x => hg_mon x
  obtain ⟨a, ha⟩ := hg_mon' (unitOfPrimeNe (p := p) ℓ hℓp)
  have hg_zpow : ∀ x : (ZMod p)ˣ, x ∈ Subgroup.zpowers g := fun x => by
    obtain ⟨m, hm⟩ := hg_mon' x
    refine ⟨(m : ℤ), ?_⟩
    change g ^ (m : ℤ) = x
    rw [zpow_natCast]
    exact hm
  have hg_order : orderOf g = n := by
    rw [← hn_units']
    exact orderOf_eq_card_of_forall_mem_zpowers hg_zpow
  have hgcd2 : n.gcd 2 = 2 :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right n 2) (Nat.dvd_gcd ⟨n2, hn2'⟩ dvd_rfl)
  have hω : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn_pos.ne'
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hω_unit : IsUnit ω := hω.isUnit hn_pos.ne'
  set ωu : ℂˣ := hω_unit.unit with hωu_def
  have hωu_val : (ωu : ℂ) = ω := by simp [hωu_def]
  have hωu_roots : ∀ k : ℕ, (ωu ^ k : ℂˣ) ∈ rootsOfUnity n ℂ := by
    intro k
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm]
    have h1 : (ωu ^ n : ℂˣ) = 1 := by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_one, hωu_val]
      exact hω.pow_eq_one
    rw [pow_mul, h1, one_pow]
  let χAt : ℕ → DirichletCharacter ℂ p := fun k =>
    MulChar.ofRootOfUnity (M := ZMod p) (R := ℂ) (ζ := ωu ^ k)
      (by rw [hn_units]; exact hωu_roots k) hg_zpow
  have hχAt_g : ∀ k : ℕ, χAt k ((g : (ZMod p)ˣ) : ZMod p) = ω ^ k := fun k => by
    simp only [χAt]
    rw [MulChar.ofRootOfUnity_spec]
    simp [Units.val_pow_eq_pow_val, hωu_val]
  have hℓ_eq : (ℓ : ZMod p) = (((g : (ZMod p)ˣ) : ZMod p)) ^ a := by
    have h1 : (((unitOfPrimeNe (p := p) ℓ hℓp : (ZMod p)ˣ) : ZMod p)) = (ℓ : ZMod p) := by
      simp [unitOfPrimeNe]
    rw [← h1, ← ha, Units.val_pow_eq_pow_val]
  have hχAt_ℓ : ∀ k : ℕ, χAt k (ℓ : ZMod p) = ω ^ (k * a) := fun k => by
    rw [hℓ_eq, map_pow, hχAt_g, ← pow_mul]
  have hg_half_sq : ((((g : (ZMod p)ˣ) : ZMod p) ^ n2) ^ 2) = 1 := by
    rw [← pow_mul]
    have : n2 * 2 = n := by
      omega
    rw [this]
    simpa [Units.val_pow_eq_pow_val, hg_order] using
      congrArg (fun x : (ZMod p)ˣ => ((x : ZMod p))) (pow_orderOf_eq_one g)
  have hg_half_ne_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) ≠ 1 := by
    intro hpow
    have hpow_units : g ^ n2 = 1 := by
      apply Units.ext
      simpa using hpow
    have hdvd : n ∣ n2 := by
      rw [← hg_order]
      exact (orderOf_dvd_iff_pow_eq_one (x := g)).2 hpow_units
    have hle : n ≤ n2 := Nat.le_of_dvd hn2_pos hdvd
    rw [hn2] at hle
    omega
  have hg_half_eq_neg_one : (((g : (ZMod p)ˣ) : ZMod p) ^ n2) = -1 := by
    rcases sq_eq_one_iff.mp hg_half_sq with h1 | h1
    · exact False.elim (hg_half_ne_one h1)
    · exact h1
  let χEvenAt : ℕ → DirichletCharacter ℂ p := fun k => χAt (2 * k)
  have hχEven_mem : ∀ k ∈ Finset.range n2, χEvenAt k ∈ E := by
    intro k hk
    have h_even : χAt (2 * k) (-1 : ZMod p) = 1 := by
      rw [← hg_half_eq_neg_one, map_pow, hχAt_g, ← pow_mul]
      have : (2 * k) * n2 = k * n := by
        rw [hn2']
        simp [Nat.mul_left_comm, Nat.mul_comm]
      rw [this, mul_comm, pow_mul, hω.pow_eq_one, one_pow]
    change χAt (2 * k) ∈ E
    rw [show E = Finset.univ.filter (fun χ : DirichletCharacter ℂ p => χ.Even) from rfl,
      Finset.mem_filter]
    simp [DirichletCharacter.Even, h_even]
  have hχEven_inj : Set.InjOn χEvenAt ↑(Finset.range n2) := by
    intro j hj k hk hjk
    simp only [Finset.coe_range, Set.mem_Iio] at hj hk
    have hval : χEvenAt j ((g : (ZMod p)ˣ) : ZMod p) = χEvenAt k ((g : (ZMod p)ˣ) : ZMod p) :=
      congrArg (fun χ : DirichletCharacter ℂ p => χ ((g : (ZMod p)ˣ) : ZMod p)) hjk
    rw [hχAt_g, hχAt_g] at hval
    have hj2 : 2 * j < n := by
      omega
    have hk2 : 2 * k < n := by
      omega
    have h_eq : 2 * j = 2 * k := by
      simpa [χEvenAt] using hω.pow_inj hj2 hk2 hval
    omega
  have hE_card : E.card = n2 := by
    rw [card_even_characters_kplus (p := p) hp_odd']
    omega
  have himage_eq : Finset.image χEvenAt (Finset.range n2) = E := by
    apply Finset.eq_of_subset_of_card_le
    · intro χ hχ
      rcases Finset.mem_image.mp hχ with ⟨k, hk, rfl⟩
      exact hχEven_mem k hk
    · rw [hE_card, Finset.card_image_of_injOn hχEven_inj, Finset.card_range]
  have hprod_transfer :
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T) =
        ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
    calc
      ∏ χ ∈ E, (1 - χ (ℓ : ZMod p) * T)
          = ∏ χ ∈ Finset.image χEvenAt (Finset.range n2), (1 - χ (ℓ : ZMod p) * T) := by
              rw [← himage_eq]
      _ = ∏ k ∈ Finset.range n2, (1 - χEvenAt k (ℓ : ZMod p) * T) := by
            rw [Finset.prod_image hχEven_inj]
      _ = ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) := by
            refine Finset.prod_congr rfl (fun k _ => ?_)
            simpa [χEvenAt] using congrArg (fun z : ℂ => 1 - z * T) (hχAt_ℓ (2 * k))
  have hω_sq_prim' : IsPrimitiveRoot (ω ^ 2) (n / n.gcd 2) :=
    IsPrimitiveRoot.pow_isPrimitiveRoot_div_gcd hn_pos 2 hω
  have hω_sq_prim : IsPrimitiveRoot (ω ^ 2) n2 := by
    simpa [hgcd2, hn2'] using hω_sq_prim'
  have hcollapse :
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T) =
        (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a := by
    calc
      ∏ k ∈ Finset.range n2, (1 - ω ^ ((2 * k) * a) * T)
          = ∏ k ∈ Finset.range n2, (1 - (ω ^ 2) ^ (k * a) * T) := by
              refine Finset.prod_congr rfl (fun k _ => ?_)
              congr 1
              have hexp : (2 * k) * a = 2 * (k * a) := by
                simp [Nat.mul_assoc, Nat.mul_comm]
              rw [hexp, pow_mul]
      _ = (1 - T ^ (n2 / n2.gcd a)) ^ n2.gcd a :=
            prod_pow_primRoot_eq_pow hn2_pos a hω_sq_prim T
  have hg_sq_order : orderOf (g ^ 2) = n2 := by
    rw [orderOf_pow, hg_order, hgcd2, hn2']
    simp
  have hu_sq : (unitOfPrimeNe (p := p) ℓ hℓp) ^ 2 = (g ^ 2) ^ a := by
    rw [← ha, ← pow_mul]
    have : a * 2 = 2 * a := by
      omega
    rw [this, pow_mul]
  have horder_u_sq : orderOf ((unitOfPrimeNe (p := p) ℓ hℓp) ^ 2) = n2 / n2.gcd a := by
    rw [hu_sq, orderOf_pow, hg_sq_order]
  have hlocalResidue :
      localResidueDegreePlus (p := p) ℓ hℓp = n2 / n2.gcd a := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp, horder_u_sq]
  have hlocalResiduePlus_pos : 0 < localResidueDegreePlus (p := p) ℓ hℓp := by
    rw [← orderOf_unitOfPrimeNe_sq_eq_localResidueDegreePlus (p := p) hℓp]
    exact orderOf_pos _
  have hlocalResidue_pos : 0 < n2 / n2.gcd a := by
    simpa [hlocalResidue] using hlocalResiduePlus_pos
  have hcount_mul : localPrimeCountPlus (p := p) ℓ hℓp * (n2 / n2.gcd a) = n2 := by
    have hbase := localPrimeCountPlus_mul_localResidueDegreePlus (p := p) hp_odd' hℓp
    rw [hlocalResidue] at hbase
    simpa [E, hE_card] using hbase
  have hgcd_mul : n2.gcd a * (n2 / n2.gcd a) = n2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left n2 a)
  have hlocalPrimeCount :
      localPrimeCountPlus (p := p) ℓ hℓp = n2.gcd a := by
    have hmul :
        (n2 / n2.gcd a) * localPrimeCountPlus (p := p) ℓ hℓp =
          (n2 / n2.gcd a) * (n2.gcd a) := by
      rw [Nat.mul_comm (n2 / n2.gcd a) (localPrimeCountPlus (p := p) ℓ hℓp),
        Nat.mul_comm (n2 / n2.gcd a) (n2.gcd a), hcount_mul, hgcd_mul]
    exact Nat.eq_of_mul_eq_mul_left hlocalResidue_pos hmul
  simpa [E] using
    (Eq.trans hprod_transfer (Eq.trans hcollapse (by rw [← hlocalResidue, ← hlocalPrimeCount])))

/--
@isnad1 id=eq.2h3v.s7.d8c5b9c44996 from=translated src=- shape=785ea3de vocab=bfdab139
-/
lemma trivial_mul_evenCharLocalFactor_eq_pow_localResidueDegreePlus
    (hp_odd' : p ≠ 2) {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ℓ ≠ p) {s : ℂ} :
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
      (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
        localPrimeCountPlus (p := p) ℓ hℓp := by
  classical
  have htriv_even : (1 : DirichletCharacter ℂ p).Even := by
    change (1 : DirichletCharacter ℂ p) (-1 : ZMod p) = 1
    rw [MulChar.one_apply (show IsUnit (-1 : ZMod p) from isUnit_one.neg)]
  have hrewrite :
      evenNontrivialCharacters (p := p) =
        (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even).erase 1 := by
    ext χ
    simp [evenNontrivialCharacters, and_comm]
  have htrivial_mul :
      (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s =
        Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
          (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := by
    unfold evenCharLocalFactor
    rw [hrewrite, ← Finset.mul_prod_erase
      (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
      (fun χ : DirichletCharacter ℂ p => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s)))]
    · have hℓ_unit : IsUnit ((ℓ : ZMod p)) := by
        rw [ZMod.isUnit_iff_coprime]
        exact (coprime_of_prime_ne (p := p) hℓp).symm
      rw [MulChar.one_apply hℓ_unit, one_mul]
    · simp [htriv_even]
  calc
    (1 - (ℓ : ℂ) ^ (-s)) * evenCharLocalFactor p ℓ s
        = Finset.prod (Finset.univ.filter fun χ : DirichletCharacter ℂ p => χ.Even)
            (fun χ => (1 - χ (ℓ : ZMod p) * (ℓ : ℂ) ^ (-s))) := htrivial_mul
    _ =
        (1 - (((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp)) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            simpa using
              prod_even_characters_eval_eq_pow_localResidueDegreePlus (p := p) hp_odd' hℓp
                ((ℓ : ℂ) ^ (-s))
    _ =
        (1 - (ℓ : ℂ) ^ (-((localResidueDegreePlus (p := p) ℓ hℓp : ℂ) * s))) ^
          localPrimeCountPlus (p := p) ℓ hℓp := by
            congr 1
            congr 1
            rw [show ((ℓ : ℂ) ^ (-s)) ^ localResidueDegreePlus (p := p) ℓ hℓp =
                (ℓ : ℂ) ^ ((-s) * ((localResidueDegreePlus (p := p) ℓ hℓp : ℕ) : ℂ)) by
                  rw [Complex.cpow_mul_nat]]
            congr 1
            ring
end KummerCriterion
