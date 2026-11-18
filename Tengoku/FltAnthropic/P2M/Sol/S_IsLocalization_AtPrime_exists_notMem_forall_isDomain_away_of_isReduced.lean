import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalization_AtPrime_exists_notMem_forall_isDomain_away_of_isReduced

set_option autoImplicit false

universe u v

namespace P2mWs2AffEtale

/--
@isnad1 id=ex.0h3v.s7.c933047a8053 from=translated src=- shape=b9ad9c66 vocab=055e1918
-/
theorem exists_notMem_isDomain_away
    {R Rp : Type*} [CommRing R] [CommRing Rp] [Algebra R Rp] [IsNoetherianRing R] [IsReduced R]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime Rp P] [IsDomain Rp] :
    ∃ f : R, f ∉ P ∧ ∀ (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf],
      IsDomain Rf := by
  classical
  set Q₀ : Ideal R := RingHom.ker (algebraMap R Rp) with hQ₀def
  have hQ₀prime : Q₀.IsPrime := RingHom.ker_isPrime _

  have hle : ∀ q : Ideal R, q.IsPrime → q ≤ P → Q₀ ≤ q := by
    intro q hq hqP r hr
    obtain ⟨⟨s, hs⟩, hsr⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl Rp r).mp hr
    have : s * r ∈ q := by simp [hsr]
    exact (hq.mem_or_mem this).resolve_left (fun h ↦ hs (hqP h))
  have hQ₀P : Q₀ ≤ P := hle P ‹_› le_rfl

  have hpick : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → ∃ g : R, g ∈ q ∧ g ∉ P := by
    intro q hq hne
    by_contra hcon
    push Not at hcon
    have hqP : q ≤ P := fun g hg ↦ hcon g hg
    exact hne (le_antisymm (hq.2 ⟨hQ₀prime, bot_le⟩ (hle q hq.1.1 hqP)) (hle q hq.1.1 hqP))
  choose g hg using hpick
  let g' : Ideal R → R := fun q ↦ if h : q ∈ minimalPrimes R ∧ q ≠ Q₀ then g q h.1 h.2 else 1
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let f : R := ∏ q ∈ hfin.toFinset, g' q
  have hfP : f ∉ P := by
    refine Finset.prod_induction g' (fun a ↦ a ∉ P) (fun a b ha hb hab ↦ ?_) ?_ ?_
    · exact (‹P.IsPrime›.mem_or_mem hab).elim ha hb
    · exact fun h1 ↦ ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
    · intro q hq
      by_cases h : q ∈ minimalPrimes R ∧ q ≠ Q₀
      · simp only [g', dite_eq_left h]; exact (hg q h.1 h.2).2
      · simp only [g', dite_eq_right h]
        exact fun h1 ↦ ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hfq : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → f ∈ q := by
    intro q hq hne
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g' (hfin.mem_toFinset.mpr hq)
    change f = _ at hc
    rw [hc]
    refine q.mul_mem_right c ?_
    simp only [g', dite_eq_left (show q ∈ minimalPrimes R ∧ q ≠ Q₀ from ⟨hq, hne⟩)]
    exact (hg q hq hne).1

  have hfr : ∀ r ∈ Q₀, f * r = 0 := by
    intro r hr
    have hmem : f * r ∈ sInf (minimalPrimes R) := by
      refine Submodule.mem_sInf.mpr fun q hq ↦ ?_
      by_cases hne : q = Q₀
      · subst hne; exact Ideal.mul_mem_left _ f hr
      · exact Ideal.mul_mem_right r q (hfq q hq hne)
    have h0 : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
      rw [minimalPrimes, Ideal.sInf_minimalPrimes]
      simpa [nilradical] using nilradical_eq_zero R
    rw [h0] at hmem
    simpa using hmem
  have hfQ₀ : f ∉ Q₀ := fun h ↦ hfP (hQ₀P h)
  refine ⟨f, hfP, fun Rf _ _ _ ↦ ?_⟩
  have hpowQ : ∀ (m : Submonoid.powers f) (r : R), (m : R) * r ∈ Q₀ → r ∈ Q₀ := by
    rintro ⟨m, ⟨k, rfl⟩⟩ r hmr
    rcases hQ₀prime.mem_or_mem hmr with h | h
    · exact absurd (hQ₀prime.mem_of_pow_mem k h) hfQ₀
    · exact h
  haveI : Nontrivial Rf := by
    refine ⟨⟨1, 0, fun h10 ↦ ?_⟩⟩
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Rf (1 : R)).mp
      (by simpa using h10)
    have : (1 : R) ∈ Q₀ := hpowQ m 1 (by simp [hm])
    exact hQ₀prime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  haveI : NoZeroDivisors Rf := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    obtain ⟨ra, sa, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) a
    obtain ⟨rb, sb, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) b
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hab
    obtain ⟨m, hm⟩ := hab
    have hab' : ra * rb ∈ Q₀ := hpowQ m _ (by simp [hm])
    rcases hQ₀prime.mem_or_mem hab' with h | h
    · left
      exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr ra h⟩
    · right
      exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr rb h⟩
  exact NoZeroDivisors.to_isDomain Rf

end P2mWs2AffEtale

open P2mWs2AffEtale in
/--
@isnad1 id=ex.0h3v.s7.f98c09907d3c from=translated src=- shape=ddbceaaf vocab=055e1918
-/
theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (P : Ideal R) [P.IsPrime]
    (Rp : Type v) [CommRing Rp] [Algebra R Rp] [IsLocalization.AtPrime Rp P] [IsDomain Rp] :
    ∃ f : R, f ∉ P ∧
      ∀ (Rf : Type u) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf], IsDomain Rf :=
  exists_notMem_isDomain_away (Rp := Rp) P
