import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow

set_option autoImplicit false

open MvPolynomial

namespace FrobRankC2

/--
@isnad1 id=and.2h5v.s8.117d43d07a76 from=translated src=- shape=67ae4475 vocab=46ca7e37
-/
theorem finite_flat_finrank_of_unique_decomposition
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} [Fintype ι] (b : ι → S)
    (hex : ∀ s : S, ∃ c : ι → R, ∑ i, f (c i) * b i = s)
    (huniq : ∀ c : ι → R, ∑ i, f (c i) * b i = 0 → ∀ i, c i = 0) :
    f.Finite ∧ f.Flat ∧ ∀ q, f.finrank q = Fintype.card ι := by
  letI : Algebra R S := f.toAlgebra
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := fun r s => Algebra.smul_def r s
  have hli : LinearIndependent R b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply huniq
    simpa [hsmul] using hg
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := by
    rintro s -
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨c, hc⟩ := hex s
    exact ⟨c, by simpa [hsmul] using hc⟩
  let B : Module.Basis ι R S := Module.Basis.mk hli hsp
  haveI : Module.Free R S := Module.Free.of_basis B
  haveI : Module.Finite R S := Module.Finite.of_basis B
  refine ⟨‹Module.Finite R S›, (inferInstance : Module.Flat R S), fun q => ?_⟩
  haveI : Nontrivial R := q.nontrivial
  change Module.rankAtStalk S q = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Module.finrank_eq_card_basis B,
    Nat.cast_id]

section

variable {σ : Type*} (p : ℕ)

noncomputable def divP (e : σ →₀ ℕ) : σ →₀ ℕ := e.mapRange (· / p) (by simp)

/--
@isnad1 id=eq.0h4v.s6.ade3ceaad1de from=translated src=- shape=b7838fcf vocab=7925cd55
-/
@[scoped simp] lemma divP_apply (e : σ →₀ ℕ) (i : σ) : divP p e i = e i / p := by
  simp [divP]

variable [Finite σ]

noncomputable def ofRes (r : σ → Fin p) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i : ℕ))

/--
@isnad1 id=eq.0h4v.s5.74e09f7ebd13 from=translated src=- shape=5d761f8c vocab=94e569f9
-/
@[scoped simp] lemma ofRes_apply (r : σ → Fin p) (i : σ) : ofRes p r i = (r i : ℕ) := by
  simp [ofRes]

variable {p} (hp : 0 < p)
include hp

def modP (e : σ →₀ ℕ) : σ → Fin p := fun i => ⟨e i % p, Nat.mod_lt _ hp⟩

omit [Finite σ] in
/--
@isnad1 id=eq.1h4v.s5.d3caf38eec1c from=translated src=- shape=dccf6e62 vocab=aeedadef
-/
@[scoped simp] lemma modP_apply (e : σ →₀ ℕ) (i : σ) : (modP hp e i : ℕ) = e i % p := rfl

/--
@isnad1 id=eq.1h3v.s6.2922d0c65356 from=translated src=- shape=8d33be10 vocab=bd02092e
-/
lemma decomp (e : σ →₀ ℕ) : p • divP p e + ofRes p (modP hp e) = e := by
  ext i
  simp [Nat.div_add_mod]

/--
@isnad1 id=eq.1h4v.s6.186cb3fbe093 from=translated src=- shape=d851f08f vocab=af370161
-/
lemma divP_add (d : σ →₀ ℕ) (r : σ → Fin p) : divP p (p • d + ofRes p r) = d := by
  ext i
  simp only [divP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (r i).isLt, Nat.zero_add]

/--
@isnad1 id=eq.1h4v.s6.62ab4d5232fa from=translated src=- shape=243c4e21 vocab=e2f02729
-/
lemma modP_add (d : σ →₀ ℕ) (r : σ → Fin p) : modP hp (p • d + ofRes p r) = r := by
  funext i
  apply Fin.ext
  simp only [modP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]

/--
@isnad1 id=iff.1h4v.s6.9b1098028126 from=translated src=- shape=e6c16016 vocab=fbacc0c8
-/
lemma le_and_dvd_iff (e : σ →₀ ℕ) (r : σ → Fin p) :
    (ofRes p r ≤ e ∧ ∀ i, p ∣ (e - ofRes p r) i) ↔ modP hp e = r := by
  constructor
  · rintro ⟨hle, hdvd⟩
    funext i
    apply Fin.ext
    simp only [modP_apply]
    have h1 : (r i : ℕ) ≤ e i := by simpa using hle i
    have h2 : p ∣ e i - r i := by simpa using hdvd i
    obtain ⟨k, hk⟩ := h2
    have : e i = r i + p * k := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]
  · rintro rfl
    refine ⟨fun i => ?_, fun i => ?_⟩
    · simpa using Nat.mod_le (e i) p
    · refine ⟨e i / p, ?_⟩
      simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply]
      have := Nat.div_add_mod (e i) p
      omega

/--
@isnad1 id=eq.1h3v.s6.cf35344334c8 from=translated src=- shape=dd19d5ab vocab=14ddcfde
-/
lemma sub_ofRes_modP (e : σ →₀ ℕ) : e - ofRes p (modP hp e) = p • divP p e := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply, Finsupp.coe_smul,
    Pi.smul_apply, divP_apply, smul_eq_mul]
  have := Nat.div_add_mod (e i) p
  omega

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ] {p : ℕ} (hp : 0 < p)
include hp

noncomputable def bvec (r : σ → Fin p) : MvPolynomial σ R := monomial (ofRes p r) 1

omit hp in
/--
@isnad1 id=eq.0h4v.s7.57dd8b906596 from=translated src=- shape=bfe3644e vocab=a3dfd076
-/
lemma bvec_def (r : σ → Fin p) : (bvec r : MvPolynomial σ R) = monomial (ofRes p r) 1 := rfl

/--
@isnad1 id=eq.1h6v.s8.730d5d77b8a6 from=translated src=- shape=2c2414f0 vocab=4b0ff829
-/
lemma coeff_expand_mul_bvec [DecidableEq (σ → Fin p)]
    (c : MvPolynomial σ R) (r : σ → Fin p) (e : σ →₀ ℕ) :
    coeff e (expand p c * bvec r) = if modP hp e = r then coeff (divP p e) c else 0 := by
  classical
  rw [bvec_def, coeff_mul_monomial', mul_one]
  by_cases hr : modP hp e = r
  · rw [ite_eq_left hr]
    have hle : ofRes p r ≤ e := ((le_and_dvd_iff hp e r).mpr hr).1
    rw [ite_eq_left hle]
    subst hr
    rw [sub_ofRes_modP hp e, coeff_expand_smul _ hp.ne']
  · rw [ite_eq_right hr]
    split_ifs with hle
    · have : ¬ ∀ i, p ∣ (e - ofRes p r) i := fun h => hr ((le_and_dvd_iff hp e r).mp ⟨hle, h⟩)
      push Not at this
      obtain ⟨i, hi⟩ := this
      exact coeff_expand_of_not_dvd _ hi
    · rfl

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ] {p : ℕ} (hp : 0 < p)
include hp

noncomputable def Ψ (c : (σ → Fin p) → MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ r, expand p (c r) * bvec r

omit hp in
/--
@isnad1 id=eq.0h4v.s8.8841aa35d2bc from=translated src=- shape=519924a1 vocab=ca36f9eb
-/
lemma Ψ_def (c : (σ → Fin p) → MvPolynomial σ R) :
    Ψ c = ∑ r, expand p (c r) * bvec r := rfl

/--
@isnad1 id=eq.1h5v.s6.704354b2f312 from=translated src=- shape=4ea09958 vocab=4e5d00ff
-/
lemma coeff_Ψ (c : (σ → Fin p) → MvPolynomial σ R) (e : σ →₀ ℕ) :
    coeff e (Ψ c) = coeff (divP p e) (c (modP hp e)) := by
  classical
  rw [Ψ_def, coeff_sum]
  simp_rw [coeff_expand_mul_bvec hp]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

/--
@isnad1 id=eq.2h5v.s7.911693533af6 from=translated src=- shape=c54c9601 vocab=e4a2331d
-/
lemma Ψ_eq_zero (c : (σ → Fin p) → MvPolynomial σ R) (h : Ψ c = 0) : ∀ r, c r = 0 := by
  intro r
  ext d
  have := coeff_Ψ hp c (p • d + ofRes p r)
  rw [h, coeff_zero, divP_add hp, modP_add hp] at this
  simpa using this.symm

/--
@isnad1 id=ex.1h4v.s6.87e219ff6bb6 from=translated src=- shape=9d792ace vocab=6eeecb7b
-/
lemma Ψ_surjective (s : MvPolynomial σ R) : ∃ c : (σ → Fin p) → MvPolynomial σ R, Ψ c = s := by
  classical
  refine ⟨fun r => ∑ e ∈ s.support,
    if modP hp e = r then monomial (divP p e) (coeff e s) else 0, ?_⟩
  ext e
  rw [coeff_Ψ hp]
  rw [coeff_sum]
  simp_rw [apply_ite (coeff (R := R) (divP p e)), coeff_monomial, coeff_zero]

  have key : ∀ e' : σ →₀ ℕ,
      (if modP hp e' = modP hp e then (if divP p e' = divP p e then coeff e' s else 0) else 0) =
        if e' = e then coeff e' s else 0 := by
    intro e'
    by_cases h : e' = e
    · subst h
      simp
    · rw [ite_eq_right h]
      by_cases h1 : modP hp e' = modP hp e
      · rw [ite_eq_left h1, ite_eq_right]
        intro h2
        apply h
        rw [← decomp hp e', ← decomp hp e, h1, h2]
      · rw [ite_eq_right h1]
  simp_rw [key]
  rw [Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · exact (notMem_support_iff.mp hmem).symm

end

/--
@isnad1 id=and.1h3v.s9.5d5384b08572 from=translated src=- shape=517d1bad vocab=6770fafe
-/
theorem main (R : Type*) [CommRing R] (σ : Type*) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q, (expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  have h := finite_flat_finrank_of_unique_decomposition
    (expand p (σ := σ) (R := R)).toRingHom (ι := σ → Fin p) (bvec (R := R))
    (fun s => by
      obtain ⟨c, hc⟩ := Ψ_surjective hp s
      exact ⟨c, hc⟩)
    (fun c hc => Ψ_eq_zero hp c hc)
  refine ⟨h.1, h.2.1, fun q => ?_⟩
  rw [h.2.2 q, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]

end FrobRankC2
open scoped _root_.P2MW.S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.FrobRankC2

universe u v

/--
@isnad1 id=and.1h3v.s9.f90401eef8fc from=translated src=- shape=517d1bad vocab=6770fafe
-/
theorem solution
    (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Finite ∧
    (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.Flat ∧
    ∀ q : PrimeSpectrum (MvPolynomial σ R),
      (MvPolynomial.expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ :=
  FrobRankC2.main R σ p hp
