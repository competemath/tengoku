import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsRegularLocalRing_of_etale_of_moduleFinite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsRegularLocalRing_of_etale_of_moduleFinite

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

open IsLocalRing Polynomial

open scoped TensorProduct

universe u v

namespace KFRDDim

open Order

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]

noncomputable def contract (q : PrimeSpectrum B) : PrimeSpectrum A :=
  ⟨q.asIdeal.comap (algebraMap A B), inferInstance⟩

/--
@isnad1 id=strictmo.0h2v.s6.5989212e0598 from=translated src=- shape=9fb30920 vocab=539b20fe
-/
theorem contract_strictMono : StrictMono (contract (A := A) (B := B)) := by
  intro p q hpq
  have hlt : p.asIdeal < q.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal p q).mpr hpq
  haveI := p.isPrime
  have := Ideal.IsIntegral.comap_lt_comap (R := A) hlt
  exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mp this

/--
@isnad1 id=le.0h2v.s5.87bbd3c6d390 from=translated src=- shape=35d53890 vocab=97bd58c3
-/
theorem le_dim : ringKrullDim B ≤ ringKrullDim A :=
  krullDim_le_of_strictMono _ contract_strictMono

/--
@isnad1 id=ex.2h4v.s9.7be3d9bec2b5 from=translated src=- shape=6ab2d965 vocab=e25f3053
-/
theorem exists_lift (hinj : Function.Injective (algebraMap A B)) :
    ∀ (n : ℕ) (p : LTSeries (PrimeSpectrum A)), p.length = n →
      ∃ q : LTSeries (PrimeSpectrum B), q.length = n ∧
        q.last.asIdeal.comap (algebraMap A B) = p.last.asIdeal := by
  intro n
  induction n with
  | zero =>
    intro p hp
    haveI := p.last.isPrime
    have hbot : (⊥ : Ideal B).comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal ⊥ hbot
    exact ⟨RelSeries.singleton _ ⟨Q, hQp⟩, rfl, by simpa using hQ⟩
  | succ n ih =>
    intro p hp
    have hpos : p.length ≠ 0 := by omega
    obtain ⟨q', hq'len, hq'⟩ := ih p.eraseLast (by simp [hp])
    have hrel : p.eraseLast.last < p.last := RelSeries.eraseLast_last_rel_last p hpos
    have hrelI : p.eraseLast.last.asIdeal < p.last.asIdeal := (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hrel
    haveI := p.last.isPrime
    haveI := q'.last.isPrime
    have hle : q'.last.asIdeal.comap (algebraMap A B) ≤ p.last.asIdeal := by
      rw [hq']; exact hrelI.le
    obtain ⟨Q, hQge, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.last.asIdeal q'.last.asIdeal hle
    have hlt : q'.last < ⟨Q, hQp⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hQge ?_
      intro heq
      apply hrelI.ne
      rw [← hq', ← hQ]
      exact congrArg _ heq
    refine ⟨q'.snoc ⟨Q, hQp⟩ hlt, by simp [hq'len], ?_⟩
    simpa using hQ

/--
@isnad1 id=le.1h2v.s6.b44ee6c1ba20 from=translated src=- shape=e3a90ee3 vocab=1a19cc10
-/
theorem dim_le (hinj : Function.Injective (algebraMap A B)) : ringKrullDim A ≤ ringKrullDim B := by
  unfold ringKrullDim krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hq, -⟩ := exists_lift hinj p.length p rfl
  exact le_iSup_of_le q (by rw [hq])

end KFRDDim

namespace KFRD

variable {R : Type*} [CommRing R] {X : Type*} [AddCommGroup X] [Module R X]

/--
@isnad1 id=eq.1h4v.s9.18ff8cb0520b from=translated src=- shape=9f7b98a0 vocab=b9001cec
-/
theorem length_quot_eq_add (S E : Submodule R X) (h : S ≤ E) :
    Module.length R (X ⧸ S) = Module.length R (↥E ⧸ S.comap E.subtype) + Module.length R (X ⧸ E) := by
  let φ : ↥E →ₗ[R] X ⧸ S := S.mkQ.comp E.subtype
  have hker : LinearMap.ker φ = S.comap E.subtype := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hrange : LinearMap.range φ = E.map S.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have e1 : (↥E ⧸ S.comap E.subtype) ≃ₗ[R] ↥(E.map S.mkQ) :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivRange.trans (LinearEquiv.ofEq _ _ hrange))
  have e2 : ((X ⧸ S) ⧸ E.map S.mkQ) ≃ₗ[R] X ⧸ E := Submodule.quotientQuotientEquivQuotient S E h
  rw [Module.length_eq_add_of_exact (E.map S.mkQ).subtype (E.map S.mkQ).mkQ (Submodule.subtype_injective _)
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _), e1.length_eq, e2.length_eq]

/--
@isnad1 id=eq.0h1v.s8.22b4c55b1c4f from=translated src=- shape=a54e6dce vocab=3f855240
-/
theorem length_quotient_maximalIdeal_sq (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.length R (R ⧸ maximalIdeal R ^ 2) = 1 + ((maximalIdeal R).spanFinrank : ℕ∞) := by
  rw [length_quot_eq_add (X := R) (maximalIdeal R ^ 2) (maximalIdeal R) (Ideal.pow_le_self two_ne_zero), add_comm]
  congr 1
  · haveI : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
    exact Module.length_eq_one R _
  ·
    have hker : Submodule.comap (maximalIdeal R).subtype (maximalIdeal R ^ 2) =
        ((maximalIdeal R) • ⊤ : Submodule R ↥(maximalIdeal R)) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, ← Ideal.toCotangent_eq_zero]
      exact Submodule.Quotient.mk_eq_zero _
    let e : (↥(maximalIdeal R) ⧸ Submodule.comap (maximalIdeal R).subtype (maximalIdeal R ^ 2)) ≃ₗ[R] CotangentSpace R :=
      Submodule.quotEquivOfEq _ _ hker
    rw [e.length_eq, Module.length_eq_of_surjective (S := R) (R := ResidueField R) (M := CotangentSpace R)
      IsLocalRing.residue_surjective, Module.length_eq_finrank, ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]

/--
@isnad1 id=and.0h2v.s7.35b64be5780c from=translated src=- shape=689d4311 vocab=46b7ad9f
-/
theorem core (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (B' : Type v) [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] [Algebra B B'] [Module.Finite B B'] [FaithfulSMul B B']
    [Algebra.Etale B B'] :
    (maximalIdeal B).spanFinrank = (maximalIdeal B').spanFinrank ∧ ringKrullDim B = ringKrullDim B' := by
  classical
  haveI : Algebra.IsIntegral B B' := inferInstance
  haveI hloc : IsLocalHom (algebraMap B B') := by
    constructor
    intro x hx
    by_contra hnu
    have hxm : x ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hcomax : ((maximalIdeal B').comap (algebraMap B B')).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B')
    have heq : (maximalIdeal B').comap (algebraMap B B') = maximalIdeal B := IsLocalRing.eq_maximalIdeal hcomax
    have : algebraMap B B' x ∈ maximalIdeal B' := by rw [← Ideal.mem_comap, heq]; exact hxm
    exact (IsLocalRing.mem_maximalIdeal _).mp this hx
  have hm : (maximalIdeal B).map (algebraMap B B') = maximalIdeal B' := Algebra.FormallyUnramified.map_maximalIdeal
  constructor
  ·
    have h1 := IsLocalRing.length_baseChange B B' (B ⧸ maximalIdeal B ^ 2)
    have h2 : Module.length B' (B' ⧸ (maximalIdeal B).map (algebraMap B B')) = 1 := by
      rw [hm]
      haveI : IsSimpleModule B' (B' ⧸ maximalIdeal B') :=
        isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal B'))
      exact Module.length_eq_one B' _
    have e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A := B) B' (maximalIdeal B ^ 2)).toLinearEquiv
    rw [h2, mul_one, ← e.length_eq, Ideal.map_pow, hm, length_quotient_maximalIdeal_sq, length_quotient_maximalIdeal_sq] at h1
    have h4 : ((maximalIdeal B').spanFinrank : ℕ∞) = (maximalIdeal B).spanFinrank :=
      ENat.add_right_injective_of_ne_top ENat.one_ne_top h1
    exact_mod_cast h4.symm
  · exact le_antisymm (KFRDDim.dim_le (FaithfulSMul.algebraMap_injective B B')) KFRDDim.le_dim

end KFRD

/--
@isnad1 id=isregula.0h2v.s6.ca096e63db7d from=translated src=- shape=5d36f627 vocab=f82743b4
-/
theorem solution
    (B : Type*) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (B' : Type*) [CommRing B'] [IsLocalRing B'] [Algebra B B'] [Module.Finite B B'] [FaithfulSMul B B']
    [Algebra.Etale B B'] [IsRegularLocalRing B'] : IsRegularLocalRing B := by
  haveI : IsNoetherianRing B' := inferInstance
  obtain ⟨hsf, hd⟩ := KFRD.core B B'
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [hsf, hd]
  exact le_of_eq ((isRegularLocalRing_iff B').mp inferInstance)
