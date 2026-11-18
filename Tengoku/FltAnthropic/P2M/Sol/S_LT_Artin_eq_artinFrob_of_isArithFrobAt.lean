import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ArtinFrobenius
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LT_Artin_eq_artinFrob_of_isArithFrobAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LT_Artin_eq_artinFrob_of_isArithFrobAt

set_option autoImplicit false

noncomputable section

namespace M4aP2R
namespace ArtinRows

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin
open scoped Pointwise

section Transport

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {G : Type*} [Group G] [MulSemiringAction G S] [SMulCommClass G R S]

/--
@isnad1 id=eq.1h4v.s8.a863f231131e from=translated src=- shape=61204daa vocab=9c03c8ed
-/
theorem inertia_smul_eq_bot (τ : G) (Q : Ideal S) (hI : Q.inertia G = ⊥) : (τ • Q).inertia G = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hg' : ∀ x : S, g • x - x ∈ τ • Q := fun x => hg x
  have hmem : τ⁻¹ * g * τ ∈ Q.inertia G := by
    intro x
    have hx := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 (hg' (τ • x))
    rw [smul_sub, inv_smul_smul, ← mul_smul, ← mul_smul] at hx
    exact hx
  rw [hI, Subgroup.mem_bot] at hmem
  have hgg : g = τ * (τ⁻¹ * g * τ) * τ⁻¹ := by group
  rw [hmem] at hgg
  simpa using hgg

theorem eq_of_isArithFrobAt_of_inertia_eq_bot {σ σ' : G} {Q : Ideal S} (H : IsArithFrobAt R σ Q) (H' : IsArithFrobAt R σ' Q)
    (hI : Q.inertia G = ⊥) : σ = σ' := by
  have h := H.mul_inv_mem_inertia H'
  rw [hI, Subgroup.mem_bot] at h
  exact mul_inv_eq_one.1 h

variable [Finite G] [Algebra.IsInvariant R S G]

/--
@isnad1 id=eq.1h5v.s9.7a43b560f077 from=translated src=- shape=012271a2 vocab=85590afa
-/
theorem arithFrobAt_smul (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] [Finite (S ⧸ τ • Q)] (hI : Q.inertia G = ⊥) :
    arithFrobAt R G (τ • Q) = τ * arithFrobAt R G Q * τ⁻¹ := by
  have h1 : IsArithFrobAt R (arithFrobAt R G (τ • Q)) (τ • Q) := IsArithFrobAt.arithFrobAt R G (τ • Q)
  have h2 : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := (IsArithFrobAt.arithFrobAt R G Q).conj τ
  have h3 := h1.mul_inv_mem_inertia h2
  rw [inertia_smul_eq_bot τ Q hI, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.1 h3

end Transport
section Rows
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
variable (v : HeightOneSpectrum (𝓞 K))

/--
@isnad1 id=eq.2h4v.s9.eaa8c83a8fc2 from=translated src=- shape=4288115b vocab=d1f63e18
-/
theorem rowA [IsMulCommutative (M ≃ₐ[K] M)] (Q : Ideal (𝓞 M)) [Q.IsPrime] [Finite (𝓞 M ⧸ Q)]
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q = artinFrob K M v := by
  haveI : Q.LiesOver v.asIdeal := ⟨hQ.symm⟩
  haveI := v.isMaximal
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K M v) Q (M ≃ₐ[K] M)
  subst hτ
  have hI₀ : (primeAbove K M v).inertia (M ≃ₐ[K] M) = ⊥ := by
    have h := inertia_smul_eq_bot τ⁻¹ (τ • primeAbove K M v) hI
    rwa [inv_smul_smul] at h
  rw [arithFrobAt_smul τ (primeAbove K M v) hI₀, IsMulCommutative.is_comm.comm τ, mul_inv_cancel_right]
  rfl

end Rows

/--
@isnad1 id=eq.3h5v.s10.07ca4145cc81 from=translated src=- shape=57be97ed vocab=45f71d3c
-/
theorem rowB (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)) [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M}
    {Q : Ideal (𝓞 M)} [Q.IsPrime] (H : IsArithFrobAt (𝓞 K) σ Q)
    (hQ : Q.under (𝓞 K) = v.asIdeal) (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = artinFrob K M v := by
  haveI := finite_quotient_of_under_eq K M v hQ
  rw [← rowA K M v Q hQ hI]
  exact eq_of_isArithFrobAt_of_inertia_eq_bot H (IsArithFrobAt.arithFrobAt (𝓞 K) (M ≃ₐ[K] M) Q) hI

end M4aP2R.ArtinRows

theorem M4aP2R.ArtinRows.eq_artinFrob_of_isArithFrobAt_impl

    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v :=
  M4aP2R.ArtinRows.rowB K M v H hQ hI

set_option autoImplicit false

/--
@isnad1 id=eq.3h5v.s10.07ca4145cc81 from=translated src=- shape=57be97ed vocab=45f71d3c
-/
theorem solution
    (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    [IsMulCommutative (M ≃ₐ[K] M)] {σ : M ≃ₐ[K] M} {Q : Ideal (NumberField.RingOfIntegers M)}
    [Q.IsPrime] (H : IsArithFrobAt (NumberField.RingOfIntegers K) σ Q)
    (hQ : Q.under (NumberField.RingOfIntegers K) = v.asIdeal)
    (hI : Q.inertia (M ≃ₐ[K] M) = ⊥) :
    σ = LanglandsTunnell.P2.Artin.artinFrob K M v := by
  exact M4aP2R.ArtinRows.eq_artinFrob_of_isArithFrobAt_impl K M v H hQ hI
