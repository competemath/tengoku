module

public import Tengoku.LanaPi1.Pi1.Orbicurve.ValuationInertia
public import Tengoku.Seed.RingTheory.Smooth.Fiber
public import Tengoku.Seed.RingTheory.Flat.TorsionFree
public import Tengoku.Seed.NumberTheory.RamificationInertia.Unramified

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Étaleness of maps of coordinate rings via inertia groups

Let `k` be a field of characteristic `0`, `t ∈ Ω` transcendental over `k` and `Ω / K₀`
(`K₀ = k(t)`) Galois. For intermediate fields `L ⊆ N` of `Ω / K₀`, finite over `K₀`, the
inclusion `coordRing k t L → coordRing k t N` of the coordinate rings of the normalizations of
the `t`-line is finite (`AffOrbicurve.module_finite_of_charZero`), and it is étale if and only
if, for every valuation subring `W` of `Ω` centered on the `t`-line, every element of the
inertia group of `W` fixing `L` fixes `N` (`AffOrbicurve.etale_iff_inertia`):

  `Etale(coordRing k t L → coordRing k t N) ↔ ∀ W, I_W ∩ Aut(Ω / L) ⊆ Aut(Ω / N)`.

Every maximal ideal of a coordinate ring is the center of a valuation subring of `Ω` centered on
the `t`-line (`AffOrbicurve.exists_isCentered_centerIdeal_eq`).
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

section Centers

/-- **Every maximal ideal of a coordinate ring is a center**: for a maximal ideal `Q` of
`coordRing k t M` there is a valuation subring `W` of `Ω` centered on the `t`-line with
`u_W(M) = Q` (extend the local ring at `Q` to a valuation subring of `Ω`).-/
theorem exists_isCentered_centerIdeal_eq (M : IntermediateField (K₀ k t) Ω)
    (Q : Ideal (coordRing k t M)) [hQ : Q.IsMaximal] :
    ∃ (W : ValuationSubring Ω) (hW : IsCentered k t W), centerIdeal hW M = Q := by
  let R := Localization.AtPrime Q
  letI : Algebra (coordRing k t M) R := OreLocalization.instAlgebra
  haveI : IsLocalization.AtPrime R Q := Localization.isLocalization
  have hunit : ∀ s : Q.primeCompl, IsUnit (toΩ t M s) := by
    intro s
    refine IsUnit.mk0 _ fun h0 => s.2 ?_
    rw [← map_zero (toΩ t M)] at h0
    rw [toΩ_injective M h0]
    exact Q.zero_mem
  let f : R →+* Ω := IsLocalization.lift (M := Q.primeCompl) (S := R) hunit
  have hf : ∀ a, f (algebraMap _ R a) = toΩ t M a := IsLocalization.lift_eq hunit
  obtain ⟨W, hmem, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  have hA : ∀ a : coordRing k t M, toΩ t M a ∈ W := fun a => by
    rw [← hf]; exact hmem _
  have hW : IsCentered k t W := by
    refine ⟨fun c => ?_, ?_⟩
    · exact hA (algebraMap k (coordRing k t M) c)
    · exact hA (algebraMap (A₀ k t) (coordRing k t M) ⟨t, Algebra.subset_adjoin rfl⟩)
  refine ⟨W, hW, (hQ.eq_of_le (Ideal.IsPrime.ne_top inferInstance) fun b hb => ?_).symm⟩
  rw [mem_centerIdeal_iff_mem_nonunits]
  intro hu
  have hb' : algebraMap _ R b ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff R Q]
    exact hb
  apply hb'
  apply hloc.map_nonunit
  have he : (f.codRestrict W.toSubring hmem) (algebraMap _ R b) =
      (⟨toΩ t M b, toΩ_mem hW M b⟩ : W) := Subtype.ext (hf b)
  rw [he]
  exact hu

end Centers

section Fix

lemma eq_one_of_forall_coordRing (M : IntermediateField (K₀ k t) Ω)
    [FiniteDimensional (K₀ k t) M] (ρ : M ≃ₐ[K₀ k t] M)
    (h : ∀ b : coordRing k t M, ρ (b : M) = b) : ρ = 1 := by
  haveI := isFractionRing_coordRing t M
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (coordRing k t M) x
  rw [map_div₀]
  exact congrArg₂ (fun y z : M => ((y / z : M) : Ω)) (h a) (h b)

/-- If the center of `W` on `M` is zero (`W` is trivial on `k(t)`), the inertia group of `W`
fixes `M`.-/
lemma fixes_of_centerIdeal_eq_bot {W : ValuationSubring Ω} (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) M] [Normal (K₀ k t) M]
    (hne : centerIdeal hW M = ⊥) {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) :
    ∀ x ∈ M, σ x = x := by
  have hρ := restrictNormal_mem_inertia hW M hσ
  rw [hne] at hρ
  have h1 : σ.restrictNormal M = 1 := eq_one_of_forall_coordRing M _ fun b => by
    have h2 := AddSubgroup.mem_inertia.mp hρ b
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_bot, sub_eq_zero] at h2
    exact congrArg Subtype.val h2
  intro x hx
  have h2 := congrArg (fun ρ : M ≃ₐ[K₀ k t] M => ((ρ ⟨x, hx⟩ : M) : Ω)) h1
  simpa using h2

end Fix

variable [CharZero k]

section Finite

instance charZero_K₀ : CharZero (K₀ k t) :=
  charZero_of_injective_algebraMap (algebraMap k (K₀ k t)).injective

lemma isSeparable_of_charZero (N : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) N] :
    Algebra.IsSeparable (K₀ k t) N :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

end Finite

section Etale

end Etale

end AffOrbicurve
