import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AffineDilatation_nonempty_algEquiv_mvPolynomial_sum

set_option autoImplicit false

universe u v

namespace PolyDil29

open AffineDilatation MvPolynomial

variable {R : Type u} [CommRing R] (π : R) (σ τ : Type v)

noncomputable abbrev J : Ideal (MvPolynomial (σ ⊕ τ) R) :=
  Ideal.span (insert (MvPolynomial.C π) (Set.range fun j : τ => (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R)))

abbrev D : Type (max u v) := AffineDilatation.Ring (J π σ τ) (MvPolynomial.C π)

abbrev L : Type (max u v) := Localization.Away (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R)

noncomputable abbrev aPow : Submonoid.powers (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R) :=
  ⟨MvPolynomial.C π, Submonoid.mem_powers _⟩

/--
@isnad1 id=mem.0h5v.s7.bafa7c8f9dae from=translated src=- shape=6539a2fe vocab=62b592b6
-/
theorem X_inr_mem (j : τ) : (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R) ∈ J π σ τ :=
  Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩)

noncomputable def v : σ ⊕ τ → D π σ τ
  | Sum.inl i => algebraMap (MvPolynomial (σ ⊕ τ) R) (D π σ τ) (MvPolynomial.X (Sum.inl i))
  | Sum.inr j => divElem (J π σ τ) (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j)) (X_inr_mem π σ τ j)

noncomputable def g : MvPolynomial (σ ⊕ τ) R →ₐ[R] D π σ τ := MvPolynomial.aeval (v π σ τ)

noncomputable def θ : MvPolynomial (σ ⊕ τ) R →ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  MvPolynomial.aeval fun k : σ ⊕ τ => match k with
    | Sum.inl i => MvPolynomial.X (Sum.inl i)
    | Sum.inr j => MvPolynomial.C π * MvPolynomial.X (Sum.inr j)

/--
@isnad1 id=eq.0h5v.s8.bb8efcbbbbee from=translated src=- shape=64cf1a34 vocab=f5e0ceff
-/
theorem θ_X_inl (i : σ) : θ π σ τ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X (Sum.inl i) := by
  simp [θ]

/--
@isnad1 id=eq.0h5v.s8.97244a3babd7 from=translated src=- shape=a398334b vocab=019a7c03
-/
theorem θ_X_inr (j : τ) :
    θ π σ τ (MvPolynomial.X (Sum.inr j)) = MvPolynomial.C π * MvPolynomial.X (Sum.inr j) := by
  simp [θ]

/--
@isnad1 id=eq.0h5v.s8.c2683ce47466 from=translated src=- shape=c03aa49a vocab=2d736ffa
-/
theorem θ_C (r : R) : θ π σ τ (MvPolynomial.C r) = MvPolynomial.C r := by
  simp [θ]

noncomputable def ψ : MvPolynomial (σ ⊕ τ) R →ₐ[R] L π σ τ :=
  ((subalgebra (J π σ τ) (MvPolynomial.C π)).val.restrictScalars R).comp (g π σ τ)

/--
@isnad1 id=eq.0h5v.s13.cccff079145e from=translated src=- shape=eb9d7240 vocab=c636ee9f
-/
theorem ψ_apply (p : MvPolynomial (σ ⊕ τ) R) : ψ π σ τ p = ((g π σ τ p : D π σ τ) : L π σ τ) := rfl

/--
@isnad1 id=eq.0h5v.s11.ad0c7fb3d34c from=translated src=- shape=04366afd vocab=7aa2a85f
-/
theorem ψ_X_inl (i : σ) :
    ψ π σ τ (MvPolynomial.X (Sum.inl i)) =
      algebraMap (MvPolynomial (σ ⊕ τ) R) (L π σ τ) (MvPolynomial.X (Sum.inl i)) := by
  rw [ψ_apply, g, MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.0h5v.s11.da19e8c22bf9 from=translated src=- shape=783174ee vocab=46b1b834
-/
theorem ψ_X_inr (j : τ) :
    ψ π σ τ (MvPolynomial.X (Sum.inr j)) =
      IsLocalization.mk' (L π σ τ) (MvPolynomial.X (Sum.inr j)) (aPow π σ τ) := by
  rw [ψ_apply, g, MvPolynomial.aeval_X]; rfl

/--
@isnad1 id=eq.0h5v.s11.f881e2bd3f3b from=translated src=- shape=be59c4e4 vocab=05487b3a
-/
theorem ψ_C (r : R) :
    ψ π σ τ (MvPolynomial.C r) = algebraMap (MvPolynomial (σ ⊕ τ) R) (L π σ τ) (MvPolynomial.C r) := by
  have hC : (MvPolynomial.C r : MvPolynomial (σ ⊕ τ) R) = algebraMap R (MvPolynomial (σ ⊕ τ) R) r := rfl
  rw [hC, AlgHom.commutes, IsScalarTower.algebraMap_apply R (MvPolynomial (σ ⊕ τ) R) (L π σ τ)]

/--
@isnad1 id=eq.0h5v.s11.e3e7a51cb878 from=translated src=- shape=458c9f73 vocab=c8eaa758
-/
theorem ψ_θ (p : MvPolynomial (σ ⊕ τ) R) : ψ π σ τ (θ π σ τ p) = algebraMap _ (L π σ τ) p := by
  suffices h : (ψ π σ τ).comp (θ π σ τ) = IsScalarTower.toAlgHom R (MvPolynomial (σ ⊕ τ) R) (L π σ τ) from
    AlgHom.congr_fun h p
  refine MvPolynomial.algHom_ext fun k => ?_
  rcases k with i | j
  · rw [AlgHom.comp_apply, θ_X_inl, ψ_X_inl]; rfl
  · rw [AlgHom.comp_apply, θ_X_inr, map_mul, ψ_C, ψ_X_inr]
    exact IsLocalization.mk'_spec' (L π σ τ) _ (aPow π σ τ)

/--
@isnad1 id=le.1h4v.s8.822b7245fab2 from=translated src=- shape=fc291392 vocab=fb7565c0
-/
theorem powers_le_nonZeroDivisors (hπ : IsSMulRegular R π) :
    Submonoid.powers (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R) ≤ nonZeroDivisors (MvPolynomial (σ ⊕ τ) R) := by
  rw [Submonoid.powers_le]
  have hreg : IsSMulRegular (MvPolynomial (σ ⊕ τ) R) π := by
    intro p q h
    ext m
    exact hπ (by simpa only [MvPolynomial.coeff_smul] using congrArg (MvPolynomial.coeff m) h)
  rw [mem_nonZeroDivisors_iff_right]
  intro p hp
  rw [mul_comm, MvPolynomial.C_mul'] at hp
  exact hreg (show π • p = π • (0 : MvPolynomial (σ ⊕ τ) R) by rw [hp, smul_zero])

noncomputable def Θ : L π σ τ →+* L π σ τ :=
  IsLocalization.map (M := Submonoid.powers (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R))
    (T := Submonoid.powers (MvPolynomial.C π : MvPolynomial (σ ⊕ τ) R)) (L π σ τ)
    (θ π σ τ).toRingHom (by
      rw [Submonoid.powers_le, Submonoid.mem_comap]
      change θ π σ τ (MvPolynomial.C π) ∈ _
      rw [θ_C]; exact Submonoid.mem_powers _)

/--
@isnad1 id=eq.0h4v.s11.230efa96e6a1 from=translated src=- shape=e1fcfc95 vocab=bb34e910
-/
theorem Θ_ψ : (Θ π σ τ).comp (ψ π σ τ).toRingHom = algebraMap (MvPolynomial (σ ⊕ τ) R) (L π σ τ) := by
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_)
  · change Θ π σ τ (ψ π σ τ (MvPolynomial.C r)) = _
    rw [ψ_C, Θ, IsLocalization.map_eq]
    change algebraMap _ (L π σ τ) (θ π σ τ (MvPolynomial.C r)) = _
    rw [θ_C]
  · change Θ π σ τ (ψ π σ τ (MvPolynomial.X k)) = _
    rcases k with i | j
    · rw [ψ_X_inl, Θ, IsLocalization.map_eq]
      change algebraMap _ (L π σ τ) (θ π σ τ (MvPolynomial.X (Sum.inl i))) = _
      rw [θ_X_inl]
    · rw [ψ_X_inr, Θ, IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
      change algebraMap _ (L π σ τ) (θ π σ τ (MvPolynomial.X (Sum.inr j))) =
        algebraMap _ (L π σ τ) (MvPolynomial.X (Sum.inr j)) * algebraMap _ (L π σ τ) (θ π σ τ (MvPolynomial.C π))
      rw [θ_X_inr, θ_C, map_mul, mul_comm]

/--
@isnad1 id=injectiv.1h4v.s12.e762c30df80d from=translated src=- shape=dbd006bf vocab=cc7fc7f0
-/
theorem g_injective (hπ : IsSMulRegular R π) : Function.Injective (g π σ τ) := by
  intro p q h
  have h' : ψ π σ τ p = ψ π σ τ q := by rw [ψ_apply, ψ_apply, h]
  have h'' : algebraMap _ (L π σ τ) p = algebraMap _ (L π σ τ) q := by
    rw [← Θ_ψ]; exact congrArg (Θ π σ τ) h'
  exact IsLocalization.injective (L π σ τ) (powers_le_nonZeroDivisors π σ τ hπ) h''

/--
@isnad1 id=le.0h4v.s11.5560345d37c4 from=translated src=- shape=fce2da0c vocab=2880c4bc
-/
theorem gen_subset_range :
    gen (J π σ τ) (MvPolynomial.C π) ⊆ Set.range (ψ π σ τ) := by
  rintro _ ⟨q, hq, rfl⟩
  change IsLocalization.mk' (L π σ τ) q (aPow π σ τ) ∈ Set.range (ψ π σ τ)
  change q ∈ Submodule.span _ _ at hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨j, rfl⟩
    · exact ⟨1, by rw [map_one, IsLocalization.mk'_self]⟩
    · exact ⟨MvPolynomial.X (Sum.inr j), ψ_X_inr π σ τ j⟩
  | zero => exact ⟨0, by rw [map_zero, IsLocalization.mk'_zero]⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp⟩ := hx
    obtain ⟨q, hq⟩ := hy
    refine ⟨p + q, ?_⟩
    rw [map_add, hp, hq, IsLocalization.mk'_eq_mul_mk'_one x, IsLocalization.mk'_eq_mul_mk'_one y,
      IsLocalization.mk'_eq_mul_mk'_one (x + y), map_add, add_mul]
  | smul c x _ hx =>
    obtain ⟨p, hp⟩ := hx
    refine ⟨θ π σ τ c * p, ?_⟩
    rw [map_mul, hp, ψ_θ, smul_eq_mul, IsLocalization.mul_mk'_eq_mk'_of_mul]

/--
@isnad1 id=surjecti.0h4v.s12.e5d02df4ba76 from=translated src=- shape=b4bd3090 vocab=bc841032
-/
theorem g_surjective : Function.Surjective (g π σ τ) := by

  let T : Subalgebra (MvPolynomial (σ ⊕ τ) R) (L π σ τ) :=
    { carrier := Set.range (ψ π σ τ)
      mul_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        exact ⟨p * q, map_mul _ _ _⟩
      one_mem' := ⟨1, map_one _⟩
      add_mem' := by
        rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
        exact ⟨p + q, map_add _ _ _⟩
      zero_mem' := ⟨0, map_zero _⟩
      algebraMap_mem' := fun p => ⟨θ π σ τ p, ψ_θ π σ τ p⟩ }
  have hle : subalgebra (J π σ τ) (MvPolynomial.C π) ≤ T := Algebra.adjoin_le (gen_subset_range π σ τ)
  intro d
  obtain ⟨p, hp⟩ := hle d.2
  exact ⟨p, Subtype.ext hp⟩

noncomputable def e (hπ : IsSMulRegular R π) : D π σ τ ≃ₐ[R] MvPolynomial (σ ⊕ τ) R :=
  (AlgEquiv.ofBijective (g π σ τ) ⟨g_injective π σ τ hπ, g_surjective π σ τ⟩).symm

/--
@isnad1 id=eq.1h5v.s13.9bcd97336e1d from=translated src=- shape=8c0c0a4e vocab=75cf633b
-/
theorem e_symm_apply (hπ : IsSMulRegular R π) (p : MvPolynomial (σ ⊕ τ) R) :
    (e π σ τ hπ).symm p = g π σ τ p := rfl

/--
@isnad1 id=eq.2h6v.s13.b6c7926b1c07 from=translated src=- shape=c72ea9a4 vocab=bd93c0f9
-/
theorem e_apply_of_eq (hπ : IsSMulRegular R π) (d : D π σ τ) (p : MvPolynomial (σ ⊕ τ) R)
    (h : g π σ τ p = d) : e π σ τ hπ d = p := by
  rw [← h, ← e_symm_apply π σ τ hπ p, AlgEquiv.apply_symm_apply]

end PolyDil29

open PolyDil29 AffineDilatation in
/--
@isnad1 id=ex.1h4v.s15.60550e49c18c from=translated src=- shape=57e72107 vocab=b9e70354
-/
theorem solution
    {R : Type u} [CommRing R] (π : R) (hπ : IsSMulRegular R π) (σ : Type v) (τ : Type v) :
    ∃ e : AffineDilatation.Ring
          (Ideal.span (insert (MvPolynomial.C π) (Set.range fun j : τ => (MvPolynomial.X (Sum.inr j) : MvPolynomial (σ ⊕ τ) R))))
          (MvPolynomial.C π) ≃ₐ[R] MvPolynomial (σ ⊕ τ) R,
      (∀ i : σ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inl i))) = MvPolynomial.X (Sum.inl i)) ∧
      (∀ j : τ, e (AffineDilatation.divElem _ (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j))
          (Ideal.subset_span (Set.mem_insert_of_mem _ ⟨j, rfl⟩))) = MvPolynomial.X (Sum.inr j)) ∧
      (∀ j : τ, e (algebraMap (MvPolynomial (σ ⊕ τ) R) _ (MvPolynomial.X (Sum.inr j))) =
          MvPolynomial.C π * MvPolynomial.X (Sum.inr j)) := by
  refine ⟨PolyDil29.e π σ τ hπ, fun i => ?_, fun j => ?_, fun j => ?_⟩
  · apply e_apply_of_eq
    rw [g, MvPolynomial.aeval_X]; rfl
  · apply e_apply_of_eq
    rw [g, MvPolynomial.aeval_X]; rfl
  · apply e_apply_of_eq
    rw [map_mul, g, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      IsScalarTower.algebraMap_apply R (MvPolynomial (σ ⊕ τ) R) (D π σ τ), MvPolynomial.algebraMap_eq]
    exact algebraMap_mul_divElem (J π σ τ) (MvPolynomial.C π) (MvPolynomial.X (Sum.inr j)) (X_inr_mem π σ τ j)
