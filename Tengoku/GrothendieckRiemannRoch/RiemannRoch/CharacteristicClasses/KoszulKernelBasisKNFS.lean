/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import Tengoku.Seed.RingTheory.Regular.Flat
import Tengoku.Seed.RingTheory.Localization.Away.Basic
import Tengoku.Seed.LinearAlgebra.Basis.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Route KNFS (pure algebra leaf): kernel of a row `A^ι → A` with a unit entry, and localization of
kernel generators

* `exists_kernelBasis`: on `F` free with basis `μ_k`, let `ρ : F → L` send `μ_k ↦ z_k • g` with `g`
  a free generator of the line and `z_j = 1`.  Then `ker ρ` is free with basis `μ_m - z_m μ_j`
  (`m ≠ j`).  This is the algebra behind "`K(W)` is free on the affine literal chart `D₊(b_j)`".
* `ker_le_span_of_localization`: if `ker f ≤ (θ_i)` for `f : A → C`, the same holds for the
  localizations `A_h → C_{f h}`, with the images of `θ_i`.
-/

set_option autoImplicit false
noncomputable section

universe u

namespace RiemannRoch.KNFS

section KernelBasis

variable {A : Type u} [CommRing A] {ι : Type u} [Fintype ι] [DecidableEq ι]
  {F L K : Type u} [AddCommGroup F] [Module A F] [AddCommGroup L] [Module A L]
  [AddCommGroup K] [Module A K]

/-- The kernel of a row with a unit entry (the entry at `j` equal to `1`) is free on
`μ_m - z_m μ_j`, `m ≠ j`.
@isnad1 id=ex.6h11v.s10.760152ae55e3 from=translated src=- shape=96ad5052 vocab=fe42d6c3
-/
theorem exists_kernelBasis (μ : Module.Basis ι A F) (ρ : F →ₗ[A] L) (g : L) (z : ι → A) (j : ι)
    (hz : z j = 1) (hρ : ∀ k, ρ (μ k) = z k • g) (hg : ∀ a : A, a • g = 0 → a = 0)
    (κ : K →ₗ[A] F) (hκ : Function.Injective κ) (hrange : ∀ f, ρ f = 0 → ∃ k, κ k = f)
    (hκρ : ∀ k, ρ (κ k) = 0) :
    ∃ e : Module.Basis {m // m ≠ j} A K, ∀ m, κ (e m) = μ m - z m • μ j := by
  have hmem : ∀ m : {m // m ≠ j}, ρ (μ m - z m • μ j) = 0 := by
    intro m
    rw [map_sub, map_smul, hρ, hρ, hz, smul_smul, mul_one, sub_self]
  choose ε hε using fun m : {m // m ≠ j} => hrange _ (hmem m)
  let T : ({m // m ≠ j} → A) →ₗ[A] K :=
    { toFun := fun a => ∑ m, a m • ε m
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp [Finset.smul_sum, smul_smul] }
  have hT : ∀ a, κ (T a) = ∑ m : {m // m ≠ j}, a m • (μ m - z m • μ j) := by
    intro a
    change κ (∑ m, a m • ε m) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, hε]
  have coord : ∀ a (m0 : {m // m ≠ j}), μ.repr (κ (T a)) m0 = a m0 := by
    intro a m0
    rw [hT]
    simp only [map_sum, map_smul, map_sub, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul, Module.Basis.repr_self,
      Finsupp.single_apply]
    have hj : (j : ι) ≠ m0 := fun h => m0.2 h.symm
    simp [hj]
    simp only [Subtype.coe_inj, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hinj : Function.Injective T := by
    intro a b hab
    funext m
    rw [← coord a m, ← coord b m, hab]
  have hsurj : Function.Surjective T := by
    intro k
    let f := κ k
    let c : ι → A := fun l => μ.repr f l
    have hf : f = ∑ l, c l • μ l := (μ.sum_repr f).symm
    have hρf : ρ f = 0 := hκρ k
    have hsum : (∑ l, c l * z l) = 0 := by
      apply hg
      rw [Finset.sum_smul, ← hρf, hf, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, hρ, smul_smul]
    have hsplit : ∀ (M : Type u) [AddCommMonoid M] (h : ι → M),
        ∑ l, h l = h j + ∑ m : {m // m ≠ j}, h m := fun M _ h =>
      Fintype.sum_eq_add_sum_subtype_ne h j
    have hcj : c j = - ∑ m : {m // m ≠ j}, c m * z m := by
      rw [hsplit A (fun l => c l * z l), hz, mul_one] at hsum
      exact eq_neg_of_add_eq_zero_left hsum
    refine ⟨fun m => c m, ?_⟩
    apply hκ
    rw [hT]
    change _ = f
    rw [hf, hsplit F (fun l => c l • μ l), hcj]
    simp only [smul_sub, Finset.sum_sub_distrib, neg_smul, Finset.sum_smul, smul_smul]
    abel
  let E : ({m // m ≠ j} → A) ≃ₗ[A] K := LinearEquiv.ofBijective T ⟨hinj, hsurj⟩
  refine ⟨Module.Basis.ofEquivFun E.symm, fun m => ?_⟩
  rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_symm]
  change κ (T (Pi.single m 1)) = _
  rw [hT]
  rw [Finset.sum_eq_single m]
  · simp
  · intro m' _ hm'
    simp [hm']
  · simp

end KernelBasis

section Localization

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra C D]

/-- **Kernel generators survive localization.**  If `ker f ≤ (θ_i)` for `f : A → C`, and
`B = A_h`, `D = C_{f h}` with `f' : B → D` the induced map, then `ker f' ≤ (θ_i)` in `B`.
@isnad1 id=le.2h9v.s9.e73e6d4245dd from=translated src=- shape=5882c4b1 vocab=20f70c15
-/
theorem ker_le_span_of_localization (h : A) [IsLocalization.Away h B] (f : A →+* C)
    [IsLocalization.Away (f h) D] (f' : B →+* D)
    (hcomm : ∀ a, f' (algebraMap A B a) = algebraMap C D (f a)) {κ : Type*} (θ : κ → A)
    (hker : RingHom.ker f ≤ Ideal.span (Set.range θ)) :
    RingHom.ker f' ≤ Ideal.span (Set.range fun i => algebraMap A B (θ i)) := by
  intro b hb
  rw [RingHom.mem_ker] at hb
  obtain ⟨⟨a, ⟨_, N, rfl⟩⟩, hab⟩ := IsLocalization.surj (Submonoid.powers h) b
  have h1 : algebraMap C D (f a) = 0 := by
    rw [← hcomm, ← hab, map_mul, hb, zero_mul]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f h)) D _).mp h1
  have h2 : h ^ k * a ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_mul, map_pow]
    exact hk
  have h3 := hker h2
  have h4 : algebraMap A B (h ^ k * a) ∈ Ideal.span (Set.range fun i => algebraMap A B (θ i)) := by
    have := Ideal.mem_map_of_mem (algebraMap A B) h3
    rwa [Ideal.map_span, ← Set.range_comp] at this
  have hu : IsUnit (algebraMap A B (h ^ (N + k))) :=
    IsLocalization.map_units B (⟨h ^ (N + k), N + k, rfl⟩ : Submonoid.powers h)
  apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
  have : b * algebraMap A B (h ^ (N + k)) = algebraMap A B (h ^ k * a) := by
    rw [pow_add, map_mul, ← mul_assoc, hab, ← map_mul, mul_comm]
  rw [mul_comm, this]
  exact h4

end Localization

end RiemannRoch.KNFS
