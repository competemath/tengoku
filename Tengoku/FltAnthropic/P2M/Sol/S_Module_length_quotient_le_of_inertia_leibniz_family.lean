import Tengoku.Seed.Algebra.Group.Subgroup.Basic
import Tengoku.Seed.RingTheory.Length
import Tengoku.Seed.LinearAlgebra.Isomorphisms
import Tengoku.Seed.LinearAlgebra.Quotient.Basic
import Tengoku.Seed.Tactic.Group
import Tengoku.Seed.Data.Matrix.Basic
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.RingTheory.OrderOfVanishing.Basic
import Tengoku.Seed.RingTheory.FiniteLength
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.Seed.RingTheory.KrullDimension.PID
import Tengoku.Seed.RingTheory.PrincipalIdealDomain
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Determinant.Basic
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_length_quotient_le_of_inertia_leibniz_family.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_length_quotient_le_of_inertia_leibniz_family

set_option autoImplicit false

namespace WCOTL13

variable {G : Type} [Group G] {C : Type} [AddCommGroup C]

/--
@isnad1 id=eq.1h4v.s7.58d85b30e9f4 from=translated src=- shape=cbb53771 vocab=6248f83f
-/
theorem apply_one (I : Subgroup G) (f : G → C) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b) :
    f 1 = 0 := by
  have h := hadd 1 I.one_mem 1 I.one_mem
  rw [mul_one] at h
  have h' : f 1 + 0 = f 1 + f 1 := by rw [add_zero]; exact h
  exact (add_left_cancel h').symm

/--
@isnad1 id=eq.2h6v.s7.0c56111341c8 from=translated src=- shape=c0eb5767 vocab=d79d81a1
-/
theorem apply_pow (I : Subgroup G) (f : G → C) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (x : G) (hx : x ∈ I) : ∀ n : ℕ, f (x ^ n) = n • f x
  | 0 => by rw [pow_zero, zero_nsmul]; exact apply_one I f hadd
  | n + 1 => by rw [pow_succ, hadd _ (I.pow_mem hx n) _ hx, apply_pow I f hadd x hx n, succ_nsmul]

/--
@isnad1 id=eq.4h9v.s8.3a36a1e05417 from=translated src=- shape=beeb97e7 vocab=2aadd0e6
-/
theorem apply_conj_eq_nsmul (I : Subgroup G) (f : G → C) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (p m q : ℕ) (hC : ∀ c : C, p ^ m • c = 0) (σ : G)
    (hdivI : ∀ τ ∈ I, ∃ w ∈ I, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (τ : G) (hτ : τ ∈ I) : f (σ * τ * σ⁻¹) = q • f τ := by
  obtain ⟨w, hw, hwe⟩ := hdivI τ hτ
  have : σ * τ * σ⁻¹ = w ^ (p ^ m) * τ ^ q := by rw [hwe]; group
  rw [this, hadd _ (I.pow_mem hw _) _ (I.pow_mem hτ _), apply_pow I f hadd w hw, apply_pow I f hadd τ hτ, hC,
    zero_add]

/--
@isnad1 id=eq.6h11v.s8.6169a33ea556 from=translated src=- shape=47c7a6dd vocab=d79d81a1
-/
theorem apply_eq_nsmul_apply_gen (I : Subgroup G) (f : G → C) (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b)
    (p m : ℕ) (hC : ∀ c : C, p ^ m • c = 0) (γ : G) (hγI : γ ∈ I)
    (τ : G) (j : ℕ) (x w : G) (hx : x ∈ I) (hw : w ∈ I) (hτ : τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m)) :
    f τ = j • f γ := by
  rw [hτ, hadd _ (I.mul_mem (I.pow_mem hγI j) (I.pow_mem hx _)) _ (I.pow_mem hw _),
    hadd _ (I.pow_mem hγI j) _ (I.pow_mem hx _), apply_pow I f hadd γ hγI, apply_pow I f hadd x hx,
    apply_pow I f hadd w hw, hC, hC, add_zero, add_zero]

/--
@isnad1 id=eq.6h8v.s8.d0b08101b701 from=translated src=- shape=85b89627 vocab=d79d81a1
-/
theorem apply_eq_zero_of_apply_gen_eq_zero (I : Subgroup G) (f : G → C)
    (hadd : ∀ a ∈ I, ∀ b ∈ I, f (a * b) = f a + f b) (p m : ℕ) (hC : ∀ c : C, p ^ m • c = 0) (γ : G) (hγI : γ ∈ I)
    (hgen : ∀ τ ∈ I, ∃ (j : ℕ) (x w : G), x ∈ I ∧ w ∈ I ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (h0 : f γ = 0) (τ : G) (hτ : τ ∈ I) : f τ = 0 := by
  obtain ⟨j, x, w, hx, hw, hτe⟩ := hgen τ hτ
  rw [apply_eq_nsmul_apply_gen I f hadd p m hC γ hγI τ j x w hx hw hτe, h0, nsmul_zero]

/--
@isnad1 id=le.6h11v.s10.7f03e53c58ec from=translated src=- shape=52a95855 vocab=33bf21a0
-/
theorem length_quotient_le {𝒪 H : Type} [CommRing 𝒪] [AddCommGroup H] [Module 𝒪 H] [Module 𝒪 C]
    (I : Subgroup G) (p m : ℕ) (hC : ∀ c : C, p ^ m • c = 0) (γ : G) (hγI : γ ∈ I)
    (hgen : ∀ τ ∈ I, ∃ (j : ℕ) (x w : G), x ∈ I ∧ w ∈ I ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (Λ : H →ₗ[𝒪] (G → C)) (hadd : ∀ φ : H, ∀ a ∈ I, ∀ b ∈ I, Λ φ (a * b) = Λ φ a + Λ φ b)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ I, Λ φ τ = 0) → φ ∈ K)
    (W : Submodule 𝒪 C) (hW : ∀ φ : H, Λ φ γ ∈ W) :
    Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 W := by
  let e : H →ₗ[𝒪] C := (LinearMap.proj γ).comp Λ
  have he : ∀ φ, e φ = Λ φ γ := fun _ => rfl
  have hker : LinearMap.ker e ≤ K := by
    intro φ hφ
    rw [LinearMap.mem_ker, he] at hφ
    exact hK φ (fun τ hτ => apply_eq_zero_of_apply_gen_eq_zero I (Λ φ) (hadd φ) p m hC γ hγI hgen hφ τ hτ)

  have h1 : Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 (H ⧸ LinearMap.ker e) := by
    refine Module.length_le_of_surjective
      (Submodule.mapQ (LinearMap.ker e) K LinearMap.id (fun x hx => hker hx)) ?_
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective K y
    exact ⟨Submodule.mkQ _ x, rfl⟩
  have h2 : Module.length 𝒪 (H ⧸ LinearMap.ker e) = Module.length 𝒪 (LinearMap.range e) :=
    (LinearMap.quotKerEquivRange e).length_eq
  have hle : LinearMap.range e ≤ W := by
    rintro _ ⟨φ, rfl⟩
    exact hW φ
  have h3 : Module.length 𝒪 (LinearMap.range e) ≤ Module.length 𝒪 W :=
    Module.length_le_of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  exact h1.trans (h2.le.trans h3)

end WCOTL13

namespace WCOTDev1f

/--
@isnad1 id=eq.1h3v.s8.fd06894d0cdc from=translated src=- shape=435aa7fe vocab=0aefcf50
-/
theorem length_ker_eq_length_quotient_range {R M : Type} [Ring R] [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) (hM : Module.length R M ≠ ⊤) :
    Module.length R (LinearMap.ker f) = Module.length R (M ⧸ LinearMap.range f) := by
  have h1 : Module.length R M =
      Module.length R (LinearMap.ker f.rangeRestrict) + Module.length R (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f.rangeRestrict).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict (LinearMap.exact_subtype_ker_map _)
  rw [LinearMap.ker_rangeRestrict] at h1
  have h2 : Module.length R M =
      Module.length R (LinearMap.range f) + Module.length R (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hr : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro htop
    rw [htop, add_top] at h1
    exact hM h1
  refine (ENat.addLECancellable_of_ne_top hr).inj_right.mp ?_

  rw [← h2, add_comm, ← h1]

end WCOTDev1f

namespace WCOTLchainB

open WCOTL13

section entry

variable {𝒪 : Type} [CommRing 𝒪] {R : Type} [CommRing R] [Algebra 𝒪 R] {G : Type}
  {H : Type} [AddCommGroup H] [Module 𝒪 H]

def entry10 (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R)) : H →ₗ[𝒪] (G → R) where
  toFun φ g := Λ φ g 1 0
  map_add' φ ψ := by
    funext g
    simp only [map_add, Pi.add_apply, Matrix.add_apply]
  map_smul' c φ := by
    funext g
    simp only [map_smul, Pi.smul_apply, Matrix.smul_apply, RingHom.id_apply]

/--
@isnad1 id=eq.0h7v.s9.fc73da4393af from=translated src=- shape=0d4dc264 vocab=c4f316d1
-/
theorem entry10_apply (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) R)) (φ : H) (g : G) :
    entry10 Λ φ g = Λ φ g 1 0 := rfl

/--
@isnad1 id=eq.4h5v.s9.0be769d59244 from=translated src=- shape=ec20f410 vocab=d6b99d3a
-/
theorem leibniz_entry10_of_shapes (Fg Fh Λg Λh : Matrix (Fin 2) (Fin 2) R)
    (hg10 : Fg 1 0 = 0) (hg11 : Fg 1 1 = 1) (hh10 : Fh 1 0 = 0) (hh00 : Fh 0 0 = 1) :
    (Fg * Λh + Λg * Fh) 1 0 = Λg 1 0 + Λh 1 0 := by
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, hg10, hg11, hh10, hh00]
  ring

/--
@isnad1 id=eq.8h7v.s10.09334b522960 from=translated src=- shape=bc5f020f vocab=607ae852
-/
theorem entry10_eq_mul_entry10_conj [Group G] (Fb : G → Matrix (Fin 2) (Fin 2) R)
    (hFmul : ∀ g h : G, Fb (g * h) = Fb g * Fb h) (hF1 : Fb 1 = 1)
    (Λ : G → Matrix (Fin 2) (Fin 2) R) (hLeib : ∀ g h : G, Λ (g * h) = Fb g * Λ h + Λ g * Fb h)
    (σ τ : G) (q : R) (hσ10 : Fb σ 1 0 = 0) (hσ00 : Fb σ 0 0 = q * Fb σ 1 1)
    (hτ10 : Fb (σ * τ * σ⁻¹) 1 0 = 0) (hτ00 : Fb (σ * τ * σ⁻¹) 0 0 = 1) (hτ11 : Fb (σ * τ * σ⁻¹) 1 1 = 1) :
    Λ τ 1 0 = q * Λ (σ * τ * σ⁻¹) 1 0 := by

  have hSS' : Fb σ * Fb σ⁻¹ = 1 := by rw [← hFmul, mul_inv_cancel, hF1]
  have e10 : Fb σ 1 1 * Fb σ⁻¹ 1 0 = 0 := by
    have h := congrFun (congrFun hSS' 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hσ10] using h
  have e11 : Fb σ 1 1 * Fb σ⁻¹ 1 1 = 1 := by
    have h := congrFun (congrFun hSS' 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, hσ10] using h
  have hS'10 : Fb σ⁻¹ 1 0 = 0 := by
    have : Fb σ⁻¹ 1 0 = Fb σ⁻¹ 1 1 * (Fb σ 1 1 * Fb σ⁻¹ 1 0) := by
      rw [← mul_assoc, mul_comm (Fb σ⁻¹ 1 1), e11, one_mul]
    rw [this, e10, mul_zero]

  have hΛ1 : Λ 1 = 0 := by
    have h := hLeib 1 1
    rw [mul_one, hF1, one_mul, mul_one] at h
    have h' : Λ 1 + 0 = Λ 1 + Λ 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hinv : Fb σ⁻¹ * Λ σ + Λ σ⁻¹ * Fb σ = 0 := by
    have h := hLeib σ⁻¹ σ
    rw [inv_mul_cancel, hΛ1] at h
    exact h.symm
  have hinv10 : Fb σ⁻¹ 1 1 * Λ σ 1 0 + Λ σ⁻¹ 1 0 * (q * Fb σ 1 1) = 0 := by
    have h := congrFun (congrFun hinv 1) 0
    simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, hS'10, hσ10, hσ00, Matrix.zero_apply] at h
    linear_combination h

  have key : Λ τ = Fb σ⁻¹ * Fb (σ * τ * σ⁻¹) * Λ σ + Fb σ⁻¹ * Λ (σ * τ * σ⁻¹) * Fb σ +
      Λ σ⁻¹ * Fb (σ * τ * σ⁻¹) * Fb σ := by
    have hτ : τ = σ⁻¹ * (σ * τ * σ⁻¹) * σ := by group
    conv_lhs => rw [hτ]
    rw [hLeib (σ⁻¹ * (σ * τ * σ⁻¹)) σ, hLeib σ⁻¹ (σ * τ * σ⁻¹), hFmul σ⁻¹ (σ * τ * σ⁻¹), add_mul, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc]
    abel
  have h := congrFun (congrFun key 1) 0
  simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, hS'10, hσ10, hσ00, hτ10, hτ00, hτ11] at h
  linear_combination h + hinv10 + (q * Λ (σ * τ * σ⁻¹) 1 0) * e11

end entry

section count

variable {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

/--
@isnad1 id=le.0h3v.s13.baf953e15fa0 from=translated src=- shape=c6566e39 vocab=56d2ef21
-/
theorem length_ker_smul_id_le (m : ℕ) (c : 𝒪) :
    Module.length 𝒪 (LinearMap.ker (c • (LinearMap.id :
      (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) →ₗ[𝒪] (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))) ≤
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {c}) := by
  haveI hP : (IsLocalRing.maximalIdeal 𝒪).IsPrincipal :=
    IsPrincipalIdealRing.principal (IsLocalRing.maximalIdeal 𝒪)
  have hg0 : Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal 𝒪) ≠ 0 := by
    intro h0
    apply IsDiscreteValuationRing.not_isField 𝒪
    rw [IsLocalRing.isField_iff_maximalIdeal_eq,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal 𝒪), h0]
    exact Ideal.span_singleton_eq_bot.mpr rfl
  have hQ : IsFiniteLength 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) := by
    rw [← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal 𝒪), Ideal.span_singleton_pow]
    exact isFiniteLength_quotient_span_singleton 𝒪
      (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m hg0))
  have hfin : Module.length 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ≠ ⊤ := Module.length_ne_top_iff.mpr hQ
  rw [WCOTDev1f.length_ker_eq_length_quotient_range _ hfin]

  set f := c • (LinearMap.id : (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) →ₗ[𝒪] (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m))
    with hf
  let g : 𝒪 →ₗ[𝒪] ((𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ⧸ LinearMap.range f) :=
    (LinearMap.range f).mkQ ∘ₗ Algebra.linearMap 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨a, rfl⟩
  have hle : Ideal.span {c} ≤ LinearMap.ker g := by
    refine (Ideal.span_singleton_le_iff_mem _).mpr ?_
    rw [LinearMap.mem_ker]
    show (LinearMap.range f).mkQ (algebraMap 𝒪 _ c) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨1, ?_⟩
    rw [hf, LinearMap.smul_apply, LinearMap.id_apply, Algebra.smul_def, mul_one]
  refine Module.length_le_of_surjective (Submodule.liftQ _ g hle) ?_
  intro y
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨Submodule.Quotient.mk a, rfl⟩

/--
@isnad1 id=le.10h12v.s13.864b7192fe47 from=translated src=- shape=1ee0682f vocab=33cea46d
-/
theorem length_quotient_le_length_sq_sub_one
    {G : Type} [Group G] (Isub : Subgroup G) (σ γ : G) (hγI : γ ∈ Isub) (p q m : ℕ)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ τ ∈ Isub, ∃ w ∈ Isub, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ τ ∈ Isub, ∃ (j : ℕ) (x w : G), x ∈ Isub ∧ w ∈ Isub ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (Fb : G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m))
    (hFmul : ∀ g h : G, Fb (g * h) = Fb g * Fb h) (hF1 : Fb 1 = 1)
    (hFI : ∀ τ ∈ Isub, Fb τ 1 0 = 0 ∧ Fb τ 0 0 = 1 ∧ Fb τ 1 1 = 1)
    (hFσ : Fb σ 1 0 = 0 ∧ Fb σ 0 0 = (q : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) * Fb σ 1 1)
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (hLeib : ∀ (φ : H) (g h : G), Λ φ (g * h) = Fb g * Λ φ h + Λ φ g * Fb h)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ Isub, Λ φ τ 1 0 = 0) → φ ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by

  have hC : ∀ c : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m, p ^ m • c = 0 := by
    intro c
    have h0 : algebraMap 𝒪 (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ((p : 𝒪) ^ m) = 0 := by
      rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_mem_pow hp𝔪 m
    rw [← Nat.cast_smul_eq_nsmul 𝒪, Nat.cast_pow, ← algebraMap_smul (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m),
      h0, zero_smul]

  have hadd : ∀ φ : H, ∀ a ∈ Isub, ∀ b ∈ Isub, entry10 Λ φ (a * b) = entry10 Λ φ a + entry10 Λ φ b := by
    intro φ a ha b hb
    rw [entry10_apply, entry10_apply, entry10_apply, hLeib]
    exact leibniz_entry10_of_shapes _ _ _ _ (hFI a ha).1 (hFI a ha).2.2 (hFI b hb).1 (hFI b hb).2.1

  have hmemI : ∀ τ ∈ Isub, σ * τ * σ⁻¹ ∈ Isub := by
    intro τ hτ
    obtain ⟨w, hw, hwe⟩ := hdivI τ hτ
    have : σ * τ * σ⁻¹ = w ^ (p ^ m) * τ ^ q := by rw [hwe]; group
    rw [this]
    exact Isub.mul_mem (Isub.pow_mem hw _) (Isub.pow_mem hτ _)

  have htors : ∀ φ : H, ∀ τ ∈ Isub, ((q : 𝒪) ^ 2 - 1) • entry10 Λ φ τ = 0 := by
    intro φ τ hτ
    have h1 := entry10_eq_mul_entry10_conj Fb hFmul hF1 (Λ φ) (hLeib φ) σ τ _ hFσ.1 hFσ.2
      (hFI _ (hmemI τ hτ)).1 (hFI _ (hmemI τ hτ)).2.1 (hFI _ (hmemI τ hτ)).2.2
    have h2 : entry10 Λ φ (σ * τ * σ⁻¹) = q • entry10 Λ φ τ :=
      apply_conj_eq_nsmul Isub (entry10 Λ φ) (hadd φ) p m q hC σ hdivI τ hτ
    rw [entry10_apply, entry10_apply, nsmul_eq_mul] at h2
    rw [h2] at h1
    have h3 : (((q : ℕ) : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) ^ 2 - 1) * Λ φ τ 1 0 = 0 := by
      linear_combination (-1 : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) * h1
    rw [entry10_apply, Algebra.smul_def, map_sub, map_pow, map_natCast, map_one]
    exact h3
  have hW : ∀ φ : H, entry10 Λ φ γ ∈ LinearMap.ker (((q : 𝒪) ^ 2 - 1) • (LinearMap.id :
      (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) →ₗ[𝒪] (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m))) := by
    intro φ
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact htors φ γ hγI
  exact (length_quotient_le Isub p m hC γ hγI hgen (entry10 Λ) hadd K (fun φ h => hK φ h) _ hW).trans
    (length_ker_smul_id_le m _)

end count

end WCOTLchainB

/--
@isnad1 id=le.10h12v.s13.864b7192fe47 from=translated src=- shape=1ee0682f vocab=33cea46d
-/
theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    {G : Type} [Group G] (Isub : Subgroup G) (σ γ : G) (hγI : γ ∈ Isub) (p q m : ℕ)
    (hp𝔪 : (p : 𝒪) ∈ IsLocalRing.maximalIdeal 𝒪)
    (hdivI : ∀ τ ∈ Isub, ∃ w ∈ Isub, w ^ (p ^ m) = σ * τ * σ⁻¹ * (τ ^ q)⁻¹)
    (hgen : ∀ τ ∈ Isub, ∃ (j : ℕ) (x w : G), x ∈ Isub ∧ w ∈ Isub ∧ τ = γ ^ j * x ^ (p ^ m) * w ^ (p ^ m))
    (Fb : G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m))
    (hFmul : ∀ g h : G, Fb (g * h) = Fb g * Fb h) (hF1 : Fb 1 = 1)
    (hFI : ∀ τ ∈ Isub, Fb τ 1 0 = 0 ∧ Fb τ 0 0 = 1 ∧ Fb τ 1 1 = 1)
    (hFσ : Fb σ 1 0 = 0 ∧ Fb σ 0 0 = (q : 𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m) * Fb σ 1 1)
    {H : Type} [AddCommGroup H] [Module 𝒪 H]
    (Λ : H →ₗ[𝒪] (G → Matrix (Fin 2) (Fin 2) (𝒪 ⧸ (IsLocalRing.maximalIdeal 𝒪) ^ m)))
    (hLeib : ∀ (φ : H) (g h : G), Λ φ (g * h) = Fb g * Λ φ h + Λ φ g * Fb h)
    (K : Submodule 𝒪 H) (hK : ∀ φ : H, (∀ τ ∈ Isub, Λ φ τ 1 0 = 0) → φ ∈ K) :
    Module.length 𝒪 (H ⧸ K) ≤ Module.length 𝒪 (𝒪 ⧸ Ideal.span {(q : 𝒪) ^ 2 - 1}) := by
  exact WCOTLchainB.length_quotient_le_length_sq_sub_one Isub σ γ hγI p q m hp𝔪 hdivI hgen Fb hFmul hF1 hFI hFσ Λ hLeib K hK
