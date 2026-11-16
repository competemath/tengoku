import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgHom_eq_of_forall_sub_mem_of_le_jacobson_of_formallyUnramified

universe u v w

set_option autoImplicit false
open scoped TensorProduct

/--
@isnad1 id=eq.2h6v.s8.36aa01b1ac64 from=translated src=- shape=fe9d9e54 vocab=1685678e
-/
theorem solution
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A]
    [Algebra.EssFiniteType R A] [Algebra.FormallyUnramified R A]
    {B : Type w} [CommRing B] [Algebra R B]
    (I : Ideal B) (hI : I ≤ Ideal.jacobson ⊥)
    (f g : A →ₐ[R] B) (hfg : ∀ a : A, f a - g a ∈ I) :
    f = g := by
  obtain ⟨t, ht₁, ht₂⟩ :=
    (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let m : A ⊗[R] A →ₐ[R] B := Algebra.TensorProduct.productMap f g
  have h1 : ∀ s, (g s - f s) * m t = 0 := by
    intro s
    have := congrArg m (ht₁ s)
    simpa [m, map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul] using this
  have h2 : 1 - m t ∈ I := by
    have hmem : 1 - t ∈ Ideal.span (Set.range fun s : A => (1 : A) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : A)) := by
      rw [KaehlerDifferential.span_range_eq_ideal]
      change 1 - t ∈ RingHom.ker _
      rw [RingHom.mem_ker, map_sub, map_one, ht₂, sub_self]
    have hle : Ideal.map m (Ideal.span (Set.range fun s : A => (1 : A) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : A))) ≤ I := by
      rw [Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
      have : m ((1 : A) ⊗ₜ[R] s - s ⊗ₜ[R] 1) = -(f s - g s) := by
        simp [m, map_sub, Algebra.TensorProduct.productMap_apply_tmul]
      rw [SetLike.mem_coe, this]
      exact I.neg_mem (hfg s)
    have := hle (Ideal.mem_map_of_mem m hmem)
    simpa [map_sub, map_one] using this
  have hunit : IsUnit (m t) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    have : -(1 - m t) ∈ Ideal.jacobson (⊥ : Ideal B) := hI (I.neg_mem h2)
    simpa using this
  ext s
  have := h1 s
  rw [hunit.mul_left_eq_zero, sub_eq_zero] at this
  exact this.symm

