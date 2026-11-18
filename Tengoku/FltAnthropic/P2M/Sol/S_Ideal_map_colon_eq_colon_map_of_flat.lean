import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_map_colon_eq_colon_map_of_flat.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_map_colon_eq_colon_map_of_flat
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open TensorProduct

namespace FlatColon

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/--
@isnad1 id=mem.0h4v.s11.e4ae86ea6c9c from=translated src=- shape=d33f48ea vocab=12ab585f
-/
theorem rid_lTensor_subtype_mem (K : Ideal R) (y : S ⊗[R] K) :
    TensorProduct.rid R S (LinearMap.lTensor S K.subtype y) ∈ K.map (algebraMap R S) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | tmul a k =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Submodule.coe_subtype, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ k.2)
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

/--
@isnad1 id=mem.1h5v.s9.6d5cb26a0d41 from=translated src=- shape=f045a62e vocab=760d2c87
-/
theorem mem_map_ker_of_tmul_eq_zero [Module.Flat R S] {N : Type*} [AddCommGroup N] [Module R N]
    (g : R →ₗ[R] N) (s : S) (hs : s ⊗ₜ[R] (g 1) = (0 : S ⊗[R] N)) :
    s ∈ Ideal.map (algebraMap R S) (LinearMap.ker g) := by
  have hex : Function.Exact (LinearMap.ker g).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype]
  have hexS := Module.Flat.lTensor_exact S hex
  have h0 : LinearMap.lTensor S g (s ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul, hs]
  obtain ⟨y, hy⟩ := (hexS _).mp h0
  have hs1 : s = TensorProduct.rid R S (s ⊗ₜ[R] (1 : R)) := by
    rw [TensorProduct.rid_tmul, one_smul]
  rw [hs1, ← hy]
  exact rid_lTensor_subtype_mem _ y

/--
@isnad1 id=eq.1h4v.s9.15ce0cf85e43 from=translated src=- shape=933f905a vocab=935ae23f
-/
theorem tmul_mk_one_eq_zero (I : Ideal R) (t : S) (ht : t ∈ I.map (algebraMap R S)) :
    t ⊗ₜ[R] (Ideal.Quotient.mk I 1) = (0 : S ⊗[R] (R ⧸ I)) := by
  apply (TensorProduct.tensorQuotEquivQuotSMul S I).injective
  rw [map_zero]
  have h1 : (TensorProduct.tensorQuotEquivQuotSMul S I) (t ⊗ₜ[R] (Ideal.Quotient.mk I 1))
      = Submodule.Quotient.mk ((1 : R) • t) := by
    simp [TensorProduct.tensorQuotEquivQuotSMul]
  rw [h1, one_smul, Submodule.Quotient.mk_eq_zero, Ideal.smul_top_eq_map]
  exact ht

/--
@isnad1 id=eq.0h4v.s8.f081c85a0fb7 from=translated src=- shape=88192068 vocab=6ad3c3ac
-/
theorem map_colon_singleton [Module.Flat R S] (I : Ideal R) (x : R) :
    (Submodule.colon I {x}).map (algebraMap R S)
      = Submodule.colon (I.map (algebraMap R S)) {algebraMap R S x} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hr
    rw [Ideal.mem_comap, Submodule.mem_colon_singleton, smul_eq_mul, ← map_mul]
    exact Ideal.mem_map_of_mem _ hr
  · intro s hs
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hs
    set g : R →ₗ[R] R ⧸ I := x • (Submodule.mkQ I) with hg
    have hker : LinearMap.ker g = Submodule.colon I {x} := by
      ext r
      rw [LinearMap.mem_ker, Submodule.mem_colon_singleton, hg, LinearMap.smul_apply, Submodule.mkQ_apply,
        ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, smul_eq_mul, mul_comm]
    rw [← hker]
    apply mem_map_ker_of_tmul_eq_zero
    have h1 : g 1 = x • (Ideal.Quotient.mk I 1) := by
      rw [hg, LinearMap.smul_apply, Submodule.mkQ_apply]; rfl
    rw [h1, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_comm]
    exact tmul_mk_one_eq_zero I _ hs

/--
@isnad1 id=eq.0h4v.s8.c4e9460c6515 from=translated src=- shape=6159098b vocab=4572f4b8
-/
theorem map_inf [Module.Flat R S] (K₁ K₂ : Ideal R) :
    (K₁ ⊓ K₂).map (algebraMap R S) = K₁.map (algebraMap R S) ⊓ K₂.map (algebraMap R S) := by
  apply le_antisymm (Ideal.map_inf_le _)
  intro s hs
  set g : R →ₗ[R] (R ⧸ K₁) × (R ⧸ K₂) := LinearMap.prod (Submodule.mkQ K₁) (Submodule.mkQ K₂) with hg
  have hker : LinearMap.ker g = K₁ ⊓ K₂ := by
    rw [hg, LinearMap.ker_prod, Submodule.ker_mkQ, Submodule.ker_mkQ]
  rw [← hker]
  apply mem_map_ker_of_tmul_eq_zero
  have h1 : g 1 = (Ideal.Quotient.mk K₁ 1, Ideal.Quotient.mk K₂ 1) := rfl
  rw [h1]
  have key : TensorProduct.prodRight R R S (R ⧸ K₁) (R ⧸ K₂)
      (s ⊗ₜ[R] (Ideal.Quotient.mk K₁ 1, Ideal.Quotient.mk K₂ 1)) = 0 := by
    rw [TensorProduct.prodRight_tmul, Prod.mk_eq_zero]
    exact ⟨tmul_mk_one_eq_zero K₁ s hs.1, tmul_mk_one_eq_zero K₂ s hs.2⟩
  exact (LinearEquiv.map_eq_zero_iff _).mp key

/--
@isnad1 id=eq.0h2v.s6.b4047e6aa400 from=translated src=- shape=b1dc82cf vocab=61c99354
-/
theorem colon_empty (I : Ideal R) : Submodule.colon I (∅ : Set R) = ⊤ := by
  rw [eq_top_iff]
  intro r _
  rw [Submodule.mem_colon]
  intro s hs
  exact absurd hs (Set.notMem_empty s)

/--
@isnad1 id=eq.0h4v.s8.62423b7b0c89 from=translated src=- shape=2082627e vocab=bec42a32
-/
theorem map_colon_finset [Module.Flat R S] [DecidableEq R] (I : Ideal R) (T : Finset R) :
    (Submodule.colon I (T : Set R)).map (algebraMap R S)
      = Submodule.colon (I.map (algebraMap R S)) (algebraMap R S '' (T : Set R)) := by
  induction T using Finset.induction_on with
  | empty =>
      rw [Finset.coe_empty, Set.image_empty, colon_empty, colon_empty, Ideal.map_top]
  | insert a T ha ih =>
      rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, Set.insert_eq, Submodule.colon_union,
        Submodule.colon_union, map_inf, map_colon_singleton, ih]

/--
@isnad1 id=eq.0h3v.s6.417f67bd1aef from=translated src=- shape=17ca357b vocab=66a7559d
-/
theorem colon_span (I : Ideal R) (s : Set R) :
    Submodule.colon I (Ideal.span s : Set R) = Submodule.colon I s := by
  ext r
  rw [Submodule.mem_colon, Submodule.mem_colon]
  constructor
  · intro h t ht
    exact h t (Ideal.subset_span ht)
  · intro h t ht
    refine Submodule.span_induction (p := fun t _ => r • t ∈ I) ?_ ?_ ?_ ?_ ht
    · intro u hu; exact h u hu
    · show r • (0 : R) ∈ I
      rw [smul_zero]; exact zero_mem _
    · intro u v _ _ hu hv
      show r • (u + v) ∈ I
      rw [smul_add]; exact add_mem hu hv
    · intro c u _ hu
      show r • (c • u) ∈ I
      rw [smul_comm]; exact Ideal.mul_mem_left _ _ hu

end FlatColon

/--
@isnad1 id=eq.1h4v.s8.9fd065ce3016 from=translated src=- shape=5a0a023f vocab=507698f4
-/
theorem solution
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (I J : Ideal R) (hJ : J.FG) :
    (Submodule.colon I (J : Set R)).map (algebraMap R S)
      = Submodule.colon (I.map (algebraMap R S)) (J.map (algebraMap R S) : Set S) := by
  classical
  obtain ⟨T, rfl⟩ := hJ
  rw [FlatColon.colon_span, Ideal.map_span, FlatColon.colon_span, FlatColon.map_colon_finset]

