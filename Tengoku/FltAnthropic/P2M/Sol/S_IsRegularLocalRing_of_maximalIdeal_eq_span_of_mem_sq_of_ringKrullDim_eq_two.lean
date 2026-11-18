import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsRegularLocalRing_of_maximalIdeal_eq_span_of_mem_sq_of_ringKrullDim_eq_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsRegularLocalRing_of_maximalIdeal_eq_span_of_mem_sq_of_ringKrullDim_eq_two

set_option autoImplicit false

/--
@isnad1 id=isregula.3h4v.s7.fe74767b63f5 from=translated src=- shape=23d04054 vocab=48e2f658
-/
theorem solution
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (π u v : B) (hgen : IsLocalRing.maximalIdeal B = Ideal.span {π, u, v})
    (hπ : π ∈ IsLocalRing.maximalIdeal B ^ 2) (hdim : ringKrullDim B = 2) :
    IsRegularLocalRing B := by
  classical
  set m := IsLocalRing.maximalIdeal B with hm_def
  have hπ' : π ∈ m • m := by rw [Ideal.smul_eq_mul, ← pow_two]; exact hπ

  have hle : m ≤ Ideal.span {u, v} ⊔ m • m := by
    conv_lhs => rw [hgen]
    rw [Ideal.span_insert]
    exact sup_le ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right hπ')) le_sup_left
  have hfg : m.FG := IsNoetherian.noetherian m
  have hjac : m ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]

  have heq : m = Ideal.span {u, v} :=
    le_antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hjac hle)
      (by rw [hgen]; exact Ideal.span_mono (Set.subset_insert _ _))

  have hspan : m.spanFinrank ≤ 2 := by
    rw [heq]
    show (Submodule.span B ({u, v} : Set B)).spanFinrank ≤ 2
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le B ?_
  rw [hdim]
  exact_mod_cast hspan
