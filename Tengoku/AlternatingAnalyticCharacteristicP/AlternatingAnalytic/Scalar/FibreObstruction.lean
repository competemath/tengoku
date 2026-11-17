import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.FibreObstruction.SourceSign

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lemma F.4 (finite fibre obstruction)

Over a field `κ` with `k! = 0`, no `k`-linear `τ : Hom(κ^{k+1}, κ^k)^k → Alt^k(κ^{k+1}; κ)`
satisfies both condition (1), `τ(g₀, …, g₀) = δ' ∘ g₀`, and condition (2), vanishing on the
finite family `F` of (F.2). Expanding `g₀ = ∑_c ε^c ⊗ e'_c` in condition (1) and evaluating at
`(e₀, …, e_{k-1})`, the left side is `1`. On the right, the terms with a non-injective target
function vanish, and by the target and source sign rules each of the `k!` permutation terms
equals `(-1)^k t(id)`; so the right side is `k! (-1)^k t(id) = 0`.
-/

namespace AlternatingAnalytic.FibreObstruction

universe u

open Function

variable {κ : Type u} [Field κ] {k : ℕ}

/-- `g₀ = ∑_c ε^c ⊗ e'_c`.
@isnad1 id=eq.0h2v.s10.1615292e5f55 from=translated src=- shape=5123def5 vocab=e9f898f4
-/
theorem firstCoords_eq_sum :
    firstCoords κ k = ∑ c : Fin k,
      (LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc c)).smulRight
        (Pi.single c 1 : Fin k → κ) := by
  refine LinearMap.ext fun x => funext fun j => ?_
  simp [firstCoords, LinearMap.funLeft_apply, Pi.single_apply]

/-- The left side of condition (1) at `(e₀, …, e_{k-1})`: `δ'(e'₀, …, e'_{k-1}) = 1`.
@isnad1 id=eq.0h2v.s11.33664350e2fa from=translated src=- shape=5fb97fdb vocab=33363e1b
-/
theorem evalFirst_detV'_compLinearMap :
    evalFirst ((detV' κ k).compLinearMap (firstCoords κ k)) = 1 := by
  rw [evalFirst_apply, AlternatingMap.compLinearMap_apply]
  have h : (fun i => firstCoords κ k (Pi.single (Fin.castSucc i) 1)) =
      ⇑(Pi.basisFun κ (Fin k)) := by
    funext i j
    simp [firstCoords, Pi.single_apply, Fin.castSucc_inj]
  rw [h, detV', Module.Basis.det_self]

/-- Lemma F.4: if `k! = 0` in `κ`, no `k`-linear map
`τ : Hom_κ(κ^{k+1}, κ^k)^k → Alt^k_κ(κ^{k+1}; κ)` satisfies both conditions (1) and (2).
@isnad1 id=not.1h2v.s11.5279a21fa6c9 from=translated src=- shape=3ee0d039 vocab=9cd40d4d
-/
theorem not_exists_fibre_map (hk : (k.factorial : κ) = 0) :
    ¬ ∃ τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
        ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ),
      FibreCondition1 κ k τ ∧ FibreCondition2 κ k τ := by
  rintro ⟨τ, h1, h2⟩
  have key := congrArg evalFirst h1
  rw [evalFirst_detV'_compLinearMap, firstCoords_eq_sum, MultilinearMap.map_sum,
    map_sum] at key
  change ∑ a : Fin k → Fin k, evalFirst (targetForm τ a
    (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (a r)))) = 1 at key
  have hsum : ∑ a : Fin k → Fin k, evalFirst (targetForm τ a
      (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (a r)))) =
      ∑ σ : Equiv.Perm (Fin k), evalFirst (targetForm τ σ
        (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (σ r)))) := by
    let e : Equiv.Perm (Fin k) ↪ (Fin k → Fin k) := ⟨fun σ => ⇑σ, DFunLike.coe_injective⟩
    calc _ = ∑ a ∈ Finset.univ.map e, evalFirst (targetForm τ a
          (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (a r)))) := by
          refine (Finset.sum_subset (Finset.subset_univ _) fun a _ ha => ?_).symm
          have hni : ¬ Injective a := fun hinj => ha (Finset.mem_map.2
            ⟨Equiv.ofBijective a (Finite.injective_iff_bijective.1 hinj), Finset.mem_univ _, rfl⟩)
          obtain ⟨s, hs⟩ : ∃ s, ∀ r, a r ≠ s := by
            by_contra hcon
            push Not at hcon
            exact hni (Finite.injective_iff_surjective.2 hcon)
          exact evalFirst_targetForm_eq_zero h2 hs _
      _ = _ := Finset.sum_map _ _ _
  have hE : ∀ α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ,
      evalFirst α = (-1) ^ k * wedgeEval (LinearMap.proj (R := κ) (φ := fun _ => κ)
        (Fin.last k)) α := by
    intro α
    rw [wedgeEval_proj_last, evalFirst_apply, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_mul]
  have hperm : ∀ σ : Equiv.Perm (Fin k), evalFirst (targetForm τ σ
      (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (σ r)))) =
      (-1) ^ k * lastSlotValue τ Fin.castSucc := by
    intro σ
    rw [evalFirst_targetForm_perm h2, hE]
    have ht : wedgeEval (LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.last k))
        (targetForm τ id
          (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.castSucc (σ r)))) =
        lastSlotValue τ (Fin.castSucc ∘ σ) := rfl
    have hs : ((Equiv.Perm.sign σ : ℤ) : κ) * ((Equiv.Perm.sign σ : ℤ) : κ) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
    rw [ht, lastSlotValue_comp_perm h2]
    linear_combination ((-1) ^ k * lastSlotValue τ Fin.castSucc) * hs
  rw [hsum, Finset.sum_congr rfl fun σ _ => hperm σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, hk, zero_mul] at key
  exact zero_ne_one key

end AlternatingAnalytic.FibreObstruction
