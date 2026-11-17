import Tengoku.Seed.Analysis.Normed.Operator.ContinuousLinearMap
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.Tails.OneVariable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Bounded multilinear forms on `ℓ^∞(ℕ)`: basic tools

`IsBddML Φ C` says that a function `Φ` of `d` arguments in `Linf 𝕜 = ℕ →ᵇ 𝕜` is additive and
homogeneous in each argument and bounded by `C * ∏ j, ‖u j‖`. Tools for the induction on the
arity in `AlternatingAnalytic.Scalar.Tails.Multilinear`: the truncations
`headOf` and `tailOf`, the expansion of `headOf` in unit vectors, freezing one slot
(`freezeSlot`), the functional in one slot (`slotCLM`), and the statement `TailAt 𝕜 d` of the tail
property in arity `d`.
-/

namespace AlternatingAnalytic.Tails

open BoundedContinuousFunction Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- A bounded function of `d` arguments in `ℓ^∞`, additive and homogeneous in each argument.-/
structure IsBddML {d : ℕ} (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ) : Prop where
  add : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜),
    Φ (Function.update u j (v + w)) = Φ (Function.update u j v) + Φ (Function.update u j w)
  smul : ∀ (u : Fin d → Linf 𝕜) (j : Fin d) (c : 𝕜) (v : Linf 𝕜),
    Φ (Function.update u j (c • v)) = c * Φ (Function.update u j v)
  bound : ∀ u : Fin d → Linf 𝕜, ‖Φ u‖ ≤ C * ∏ j, ‖u j‖

/-! ### Elementary consequences of `IsBddML` -/

namespace IsBddML

variable {d : ℕ} {Φ : (Fin d → Linf 𝕜) → 𝕜} {C : ℝ}

/-- If one of the arguments is zero, the value is zero.-/
theorem eq_zero_of_eq_zero (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d)
    (hj : u j = 0) : Φ u = 0 := by
  have h0 : Φ (Function.update u j ((0 : 𝕜) • u j)) = (0 : 𝕜) * Φ (Function.update u j (u j)) :=
    hΦ.smul u j 0 (u j)
  rwa [zero_smul, ← hj, Function.update_eq_self, zero_mul] at h0

/-- Updating a slot by zero gives zero.
@isnad1 id=eq.1h6v.s6.c7a9791509a8 from=translated src=- shape=e07d989f vocab=76137055
-/
theorem update_zero (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Φ (Function.update u j 0) = 0 :=
  hΦ.eq_zero_of_eq_zero _ j (Function.update_self _ _ _)

/--
@isnad1 id=eq.1h8v.s7.49bd92831a97 from=translated src=- shape=709b004d vocab=e65c727f
-/
theorem update_sub (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v w : Linf 𝕜) :
    Φ (Function.update u j (v - w)) = Φ (Function.update u j v) - Φ (Function.update u j w) := by
  have := hΦ.add u j (v - w) w
  rw [sub_add_cancel] at this
  rw [this]
  ring

/--
@isnad1 id=eq.1h9v.s7.67a551414427 from=translated src=- shape=c1bd9d04 vocab=2eb21010
-/
theorem update_sum (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) {ι : Type*}
    (s : Finset ι) (f : ι → Linf 𝕜) :
    Φ (Function.update u j (∑ i ∈ s, f i)) = ∑ i ∈ s, Φ (Function.update u j (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hΦ.update_zero u j
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hΦ.add, ih]

end IsBddML

/-! ### Truncations in `ℓ^∞` -/

/--
@isnad1 id=eq.0h4v.s7.c8803bf51759 from=translated src=- shape=2b6e3d21 vocab=24d07775
-/
theorem Linf.add_apply (f g : Linf 𝕜) (k : ℕ) : (f + g) k = f k + g k := rfl

/--
@isnad1 id=eq.0h5v.s7.c6ba9ce15238 from=translated src=- shape=5a885f43 vocab=65378d83
-/
theorem Linf.sum_apply {ι : Type*} (s : Finset ι) (f : ι → Linf 𝕜) (k : ℕ) :
    (∑ i ∈ s, f i) k = ∑ i ∈ s, f i k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

/-- `headOf M x` keeps the coordinates `< M` of `x` and kills the others.-/
noncomputable def headOf (M : ℕ) (x : Linf 𝕜) : Linf 𝕜 :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun i => if i < M then x i else 0) ‖x‖ (by
      intro i
      split_ifs
      · exact x.norm_coe_le_norm i
      · simp)

/--
@isnad1 id=eq.0h4v.s6.67b345ffaa36 from=translated src=- shape=ec6839c2 vocab=fc90dd3a
-/
@[simp] theorem headOf_apply (M : ℕ) (x : Linf 𝕜) (i : ℕ) :
    headOf M x i = if i < M then x i else 0 := rfl

/-- `tailOf M x` kills the coordinates `< M` of `x` and keeps the others.-/
noncomputable def tailOf (M : ℕ) (x : Linf 𝕜) : Linf 𝕜 := x - headOf M x

/--
@isnad1 id=eq.0h4v.s6.d74215ac66b0 from=translated src=- shape=489c3104 vocab=ce50157a
-/
theorem tailOf_apply (M : ℕ) (x : Linf 𝕜) (i : ℕ) :
    tailOf M x i = if i < M then 0 else x i := by
  show x i - (if i < M then x i else 0) = _
  split_ifs <;> simp

/--
@isnad1 id=eq.1h4v.s6.a407115f5b61 from=translated src=- shape=75803838 vocab=38074652
-/
theorem tailOf_apply_of_lt {M : ℕ} (x : Linf 𝕜) {i : ℕ} (hi : i < M) : tailOf M x i = 0 := by
  simp [tailOf_apply, hi]

/--
@isnad1 id=eq.0h3v.s6.5d505f378da3 from=translated src=- shape=a01a72aa vocab=fdb1b529
-/
theorem headOf_add_tailOf (M : ℕ) (x : Linf 𝕜) : headOf M x + tailOf M x = x := by
  simp [tailOf]

/--
@isnad1 id=le.0h3v.s5.ee0e2ac5c19d from=translated src=- shape=ddc28be3 vocab=8f0fe1fb
-/
theorem norm_headOf_le (M : ℕ) (x : Linf 𝕜) : ‖headOf M x‖ ≤ ‖x‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg x)]
  intro i
  rw [headOf_apply]
  split_ifs
  · exact x.norm_coe_le_norm i
  · simp

/--
@isnad1 id=le.0h3v.s5.5d16683886e9 from=translated src=- shape=ddc28be3 vocab=9ea8a197
-/
theorem norm_tailOf_le (M : ℕ) (x : Linf 𝕜) : ‖tailOf M x‖ ≤ ‖x‖ := by
  rw [BoundedContinuousFunction.norm_le (norm_nonneg x)]
  intro i
  rw [tailOf_apply]
  split_ifs
  · simp
  · exact x.norm_coe_le_norm i

/-- If `x` already vanishes below `M`, truncating changes nothing.
@isnad1 id=eq.1h3v.s6.baf2adaef4b9 from=translated src=- shape=199c085d vocab=38074652
-/
theorem tailOf_eq_self {M : ℕ} {x : Linf 𝕜} (h : ∀ i < M, x i = 0) : tailOf M x = x := by
  ext i
  rw [tailOf_apply]
  split_ifs with hi
  · exact (h i hi).symm
  · rfl

/-! ### Unit vectors -/

/--
@isnad1 id=eq.0h3v.s7.1f455993dafb from=translated src=- shape=f24414d8 vocab=1ea1ba65
-/
theorem headOf_eq_sum (M : ℕ) (x : Linf 𝕜) :
    headOf M x = ∑ i ∈ Finset.range M, x i • basisVec 𝕜 i := by
  ext k
  rw [headOf_apply, Linf.sum_apply]
  simp only [BoundedContinuousFunction.smul_apply, smul_eq_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single_of_mem k (Finset.mem_range.mpr hk)]
    · rw [basisVec_apply_self, mul_one]
    · intro b _ hb
      rw [basisVec_apply_ne (Ne.symm hb), mul_zero]
  · symm
    refine Finset.sum_eq_zero ?_
    intro b hb
    have hb' : b < M := Finset.mem_range.mp hb
    rw [basisVec_apply_ne (show k ≠ b by omega), mul_zero]

/-! ### Freezing a slot, and the functional in one slot -/

/-- Freeze the `j`-th slot of a `(d+1)`-linear form at `v`, obtaining a `d`-linear form.-/
def freezeSlot {d : ℕ} (Φ : (Fin (d + 1) → Linf 𝕜) → 𝕜) (j : Fin (d + 1)) (v : Linf 𝕜) :
    (Fin d → Linf 𝕜) → 𝕜 := fun u => Φ (j.insertNth v u)

/--
@isnad1 id=isbddml.1h6v.s6.94fcbff5014c from=translated src=- shape=d2002d3a vocab=1a69b3bc
-/
theorem IsBddML.freezeSlot {d : ℕ} {Φ : (Fin (d + 1) → Linf 𝕜) → 𝕜} {C : ℝ} (hΦ : IsBddML Φ C)
    (j : Fin (d + 1)) (v : Linf 𝕜) : IsBddML (Tails.freezeSlot Φ j v) (C * ‖v‖) where
  add := by
    intro u k a b
    simp only [Tails.freezeSlot, Fin.insertNth_update]
    exact hΦ.add _ _ a b
  smul := by
    intro u k c a
    simp only [Tails.freezeSlot, Fin.insertNth_update]
    exact hΦ.smul _ _ c a
  bound := by
    intro u
    refine (hΦ.bound (j.insertNth v u)).trans_eq ?_
    rw [Fin.prod_univ_succAbove _ j]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    ring

variable {d : ℕ} {Φ : (Fin d → Linf 𝕜) → 𝕜} {C : ℝ}

/-- The linear map obtained by letting the `j`-th slot vary.-/
noncomputable def slotMap (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Linf 𝕜 →ₗ[𝕜] 𝕜 where
  toFun v := Φ (Function.update u j v)
  map_add' := hΦ.add u j
  map_smul' := by intro c v; simpa using hΦ.smul u j c v

/--
@isnad1 id=le.1h7v.s8.97a58eb05797 from=translated src=- shape=38679a39 vocab=415ae91c
-/
theorem slotMap_bound (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v : Linf 𝕜) :
    ‖slotMap hΦ u j v‖ ≤ (C * ∏ i ∈ Finset.univ \ {j}, ‖u i‖) * ‖v‖ := by
  classical
  refine (hΦ.bound (Function.update u j v)).trans_eq ?_
  have hfun : (fun i => ‖(Function.update u j v) i‖)
      = Function.update (fun i => ‖u i‖) j ‖v‖ := by
    funext i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Function.update_of_ne hij]
  rw [show (∏ i, ‖(Function.update u j v) i‖) = ∏ i, Function.update (fun i => ‖u i‖) j ‖v‖ i by
        rw [hfun]]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
  ring

/-- The continuous linear functional obtained by letting the `j`-th slot vary.-/
noncomputable def slotCLM (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) :
    Linf 𝕜 →L[𝕜] 𝕜 :=
  (slotMap hΦ u j).mkContinuous (C * ∏ i ∈ Finset.univ \ {j}, ‖u i‖) (slotMap_bound hΦ u j)

/--
@isnad1 id=eq.1h7v.s8.61f1d8c85a29 from=translated src=- shape=89a4d3ed vocab=821ac8b0
-/
@[simp] theorem slotCLM_apply (hΦ : IsBddML Φ C) (u : Fin d → Linf 𝕜) (j : Fin d) (v : Linf 𝕜) :
    slotCLM hΦ u j v = Φ (Function.update u j v) := rfl

/-- Updating a slot is the same as inserting into the tuple with that slot removed.
@isnad1 id=eq.0h5v.s7.b85b156a4f12 from=translated src=- shape=1df43fe0 vocab=30cfbbcd
-/
theorem update_eq_insertNth {D : ℕ} (u : Fin (D + 1) → Linf 𝕜) (j : Fin (D + 1)) (v : Linf 𝕜) :
    Function.update u j v = j.insertNth v (fun l => u (j.succAbove l)) := by
  funext m
  induction m using j.succAboveCases with
  | x => simp
  | p l =>
      rw [Function.update_of_ne (Fin.succAbove_ne j l), Fin.insertNth_apply_succAbove]

variable (𝕜) in
/-- The conclusion of `tail_multilinear` at a fixed arity.-/
def TailAt (d : ℕ) : Prop :=
  ∀ (Φ : (Fin d → Linf 𝕜) → 𝕜) (C : ℝ), IsBddML Φ C → ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ u : Fin d → Linf 𝕜, (∀ j, ‖u j‖ ≤ 1) →
      (∃ j, ∀ i < N, u j i = 0) → ‖Φ u‖ ≤ ε

/--
@isnad1 id=tailat.0h1v.s3.817ff956041f from=translated src=- shape=89d4eb60 vocab=45d04000
-/
theorem tailAt_zero : TailAt 𝕜 0 := by
  intro Φ C hΦ ε hε
  refine ⟨0, ?_⟩
  rintro u - ⟨j, -⟩
  exact j.elim0

end AlternatingAnalytic.Tails
