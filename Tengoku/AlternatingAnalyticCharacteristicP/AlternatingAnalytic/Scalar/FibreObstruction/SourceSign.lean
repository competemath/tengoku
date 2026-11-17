import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.FibreObstruction.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite fibre obstruction: the source sign rule

Second half of the proof of Lemma F.4. For `τ` satisfying condition (2), the paper's
`(k+1)`-linear form `β(ψ₁, …, ψ_k; χ) = χ(w_{B(ψ)})`, with `B = B_id`, vanishes when the `s`th
argument and the last argument are the same `ν ∈ N` (condition (2) for `(ker ν, C'_s)` and (F.3)).
Expanding at `ν = εᵃ + εᵇ` makes `β` antisymmetric under exchanging a coordinate form in a slot
with the one in the last slot; three such exchanges swap two of the first `k` slots. Hence
`t(f) = β(ε^{f(1)}, …, ε^{f(k)}; ε^{k+1})` satisfies `t(f ∘ σ) = sign(σ) t(f)` for `σ ∈ S_k`.
-/

namespace AlternatingAnalytic.FibreObstruction

universe u

open Function

variable {κ : Type u} [Field κ] {k : ℕ}
  {τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
    ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)}

variable (τ) in
/-- The paper's `(k+1)`-linear form `β(ψ₁, …, ψ_k; χ) = χ(w_{B(ψ)})`.-/
noncomputable def sourceForm (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ))
    (χ : (Fin (k + 1) → κ) →ₗ[κ] κ) : κ :=
  wedgeEval χ (targetForm τ id ψ)

theorem smulRight_add_left (φ φ' : (Fin (k + 1) → κ) →ₗ[κ] κ) (v : Fin k → κ) :
    (φ + φ').smulRight v = φ.smulRight v + φ'.smulRight v := by
  refine LinearMap.ext fun x => ?_
  simp [add_smul]

theorem targetForm_id_update (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k)
    (ν : (Fin (k + 1) → κ) →ₗ[κ] κ) :
    targetForm τ id (update ψ s ν) =
      τ (update (fun r => (ψ r).smulRight (Pi.single (id r) (1 : κ) : Fin k → κ)) s
        (ν.smulRight (Pi.single (id s) 1))) := by
  rw [update_smulRight_single]
  simp only [update_eq_self]
  rfl

theorem sourceForm_update_add (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k)
    (μ ρ χ : (Fin (k + 1) → κ) →ₗ[κ] κ) :
    sourceForm τ (update ψ s (μ + ρ)) χ =
      sourceForm τ (update ψ s μ) χ + sourceForm τ (update ψ s ρ) χ := by
  simp only [sourceForm, targetForm_id_update, smulRight_add_left, τ.map_update_add,
    wedgeEval_add_right]

theorem sourceForm_add_right (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ))
    (χ χ' : (Fin (k + 1) → κ) →ₗ[κ] κ) :
    sourceForm τ ψ (χ + χ') = sourceForm τ ψ χ + sourceForm τ ψ χ' :=
  wedgeEval_add_left _ _ _

/-- Condition (2) for `(ker ν, C'_s)`: `B(ψ)` with `ν` in slot `s` vanishes on `(ker ν)^k`.-/
theorem targetForm_update_apply_eq_zero (h2 : FibreCondition2 κ k τ)
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k) {ν : (Fin (k + 1) → κ) →ₗ[κ] κ}
    (hν : ν ∈ coordForms κ k) (ξ : Fin k → (Fin (k + 1) → κ))
    (hξ : ∀ r, ξ r ∈ LinearMap.ker ν) : targetForm τ id (update ψ s ν) ξ = 0 := by
  refine h2 (LinearMap.ker ν, colZero κ k s) (Or.inr ⟨ν, hν, s, rfl⟩) _ (fun r => ?_) ξ hξ
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  by_cases hrs : r = s
  · subst hrs
    simp [colZero, LinearMap.mem_ker.1 hx]
  · simp [colZero, hrs]

theorem sourceForm_update_self_proj (h2 : FibreCondition2 κ k τ)
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k) (a : Fin (k + 1)) :
    sourceForm τ (update ψ s (LinearMap.proj (R := κ) (φ := fun _ => κ) a))
      (LinearMap.proj (R := κ) (φ := fun _ => κ) a) = 0 :=
  wedgeEval_proj_eq_zero a (targetForm_update_apply_eq_zero h2 ψ s (Or.inl ⟨a, rfl⟩))

theorem sourceForm_update_self_proj_add (h2 : FibreCondition2 κ k τ)
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k) {a b : Fin (k + 1)} (hab : a ≠ b) :
    sourceForm τ (update ψ s (LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b))
      (LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b) = 0 := by
  have hν : LinearMap.proj (R := κ) (φ := fun _ => κ) a +
      LinearMap.proj (R := κ) (φ := fun _ => κ) b ∈ coordForms κ k := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact Or.inr ⟨a, b, h, rfl⟩
    · exact Or.inr ⟨b, a, h, add_comm _ _⟩
  exact wedgeEval_proj_add_eq_zero hab (targetForm_update_apply_eq_zero h2 ψ s hν)

/-- Exchanging the coordinate forms in slot `s` and in the last slot changes the sign of `β`.-/
theorem sourceForm_update_swap (h2 : FibreCondition2 κ k τ)
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (s : Fin k) (a b : Fin (k + 1)) :
    sourceForm τ (update ψ s (LinearMap.proj (R := κ) (φ := fun _ => κ) a))
        (LinearMap.proj (R := κ) (φ := fun _ => κ) b) =
      -sourceForm τ (update ψ s (LinearMap.proj (R := κ) (φ := fun _ => κ) b))
        (LinearMap.proj (R := κ) (φ := fun _ => κ) a) := by
  by_cases hab : a = b
  · subst hab
    rw [sourceForm_update_self_proj h2, neg_zero]
  · have h := sourceForm_update_self_proj_add h2 ψ s hab
    rw [sourceForm_update_add, sourceForm_add_right, sourceForm_add_right,
      sourceForm_update_self_proj h2, sourceForm_update_self_proj h2] at h
    linear_combination h

/-- Exchanging the coordinate forms in two of the first `k` slots changes the sign of `β`.-/
theorem sourceForm_update_update_swap (h2 : FibreCondition2 κ k τ)
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) {i j : Fin k} (hij : i ≠ j) (a b c : Fin (k + 1)) :
    sourceForm τ (update (update ψ i (LinearMap.proj (R := κ) (φ := fun _ => κ) a)) j
        (LinearMap.proj (R := κ) (φ := fun _ => κ) b))
        (LinearMap.proj (R := κ) (φ := fun _ => κ) c) =
      -sourceForm τ (update (update ψ i (LinearMap.proj (R := κ) (φ := fun _ => κ) b)) j
        (LinearMap.proj (R := κ) (φ := fun _ => κ) a))
        (LinearMap.proj (R := κ) (φ := fun _ => κ) c) := by
  rw [update_comm hij, sourceForm_update_swap h2, update_comm hij.symm,
    sourceForm_update_swap h2, update_comm hij, sourceForm_update_swap h2, update_comm hij.symm,
    neg_neg]

variable (τ) in
/-- `t(f) = β(ε^{f(1)}, …, ε^{f(k)}; ε^{k+1})` for `f : [k] → [k+1]`.-/
noncomputable def lastSlotValue (f : Fin k → Fin (k + 1)) : κ :=
  sourceForm τ (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (f r))
    (LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.last k))

theorem lastSlotValue_comp_swap (h2 : FibreCondition2 κ k τ) (f : Fin k → Fin (k + 1))
    {i j : Fin k} (hij : i ≠ j) :
    lastSlotValue τ (f ∘ Equiv.swap i j) = -lastSlotValue τ f := by
  set ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ) :=
    fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) (f r) with hψ
  have e1 : (fun r => LinearMap.proj (R := κ) (φ := fun _ => κ) ((f ∘ Equiv.swap i j) r)) =
      update (update ψ i (LinearMap.proj (R := κ) (φ := fun _ => κ) (f j))) j
        (LinearMap.proj (R := κ) (φ := fun _ => κ) (f i)) := by
    funext r
    by_cases hrj : r = j
    · subst hrj
      simp
    · by_cases hri : r = i
      · subst hri
        simp [update_of_ne hrj]
      · simp [update_of_ne hri, update_of_ne hrj, hψ, Equiv.swap_apply_of_ne_of_ne hri hrj]
  have e2 : update (update ψ i (LinearMap.proj (R := κ) (φ := fun _ => κ) (f i))) j
      (LinearMap.proj (R := κ) (φ := fun _ => κ) (f j)) = ψ := by
    rw [hψ]
    simp only [update_eq_self]
  rw [lastSlotValue, lastSlotValue, e1, sourceForm_update_update_swap h2 _ hij, e2]

/-- The source sign rule: `t(f ∘ σ) = sign(σ) t(f)` for `σ ∈ S_k`.-/
theorem lastSlotValue_comp_perm (h2 : FibreCondition2 κ k τ) (f : Fin k → Fin (k + 1))
    (σ : Equiv.Perm (Fin k)) :
    lastSlotValue τ (f ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : κ) * lastSlotValue τ f := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap g x y hxy ih =>
    rw [Equiv.Perm.coe_mul, ← comp_assoc, lastSlotValue_comp_swap h2 _ hxy, ih,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    push_cast
    ring

end AlternatingAnalytic.FibreObstruction
