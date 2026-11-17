import Tengoku.Seed.LinearAlgebra.Alternating.Uncurry.Fin
import Tengoku.Seed.LinearAlgebra.StdBasis

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The functional `χ(w_α)` of an alternating `k`-form on `κ^{k+1}`

For an alternating `k`-form `α` on `κ^{k+1}` and a linear form `χ`, `wedgeEval χ α` is
`∑ᵢ (-1)^i χ(eᵢ) α(e₀, …, êᵢ, …, e_k)`, the paper's `χ(w_α)` in the proof of Lemma F.4. It is
the value at the standard basis of the alternating `(k+1)`-form
`AlternatingMap.alternatizeUncurryFin (χ.smulRight α)`, and the alternation of that form gives
the directions of (F.3) used in the paper: `ν(w_α) = 0` whenever `α` vanishes on `(ker ν)^k`,
for `ν = εᵃ` and `ν = εᵃ + εᵇ`.
-/

namespace AlternatingAnalytic.FibreObstruction

open Function

variable {κ : Type*} [Field κ] {k : ℕ}

/-- The paper's `χ(w_α)`: `∑ᵢ (-1)^i χ(eᵢ) α(e₀, …, êᵢ, …, e_k)`.-/
noncomputable def wedgeEval (χ : (Fin (k + 1) → κ) →ₗ[κ] κ)
    (α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) : κ :=
  AlternatingMap.alternatizeUncurryFin (χ.smulRight α) (fun i => Pi.single i 1)

/--
@isnad1 id=eq.0h5v.s10.09baaef753bc from=translated src=- shape=d35019ae vocab=4e774fd1
-/
theorem wedgeEval_add_left (χ χ' : (Fin (k + 1) → κ) →ₗ[κ] κ)
    (α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) :
    wedgeEval (χ + χ') α = wedgeEval χ α + wedgeEval χ' α := by
  simp only [wedgeEval, AlternatingMap.alternatizeUncurryFin_apply, LinearMap.smulRight_apply,
    LinearMap.add_apply, add_smul, AlternatingMap.add_apply, smul_add, Finset.sum_add_distrib]

/--
@isnad1 id=eq.0h5v.s10.2aa5ac427784 from=translated src=- shape=09bd7b0a vocab=4e774fd1
-/
theorem wedgeEval_add_right (χ : (Fin (k + 1) → κ) →ₗ[κ] κ)
    (α β : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) :
    wedgeEval χ (α + β) = wedgeEval χ α + wedgeEval χ β := by
  simp only [wedgeEval, AlternatingMap.alternatizeUncurryFin_apply, LinearMap.smulRight_apply,
    smul_add, AlternatingMap.add_apply, Finset.sum_add_distrib]

/-- If `α` vanishes on `(ker ν)^k` and all but one vector of `x` lie in `ker ν`, then the
alternating form `alternatizeUncurryFin (ν.smulRight α)` vanishes at `x`.
@isnad1 id=eq.2h6v.s11.b1b90c072ba2 from=translated src=- shape=e2b5b325 vocab=c4d239b8
-/
theorem alternatizeUncurryFin_smulRight_eq_zero {ν : (Fin (k + 1) → κ) →ₗ[κ] κ}
    {α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ}
    (hα : ∀ ξ : Fin k → (Fin (k + 1) → κ), (∀ r, ξ r ∈ LinearMap.ker ν) → α ξ = 0)
    (x : Fin (k + 1) → (Fin (k + 1) → κ)) (i₀ : Fin (k + 1))
    (hx : ∀ j, j ≠ i₀ → ν (x j) = 0) :
    AlternatingMap.alternatizeUncurryFin (ν.smulRight α) x = 0 := by
  rw [AlternatingMap.alternatizeUncurryFin_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smulRight_apply, AlternatingMap.smul_apply]
  by_cases hi : i = i₀
  · subst hi
    rw [hα (i.removeNth x) fun r => LinearMap.mem_ker.2 (hx _ (Fin.succAbove_ne _ _)), smul_zero,
      smul_zero]
  · rw [hx i hi, zero_smul, smul_zero]

/-- (F.3) for `ν = εᵃ`: if `α` vanishes on `(ker εᵃ)^k`, then `εᵃ(w_α) = 0`.
@isnad1 id=eq.1h4v.s10.af795443d28d from=translated src=- shape=0bbb5769 vocab=9c4f4401
-/
theorem wedgeEval_proj_eq_zero (a : Fin (k + 1)) {α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ}
    (hα : ∀ ξ : Fin k → (Fin (k + 1) → κ),
      (∀ r, ξ r ∈ LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) a)) → α ξ = 0) :
    wedgeEval (LinearMap.proj (R := κ) (φ := fun _ => κ) a) α = 0 :=
  alternatizeUncurryFin_smulRight_eq_zero hα _ a fun j hj => by
    simp [Ne.symm hj]

/-- (F.3) for `ν = εᵃ + εᵇ` with `a ≠ b`: if `α` vanishes on `(ker ν)^k`, then `ν(w_α) = 0`.
@isnad1 id=eq.2h5v.s11.085244440220 from=translated src=- shape=d60d3aa9 vocab=15e65053
-/
theorem wedgeEval_proj_add_eq_zero {a b : Fin (k + 1)} (hab : a ≠ b)
    {α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ}
    (hα : ∀ ξ : Fin k → (Fin (k + 1) → κ),
      (∀ r, ξ r ∈ LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b)) → α ξ = 0) :
    wedgeEval (LinearMap.proj (R := κ) (φ := fun _ => κ) a +
      LinearMap.proj (R := κ) (φ := fun _ => κ) b) α = 0 := by
  set F := AlternatingMap.alternatizeUncurryFin
    ((LinearMap.proj (R := κ) (φ := fun _ => κ) a +
      LinearMap.proj (R := κ) (φ := fun _ => κ) b).smulRight α)
  set e : Fin (k + 1) → (Fin (k + 1) → κ) := fun i => Pi.single i 1 with he
  have h1 : F e = F (update e b (e b - e a)) := by
    rw [F.map_update_sub, update_eq_self,
      F.map_eq_zero_of_eq (update e b (e a)) (i := a) (j := b) (by simp [update_of_ne hab]) hab,
      sub_zero]
  change F e = 0
  rw [h1]
  refine alternatizeUncurryFin_smulRight_eq_zero hα _ a fun j hj => ?_
  by_cases hjb : j = b
  · subst hjb
    simp [he, hab, Ne.symm hab]
  · simp [he, update_of_ne hjb, Ne.symm hj, Ne.symm hjb]

/-- At the last coordinate form (index `Fin.last k`), `ε^{k+1}(w_α) = (-1)^k α(e₀, …, e_{k-1})`.
@isnad1 id=eq.0h3v.s9.0983ae4882c4 from=translated src=- shape=944446d3 vocab=9f4c798e
-/
theorem wedgeEval_proj_last (α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) :
    wedgeEval (LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.last k)) α =
      (-1) ^ k * α (fun i => Pi.single (Fin.castSucc i) 1) := by
  rw [wedgeEval, AlternatingMap.alternatizeUncurryFin_apply,
    Finset.sum_eq_single (Fin.last k)]
  · simp [zsmul_eq_mul]
    rfl
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

end AlternatingAnalytic.FibreObstruction
