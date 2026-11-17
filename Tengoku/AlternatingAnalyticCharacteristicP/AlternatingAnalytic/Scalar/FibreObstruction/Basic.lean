import Tengoku.Seed.LinearAlgebra.Determinant
import Tengoku.Seed.LinearAlgebra.Alternating.Basic
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.LinearAlgebra.StdBasis
import Tengoku.Seed.Algebra.Module.Equiv.Basic
import Tengoku.Seed.Data.Nat.Factorial.Basic
import Tengoku.Seed.Tactic.LinearCombination
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.FibreObstruction.WedgeEval

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite fibre obstruction: the forms `B_a` and the target sign rule

Definitions and first steps for Lemma F.4: the family `F` of pairs from (F.2), the projection
`g₀`, the determinant `δ'` and the two conditions on a `k`-linear
`τ : Hom(κ^{k+1}, κ^k)^k → Alt^k(κ^{k+1}; κ)`. Evaluated at the basis tuple `(e₀, …, e_{k-1})`,
the forms `B_a(ψ) = τ(ψ₁ ⊗ e'_{a(1)}, …, ψ_k ⊗ e'_{a(k)})` vanish when `a` misses a target
coordinate, and `B_σ = sign(σ) B_id` for permutations `σ` (F.4).
-/

namespace AlternatingAnalytic.FibreObstruction

universe u

open Function

section Defs

variable (κ : Type u) [Field κ] (k : ℕ)

/-- The set `N` of linear forms `ε^a` and `ε^a + ε^b` (`a < b`) on `V = κ^{k+1}`.-/
def coordForms : Set ((Fin (k + 1) → κ) →ₗ[κ] κ) :=
  Set.range (fun a : Fin (k + 1) => LinearMap.proj (R := κ) (φ := fun _ => κ) a) ∪
    {ν | ∃ a b : Fin (k + 1), a < b ∧
      ν = LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b}

/-- `H'_{cd} = {z ∈ κ^k : z_c = z_d}`.-/
def colEq (c d : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker
    (LinearMap.proj (R := κ) (φ := fun _ => κ) c - LinearMap.proj (R := κ) (φ := fun _ => κ) d)

/-- `C'_s = {z ∈ κ^k : z_s = 0}`.-/
def colZero (s : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) s)

/-- The finite family `F` of pairs `(Σ, Σ')` from (F.2).-/
def pairFamily : Set (Submodule κ (Fin (k + 1) → κ) × Submodule κ (Fin k → κ)) :=
  {P | ∃ c d : Fin k, c < d ∧ P = (⊤, colEq κ k c d)} ∪
    {P | ∃ ν ∈ coordForms κ k, ∃ s : Fin k, P = (LinearMap.ker ν, colZero κ k s)}

/-- The coordinate projection `g₀ : κ^{k+1} → κ^k` onto the first `k` coordinates.-/
def firstCoords : (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ) :=
  LinearMap.funLeft κ κ Fin.castSucc

/-- The determinant `δ'` on `V' = κ^k`.-/
noncomputable def detV' : (Fin k → κ) [⋀^Fin k]→ₗ[κ] κ :=
  (Pi.basisFun κ (Fin k)).det

/-- Condition (1): `τ(g₀, …, g₀) = δ' ∘ (g₀, …, g₀)`.-/
def FibreCondition1
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  τ (fun _ => firstCoords κ k) = (detV' κ k).compLinearMap (firstCoords κ k)

/-- Condition (2): for every `(Σ, Σ') ∈ F`, `τ(g¹, …, gᵏ)` vanishes on `Σ^k` whenever every
`g^r` maps `Σ` into `Σ'`.-/
def FibreCondition2
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  ∀ P ∈ pairFamily κ k, ∀ g : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ)),
    (∀ r, P.1.map (g r) ≤ P.2) →
      ∀ ξ : Fin k → (Fin (k + 1) → κ), (∀ r, ξ r ∈ P.1) → τ g ξ = 0

end Defs

section Steps

variable {κ : Type u} [Field κ] {k : ℕ}
  (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
    ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ))

/-- `B_a(ψ) = τ(ψ₁ ⊗ e'_{a(1)}, …, ψ_k ⊗ e'_{a(k)})`, with `(φ ⊗ v)(x) = φ(x) v`.-/
noncomputable def targetForm (a : Fin k → Fin k) (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) :
    (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ :=
  τ (fun r => (ψ r).smulRight (Pi.single (a r) 1))

/-- Evaluation of an alternating `k`-form on `κ^{k+1}` at the basis tuple `(e₀, …, e_{k-1})`.-/
noncomputable def evalFirst : ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) →+ κ where
  toFun α := α (fun i => Pi.single (Fin.castSucc i) 1)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evalFirst_apply (α : (Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ) :
    evalFirst α = α (fun i => Pi.single (Fin.castSucc i) 1) := rfl

theorem smulRight_add_right (φ : (Fin (k + 1) → κ) →ₗ[κ] κ) (v w : Fin k → κ) :
    φ.smulRight (v + w) = φ.smulRight v + φ.smulRight w := by
  refine LinearMap.ext fun x => ?_
  simp [smul_add]

theorem update_smulRight_single (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) (a : Fin k → Fin k)
    (i : Fin k) (φ : (Fin (k + 1) → κ) →ₗ[κ] κ) (c : Fin k) :
    update (fun r => (ψ r).smulRight (Pi.single (a r) (1 : κ) : Fin k → κ)) i
        (φ.smulRight (Pi.single c 1)) =
      fun r => (update ψ i φ r).smulRight (Pi.single (update a i c r) 1 : Fin k → κ) := by
  funext r
  by_cases h : r = i
  · subst h
    simp
  · simp [update_of_ne h]

/-- Expansion of a multilinear map in two distinct slots.-/
theorem map_update_update_add {ι M N : Type*} [DecidableEq ι] [AddCommGroup M] [Module κ M]
    [AddCommGroup N] [Module κ N] (f : MultilinearMap κ (fun _ : ι => M) N) (m : ι → M)
    {i j : ι} (hij : i ≠ j) (x x' y y' : M) :
    f (update (update m j (y + y')) i (x + x')) =
      (f (update (update m j y) i x) + f (update (update m j y') i x)) +
        (f (update (update m j y) i x') + f (update (update m j y') i x')) := by
  rw [f.map_update_add, update_comm (β := fun _ => M) hij.symm (y + y') x,
    update_comm (β := fun _ => M) hij.symm (y + y') x', f.map_update_add, f.map_update_add,
    update_comm (β := fun _ => M) hij x y, update_comm (β := fun _ => M) hij x y',
    update_comm (β := fun _ => M) hij x' y, update_comm (β := fun _ => M) hij x' y']

variable {τ}

/-- A missing target coordinate: if `a` omits `s`, then `B_a(ψ)(e₀, …, e_{k-1}) = 0`
(condition (2) for the pair `(ker ε^k, C'_s)`).-/
theorem evalFirst_targetForm_eq_zero (h2 : FibreCondition2 κ k τ) {a : Fin k → Fin k} {s : Fin k}
    (hs : ∀ r, a r ≠ s) (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) :
    evalFirst (targetForm τ a ψ) = 0 := by
  refine h2 (LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) (Fin.last k)),
    colZero κ k s) (Or.inr ⟨_, Or.inl ⟨Fin.last k, rfl⟩, s, rfl⟩) _ (fun r => ?_) _ fun r => ?_
  · rw [Submodule.map_le_iff_le_comap]
    intro x _
    simp [colZero, hs r]
  · simp [Fin.castSucc_ne_last]

/-- Condition (2) for the pairs `(V, H'_{cd})`: if every `g r` takes values in `{z_c = z_d}`,
then `τ g = 0`.-/
theorem apply_eq_zero_of_colEq (h2 : FibreCondition2 κ k τ) {c d : Fin k} (hcd : c ≠ d)
    (g : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))) (hg : ∀ r x, g r x c = g r x d)
    (ξ : Fin k → (Fin (k + 1) → κ)) : τ g ξ = 0 := by
  rcases lt_or_gt_of_ne hcd with h | h
  · refine h2 (⊤, colEq κ k c d) (Or.inl ⟨c, d, h, rfl⟩) g (fun r => ?_) ξ
      fun _ => Submodule.mem_top
    rintro _ ⟨x, -, rfl⟩
    simp [colEq, hg r x]
  · refine h2 (⊤, colEq κ k d c) (Or.inl ⟨d, c, h, rfl⟩) g (fun r => ?_) ξ
      fun _ => Submodule.mem_top
    rintro _ ⟨x, -, rfl⟩
    simp [colEq, hg r x]

/-- Swapping two target coordinates of an injective `a` changes the sign of
`B_a(ψ)(e₀, …, e_{k-1})`.-/
theorem evalFirst_targetForm_comp_swap (h2 : FibreCondition2 κ k τ) {a : Fin k → Fin k}
    (ha : Injective a) {i j : Fin k} (hij : i ≠ j) (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) :
    evalFirst (targetForm τ (a ∘ Equiv.swap i j) ψ) = -evalFirst (targetForm τ a ψ) := by
  have hcd : a i ≠ a j := ha.ne hij
  set M : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ)) :=
    fun r => (ψ r).smulRight (Pi.single (a r) (1 : κ) : Fin k → κ) with hM
  have key : ∀ x y : Fin k, τ (update (update M j ((ψ j).smulRight (Pi.single y 1))) i
      ((ψ i).smulRight (Pi.single x 1))) = targetForm τ (update (update a j y) i x) ψ := by
    intro x y
    rw [hM, update_smulRight_single, update_smulRight_single]
    simp only [update_eq_self]
    rfl
  have hzero : evalFirst (τ (update (update M j ((ψ j).smulRight
      (Pi.single (a i) 1 + Pi.single (a j) 1))) i ((ψ i).smulRight
      (Pi.single (a i) 1 + Pi.single (a j) 1)))) = 0 := by
    rw [evalFirst_apply]
    refine apply_eq_zero_of_colEq h2 hcd _ (fun r x => ?_) _
    by_cases hri : r = i
    · subst hri
      simp [hcd, hcd.symm]
    · by_cases hrj : r = j
      · subst hrj
        simp [update_of_ne hri, hcd, hcd.symm]
      · simp [update_of_ne hri, update_of_ne hrj, hM, (ha.ne hri).symm, (ha.ne hrj).symm]
  rw [smulRight_add_right, smulRight_add_right, map_update_update_add τ M hij, key, key, key, key,
    map_add, map_add, map_add] at hzero
  have h1 : update (update a j (a j)) i (a i) = a := by simp
  have h2' : update (update a j (a i)) i (a j) = a ∘ Equiv.swap i j := by
    funext r
    by_cases hri : r = i
    · subst hri
      simp
    · by_cases hrj : r = j
      · subst hrj
        simp [update_of_ne hri]
      · simp [update_of_ne hri, update_of_ne hrj, Equiv.swap_apply_of_ne_of_ne hri hrj]
  have h3 : evalFirst (targetForm τ (update (update a j (a i)) i (a i)) ψ) = 0 := by
    refine evalFirst_targetForm_eq_zero h2 (s := a j) (fun r => ?_) ψ
    by_cases hri : r = i
    · subst hri
      simp [hcd]
    · by_cases hrj : r = j
      · subst hrj
        simp [update_of_ne hri, hcd]
      · simp [update_of_ne hri, update_of_ne hrj, ha.ne hrj]
  have h4 : evalFirst (targetForm τ (update (update a j (a j)) i (a j)) ψ) = 0 := by
    refine evalFirst_targetForm_eq_zero h2 (s := a i) (fun r => ?_) ψ
    by_cases hri : r = i
    · subst hri
      simp [hcd.symm]
    · by_cases hrj : r = j
      · subst hrj
        simp [update_of_ne hri, hcd.symm]
      · simp [update_of_ne hri, ha.ne hri]
  rw [h1, h2', h3, h4] at hzero
  linear_combination hzero

/-- (F.4) at `(e₀, …, e_{k-1})`: `B_σ = sign(σ) B_id` for permutations `σ`.-/
theorem evalFirst_targetForm_perm (h2 : FibreCondition2 κ k τ) (σ : Equiv.Perm (Fin k))
    (ψ : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] κ)) :
    evalFirst (targetForm τ σ ψ) =
      ((Equiv.Perm.sign σ : ℤ) : κ) * evalFirst (targetForm τ id ψ) := by
  induction σ using Equiv.Perm.swap_induction_on' generalizing ψ with
  | one => simp
  | mul_swap f x y hxy ih =>
    rw [Equiv.Perm.coe_mul, evalFirst_targetForm_comp_swap h2 f.injective hxy, ih,
      Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
    push_cast
    ring

end Steps

end AlternatingAnalytic.FibreObstruction
