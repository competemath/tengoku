import Tengoku.Seed.LinearAlgebra.Determinant
import Tengoku.Seed.LinearAlgebra.Alternating.Basic
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.LinearAlgebra.StdBasis
import Tengoku.Seed.LinearAlgebra.Projection
import Tengoku.Seed.LinearAlgebra.Basis.VectorSpace
import Tengoku.Seed.Algebra.Module.Equiv.Basic
import Tengoku.Seed.Analysis.Normed.Field.Basic
import Tengoku.Seed.Data.Nat.Factorial.Basic
import Tengoku.Seed.Data.Finset.Defs
import Tengoku.Seed.Data.Set.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite family of pairs of subspaces (F.2)

Over a normed field `K` put `V = K^{k+1}`, `V' = K^k`. We define the forms `N`, the subspaces
`H'_{cd}`, `C'_s`, the family `F` of pairs `(Σ, Σ')`, the projection `g₀`, the determinant `δ'`
and condition (1), as in the statement of Lemma F.5, and prove the facts used for Theorem F.1:
`F` is finite, `δ'` vanishes on `(Σ')^k` for every pair (each `Σ'` is `H'_{cd}` with `c ≠ d` or
`C'_s`, so the matrix has two equal rows or a zero row), and every subspace is the kernel of an
idempotent linear map. `FiniteTestCertificate K k` states Lemma F.5, which enters the proof of
Theorem F.1 as a hypothesis.
-/

namespace AlternatingAnalytic.ChainSpaces

universe u

variable (K : Type u) [NormedField K] (k : ℕ)

/-- The set `N` of linear forms `ε^a` and `ε^a + ε^b` (`a < b`) on `V = K^{k+1}`.-/
def coordForms : Set ((Fin (k + 1) → K) →ₗ[K] K) :=
  Set.range (fun a : Fin (k + 1) => LinearMap.proj (R := K) (φ := fun _ => K) a) ∪
    {ν | ∃ a b : Fin (k + 1), a < b ∧
      ν = LinearMap.proj (R := K) (φ := fun _ => K) a +
        LinearMap.proj (R := K) (φ := fun _ => K) b}

/-- `H'_{cd} = {z ∈ K^k : z_c = z_d}`.-/
def colEq (c d : Fin k) : Submodule K (Fin k → K) :=
  LinearMap.ker
    (LinearMap.proj (R := K) (φ := fun _ => K) c - LinearMap.proj (R := K) (φ := fun _ => K) d)

/-- `C'_s = {z ∈ K^k : z_s = 0}`.-/
def colZero (s : Fin k) : Submodule K (Fin k → K) :=
  LinearMap.ker (LinearMap.proj (R := K) (φ := fun _ => K) s)

/-- The finite family `F` of pairs `(Σ, Σ')` from (F.2).-/
def pairFamily : Set (Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K)) :=
  {P | ∃ c d : Fin k, c < d ∧ P = (⊤, colEq K k c d)} ∪
    {P | ∃ ν ∈ coordForms K k, ∃ s : Fin k, P = (LinearMap.ker ν, colZero K k s)}

/-- The coordinate projection `g₀ : K^{k+1} → K^k` onto the first `k` coordinates.-/
def firstCoords : (Fin (k + 1) → K) →ₗ[K] (Fin k → K) :=
  LinearMap.funLeft K K Fin.castSucc

/-- The determinant `δ'` on `V' = K^k`.-/
noncomputable def detV' : (Fin k → K) [⋀^Fin k]→ₗ[K] K :=
  (Pi.basisFun K (Fin k)).det

/-- Condition (1): `τ(g₀, …, g₀) = δ' ∘ (g₀, …, g₀)`.-/
def FibreCondition1
    (τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
      ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K)) : Prop :=
  τ (fun _ => firstCoords K k) = (detV' K k).compLinearMap (firstCoords K k)

/-- The statement of Lemma F.5 (finite test certificate) for `K` in degree `k`: if `k! = 0` in
`K`, there are finite test sets for the pairs of `F` such that every `k`-linear `τ` satisfying
condition (1) has a test value of absolute value at least `1`.-/
def FiniteTestCertificate : Prop :=
  (k.factorial : K) = 0 →
    ∃ T : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K) →
        Finset ((Fin k → ((Fin (k + 1) → K) →ₗ[K] (Fin k → K))) × (Fin k → (Fin (k + 1) → K))),
      (∀ j ∈ pairFamily K k, ∀ t ∈ T j,
        (∀ r, j.1.map (t.1 r) ≤ j.2) ∧ ∀ r, t.2 r ∈ j.1) ∧
      ∀ τ : MultilinearMap K (fun _ : Fin k => (Fin (k + 1) → K) →ₗ[K] (Fin k → K))
          ((Fin (k + 1) → K) [⋀^Fin k]→ₗ[K] K),
        FibreCondition1 K k τ →
          ∃ j ∈ pairFamily K k, ∃ t ∈ T j, 1 ≤ ‖τ t.1 t.2‖

theorem coordForms_finite : (coordForms K k).Finite := by
  refine (Set.finite_range _).union ((Set.finite_range
    (fun ab : Fin (k + 1) × Fin (k + 1) => LinearMap.proj (R := K) (φ := fun _ => K) ab.1 +
      LinearMap.proj (R := K) (φ := fun _ => K) ab.2)).subset ?_)
  rintro ν ⟨a, b, -, rfl⟩
  exact ⟨(a, b), rfl⟩

/-- The family `F` is finite.-/
theorem pairFamily_finite : (pairFamily K k).Finite := by
  refine Set.Finite.union ((Set.finite_range
    (fun cd : Fin k × Fin k => ((⊤ : Submodule K (Fin (k + 1) → K)), colEq K k cd.1 cd.2))).subset
      ?_) ((((coordForms_finite K k).prod (Set.finite_univ (α := Fin k))).image
        (fun x => (LinearMap.ker x.1, colZero K k x.2))).subset ?_)
  · rintro P ⟨c, d, -, rfl⟩
    exact ⟨(c, d), rfl⟩
  · rintro P ⟨ν, hν, s, rfl⟩
    exact ⟨(ν, s), ⟨hν, Set.mem_univ _⟩, rfl⟩

theorem pairFamily_top_colEq {c d : Fin k} (hcd : c < d) :
    ((⊤ : Submodule K (Fin (k + 1) → K)), colEq K k c d) ∈ pairFamily K k :=
  Or.inl ⟨c, d, hcd, rfl⟩

theorem detV'_apply (z : Fin k → Fin k → K) :
    detV' K k z = Matrix.det (Matrix.of fun a r => z r a) := by
  rw [detV', Module.Basis.det_apply]
  congr 1

/-- `δ'` vanishes on `(Σ')^k` for every pair `(Σ, Σ')` of the family.-/
theorem detV'_eq_zero_of_mem {P : Submodule K (Fin (k + 1) → K) × Submodule K (Fin k → K)}
    (hP : P ∈ pairFamily K k) (z : Fin k → Fin k → K) (hz : ∀ r, z r ∈ P.2) :
    detV' K k z = 0 := by
  rw [detV'_apply]
  rcases hP with ⟨c, d, hcd, rfl⟩ | ⟨ν, -, s, rfl⟩
  · refine Matrix.det_zero_of_row_eq hcd.ne (funext fun r => ?_)
    have := hz r
    simp only [colEq, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply,
      sub_eq_zero] at this
    simpa only [Matrix.of_apply] using this
  · refine Matrix.det_eq_zero_of_row_eq_zero s fun r => ?_
    have := hz r
    simpa only [colZero, LinearMap.mem_ker, LinearMap.proj_apply, Matrix.of_apply] using this

/-- Every subspace is the kernel of an idempotent linear map.-/
theorem exists_idempotent_ker {V : Type*} [AddCommGroup V] [Module K V] (W : Submodule K V) :
    ∃ ρ : V →ₗ[K] V, (∀ v, ρ (ρ v) = ρ v) ∧ ∀ v, ρ v = 0 ↔ v ∈ W := by
  obtain ⟨C, hC⟩ := W.exists_isCompl
  refine ⟨C.projection W hC.symm, fun v => ?_, fun v => Submodule.projection_apply_eq_zero_iff _⟩
  exact congrArg (fun f : V →ₗ[K] V => f v) (Submodule.isIdempotentElem_projection hC.symm).eq

/-- `k! = 0` forces `k ≥ 2`.-/
theorem two_le_of_factorial_eq_zero {k : ℕ} (hk : (k.factorial : K) = 0) : 2 ≤ k := by
  by_contra h
  interval_cases k <;> simp at hk

end AlternatingAnalytic.ChainSpaces
