import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.TestCertificate.BaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transfer of admissible tests from a subfield

Let `K / F` be a field extension. An admissible test over `F` for a pair `(Σ, Σ')` of the family
(F.2), that is maps `g^r : F^{k+1} → F^k` with `g^r Σ ⊆ Σ'` and vectors `ξ_r ∈ Σ`, becomes an
admissible test over `K` for the corresponding pair over `K` after base change. For the pairs
`(ker ν, C'_s)` this uses that a form vanishing on `ker ν` is a multiple of `ν`.
-/

namespace AlternatingAnalytic.TestCertificate

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {k : ℕ}

/-- Each form of `N` over `F` has a counterpart in `N` over `K` computing its base change.-/
theorem exists_coordForms_bcForm {ν : (Fin (k + 1) → F) →ₗ[F] F} (hν : ν ∈ coordForms F k) :
    ∃ ν' ∈ coordForms K k, ∀ x, ν' x = bcForm ν x := by
  rcases hν with ⟨a, rfl⟩ | ⟨a, b, hab, rfl⟩
  · exact ⟨_, Or.inl ⟨a, rfl⟩, fun x => (bcForm_proj a x).symm⟩
  · refine ⟨_, Or.inr ⟨a, b, hab, rfl⟩, fun x => ?_⟩
    rw [bcForm_add, bcForm_proj, bcForm_proj]
    rfl

/-- An admissible test over `F` for a pair of (F.2) base changes to an admissible test over `K`
for the corresponding pair.-/
theorem exists_pairFamily_transfer {P : Submodule F (Fin (k + 1) → F) × Submodule F (Fin k → F)}
    (hP : P ∈ pairFamily F k) {g : Fin k → ((Fin (k + 1) → F) →ₗ[F] (Fin k → F))}
    (hg : ∀ r, P.1.map (g r) ≤ P.2) {ξ : Fin k → (Fin (k + 1) → F)} (hξ : ∀ r, ξ r ∈ P.1) :
    ∃ j ∈ pairFamily K k, (∀ r, j.1.map (bcMap (K := K) (g r)) ≤ j.2) ∧
      ∀ r, (incl (ξ r) : Fin (k + 1) → K) ∈ j.1 := by
  rcases hP with ⟨c, d, hcd, rfl⟩ | ⟨ν, hν, s, rfl⟩
  · refine ⟨(⊤, colEq K k c d), Or.inl ⟨c, d, hcd, rfl⟩, fun r => ?_, fun r => Submodule.mem_top⟩
    rintro _ ⟨x, -, rfl⟩
    have hker : LinearMap.ker (0 : (Fin (k + 1) → F) →ₗ[F] F) ≤
        LinearMap.ker ((LinearMap.proj (R := F) (φ := fun _ => F) c -
          LinearMap.proj (R := F) (φ := fun _ => F) d).comp (g r)) :=
      fun y _ => hg r (Submodule.mem_map_of_mem Submodule.mem_top)
    have h := bcForm_eq_zero_of_ker_le hker (x := x) (bcForm_zero x)
    show bcMap (g r) x c - bcMap (g r) x d = 0
    rw [bcMap_apply, bcMap_apply, ← bcForm_sub, ← LinearMap.sub_comp]
    exact h
  · obtain ⟨ν', hν', hν'eq⟩ := exists_coordForms_bcForm (K := K) hν
    refine ⟨(LinearMap.ker ν', colZero K k s), Or.inr ⟨ν', hν', s, rfl⟩, fun r => ?_, fun r => ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hker : LinearMap.ker ν ≤
          LinearMap.ker ((LinearMap.proj (R := F) (φ := fun _ => F) s).comp (g r)) :=
        fun y hy => hg r (Submodule.mem_map_of_mem hy)
      have hx' : bcForm ν x = 0 := by rw [← hν'eq]; exact hx
      show bcMap (g r) x s = 0
      rw [bcMap_apply]
      exact bcForm_eq_zero_of_ker_le hker hx'
    · show ν' (incl (ξ r)) = 0
      rw [hν'eq, bcForm_incl, LinearMap.mem_ker.mp (hξ r), map_zero]

end AlternatingAnalytic.TestCertificate
