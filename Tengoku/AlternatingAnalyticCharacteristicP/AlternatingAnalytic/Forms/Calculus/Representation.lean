import Tengoku.Seed.LinearAlgebra.Alternating.Basic
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.StdBasis
import Tengoku.Seed.Data.Fin.Tuple.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Alternating maps on `R^N` are alternatizations

Over any commutative ring `R`, every scalar alternating map `μ` on the free module `Fin N → R`
is the alternatization of a multilinear map (`exists_alternatization_eq`). Together with
`tupleMap v : (Fin N → R) →ₗ M`, which sends the standard basis to a tuple `v`, this reduces
identities between alternating maps evaluated at `v` to identities between alternatizations.
-/

open Equiv

namespace AlternatingAnalytic.Forms

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Every scalar alternating map on `Fin N → R` is an alternatization.-/
theorem exists_alternatization_eq {N k : ℕ} (μ : (Fin N → R) [⋀^Fin k]→ₗ[R] R) :
    ∃ a : MultilinearMap R (fun _ : Fin k => Fin N → R) R,
      MultilinearMap.alternatization a = μ := by
  classical
  let e := Pi.basisFun R (Fin N)
  let S : Finset (Fin k → Fin N) := Finset.univ.filter fun f => StrictMono f
  refine ⟨∑ f ∈ S, μ (fun t => e (f t)) •
      (MultilinearMap.mkPiAlgebra R (Fin k) R).compLinearMap (fun t => LinearMap.proj (f t)), ?_⟩
  refine e.ext_alternating fun g hg => ?_
  have key : ∀ σ : Perm (Fin k),
      (∑ f ∈ S, μ (fun t => e (f t)) •
        (MultilinearMap.mkPiAlgebra R (Fin k) R).compLinearMap
          (fun t => LinearMap.proj (f t))) (fun i => e (g (σ i))) =
        if StrictMono (g ∘ σ) then (Perm.sign σ : ℤ) • μ (fun i => e (g i)) else 0 := by
    intro σ
    simp only [sum_apply, smul_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, LinearMap.proj_apply, e, Pi.basisFun_apply,
      Pi.single_apply, Finset.prod_boole, Finset.mem_univ, true_implies, smul_eq_mul, mul_ite,
      mul_one, mul_zero]
    have hfun : ∀ f : Fin k → Fin N, (∀ t, f t = g (σ t)) ↔ f = g ∘ σ :=
      fun f => ⟨fun h => funext h, fun h t => congrFun h t⟩
    simp only [hfun, Finset.sum_ite_eq', S, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs with h
    · have := μ.map_perm (fun i => Pi.single (g i) (1 : R)) σ
      simp only [Function.comp_def] at this ⊢
      rw [this, Units.smul_def]
    · rfl
  rw [MultilinearMap.alternatization_apply]
  simp only [MultilinearMap.domDomCongr_apply, key, smul_ite, smul_zero]
  have hsort : StrictMono (g ∘ Tuple.sort g) :=
    (Tuple.monotone_sort g).strictMono_of_injective (hg.comp (Tuple.sort g).injective)
  rw [Finset.sum_eq_single (Tuple.sort g)]
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hsort), ← Units.smul_def, ← mul_smul,
      Int.units_mul_self, one_smul]
  · intro σ _ hσ
    refine ite_eq_right_of_eq_false _ _ (eq_false fun h => ?_)
    apply hσ
    have := Tuple.unique_monotone h.monotone hsort.monotone
    ext i
    exact congrArg Fin.val (hg (congrFun this i))
  · simp

/-- The linear map `R^N → M` sending the `i`-th standard basis vector to `v i`.-/
noncomputable def tupleMap {N : ℕ} (v : Fin N → M) : (Fin N → R) →ₗ[R] M :=
  Fintype.linearCombination R v

/-- `tupleMap v` sends the `i`-th basis vector to `v i`.-/
theorem tupleMap_single {N : ℕ} (v : Fin N → M) (i : Fin N) :
    tupleMap (R := R) v (Pi.single i 1) = v i := by
  classical
  simp [tupleMap, Fintype.linearCombination_apply_single]

/-- Evaluating an alternating map at a reindexed tuple, through `tupleMap`.-/
theorem compLinearMap_tupleMap_apply {N' : Type*} [AddCommGroup N'] [Module R N'] {ι : Type*}
    {N : ℕ} (F : M [⋀^ι]→ₗ[R] N') (v : Fin N → M) (τ : ι → Fin N) :
    F.compLinearMap (tupleMap v) (fun i => Pi.single (τ i) (1 : R)) = F (v ∘ τ) := by
  simp only [AlternatingMap.compLinearMap_apply, tupleMap_single]
  rfl

/-- Evaluating an alternating map at a tuple, through `tupleMap`.-/
theorem compLinearMap_tupleMap_apply_self {N' : Type*} [AddCommGroup N'] [Module R N'] {N : ℕ}
    (F : M [⋀^Fin N]→ₗ[R] N') (v : Fin N → M) :
    F.compLinearMap (tupleMap v) (fun i => Pi.single i (1 : R)) = F v :=
  compLinearMap_tupleMap_apply F v id

end AlternatingAnalytic.Forms
