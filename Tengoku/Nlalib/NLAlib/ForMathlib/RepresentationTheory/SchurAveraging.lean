import Tengoku.Seed.RepresentationTheory.Invariants
import Tengoku.Seed.RepresentationTheory.Irreducible
import Tengoku.Seed.LinearAlgebra.Trace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Finite Schur averaging

The average of conjugates of an arbitrary linear map is an actual intertwiner.
Schur's lemma makes it zero between inequivalent irreducibles and scalar on
an irreducible representation over an algebraically closed field.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Finset Module
namespace Representation

variable {k G V W : Type*} [Field k] [CharZero k] [Group G] [Fintype G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- Average an arbitrary linear map over a finite group to obtain an
intertwining map, without assuming equivariance of the input.-/
def averagedIntertwiningMap (ρ : Representation k G V) (σ : Representation k G W)
    (M : V →ₗ[k] W) : IntertwiningMap ρ σ := by
  letI : Invertible (Fintype.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact invariantsEquivIntertwiningMap ρ σ
    ⟨(linHom ρ σ).averageMap M, (linHom ρ σ).averageMap_invariant M⟩

/-- The intertwining average has its ordinary finite sum formula.
@isnad1 id=eq.0h7v.s10.8edb722d8855 from=translated src=- shape=0f8f8f92 vocab=7ccaf4c6
-/
theorem averagedIntertwiningMap_toLinearMap
    (ρ : Representation k G V) (σ : Representation k G W) (M : V →ₗ[k] W) :
    (averagedIntertwiningMap ρ σ M).toLinearMap =
      (Fintype.card G : k)⁻¹ • ∑ g : G, (σ g).comp (M.comp (ρ g⁻¹)) := by
  simp [averagedIntertwiningMap, invariantsEquivIntertwiningMap, averageMap,
    GroupAlgebra.average, map_sum, linHom_apply,
    LinearMap.intertwiningMap_of_isIntertwiningMap]

/-- Conjugation averaging preserves the ordinary trace.
@isnad1 id=eq.0h5v.s10.fe526915bc5f from=translated src=- shape=2ef1fe92 vocab=3f73899d
-/
theorem trace_averagedIntertwiningMap [FiniteDimensional k V]
    (ρ : Representation k G V) (M : V →ₗ[k] V) :
    LinearMap.trace k V (averagedIntertwiningMap ρ ρ M).toLinearMap =
      LinearMap.trace k V M := by
  rw [averagedIntertwiningMap_toLinearMap, map_smul, map_sum]
  have hg (g : G) : LinearMap.trace k V ((ρ g).comp (M.comp (ρ g⁻¹))) =
      LinearMap.trace k V M := by
    change LinearMap.trace k V (ρ g * (M * ρ g⁻¹)) = _
    rw [LinearMap.trace_mul_cycle', ← mul_assoc, ← map_mul]
    simp
  simp_rw [hg]
  simp [smul_eq_mul, ← mul_assoc, Fintype.card_ne_zero]

/-- Averaging a map between inequivalent irreducible representations gives zero.
@isnad1 id=eq.1h7v.s8.409bef0012e0 from=translated src=- shape=b7ebd98a vocab=c105e20e
-/
theorem averagedIntertwiningMap_eq_zero
    (ρ : Representation k G V) (σ : Representation k G W)
    [IsIrreducible ρ] [IsIrreducible σ] (hne : IsEmpty (Equiv ρ σ))
    (M : V →ₗ[k] W) : averagedIntertwiningMap ρ σ M = 0 := by
  haveI := hne
  exact Subsingleton.elim _ _

/-- On a finite-dimensional irreducible over an algebraically closed field,
the intertwining average is a scalar endomorphism.
@isnad1 id=ex.0h5v.s8.1174590a95ce from=translated src=- shape=362fe978 vocab=13ce9040
-/
theorem exists_averagedIntertwiningMap_eq_smul_id
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsIrreducible ρ] (M : V →ₗ[k] V) :
    ∃ c : k, (averagedIntertwiningMap ρ ρ M).toLinearMap = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.surjective (averagedIntertwiningMap ρ ρ M)
  refine ⟨c, ?_⟩
  rw [← hc]
  rfl

/-- Trace identifies the scalar in Schur averaging, in ordinary unnormalized
trace convention.
@isnad1 id=eq.1h5v.s9.5dbe974bbef4 from=translated src=- shape=9893766e vocab=138e5346
-/
theorem averagedIntertwiningMap_self_toLinearMap
    [IsAlgClosed k] [FiniteDimensional k V]
    (ρ : Representation k G V) [IsIrreducible ρ]
    (hV : (Module.finrank k V : k) ≠ 0) (M : V →ₗ[k] V) :
    (averagedIntertwiningMap ρ ρ M).toLinearMap =
      (LinearMap.trace k V M / Module.finrank k V) • LinearMap.id := by
  obtain ⟨c, hc⟩ := exists_averagedIntertwiningMap_eq_smul_id ρ M
  have ht := trace_averagedIntertwiningMap ρ M
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hc' : c = LinearMap.trace k V M / Module.finrank k V :=
    (eq_div_iff hV).mpr ht
  rw [hc, hc']

end Representation
