import Tengoku.Seed.RingTheory.AdicCompletion.Functoriality
import Tengoku.Seed.RingTheory.AdicCompletion.Exactness
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.Seed.RingTheory.LocalRing.Quotient
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Ideal.Over

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAdicComplete_of_module_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAdicComplete_of_module_finite

universe u v w

namespace M4cP1X1

open IsLocalRing

section Compare

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I J : Ideal R}

end Compare

section ModuleFinite

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

open AdicCompletion

theorem isPrecomplete_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  rw [← of_surjective_iff]
  intro z
  obtain ⟨w, rfl⟩ := map_surjective I hf z
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M w
  exact ⟨f x, (map_of I f x).symm⟩

theorem isPrecomplete_pi (ι : Type*) [Fintype ι] [DecidableEq ι] [IsPrecomplete I R] :
    IsPrecomplete I (ι → R) := by
  rw [← of_surjective_iff]
  intro z
  choose x hx using fun j =>
    AdicCompletion.of_surjective I R (piEquivOfFintype I (fun _ : ι => R) z j)
  refine ⟨x, (piEquivOfFintype I (fun _ : ι => R)).injective ?_⟩
  funext j
  rw [piEquivOfFintype_apply, ← hx j]
  change map I (LinearMap.proj j) (of I (ι → R) x) = _
  rw [map_of]
  rfl

theorem isPrecomplete_of_module_finite [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

theorem isAdicComplete_of_module_finite [IsNoetherianRing R] [IsAdicComplete I R]
    [Module.Finite R M] : IsAdicComplete I M :=
  haveI := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  haveI := isPrecomplete_of_module_finite I (M := M)
  ⟨⟩

end ModuleFinite

section Local

variable {𝒪 : Type*} {T : Type*} [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  [Module.Finite 𝒪 T] [IsLocalRing T]

end Local

end M4cP1X1

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M :=
  M4cP1X1.isAdicComplete_of_module_finite I
