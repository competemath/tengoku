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

/--
@isnad1 id=isprecom.1h5v.s7.3435b7ee18a3 from=translated src=- shape=87d83dc4 vocab=35f2f1aa
-/
theorem isPrecomplete_of_surjective (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [IsPrecomplete I M] : IsPrecomplete I N := by
  rw [← of_surjective_iff]
  intro z
  obtain ⟨w, rfl⟩ := map_surjective I hf z
  obtain ⟨x, rfl⟩ := AdicCompletion.of_surjective I M w
  exact ⟨f x, (map_of I f x).symm⟩

/--
@isnad1 id=isprecom.0h3v.s6.44396f47e601 from=translated src=- shape=d65608f3 vocab=992426d9
-/
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

/--
@isnad1 id=isprecom.0h3v.s6.dcf88c8146f3 from=translated src=- shape=67461377 vocab=3c050046
-/
theorem isPrecomplete_of_module_finite [IsPrecomplete I R] [Module.Finite R M] :
    IsPrecomplete I M := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I (Fin n)
  exact isPrecomplete_of_surjective I f hf

/--
@isnad1 id=isadicco.0h3v.s6.45ac6f523380 from=translated src=- shape=b15414e4 vocab=8fb8cfab
-/
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

/--
@isnad1 id=isadicco.0h3v.s6.ba3c32a3c4bd from=translated src=- shape=915833f0 vocab=8fb8cfab
-/
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.Finite R M] : IsAdicComplete I M :=
  M4cP1X1.isAdicComplete_of_module_finite I
