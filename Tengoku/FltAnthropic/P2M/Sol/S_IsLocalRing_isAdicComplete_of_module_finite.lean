import Tengoku.Seed.RingTheory.AdicCompletion.Functoriality
import Tengoku.Seed.RingTheory.AdicCompletion.Exactness
import Tengoku.Seed.RingTheory.AdicCompletion.Noetherian
import Tengoku.Seed.RingTheory.Finiteness.Cardinality
import Tengoku.Seed.RingTheory.LocalRing.Quotient
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic
import Tengoku.Seed.RingTheory.Artinian.Module
import Tengoku.Seed.RingTheory.Ideal.Over

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsLocalRing_isAdicComplete_of_module_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsLocalRing_isAdicComplete_of_module_finite

universe u v w

namespace M4cP1X1

open IsLocalRing

section Compare

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {I J : Ideal R}

/--
@isnad1 id=le.1h5v.s8.822be58b9916 from=translated src=- shape=e860a981 vocab=560d288d
-/
theorem smul_top_pow_le_of_le (hIJ : I ≤ J) (n : ℕ) :
    (I ^ n • ⊤ : Submodule R M) ≤ J ^ n • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_right_mono hIJ n)

/--
@isnad1 id=le.1h6v.s8.aecd6ef3d586 from=translated src=- shape=fcf3a132 vocab=30247bd9
-/
theorem smul_top_pow_mul_le_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) (n : ℕ) :
    (J ^ (N * n) • ⊤ : Submodule R M) ≤ I ^ n • ⊤ := by
  rw [pow_mul]
  exact Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)

/--
@isnad1 id=ishausdo.1h4v.s6.fde870b4fed4 from=translated src=- shape=7e6a84cd vocab=4e989fe5
-/
theorem isHausdorff_of_le (hIJ : I ≤ J) [h : IsHausdorff J M] : IsHausdorff I M :=
  ⟨fun x hx => h.haus x fun n => (hx n).mono (smul_top_pow_le_of_le hIJ n)⟩

/--
@isnad1 id=ishausdo.1h5v.s7.e34e02915653 from=translated src=- shape=5cb74b95 vocab=db4abf92
-/
theorem isHausdorff_of_pow_le {N : ℕ} (hJI : J ^ N ≤ I) [h : IsHausdorff I M] :
    IsHausdorff J M :=
  ⟨fun x hx => h.haus x fun n => (hx (N * n)).mono (smul_top_pow_mul_le_of_pow_le hJI n)⟩

/--
@isnad1 id=isprecom.2h5v.s7.6b7850cf8637 from=translated src=- shape=8c129aaf vocab=33252d23
-/
theorem isPrecomplete_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete I M] : IsPrecomplete J M := by

  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩

  obtain ⟨L, hL⟩ := h.prec (f := fun n => f (N' * n)) fun {m n} hmn =>
    (hf (Nat.mul_le_mul_left N' hmn)).mono (smul_top_pow_mul_le_of_pow_le hJI' m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans ((hL n).mono (smul_top_pow_le_of_le hIJ n))

/--
@isnad1 id=isprecom.2h5v.s7.851d57034b2b from=translated src=- shape=646f0491 vocab=33252d23
-/
theorem isPrecomplete_of_pow_le_of_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I)
    [h : IsPrecomplete J M] : IsPrecomplete I M := by
  set N' := max N 1 with hN'
  have hJI' : J ^ N' ≤ I := (Ideal.pow_le_pow_right (le_max_left N 1)).trans hJI
  have hN1 : 1 ≤ N' := le_max_right N 1
  refine ⟨fun f hf => ?_⟩
  obtain ⟨L, hL⟩ := h.prec (f := f) fun {m n} hmn => (hf hmn).mono (smul_top_pow_le_of_le hIJ m)
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n hN1)).trans
    ((hL (N' * n)).mono (smul_top_pow_mul_le_of_pow_le hJI' n))

/--
@isnad1 id=iff.2h5v.s7.f3c48f48d35b from=translated src=- shape=830191de vocab=325d5b63
-/
theorem isAdicComplete_iff_of_le_of_pow_le {N : ℕ} (hIJ : I ≤ J) (hJI : J ^ N ≤ I) :
    IsAdicComplete I M ↔ IsAdicComplete J M := by
  constructor
  · intro h
    haveI := isHausdorff_of_pow_le (M := M) hJI
    haveI := isPrecomplete_of_le_of_pow_le (M := M) hIJ hJI
    exact ⟨⟩
  · intro h
    haveI := isHausdorff_of_le (M := M) hIJ
    haveI := isPrecomplete_of_pow_le_of_le (M := M) hIJ hJI
    exact ⟨⟩

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

/--
@isnad1 id=ex.0h2v.s8.0f5c740c036c from=translated src=- shape=750f736e vocab=e0a79540
-/
theorem exists_maximalIdeal_pow_le_map :
    ∃ N, maximalIdeal T ^ N ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 T) := by
  letI : Field (𝒪 ⧸ maximalIdeal 𝒪) := Ideal.Quotient.field _
  haveI : Module.Finite (𝒪 ⧸ maximalIdeal 𝒪) (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    Module.Finite.of_restrictScalars_finite 𝒪 _ _
  haveI : IsArtinianRing (T ⧸ (maximalIdeal 𝒪).map (algebraMap 𝒪 T)) :=
    IsArtinianRing.of_finite (𝒪 ⧸ maximalIdeal 𝒪) _
  exact exists_maximalIdeal_pow_le_of_isArtinianRing_quotient _

/--
@isnad1 id=isadicco.0h2v.s7.164fc8178fad from=translated src=- shape=8ecbf6eb vocab=193e36ce
-/
theorem isAdicComplete_maximalIdeal_of_module_finite [IsNoetherianRing 𝒪]
    [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [IsLocalHom (algebraMap 𝒪 T)] :
    IsAdicComplete (maximalIdeal T) T := by
  haveI h1 : IsAdicComplete (maximalIdeal 𝒪) T := isAdicComplete_of_module_finite _
  haveI h2 : IsAdicComplete ((maximalIdeal 𝒪).map (algebraMap 𝒪 T)) T :=
    (IsAdicComplete.map_algebraMap_iff (maximalIdeal 𝒪) T).mpr h1
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map (𝒪 := 𝒪) (T := T)
  exact (isAdicComplete_iff_of_le_of_pow_le (map_maximalIdeal_le (algebraMap 𝒪 T)) hN).mp h2

end Local

end M4cP1X1

/--
@isnad1 id=isadicco.0h2v.s7.4147c8093e92 from=translated src=- shape=e3a16f50 vocab=193e36ce
-/
theorem solution {𝒪 : Type u} {T : Type v} [CommRing 𝒪]
    [IsNoetherianRing 𝒪] [IsLocalRing 𝒪] [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    [CommRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [IsLocalRing T] [IsLocalHom (algebraMap 𝒪 T)] :
    IsAdicComplete (IsLocalRing.maximalIdeal T) T :=
  M4cP1X1.isAdicComplete_maximalIdeal_of_module_finite (𝒪 := 𝒪) (T := T)
