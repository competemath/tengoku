import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom

set_option autoImplicit false

universe u v

/--
@isnad1 id=and.1h3v.s6.6dac64e20bba from=translated src=- shape=7a6fa939 vocab=0876c875
-/
theorem solution
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain S]
    [IsIntegrallyClosed S] (f : R →+* S) (hf : f.Flat) [IsLocalHom f] :
    IsDomain R ∧ IsIntegrallyClosed R := by
  algebraize [f]
  haveI hff : Module.FaithfullyFlat R S :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ inferInstance ‹_›
  have hinj : Function.Injective (algebraMap R S) :=
    (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
  haveI : IsDomain R := hinj.isDomain _
  refine ⟨inferInstance, ?_⟩
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb

  let φ : FractionRing R →+* FractionRing S :=
    IsFractionRing.map (A := R) (B := S) (K := FractionRing R) (L := FractionRing S) (j := algebraMap R S) hinj
  have hφ : ∀ r : R, φ (algebraMap R (FractionRing R) r) = algebraMap S (FractionRing S) (algebraMap R S r) := by
    intro r; simp [φ, IsFractionRing.map]

  have hx' : IsIntegral S (φ (algebraMap R _ a / algebraMap R _ b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap R S), hp.map _, ?_⟩
    have hcomp : φ.comp (algebraMap R (FractionRing R)) = (algebraMap S (FractionRing S)).comp (algebraMap R S) :=
      RingHom.ext hφ
    rw [Polynomial.eval₂_map, ← hcomp, ← Polynomial.hom_eval₂, hpx, map_zero]
  obtain ⟨s, hs⟩ := (isIntegrallyClosed_iff (FractionRing S)).mp ‹IsIntegrallyClosed S› hx'

  have hfb0 : algebraMap R S b ≠ 0 := fun h => hb0 (hinj (by simpa using h))
  have hdiv : algebraMap R S a = s * algebraMap R S b := by
    have h1 : algebraMap S (FractionRing S) s =
        algebraMap S (FractionRing S) (algebraMap R S a) / algebraMap S (FractionRing S) (algebraMap R S b) := by
      rw [hs, map_div₀, hφ, hφ]
    have h2 : algebraMap S (FractionRing S) (algebraMap R S b) ≠ 0 := by
      simpa using hfb0
    apply IsFractionRing.injective S (FractionRing S)
    rw [map_mul, h1, div_mul_cancel₀ _ h2]

  have hmem : a ∈ Ideal.comap (algebraMap R S) ((Ideal.span {b}).map (algebraMap R S)) := by
    rw [Ideal.mem_comap, Ideal.map_span, Set.image_singleton, hdiv]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨r, ?_⟩
  have : algebraMap R (FractionRing R) b ≠ 0 := by simpa using hb0
  rw [eq_div_iff this, ← map_mul, hr]
