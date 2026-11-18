import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Module_faithfullyFlat_pi_of_forall_faithfullyFlat_localizationAway_of_span_eq_top

set_option autoImplicit false

universe u

/--
@isnad1 id=faithful.2h4v.s8.28dcfae9b651 from=translated src=- shape=c83f9981 vocab=ec03f4d1
-/
theorem solution
    {S : Type u} [CommRing S] {k : ℕ} (r : Fin k → S) (hr : Ideal.span (Set.range r) = ⊤)
    (S' : Fin k → Type u) [∀ i, CommRing (S' i)] [∀ i, Algebra S (S' i)]
    [∀ i, Algebra (Localization.Away (r i)) (S' i)] [∀ i, IsScalarTower S (Localization.Away (r i)) (S' i)]
    (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (r i)) (S' i)) :
    Module.FaithfullyFlat S (∀ i : Fin k, S' i) := by
  classical

  haveI : ∀ i, Module.Flat S (S' i) := fun i => by
    haveI : Module.Flat (Localization.Away (r i)) (S' i) := (hff i).toFlat
    haveI : Module.Flat S (Localization.Away (r i)) := IsLocalization.flat _ (Submonoid.powers (r i))
    exact Module.Flat.trans S (Localization.Away (r i)) (S' i)
  haveI : Module.Flat S (∀ i : Fin k, S' i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S (Fin k) (fun i => S' i)).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_

  have hi : ∃ i, r i ∉ p.asIdeal := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have : Ideal.span (Set.range r) ≤ p.asIdeal := Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hcon i)
    rw [hr, top_le_iff] at this
    exact p.2.ne_top this
  obtain ⟨i, hi⟩ := hi

  have hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away (r i)))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away (r i)) (r i)]
    exact hi
  obtain ⟨q, hq⟩ := hp
  haveI := hff i
  obtain ⟨q', hq'⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Localization.Away (r i)) (B := S' i) q
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j : Fin k => S' j) i) q', ?_⟩
  rw [← PrimeSpectrum.comap_comp_apply]
  have h1 : (Pi.evalRingHom (fun j : Fin k => S' j) i).comp (algebraMap S (∀ j : Fin k, S' j)) = algebraMap S (S' i) :=
    RingHom.ext fun _ => rfl
  rw [h1, IsScalarTower.algebraMap_eq S (Localization.Away (r i)) (S' i), PrimeSpectrum.comap_comp_apply, hq', hq]
