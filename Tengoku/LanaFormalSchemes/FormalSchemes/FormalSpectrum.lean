import Tengoku.LanaFormalSchemes.FormalSchemes.AdicRing
import Tengoku.Seed.RingTheory.Spectrum.Prime.Homeomorph
import Tengoku.Seed.RingTheory.Spectrum.Prime.Topology
import Tengoku.Seed.Topology.Spectral.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.LanaFormalSchemes end Tengoku.LanaFormalSchemes open Tengoku.LanaFormalSchemes
set_option linter.style.header false

/-!
# The formal spectrum of an adic ring

Given an adic ring `R` with ideal of definition `I` (see `IsAdicRing`), its **formal spectrum**
`Spf R` is, as a set, the collection of *open* prime ideals of `R`: those primes that are open
subsets of `R` for its given topology. Since the topology is the `I`-adic one, a prime `p` is
open iff it contains some power `I ^ n`, and since `p` is prime this happens iff `p` contains `I`
itself. So the underlying set of `Spf R` is `{p : PrimeSpectrum R // I ≤ p.asIdeal}`, which is in
canonical order- and homeomorphism with `Spec (R ⧸ I)` via
`Ideal.primeSpectrumQuotientOrderIsoZeroLocus`. We take this quotient description as our
*definition* of the topological space underlying `Spf R`, and record that it sits inside `Spec R`
as the closed subspace of primes containing `I`.

This file only builds the underlying topological space of `Spf R`; the structure sheaf of adically
complete rings that makes it a locally ringed space is future work.

## Main definitions

* `FormalSpectrum I`: the topological space `Spf R`, defined as `Spec (R ⧸ I)`.
* `FormalSpectrum.toPrimeSpectrum`: the induced inclusion `Spf R → Spec R`.
* `FormalSpectrum.map`: a ring homomorphism `φ : R →+* S` mapping the ideal of definition `I`
  into the ideal of definition `J` induces a map `Spf S → Spf R`, making `Spf` a contravariant
  functor.

## Main results

* `FormalSpectrum.isClosedEmbedding_toPrimeSpectrum`: `toPrimeSpectrum` is a closed embedding.
* `FormalSpectrum.range_toPrimeSpectrum`: the range of `toPrimeSpectrum` is `zeroLocus I`, i.e.
  exactly the primes of `R` containing the ideal of definition `I`.
* `FormalSpectrum.instSpectralSpace`: `Spf R` is a spectral space, i.e. it is quasi-compact,
  T0, sober, quasi-separated, and its quasi-compact opens form a basis, just like `Spec R`.
* `FormalSpectrum.continuous_map`, `FormalSpectrum.map_id`, `FormalSpectrum.map_comp`:
  `FormalSpectrum.map` is continuous and functorial.
* `FormalSpectrum.toPrimeSpectrum_map`: `FormalSpectrum.map` commutes with the inclusions
  into the prime spectra, i.e. the square relating `Spf` and `Spec` commutes.
* `FormalSpectrum.thickeningHomeomorph`: `Spf R` is homeomorphic to each of its infinitesimal
  thickenings `Spec (R ⧸ I ^ n)`, `n ≠ 0`, compatibly with the transition maps of the tower
  (`FormalSpectrum.comap_factor_comp_toThickening`) and with the closed embeddings into
  `Spec R` (`FormalSpectrum.comap_mk_toThickening`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
* [The Stacks Project, Tag 0AHY](https://stacks.math.columbia.edu/tag/0AHY)
-/

open Topology

variable {R : Type*} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- The **formal spectrum** `Spf R` of an adic ring `R` with ideal of definition `I`, as a
topological space. It is defined as `Spec (R ⧸ I)`, which parametrizes exactly the open primes
of `R`, i.e. those primes containing `I`; see `FormalSpectrum.range_toPrimeSpectrum`. -/
def _root_.Tengoku.LanaFormalSchemes.FormalSpectrum : Type _ := PrimeSpectrum (R ⧸ I)

namespace Tengoku.LanaFormalSchemes.FormalSpectrum

noncomputable instance : TopologicalSpace (FormalSpectrum I) :=
  inferInstanceAs (TopologicalSpace (PrimeSpectrum (R ⧸ I)))

/-- The inclusion of the formal spectrum `Spf R` into `Spec R`, sending an open prime of `R ⧸ I`
to its preimage under `R → R ⧸ I`. -/
def toPrimeSpectrum : FormalSpectrum I → PrimeSpectrum R :=
  PrimeSpectrum.comap (Ideal.Quotient.mk I)

omit [TopologicalSpace R] [IsAdicRing I] in
/--
@isnad1 id=eq.0h2v.s6.86b2128522c7 from=translated src=- shape=05d53e33 vocab=d9bc3868
-/
theorem range_toPrimeSpectrum :
    Set.range (toPrimeSpectrum I) = PrimeSpectrum.zeroLocus (I : Set R) := by
  have := range_comap_of_surjective _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  rwa [Ideal.mk_ker] at this

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf R` is a closed subspace of `Spec R`: the primes of `R` containing the ideal of
definition `I`.
@isnad1 id=isclosed.0h2v.s5.f5a983ca3226 from=translated src=- shape=cb18e303 vocab=29686c56
-/
theorem isClosedEmbedding_toPrimeSpectrum : IsClosedEmbedding (toPrimeSpectrum I) :=
  PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective

/-!
### Basic opens

The topology of `Spf R` has a basis of *basic opens* `D(f)`, `f ∈ R`, consisting of the open
primes not containing `f`. Under the identification of `Spf R` with `Spec (R ⧸ I)` these are
the usual basic opens attached to the residues `f mod I`, and every basic open of `Spec (R ⧸ I)`
arises this way since `R → R ⧸ I` is surjective. See EGA I, 10.1.4.
-/

section BasicOpen

omit [TopologicalSpace R] [IsAdicRing I]

/-- The basic open `D(f) ⊆ Spf R` attached to `f : R`: the set of open primes of `R` not
containing `f`. Under the identification `Spf R = Spec (R ⧸ I)` it is the basic open of the
residue of `f` modulo `I`. -/
def basicOpen (f : R) : TopologicalSpace.Opens (FormalSpectrum I) :=
  PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f)

/--
@isnad1 id=iff.0h4v.s8.30210e963b43 from=translated src=- shape=73f90295 vocab=e39823b7
-/
theorem mem_basicOpen (f : R) (x : FormalSpectrum I) :
    x ∈ basicOpen I f ↔ Ideal.Quotient.mk I f ∉ x.asIdeal :=
  Iff.rfl

/--
@isnad1 id=eq.0h2v.s7.1859809d77d0 from=translated src=- shape=750f3ad5 vocab=62fb4296
-/
@[simp]
theorem basicOpen_one : basicOpen I (1 : R) = ⊤ := by
  rw [basicOpen, map_one]
  exact PrimeSpectrum.basicOpen_one

/--
@isnad1 id=eq.0h2v.s7.686545656e91 from=translated src=- shape=750f3ad5 vocab=95133c38
-/
@[simp]
theorem basicOpen_zero : basicOpen I (0 : R) = ⊥ := by
  rw [basicOpen, map_zero]
  exact PrimeSpectrum.basicOpen_zero

/--
@isnad1 id=eq.0h4v.s6.4040232fd838 from=translated src=- shape=89cbd3ac vocab=84f71af2
-/
theorem basicOpen_mul (f g : R) : basicOpen I (f * g) = basicOpen I f ⊓ basicOpen I g := by
  rw [basicOpen, map_mul]
  exact PrimeSpectrum.basicOpen_mul _ _

/-- Every basic open of `Spec (R ⧸ I)` is a basic open of `Spf R`, since `R → R ⧸ I` is
surjective.
@isnad1 id=ex.0h3v.s6.d57ff247a102 from=translated src=- shape=d19c77b5 vocab=5ae9386e
-/
theorem exists_basicOpen_eq (g : R ⧸ I) :
    ∃ f : R, basicOpen I f = PrimeSpectrum.basicOpen g := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  exact ⟨f, rfl⟩

/-- The basic opens `D(f)`, `f ∈ R`, form a basis of the topology of `Spf R`.
@isnad1 id=istopolo.0h2v.s5.1829f0952e9b from=translated src=- shape=2321b3b1 vocab=71fff5ae
-/
theorem isTopologicalBasis_basicOpen :
    TopologicalSpace.IsTopologicalBasis
      (Set.range fun f : R => (basicOpen I f : Set (FormalSpectrum I))) := by
  have h : (Set.range fun f : R => (basicOpen I f : Set (FormalSpectrum I))) =
      Set.range fun g : R ⧸ I => (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum (R ⧸ I))) := by
    apply subset_antisymm
    · rintro _ ⟨f, rfl⟩
      exact ⟨Ideal.Quotient.mk I f, rfl⟩
    · rintro _ ⟨g, rfl⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
      exact ⟨f, rfl⟩
  rw [h]
  exact PrimeSpectrum.isTopologicalBasis_basic_opens

end BasicOpen

/-!
### Functoriality

A ring homomorphism `φ : R →+* S` between adic rings that maps the ideal of definition `I`
of `R` into the ideal of definition `J` of `S` induces a map `Spf S → Spf R`, sending an open
prime `q` of `S` to the open prime `φ ⁻¹' q` of `R`. Note that such a `φ` is automatically
continuous for the adic topologies, since `φ '' (I ^ n) ⊆ J ^ n` for all `n`. This makes
`Spf` a contravariant functor, compatible with `Spec` under the closed embeddings
`toPrimeSpectrum`; see EGA I, 10.2.
-/

section Functoriality

omit [TopologicalSpace R] [IsAdicRing I]

variable {S : Type*} [CommRing S] (J : Ideal S) {T : Type*} [CommRing T] (K : Ideal T)

/-- The map `Spf S → Spf R` induced by a ring homomorphism `φ : R →+* S` mapping the ideal
of definition `I` of `R` into the ideal of definition `J` of `S`. It sends an open prime of
`S` to its preimage under `φ`, which is open since `φ` is continuous for the adic
topologies. -/
def map (φ : R →+* S) (h : I ≤ J.comap φ) : FormalSpectrum J → FormalSpectrum I :=
  PrimeSpectrum.comap (Ideal.quotientMap J φ h)

/--
@isnad1 id=continuo.1h5v.s7.2f34d02c0de1 from=translated src=- shape=0ee1b561 vocab=2633a9be
-/
theorem continuous_map (φ : R →+* S) (h : I ≤ J.comap φ) : Continuous (map I J φ h) :=
  PrimeSpectrum.continuous_comap (Ideal.quotientMap J φ h)

/--
@isnad1 id=eq.0h2v.s5.7dbf2bae29a4 from=translated src=- shape=83771760 vocab=23b1488b
-/
@[simp]
theorem map_id : map I I (RingHom.id R) (Ideal.comap_id I).ge = id := by
  have hq : Ideal.quotientMap I (RingHom.id R) (Ideal.comap_id I).ge = RingHom.id (R ⧸ I) :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun x => by simp [Ideal.quotientMap_mk])
  funext x
  change PrimeSpectrum.comap (Ideal.quotientMap I (RingHom.id R) (Ideal.comap_id I).ge) x = x
  rw [hq, PrimeSpectrum.comap_id]

/-- The inclusions `Spf → Spec` intertwine `FormalSpectrum.map φ` with the usual induced map
`Spec S → Spec R`: the square

```
Spf S  →  Spf R
  ↓          ↓
Spec S →  Spec R
```

commutes.
@isnad1 id=eq.1h6v.s7.0ac3e790cd2a from=translated src=- shape=e80f15f7 vocab=d8d8b86c
-/
theorem toPrimeSpectrum_map (φ : R →+* S) (h : I ≤ J.comap φ) (x : FormalSpectrum J) :
    toPrimeSpectrum I (map I J φ h x) = PrimeSpectrum.comap φ (toPrimeSpectrum J x) := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

end Functoriality

/-!
### Infinitesimal thickenings

For `n ≠ 0` the canonical surjection `R ⧸ I ^ n →+* R ⧸ I` has nilpotent kernel `I ⧸ I ^ n`,
so the induced map `Spf R = Spec (R ⧸ I) → Spec (R ⧸ I ^ n)` is a homeomorphism: all the
infinitesimal thickenings `Spec (R ⧸ I ^ n)` share the same underlying topological space,
namely `Spf R`. This is the topological content of EGA I, 10.6.3: the formal spectrum is the
colimit of the tower `Spec (R ⧸ I) ↪ Spec (R ⧸ I ^ 2) ↪ ⋯`, and topologically the tower is
constant. The structure sheaf of `Spf R` (future work) will be the inverse limit of the
structure sheaves of the thickenings, transported along these homeomorphisms.
-/

section Thickenings

omit [TopologicalSpace R] [IsAdicRing I]

/-- The canonical map from `Spf R` to its `n`-th infinitesimal thickening `Spec (R ⧸ I ^ n)`,
induced by the surjection `R ⧸ I ^ n →+* R ⧸ I`. It is a homeomorphism; see
`FormalSpectrum.isHomeomorph_toThickening` and `FormalSpectrum.thickeningHomeomorph`. -/
def toThickening (n : ℕ) (hn : n ≠ 0) : FormalSpectrum I → PrimeSpectrum (R ⧸ I ^ n) :=
  PrimeSpectrum.comap (Ideal.Quotient.factor (Ideal.pow_le_self hn))

/-- The kernel of `R ⧸ I ^ n →+* R ⧸ I` consists of nilpotent elements, since any lift of an
element of the kernel lies in `I` and hence its `n`-th power lies in `I ^ n`.
@isnad1 id=le.1h3v.s10.5a2de12c9c86 from=translated src=- shape=cb7bdefc vocab=e730aaf5
-/
theorem ker_factor_le_nilradical (n : ℕ) (hn : n ≠ 0) :
    RingHom.ker (Ideal.Quotient.factor (Ideal.pow_le_self hn : I ^ n ≤ I)) ≤
      nilradical (R ⧸ I ^ n) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  refine mem_nilradical.mpr ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hx n)

/-- The map from `Spf R` to its `n`-th infinitesimal thickening `Spec (R ⧸ I ^ n)` is a
homeomorphism: nilpotents do not affect the prime spectrum.
@isnad1 id=ishomeom.1h3v.s8.3946fba01893 from=translated src=- shape=f4df3451 vocab=e4f07896
-/
theorem isHomeomorph_toThickening (n : ℕ) (hn : n ≠ 0) :
    IsHomeomorph (toThickening I n hn) :=
  PrimeSpectrum.isHomeomorph_comap _
    (fun x => ⟨1, one_pos, by
      rw [pow_one]
      exact RingHom.mem_range.mpr (Ideal.Quotient.factor_surjective _ x)⟩)
    (ker_factor_le_nilradical I n hn)

/-- `Spf R` is homeomorphic to each of its infinitesimal thickenings `Spec (R ⧸ I ^ n)`,
`n ≠ 0`, via `FormalSpectrum.toThickening`. -/
noncomputable def thickeningHomeomorph (n : ℕ) (hn : n ≠ 0) :
    FormalSpectrum I ≃ₜ PrimeSpectrum (R ⧸ I ^ n) :=
  IsHomeomorph.homeomorph _ (isHomeomorph_toThickening I n hn)

/--
@isnad1 id=eq.1h4v.s10.8f79bf2950e0 from=translated src=- shape=69c7bab7 vocab=40df9788
-/
@[simp]
theorem thickeningHomeomorph_apply (n : ℕ) (hn : n ≠ 0) (x : FormalSpectrum I) :
    thickeningHomeomorph I n hn x = toThickening I n hn x :=
  rfl

/-- The closed embedding `Spec (R ⧸ I ^ n) → Spec R` restricted along `toThickening`
recovers the inclusion `Spf R → Spec R`: the thickenings all sit inside `Spec R`
compatibly.
@isnad1 id=eq.1h4v.s7.356081373f98 from=translated src=- shape=92b0cc01 vocab=2178fefc
-/
theorem comap_mk_toThickening (n : ℕ) (hn : n ≠ 0) (x : FormalSpectrum I) :
    PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ n)) (toThickening I n hn x) =
      toPrimeSpectrum I x := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The preimage of the basic open `D(f mod I ^ n) ⊆ Spec (R ⧸ I ^ n)` under the map to the
`n`-th infinitesimal thickening is the basic open `D(f) ⊆ Spf R`.
@isnad1 id=eq.1h4v.s10.853f32ed6bce from=translated src=- shape=defdb5ff vocab=c0d217e5
-/
theorem toThickening_preimage_basicOpen (n : ℕ) (hn : n ≠ 0) (f : R) :
    toThickening I n hn ⁻¹'
        (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ n) f) : Set (PrimeSpectrum (R ⧸ I ^ n)))
      = (basicOpen I f : Set (FormalSpectrum I)) := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The image of the basic open `D(f) ⊆ Spf R` in the `n`-th infinitesimal thickening
`Spec (R ⧸ I ^ n)` is the basic open `D(f mod I ^ n)`.
@isnad1 id=eq.1h4v.s10.e0b0eec11c87 from=translated src=- shape=5234c9b2 vocab=a3083187
-/
theorem toThickening_image_basicOpen (n : ℕ) (hn : n ≠ 0) (f : R) :
    toThickening I n hn '' (basicOpen I f : Set (FormalSpectrum I)) =
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (I ^ n) f) :
        Set (PrimeSpectrum (R ⧸ I ^ n))) := by
  rw [← toThickening_preimage_basicOpen I n hn f,
    Set.image_preimage_eq _ (isHomeomorph_toThickening I n hn).bijective.surjective]

end Thickenings

end Tengoku.LanaFormalSchemes.FormalSpectrum
-- Tengoku: root names of this library moved to Tengoku.LanaFormalSchemes so they do not collide with other libraries (generated)
