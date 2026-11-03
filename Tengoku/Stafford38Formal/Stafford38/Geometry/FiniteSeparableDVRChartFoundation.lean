module
public import Tengoku.Seed.RingTheory.Etale.Field
public import Tengoku.Seed.RingTheory.Smooth.Basic
public import Tengoku.Seed.RingTheory.Unramified.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms finiteSeparableSection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms residue_comp_finiteSeparableSection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms finiteSeparableSection_unique` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms existsUnique_finiteSeparableSection` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms finiteSeparableSection_naturality` (it only prints; the queue checks the axioms of every declaration). -/

@[expose] public section

/-!
# Finite-separable coefficient sections through nilpotent thickenings

Let `K/E` be a separable field extension.  Formal etaleness constructs a
unique `E`-algebra section of every surjective `E`-algebra map to `K` whose
kernel is nilpotent.  These sections are automatically compatible with maps
between such thickenings.

Applied to the quotients of an equicharacteristic DVR by positive powers of
its maximal ideal, this supplies the finite-level coefficient fields needed
for a completed power-series chart.  The passage from this compatible family
to the inverse limit is outside this module's finite-level scope; the
completion comparison is supplied by the downstream completed-DVR chart.
-/

namespace Stafford38.Geometry.FiniteSeparableDVRChartFoundation

noncomputable section

universe u

variable (E K R : Type u)
variable [Field E] [Field K] [CommRing R]
variable [Algebra E K] [Algebra E R]

/-- The canonical coefficient-field lift through a nilpotent thickening.

The construction uses only the formal smoothness of the separable field
extension `K/E`; in particular it does not assume a coefficient field in `R`.-/
def finiteSeparableSection
    (hsep : Algebra.IsSeparable E K)
    (residue : R →ₐ[E] K)
    (hsurj : Function.Surjective residue)
    (hnil : IsNilpotent (RingHom.ker residue.toRingHom)) :
    K →ₐ[E] R := by
  letI : Algebra.IsSeparable E K := hsep
  letI : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact Algebra.FormallySmooth.liftOfSurjective
    (AlgHom.id E K) residue hsurj hnil

/-- The canonical lift is a section of the residue homomorphism.
@isnad1 id=eq.3h4v.s8.2bef8dc32d18 from=translated src=- shape=53c206f7 vocab=298bca3c
-/
@[simp]
theorem residue_comp_finiteSeparableSection
    (hsep : Algebra.IsSeparable E K)
    (residue : R →ₐ[E] K)
    (hsurj : Function.Surjective residue)
    (hnil : IsNilpotent (RingHom.ker residue.toRingHom)) :
    residue.comp (finiteSeparableSection E K R hsep residue hsurj hnil) =
      AlgHom.id E K := by
  letI : Algebra.IsSeparable E K := hsep
  letI : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  exact Algebra.FormallySmooth.comp_liftOfSurjective
    (AlgHom.id E K) residue hsurj hnil

/-- Every coefficient-field lift through the same nilpotent thickening is the
canonical one.  This is the formal-unramified half of separability.
@isnad1 id=eq.4h5v.s8.248ef9a30b4e from=translated src=- shape=828c4a2b vocab=298bca3c
-/
theorem finiteSeparableSection_unique
    (hsep : Algebra.IsSeparable E K)
    (residue : R →ₐ[E] K)
    (hsurj : Function.Surjective residue)
    (hnil : IsNilpotent (RingHom.ker residue.toRingHom))
    (lift : K →ₐ[E] R)
    (hlift : residue.comp lift = AlgHom.id E K) :
    lift = finiteSeparableSection E K R hsep residue hsurj hnil := by
  letI : Algebra.IsSeparable E K := hsep
  letI : Algebra.FormallyEtale E K :=
    Algebra.FormallyEtale.of_isSeparable E K
  apply Algebra.FormallyUnramified.lift_unique' residue hnil
  rw [hlift, residue_comp_finiteSeparableSection]

/-- A separable residue field has a unique coefficient-field section through
every surjective nilpotent `E`-algebra thickening.
@isnad1 id=existsun.3h4v.s8.a5be7aa89450 from=translated src=- shape=b14d57bd vocab=8fcdd9d7
-/
theorem existsUnique_finiteSeparableSection
    (hsep : Algebra.IsSeparable E K)
    (residue : R →ₐ[E] K)
    (hsurj : Function.Surjective residue)
    (hnil : IsNilpotent (RingHom.ker residue.toRingHom)) :
    ∃! lift : K →ₐ[E] R,
      residue.comp lift = AlgHom.id E K := by
  refine ⟨finiteSeparableSection E K R hsep residue hsurj hnil,
    residue_comp_finiteSeparableSection E K R hsep residue hsurj hnil, ?_⟩
  intro lift hlift
  exact finiteSeparableSection_unique E K R hsep residue hsurj hnil
    lift hlift

section Compatibility

variable (S : Type u) [CommRing S] [Algebra E S]

/-- The finite-level coefficient sections are compatible with every
`E`-algebra transition map commuting with residue specialization.  Thus no
extra choices have to be synchronized along an Artinian quotient tower.
@isnad1 id=eq.6h7v.s9.91279e94440c from=translated src=- shape=68bb48ab vocab=6c619fba
-/
theorem finiteSeparableSection_naturality
    (hsep : Algebra.IsSeparable E K)
    (residueR : R →ₐ[E] K)
    (hsurjR : Function.Surjective residueR)
    (hnilR : IsNilpotent (RingHom.ker residueR.toRingHom))
    (residueS : S →ₐ[E] K)
    (hsurjS : Function.Surjective residueS)
    (hnilS : IsNilpotent (RingHom.ker residueS.toRingHom))
    (transition : S →ₐ[E] R)
    (htransition : residueR.comp transition = residueS) :
    transition.comp
        (finiteSeparableSection E K S hsep residueS hsurjS hnilS) =
      finiteSeparableSection E K R hsep residueR hsurjR hnilR := by
  apply finiteSeparableSection_unique E K R hsep residueR hsurjR hnilR
  rw [← AlgHom.comp_assoc, htransition,
    residue_comp_finiteSeparableSection]

end Compatibility

end

end Stafford38.Geometry.FiniteSeparableDVRChartFoundation
