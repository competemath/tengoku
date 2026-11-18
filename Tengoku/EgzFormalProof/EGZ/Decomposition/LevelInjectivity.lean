import Tengoku.EgzFormalProof.EGZ.Decomposition.Levels
import Tengoku.EgzFormalProof.EGZ.Decomposition.ModularRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Injective coordinate transport at equal levels

If a new represented space is contained in an old one and an integral
coordinate map factors the old representation through the new one, equal
levels force equal spaces and equal ranks. The factor is then bijective
modulo the prime, injective on integer lattices, and bijective over the reals.
-/

namespace EGZ.FpRepresentation

variable {p d : ℕ} [Fact p.Prime] {F G : ConvexFlag}

/-- At equal levels, any affine factor between the coordinate spaces is
injective over the represented field.
@isnad1 id=injectiv.3h9v.s11.9065f0fd4c79 from=translated src=- shape=f91f1f74 vocab=7f38b9ab
-/
theorem factor_modp_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A := by
  obtain ⟨hcodim, hrank⟩ := R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel
  have hs := R.space_eq_of_codimension_eq_of_le T x y hspace hcodim
  have hsurj := R.factor_surjective_of_space_eq T x y A hs hfactor
  apply A.linear_injective_iff.mp
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (A.linear_surjective_iff.mpr hsurj)
  simpa using hrank.symm

/--
@isnad1 id=injectiv.3h9v.s10.bf87b3b2df55 from=translated src=- shape=fb1d8efb vocab=bfab55f3
-/
theorem factor_real_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A.real :=
  A.real_injective_of_modp_of_rank_eq
    (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm
    (R.factor_modp_injective_of_level_eq T x y (A.modp p) hspace hfactor hlevel)

/--
@isnad1 id=injectiv.3h9v.s10.e36de75d6b33 from=translated src=- shape=50bb243b vocab=31221c9e
-/
theorem factor_integer_injective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Injective A.integer :=
  A.integer_injective_of_modp_of_rank_eq
    (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm
    (R.factor_modp_injective_of_level_eq T x y (A.modp p) hspace hfactor hlevel)

/-- Real coordinate transport at an unchanged level is an affine
isomorphism; lattice indices need not be one.
@isnad1 id=bijectiv.3h9v.s10.9c71b31c7928 from=translated src=- shape=fb1d8efb vocab=b21492ae
-/
theorem factor_real_bijective_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : IntegralAffineMap (G.rank y) (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A.modp p (T.map y v))
    (hlevel : R.level x = T.level y) : Function.Bijective A.real := by
  have hi := R.factor_real_injective_of_level_eq T x y A hspace hfactor hlevel
  refine ⟨hi, A.real.linear_surjective_iff.mp ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (A.real.linear_injective_iff.mpr hi)
  simpa using (R.codimension_eq_and_rank_eq_of_level_eq T x y hlevel).2.symm

/--
@isnad1 id=injectiv.2h6v.s8.c54e0aaec572 from=translated src=- shape=bdb07443 vocab=d58debef
-/
theorem transition_real_injective_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    Function.Injective (F.transition h).real :=
  R.factor_real_injective_of_level_eq R x y (F.transition h) (R.space_mono h)
    (fun _ hv ↦ R.compatible h hv) heq.symm

/--
@isnad1 id=injectiv.2h6v.s6.1b4908e5a358 from=translated src=- shape=08b6716d vocab=9dae365b
-/
theorem transition_integer_injective_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    Function.Injective (F.transition h).integer :=
  R.factor_integer_injective_of_level_eq R x y (F.transition h) (R.space_mono h)
    (fun _ hv ↦ R.compatible h hv) heq.symm

end EGZ.FpRepresentation
