import Tengoku.EgzFormalProof.EGZ.Decomposition.RechartPreservation
import Tengoku.EgzFormalProof.EGZ.Decomposition.GapCleanup
import Tengoku.EgzFormalProof.EGZ.Decomposition.ThinDirections

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Levels of represented flag nodes

The lexicographic pair consisting of representation codimension and lattice
rank is encoded by a natural number. Levels are antitone along flag nodes
and increase under restriction of the represented space when the old map
factors through the new map. This includes minimalization.
-/

namespace EGZ

namespace LevelCode

/-- Encode two coordinates in the square `[0,d]²` in lexicographic order.-/
def code (d a b : ℕ) : ℕ := (d + 1) * a + b

/--
@isnad1 id=lt.2h5v.s5.a4d65b533f66 from=translated src=- shape=fc97b98c vocab=4bcf959d
-/
theorem lt_of_first_lt {d a b a' b' : ℕ} (h : a < a') (hb : b ≤ d) :
    code d a b < code d a' b' := by
  have hm := Nat.mul_le_mul_left (d + 1) (Nat.succ_le_of_lt h)
  dsimp [code]
  nlinarith

/--
@isnad1 id=le.3h5v.s5.ad9ea3167327 from=translated src=- shape=268a00d5 vocab=7f83d855
-/
theorem le_of_first_le {d a b a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ d)
    (heq : a = a' → b ≤ b') : code d a b ≤ code d a' b' := by
  rcases lt_or_eq_of_le ha with h | h
  · exact (lt_of_first_lt h hb).le
  · dsimp [code]
    simpa only [h] using Nat.add_le_add_left (heq h) ((d + 1) * a')

theorem eq_iff {d a b a' b' : ℕ} (hb : b ≤ d) (hb' : b' ≤ d) :
    code d a b = code d a' b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro heq
    have ha : a = a' := by
      rcases lt_trichotomy a a' with h | h | h
      · exact False.elim ((ne_of_lt (lt_of_first_lt h hb)) heq)
      · exact h
      · exact False.elim ((ne_of_lt (lt_of_first_lt h hb')) heq.symm)
    refine ⟨ha, ?_⟩
    simpa only [code, ha, Nat.add_left_cancel_iff] using heq
  · rintro ⟨rfl, rfl⟩
    rfl

/--
@isnad1 id=lt.2h3v.s5.1523365eaed1 from=translated src=- shape=a12f8e35 vocab=2e53c076
-/
theorem lt_square {d a b : ℕ} (ha : a ≤ d) (hb : b ≤ d) :
    code d a b < (d + 1) ^ 2 := by
  have hm := Nat.mul_le_mul_left (d + 1) ha
  dsimp [code]
  nlinarith

end LevelCode

namespace FpRepresentation

variable {p d : ℕ} [Fact p.Prime] {F G : ConvexFlag}

/-- Dimension of the represented affine space.-/
noncomputable def spaceDimension (R : FpRepresentation p d F) (x : F.Node) : ℕ :=
  Module.finrank (ZMod p) (R.space x).direction

/-- Codimension of the represented affine space in the ambient space.-/
noncomputable def codimension (R : FpRepresentation p d F) (x : F.Node) : ℕ :=
  d - R.spaceDimension x

/-- Natural-number encoding of `(codim V_x, rank Λ_x)`.-/
noncomputable def level (R : FpRepresentation p d F) (x : F.Node) : ℕ :=
  LevelCode.code d (R.codimension x) (F.rank x)

/--
@isnad1 id=nonempty.0h5v.s7.5b6cfa6faaee from=translated src=- shape=04a6e0da vocab=1344929d
-/
theorem space_nonempty (R : FpRepresentation p d F) (x : F.Node) :
    (R.space x : Set (FpCoord p d)).Nonempty := by
  obtain ⟨v, hv, _⟩ := R.map_surjective x (Set.mem_univ (0 : FpCoord p (F.rank x)))
  exact ⟨v, hv⟩

/--
@isnad1 id=le.0h5v.s4.46f460846d4b from=translated src=- shape=10007c6d vocab=17e6a387
-/
theorem spaceDimension_le (R : FpRepresentation p d F) (x : F.Node) :
    R.spaceDimension x ≤ d := by
  simpa [spaceDimension] using (R.space x).direction.finrank_le

/--
@isnad1 id=le.0h5v.s4.a842dfbd9dde from=translated src=- shape=10007c6d vocab=13a526ce
-/
theorem codimension_le (R : FpRepresentation p d F) (x : F.Node) :
    R.codimension x ≤ d := Nat.sub_le _ _

/--
@isnad1 id=lt.0h5v.s5.7d9f7bcee376 from=translated src=- shape=9ddd4a09 vocab=43910cc1
-/
theorem level_lt (R : FpRepresentation p d F) (x : F.Node) :
    R.level x < (d + 1) ^ 2 :=
  LevelCode.lt_square (R.codimension_le x) (R.rank_le x)

/--
@isnad1 id=le.0h5v.s6.942d5096d9ff from=translated src=- shape=5523696a vocab=651ae252
-/
theorem level_le (R : FpRepresentation p d F) (x : F.Node) :
    R.level x ≤ (d + 1) ^ 2 - 1 := by
  have h := R.level_lt x
  omega

/--
@isnad1 id=le.1h8v.s8.e98ff5b0b56b from=translated src=- shape=ce81032a vocab=97baa0b0
-/
theorem codimension_le_of_space_le (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (h : T.space y ≤ R.space x) : R.codimension x ≤ T.codimension y := by
  have hd := Submodule.finrank_mono (AffineSubspace.direction_le h)
  change d - R.spaceDimension x ≤ d - T.spaceDimension y
  exact Nat.sub_le_sub_left hd d

/--
@isnad1 id=eq.2h8v.s8.61b7fea2f136 from=translated src=- shape=88ffb347 vocab=97baa0b0
-/
theorem space_eq_of_codimension_eq_of_le (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (h : T.space y ≤ R.space x) (heq : R.codimension x = T.codimension y) :
    T.space y = R.space x := by
  by_contra hn
  have hlt : T.space y < R.space x := lt_of_le_of_ne h hn
  have hdim := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hlt (T.space_nonempty y))
  have hdx := R.spaceDimension_le x
  have hdy := T.spaceDimension_le y
  dsimp [codimension, spaceDimension] at *
  omega

/-- Factoring a surjective represented map gives a surjective coordinate
map when the two represented affine spaces coincide.
@isnad1 id=surjecti.2h9v.s11.209fbcb605f7 from=translated src=- shape=58f803dd vocab=7ba72abc
-/
theorem factor_surjective_of_space_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y = R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v)) : Function.Surjective A := by
  intro q
  obtain ⟨v, hv, hvq⟩ := R.map_surjective x (Set.mem_univ q)
  refine ⟨T.map y v, ?_⟩
  rw [← hfactor v (hspace.symm ▸ hv)]
  exact hvq

/--
@isnad1 id=le.2h9v.s10.80ebad8cd162 from=translated src=- shape=db4b67cc vocab=14eed0a0
-/
theorem rank_le_of_factor_of_space_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y = R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v)) : F.rank x ≤ G.rank y := by
  simpa using LinearMap.finrank_le_finrank_of_surjective
    (A.linear_surjective_iff.mpr (R.factor_surjective_of_space_eq T x y A hspace hfactor))

/-- The basic level comparison used by all support refinements.
@isnad1 id=le.2h9v.s11.1efcc442d98f from=translated src=- shape=c17c0bd1 vocab=6fa29fea
-/
theorem level_le_of_space_le_of_factor (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v)) : R.level x ≤ T.level y := by
  apply LevelCode.le_of_first_le (R.codimension_le_of_space_le T x y hspace) (R.rank_le x)
  intro heq
  exact R.rank_le_of_factor_of_space_eq T x y A
    (R.space_eq_of_codimension_eq_of_le T x y hspace heq) hfactor

/--
@isnad1 id=lt.1h8v.s8.f1a22ac463a1 from=translated src=- shape=ce81032a vocab=eac80c3d
-/
theorem level_lt_of_space_lt (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (hspace : T.space y < R.space x) : R.level x < T.level y := by
  apply LevelCode.lt_of_first_lt _ (R.rank_le x)
  have hd := Submodule.finrank_lt_finrank_of_lt
    (AffineSubspace.direction_lt_of_nonempty hspace (T.space_nonempty y))
  have hdx := R.spaceDimension_le x
  have hdy := T.spaceDimension_le y
  dsimp [codimension, spaceDimension] at *
  omega

/--
@isnad1 id=lt.2h8v.s7.fd21908d38ed from=translated src=- shape=cb82943f vocab=0bb50453
-/
theorem level_lt_of_space_eq_of_rank_lt (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (hspace : T.space y = R.space x) (hrank : F.rank x < G.rank y) :
    R.level x < T.level y := by
  change (d + 1) * (d - Module.finrank (ZMod p) (R.space x).direction) + F.rank x <
    (d + 1) * (d - Module.finrank (ZMod p) (T.space y).direction) + G.rank y
  rw [hspace]
  exact Nat.add_lt_add_left hrank _

/-- Losing lattice rank under a factorization forces loss of represented
space, and therefore a strict increase in level.
@isnad1 id=lt.3h9v.s11.7e9b779082e8 from=translated src=- shape=0d748117 vocab=239bcc05
-/
theorem level_lt_of_rank_lt_of_factor (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v))
    (hrank : G.rank y < F.rank x) : R.level x < T.level y := by
  apply R.level_lt_of_space_lt T x y
  refine lt_of_le_of_ne hspace ?_
  intro heq
  exact (not_le_of_gt hrank) (R.rank_le_of_factor_of_space_eq T x y A heq hfactor)

/-- A newly represented functional which is nonconstant on an old fibre
forces a strict level increase. Only one such functional is needed.
@isnad1 id=lt.4h11v.s11.be5036250bae from=translated src=- shape=e13dbab0 vocab=70cbe3c1
-/
theorem level_lt_of_nonconstant_factor (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (A : FpCoord p (G.rank y) →ᵃ[ZMod p] FpCoord p (F.rank x))
    (hspace : T.space y ≤ R.space x)
    (hfactor : ∀ v ∈ T.space y, R.map x v = A (T.map y v))
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (hξ : R.NonconstantOnFibers x ξ)
    (B : FpCoord p (G.rank y) →ᵃ[ZMod p] ZMod p)
    (hB : ∀ v ∈ T.space y, ξ v = B (T.map y v)) : R.level x < T.level y := by
  by_cases heq : T.space y = R.space x
  · apply R.level_lt_of_space_eq_of_rank_lt T x y heq
    have hrank := R.rank_le_of_factor_of_space_eq T x y A heq hfactor
    apply lt_of_le_of_ne hrank
    intro hr
    have hs := R.factor_surjective_of_space_eq T x y A heq hfactor
    have hA : Function.Injective A := by
      apply A.linear_injective_iff.mp
      apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
        (A.linear_surjective_iff.mpr hs)
      simpa using hr.symm
    obtain ⟨v, w, hv, hw, hvw, hne⟩ := hξ
    have hv' : v ∈ T.space y := heq.symm ▸ hv
    have hw' : w ∈ T.space y := heq.symm ▸ hw
    apply hne
    rw [hB v hv', hB w hw']
    apply congrArg B
    apply hA
    rwa [← hfactor v hv', ← hfactor w hw']
  · exact R.level_lt_of_space_lt T x y (lt_of_le_of_ne hspace heq)

/--
@isnad1 id=antitone.0h4v.s5.dafc72c48cd7 from=translated src=- shape=a66055db vocab=7afb9eec
-/
theorem level_antitone (R : FpRepresentation p d F) : Antitone R.level := by
  intro y x h
  exact R.level_le_of_space_le_of_factor R x y ((F.transition h).modp p)
    (R.space_mono h) (fun _ hv ↦ R.compatible h hv)

/-- Equal levels determine both coordinates of the lexicographic pair.
@isnad1 id=and.1h8v.s6.9e53a65653c3 from=translated src=- shape=0468ad2f vocab=044ce9f8
-/
theorem codimension_eq_and_rank_eq_of_level_eq (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) (x : F.Node) (y : G.Node)
    (h : R.level x = T.level y) : R.codimension x = T.codimension y ∧ F.rank x = G.rank y :=
  (LevelCode.eq_iff (R.rank_le x) (T.rank_le y)).mp h

/--
@isnad1 id=eq.2h6v.s7.b4f07fc5fc1d from=translated src=- shape=687d9653 vocab=09437258
-/
theorem space_eq_of_le_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) : R.space y = R.space x :=
  R.space_eq_of_codimension_eq_of_le R x y (R.space_mono h)
    (R.codimension_eq_and_rank_eq_of_level_eq R y x heq).1.symm

/-- A transition between comparable nodes of equal level is injective
over the represented field.
@isnad1 id=injectiv.2h6v.s8.c288d5a04295 from=translated src=- shape=81a551df vocab=ee649ed2
-/
theorem transition_modp_injective_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    Function.Injective ((F.transition h).modp p) := by
  let A := (F.transition h).modp p
  have hsurj := R.factor_surjective_of_space_eq R x y A
    (R.space_eq_of_le_of_level_eq h heq) (fun _ hv ↦ R.compatible h hv)
  apply A.linear_injective_iff.mp
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mpr
    (A.linear_surjective_iff.mpr hsurj)
  simpa using (R.codimension_eq_and_rank_eq_of_level_eq R y x heq).2

/-- Comparable equal-level nodes have exactly the same fibre-constant
functionals. This is the equality case needed by complete refinement.
@isnad1 id=eq.2h6v.s9.729cf6aa1d9e from=translated src=- shape=ef10b95c vocab=50fc1616
-/
theorem fiberConstantSubmodule_eq_of_level_eq (R : FpRepresentation p d F)
    {y x : F.Node} (h : y ≤ x) (heq : R.level y = R.level x) :
    R.fiberConstantSubmodule y = R.fiberConstantSubmodule x := by
  have hs := R.space_eq_of_le_of_level_eq h heq
  have hi := R.transition_modp_injective_of_level_eq h heq
  ext ξ
  constructor
  · intro hξ v w hv hw hvw
    have hv' : v ∈ R.space y := hs.symm ▸ hv
    have hw' : w ∈ R.space y := hs.symm ▸ hw
    apply hξ v w hv' hw'
    apply hi
    rwa [← R.compatible h hv', ← R.compatible h hw']
  · intro hξ v w hv hw hvw
    apply hξ v w (hs ▸ hv) (hs ▸ hw)
    rw [R.compatible h hv, R.compatible h hw, hvw]

/-- Representing a functional nonconstant on an upper node's fibres gives
a strict increase over that upper level at every retained lower node.
@isnad1 id=lt.5h12v.s11.9e86e3a194ef from=translated src=- shape=013bcbcf vocab=70cbe3c1
-/
theorem level_lt_of_nonconstant_factor_at_upper (R : FpRepresentation p d F)
    (T : FpRepresentation p d G) {x y : F.Node} (h : y ≤ x) (z : G.Node)
    (A : FpCoord p (G.rank z) →ᵃ[ZMod p] FpCoord p (F.rank y))
    (hspace : T.space z ≤ R.space y)
    (hfactor : ∀ v ∈ T.space z, R.map y v = A (T.map z v))
    (ξ : FpCoord p d →ᵃ[ZMod p] ZMod p) (hξ : R.NonconstantOnFibers x ξ)
    (B : FpCoord p (G.rank z) →ᵃ[ZMod p] ZMod p)
    (hB : ∀ v ∈ T.space z, ξ v = B (T.map z v)) : R.level x < T.level z := by
  rcases lt_or_eq_of_le (R.level_antitone h) with hl | heq
  · exact hl.trans_le (R.level_le_of_space_le_of_factor T y z A hspace hfactor)
  · have hξy : R.NonconstantOnFibers y ξ := by
      by_contra hn
      have hm := (R.mem_fiberConstantSubmodule_iff y ξ).mpr hn
      rw [R.fiberConstantSubmodule_eq_of_level_eq h heq.symm] at hm
      exact (R.mem_fiberConstantSubmodule_iff x ξ).mp hm hξ
    rw [heq]
    exact R.level_lt_of_nonconstant_factor T y z A hspace hfactor ξ hξy B hB

end FpRepresentation

namespace FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- Level of a node of a flag decomposition.-/
noncomputable abbrev level (Φ : FlagDecomposition p d f) : Φ.flag.Node → ℕ :=
  Φ.representation.level

/--
@isnad1 id=antitone.0h4v.s5.f294e45c010d from=translated src=- shape=0c1509e6 vocab=6e2b91c4
-/
theorem level_antitone (Φ : FlagDecomposition p d f) : Antitone Φ.level :=
  Φ.representation.level_antitone

/--
@isnad1 id=eq.1h5v.s6.38b7ae2da40e from=translated src=- shape=49605922 vocab=9e5da16a
-/
@[simp]
theorem reduced_level (Φ : FlagDecomposition p d f) (hp : Odd p)
    (x : (Φ.reduced hp).flag.Node) : (Φ.reduced hp).level x = Φ.level x.1 := rfl

/--
@isnad1 id=eq.1h6v.s6.2602e210404f from=translated src=- shape=1f8dfc99 vocab=5a1feed4
-/
@[simp]
theorem PrunedWeights.rebuilt_level {Φ : FlagDecomposition p d f} (D : PrunedWeights Φ)
    (hp : Odd p) (x : (D.rebuilt hp).flag.Node) :
    (D.rebuilt hp).level x = Φ.level x.1 := rfl

/--
@isnad1 id=eq.1h6v.s7.fde67b0ada59 from=translated src=- shape=ba485bab vocab=2888d7f6
-/
@[simp]
theorem PrunedWeights.cleaned_level {Φ : FlagDecomposition p d f} (D : PrunedWeights Φ)
    (hp : Odd p) (x : (D.cleaned hp).flag.Node) :
    (D.cleaned hp).level x = Φ.level x.1.1 := rfl

namespace Rechart

variable (Φ : FlagDecomposition p d f) (C : ∀ x, IntegerLatticeChart (Φ.liftedSupport x))
    (hp : Odd p) (hinj : ∀ x, Function.Injective ((chart Φ C x).modp p))
    (hcenter : ∀ x q, q ∈ (C x).coordinateSupport → IsCenteredLift p q)

/-- Minimalization cannot lower a node's level. A decrease in lattice
rank forces a strict decrease in its represented affine space.
@isnad1 id=le.3h6v.s10.5321368ca8a7 from=translated src=- shape=218d3d4e vocab=96412683
-/
theorem decomposition_level_le (x : Φ.flag.Node) :
    Φ.level x ≤ (decomposition Φ C hp hinj hcenter).level x :=
  Φ.representation.level_le_of_space_le_of_factor
    (decomposition Φ C hp hinj hcenter).representation x x ((chart Φ C x).modp p)
    (space_le_original Φ x) (fun v hv ↦ (chart_map Φ C hp hinj x v hv).symm)

end Rechart
end FlagDecomposition

end EGZ
