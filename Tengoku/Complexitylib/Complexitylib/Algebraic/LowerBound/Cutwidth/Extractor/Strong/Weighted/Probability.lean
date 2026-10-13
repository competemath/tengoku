/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Probability.Internal

/-!
# Finite probability weights and statistical distance

Probability weights remain normalized under marginalization and
deterministic maps. Their total variation distance lies in `[0,1]`, obeys
the triangle inequality, and contracts under deterministic maps. For equal
total mass, a distance bound is equivalent to the same bound on every
finite test. These results connect weighted conditional-source arguments
to the existing extractor contracts phrased using tests.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- A normalized nonnegative weighting has a point of positive mass.
@isnad1 id=ex.1h2v.s4.f552665170c1 from=translated src=- shape=ce542171 vocab=3de1133a
-/
theorem IsProbabilityWeight.exists_pos {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) : ∃ x, 0 < p x :=
  Internal.probabilityWeight_exists_pos hp

/-- No point of a finite probability distribution has mass greater than one.
@isnad1 id=le.1h3v.s4.9c749f4267c7 from=translated src=- shape=9c0ab710 vocab=2314673e
-/
theorem IsProbabilityWeight.le_one {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbabilityWeight p) (x : α) : p x ≤ 1 :=
  Internal.probabilityWeight_le_one hp x

/-- Taking the first marginal preserves finite probability weights.
@isnad1 id=isprobab.1h3v.s5.49ad5c5a58cd from=translated src=- shape=f9f93525 vocab=1c39d278
-/
theorem IsProbabilityWeight.first {α β : Type*} [Fintype α] [Fintype β]
    {p : α × β → ℝ} (hp : IsProbabilityWeight p) : IsProbabilityWeight (firstWeight p) :=
  Internal.probabilityWeight_first hp

/-- A deterministic image counts all source occurrences and preserves normalization.
@isnad1 id=isprobab.1h4v.s5.96dee1503e25 from=translated src=- shape=b373aadd vocab=18ec3ff6
-/
theorem IsProbabilityWeight.map {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f : α → β) :
    IsProbabilityWeight (mapWeight f p) :=
  Internal.probabilityWeight_map hp f

/-- Uniform weights on a nonempty finite type form a probability distribution.
@isnad1 id=isprobab.0h1v.s3.2cd0db710f7e from=translated src=- shape=4c9b52a8 vocab=ab32b88b
-/
theorem isProbabilityWeight_uniform (α : Type*) [Fintype α] [Nonempty α] :
    IsProbabilityWeight (uniformWeight α) :=
  Internal.probabilityWeight_uniform α

/-- The identity map preserves every finite weighting.
@isnad1 id=eq.0h2v.s4.d639d81aa732 from=translated src=- shape=2f3ee489 vocab=a250473f
-/
theorem mapWeight_id {α : Type*} [Fintype α] (p : α → ℝ) : mapWeight id p = p :=
  Internal.mapWeight_id p

/-- An equivalence transports each point mass to its unique image.
@isnad1 id=eq.0h5v.s6.7981240f64b5 from=translated src=- shape=b9fa914f vocab=881edbd0
-/
theorem mapWeight_equiv_apply {α β : Type*} [Fintype α]
    (e : α ≃ β) (p : α → ℝ) (y : β) : mapWeight e p y = p (e.symm y) :=
  Internal.mapWeight_equiv_apply e p y

/-- Deterministic pushforwards compose, including when either map identifies points.
@isnad1 id=eq.0h6v.s5.8ea47377c59d from=translated src=- shape=ef1fabd2 vocab=2f7befe1
-/
theorem mapWeight_comp {α β γ : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (f : α → β) (g : β → γ) :
    mapWeight g (mapWeight f p) = mapWeight (fun x => g (f x)) p :=
  Internal.mapWeight_comp p f g

/-- The first marginal is the deterministic image under the first projection.
@isnad1 id=eq.0h3v.s5.10ca3ca726a2 from=translated src=- shape=649991af vocab=fc394cae
-/
theorem mapWeight_fst {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) : mapWeight Prod.fst p = firstWeight p :=
  Internal.mapWeight_fst p

/-- The second marginal sums over every first-coordinate occurrence.
@isnad1 id=eq.0h4v.s5.24debb85b536 from=translated src=- shape=46090175 vocab=d96b02d9
-/
theorem mapWeight_snd_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : α × β → ℝ) (b : β) : mapWeight Prod.snd p b = ∑ a, p (a, b) :=
  Internal.mapWeight_snd_apply p b

/-- A point-mass cap cannot exceed the size of the finite sampling space.
@isnad1 id=le.2h3v.s4.0c08bc76a512 from=translated src=- shape=d0b6a9b7 vocab=aa8cd95b
-/
theorem CappedWeight.card_le {α : Type*} [Fintype α] {p : α → ℝ} {K : Nat}
    (cap : CappedWeight p K) (hp : IsProbabilityWeight p) : K ≤ Fintype.card α :=
  Internal.cappedWeight_card_le hp cap

/-- A normalized source with full possible min-entropy is exactly uniform. -/
theorem CappedWeight.eq_uniform {α : Type*} [Fintype α] {p : α → ℝ}
    (cap : CappedWeight p (Fintype.card α)) (hp : IsProbabilityWeight p) :
    p = uniformWeight α :=
  Internal.cappedWeight_eq_uniform cap hp

/-- Total variation is nonnegative, including for unnormalized weights.
@isnad1 id=le.0h3v.s4.1c68e6422e5c from=translated src=- shape=7325c23d vocab=385b4534
-/
theorem weightDist_nonneg {α : Type*} [Fintype α] (p q : α → ℝ) :
    0 ≤ weightDist p q :=
  Internal.weightDist_nonneg p q

/-- A weighting has zero distance from itself.
@isnad1 id=eq.0h2v.s4.05305a4ef327 from=translated src=- shape=46428dbe vocab=0061b34f
-/
theorem weightDist_self {α : Type*} [Fintype α] (p : α → ℝ) : weightDist p p = 0 :=
  Internal.weightDist_self p

/-- Finite total variation is symmetric.
@isnad1 id=eq.0h3v.s4.d5b0dfae6a3c from=translated src=- shape=8cef85e8 vocab=0061b34f
-/
theorem weightDist_comm {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = weightDist q p :=
  Internal.weightDist_comm p q

/-- Successive repairs add their total variation errors.
@isnad1 id=le.0h4v.s5.a39861a1508a from=translated src=- shape=f79ff783 vocab=ecd8eb77
-/
theorem weightDist_triangle {α : Type*} [Fintype α] (p q r : α → ℝ) :
    weightDist p r ≤ weightDist p q + weightDist q r :=
  Internal.weightDist_triangle p q r

/-- Zero total variation means equality at every point.
@isnad1 id=iff.0h3v.s5.e5cba8f816c6 from=translated src=- shape=ef9397c1 vocab=0061b34f
-/
theorem weightDist_eq_zero_iff {α : Type*} [Fintype α] (p q : α → ℝ) :
    weightDist p q = 0 ↔ p = q :=
  Internal.weightDist_eq_zero_iff p q

/-- Two finite probability distributions have total variation at most one.
@isnad1 id=le.2h3v.s5.947ffebd438b from=translated src=- shape=da694d26 vocab=b208f2d8
-/
theorem weightDist_le_one {α : Type*} [Fintype α] {p q : α → ℝ}
    (hp : IsProbabilityWeight p) (hq : IsProbabilityWeight q) : weightDist p q ≤ 1 :=
  Internal.weightDist_le_one hp hq

/-- Equal-mass weights differ on any finite test by at most their total variation.
@isnad1 id=le.1h4v.s6.8040922728ed from=translated src=- shape=446606cc vocab=4f5e12f2
-/
theorem weightTestProb_sub_le_dist {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) (T : Finset α) :
    |weightTestProb p T - weightTestProb q T| ≤ weightDist p q :=
  Internal.weightTestProb_sub_le_dist p q mass T

/-- For equal total mass, the finite-test and total-variation bounds are equivalent.
@isnad1 id=iff.1h4v.s6.90f8463b3f68 from=translated src=- shape=233206be vocab=4f5e12f2
-/
theorem weightDist_le_iff_tests {α : Type*} [Fintype α] (p q : α → ℝ)
    (mass : ∑ x, p x = ∑ x, q x) {ε : ℝ} :
    weightDist p q ≤ ε ↔ ∀ T : Finset α,
      |weightTestProb p T - weightTestProb q T| ≤ ε :=
  Internal.weightDist_le_iff_tests p q mass

open scoped Classical in
/-- Testing a deterministic image is the same as testing its preimage.
@isnad1 id=eq.0h5v.s6.b62e3c3b6f55 from=translated src=- shape=c009b578 vocab=991fd976
-/
theorem weightTestProb_map {α β : Type*} [Fintype α] (p : α → ℝ)
    (f : α → β) (T : Finset β) :
    weightTestProb (mapWeight f p) T = ∑ x, if f x ∈ T then p x else 0 :=
  Internal.weightTestProb_map p f T

open scoped Classical in
/-- Two deterministic observations differ in total variation by at most
their disagreement probability under the same source.
@isnad1 id=le.1h5v.s6.00d936ba8978 from=translated src=- shape=a512069b vocab=2a096b52
-/
theorem weightDist_map_map_le {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hp : IsProbabilityWeight p) (f g : α → β) :
    weightDist (mapWeight f p) (mapWeight g p) ≤ ∑ x with f x ≠ g x, p x :=
  Internal.weightDist_map_map_le hp f g

end Algebraic.Cutwidth.Extractor
