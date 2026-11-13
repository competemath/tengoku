import Tengoku.Rankamplificationtotient.RankAmplification.SameSupportSUnitReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Terminal specialization of the natural S-unit equation This file turns finiteness of the special positive equation `u + h = v` into an actual finite carrier, and reduces the general-shift endpoint to primitive equations indexed by the divisors of the shift. -/

namespace RankAmplification

open Finset Nat
open scoped BigOperators

noncomputable section

namespace SUnitTerminal

/-! ## Finite types and exact carriers -/

/-- The subtype of positive natural solutions of the affine S-unit equation.-/
def AffineSolution (S : Finset ℕ) (h : ℕ) :=
  {z : ℕ × ℕ // IsSUnitAffineSolution S h z.1 z.2}

/-- Forgetful embedding of affine solutions into pairs of naturals.-/
def affineSolutionEmbedding (S : Finset ℕ) (h : ℕ) :
    AffineSolution S h ↪ ℕ × ℕ where
  toFun z := z.1
  inj' := Subtype.val_injective

/-- A `Finite` instance for the solution subtype canonically produces an exact ambient finset.-/
def affineCarrierOfFinite (S : Finset ℕ) (h : ℕ)
    [Finite (AffineSolution S h)] : Finset (ℕ × ℕ) := by
  letI := Fintype.ofFinite (AffineSolution S h)
  exact Finset.univ.map (affineSolutionEmbedding S h)

@[simp]
theorem mem_affineCarrierOfFinite (S : Finset ℕ) (h u v : ℕ)
    [Finite (AffineSolution S h)] :
    (u, v) ∈ affineCarrierOfFinite S h ↔
      IsSUnitAffineSolution S h u v := by
  classical
  letI := Fintype.ofFinite (AffineSolution S h)
  constructor
  · intro huv
    obtain ⟨z, _hz, hz⟩ := Finset.mem_map.mp huv
    have hzVal : z.1 = (u, v) := hz
    simpa only [hzVal] using z.2
  · intro huv
    let z : AffineSolution S h := ⟨(u, v), huv⟩
    exact Finset.mem_map.mpr ⟨z, Finset.mem_univ z, rfl⟩

theorem isSUnitAffineCarrier_affineCarrierOfFinite
    (S : Finset ℕ) (h : ℕ) [Finite (AffineSolution S h)] :
    IsSUnitAffineCarrier S h (affineCarrierOfFinite S h) := by
  intro u v
  exact mem_affineCarrierOfFinite S h u v

/-- Conversely, an exact carrier makes the solution subtype finite.-/
theorem finite_affineSolution_of_carrier
    {S : Finset ℕ} {h : ℕ} {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier S h U) :
    Finite (AffineSolution S h) := by
  classical
  let target := {z : ℕ × ℕ // z ∈ U}
  let f : AffineSolution S h → target := fun z ↦
    ⟨z.1, (hU z.1.1 z.1.2).mpr z.2⟩
  apply Finite.of_injective f
  intro z w hzw
  apply Subtype.ext
  exact congrArg (fun q : target ↦ q.1) hzw

/-- `TerminalEvertseSUnitFiniteness` is exactly finiteness of the special solution subtype.-/
theorem terminalEvertseSUnitFiniteness_iff_finite (h : ℕ) :
    TerminalEvertseSUnitFiniteness h ↔
      Finite (AffineSolution (primeSupport h) h) := by
  constructor
  · rintro ⟨U, hU⟩
    exact finite_affineSolution_of_carrier hU
  · intro hfinite
    letI : Finite (AffineSolution (primeSupport h) h) := hfinite
    exact ⟨affineCarrierOfFinite (primeSupport h) h,
      isSUnitAffineCarrier_affineCarrierOfFinite (primeSupport h) h⟩

/-! ## Explicit bounded enumeration -/

/-- A purely arithmetic height bound for every solution.-/
def AffineSolutionHeightBound (S : Finset ℕ) (h B : ℕ) : Prop :=
  ∀ u v, IsSUnitAffineSolution S h u v → u ≤ B ∧ v ≤ B

/-- Enumerate a bounded box and retain precisely the affine S-unit solutions.-/
def boundedAffineCarrier (S : Finset ℕ) (h B : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.range (B + 1)).product (Finset.range (B + 1))).filter
    fun z ↦ IsSUnitAffineSolution S h z.1 z.2

theorem isSUnitAffineCarrier_boundedAffineCarrier
    {S : Finset ℕ} {h B : ℕ} (hB : AffineSolutionHeightBound S h B) :
    IsSUnitAffineCarrier S h (boundedAffineCarrier S h B) := by
  classical
  intro u v
  rw [boundedAffineCarrier, Finset.mem_filter]
  constructor
  · exact fun huv ↦ huv.2
  · intro huv
    have hbounds := hB u v huv
    exact ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, huv⟩

theorem terminalEvertseSUnitFiniteness_of_heightBound
    {h B : ℕ}
    (hB : AffineSolutionHeightBound (primeSupport h) h B) :
    TerminalEvertseSUnitFiniteness h :=
  ⟨boundedAffineCarrier (primeSupport h) h B,
    isSUnitAffineCarrier_boundedAffineCarrier hB⟩

/-- Every exact carrier supplies an explicit (though deliberately crude) numeric height bound.-/
def affineCarrierHeight (U : Finset (ℕ × ℕ)) : ℕ :=
  U.sum fun z ↦ z.1 + z.2

theorem affineSolutionHeightBound_of_carrier
    {S : Finset ℕ} {h : ℕ} {U : Finset (ℕ × ℕ)}
    (hU : IsSUnitAffineCarrier S h U) :
    AffineSolutionHeightBound S h (affineCarrierHeight U) := by
  intro u v huv
  have huvMem : (u, v) ∈ U := (hU u v).mpr huv
  have hterm : u + v ≤ affineCarrierHeight U := by
    unfold affineCarrierHeight
    exact Finset.single_le_sum (fun z _hz ↦ Nat.zero_le (z.1 + z.2)) huvMem
  omega

theorem terminalEvertseSUnitFiniteness_iff_heightBound (h : ℕ) :
    TerminalEvertseSUnitFiniteness h ↔
      ∃ B, AffineSolutionHeightBound (primeSupport h) h B := by
  constructor
  · rintro ⟨U, hU⟩
    exact ⟨affineCarrierHeight U, affineSolutionHeightBound_of_carrier hU⟩
  · rintro ⟨B, hB⟩
    exact terminalEvertseSUnitFiniteness_of_heightBound hB

/-! ## The zero shift -/

theorem isPrimeSupportUnit_empty_iff {n : ℕ} :
    IsPrimeSupportUnit ∅ n ↔ n = 1 := by
  constructor
  · rintro ⟨hnPos, hnSupport⟩
    have hempty : primeSupport n = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      exact Finset.notMem_empty p (hnSupport hp)
    rcases Nat.primeFactors_eq_empty.mp hempty with hn | hn
    · omega
    · exact hn
  · rintro rfl
    simp [IsPrimeSupportUnit]

theorem isSUnitAffineCarrier_zero :
    IsSUnitAffineCarrier (primeSupport 0) 0 {(1, 1)} := by
  intro u v
  simp [IsSUnitAffineSolution, isPrimeSupportUnit_empty_iff]
  omega

theorem terminalEvertseSUnitFiniteness_zero :
    TerminalEvertseSUnitFiniteness 0 :=
  ⟨{(1, 1)}, isSUnitAffineCarrier_zero⟩

/-! ## Primitive divisor equations -/

/-- The primitive positive equation remaining after division by `gcd(u,v)`.-/
def IsPrimitiveSUnitAffineSolution
    (S : Finset ℕ) (c a b : ℕ) : Prop :=
  IsPrimeSupportUnit S a ∧ IsPrimeSupportUnit S b ∧
    Nat.Coprime a b ∧ a + c = b

/-- Exact finite carrier predicate for primitive affine S-unit solutions.-/
def IsPrimitiveSUnitAffineCarrier
    (S : Finset ℕ) (c : ℕ) (U : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b, (a, b) ∈ U ↔ IsPrimitiveSUnitAffineSolution S c a b

@[simp, nolint simpNF]
theorem mem_primitiveSUnitAffineCarrier
    {S : Finset ℕ} {c : ℕ} {U : Finset (ℕ × ℕ)}
    (hU : IsPrimitiveSUnitAffineCarrier S c U) {a b : ℕ} :
    (a, b) ∈ U ↔ IsPrimitiveSUnitAffineSolution S c a b :=
  hU a b

/-- Subtype of primitive positive solutions to the affine S-unit equation.-/
def PrimitiveAffineSolution (S : Finset ℕ) (c : ℕ) :=
  {z : ℕ × ℕ // IsPrimitiveSUnitAffineSolution S c z.1 z.2}

/-- Forgetful embedding of primitive affine solutions into natural pairs.-/
def primitiveAffineSolutionEmbedding (S : Finset ℕ) (c : ℕ) :
    PrimitiveAffineSolution S c ↪ ℕ × ℕ where
  toFun z := z.1
  inj' := Subtype.val_injective

/-- Canonical finite carrier obtained from a finite primitive solution type.-/
def primitiveAffineCarrierOfFinite (S : Finset ℕ) (c : ℕ)
    [Finite (PrimitiveAffineSolution S c)] : Finset (ℕ × ℕ) := by
  letI := Fintype.ofFinite (PrimitiveAffineSolution S c)
  exact Finset.univ.map (primitiveAffineSolutionEmbedding S c)

@[simp]
theorem mem_primitiveAffineCarrierOfFinite (S : Finset ℕ) (c a b : ℕ)
    [Finite (PrimitiveAffineSolution S c)] :
    (a, b) ∈ primitiveAffineCarrierOfFinite S c ↔
      IsPrimitiveSUnitAffineSolution S c a b := by
  classical
  letI := Fintype.ofFinite (PrimitiveAffineSolution S c)
  constructor
  · intro hab
    obtain ⟨z, _hz, hz⟩ := Finset.mem_map.mp hab
    have hzVal : z.1 = (a, b) := hz
    simpa only [hzVal] using z.2
  · intro hab
    let z : PrimitiveAffineSolution S c := ⟨(a, b), hab⟩
    exact Finset.mem_map.mpr ⟨z, Finset.mem_univ z, rfl⟩

theorem isPrimitiveSUnitAffineCarrier_of_finite
    (S : Finset ℕ) (c : ℕ) [Finite (PrimitiveAffineSolution S c)] :
    IsPrimitiveSUnitAffineCarrier S c
      (primitiveAffineCarrierOfFinite S c) := by
  intro a b
  exact mem_primitiveAffineCarrierOfFinite S c a b

theorem finite_primitiveAffineSolution_of_carrier
    {S : Finset ℕ} {c : ℕ} {U : Finset (ℕ × ℕ)}
    (hU : IsPrimitiveSUnitAffineCarrier S c U) :
    Finite (PrimitiveAffineSolution S c) := by
  classical
  let target := {z : ℕ × ℕ // z ∈ U}
  let f : PrimitiveAffineSolution S c → target := fun z ↦
    ⟨z.1, (hU z.1.1 z.1.2).mpr z.2⟩
  apply Finite.of_injective f
  intro z w hzw
  apply Subtype.ext
  exact congrArg (fun q : target ↦ q.1) hzw

theorem normalizedSUnitA_isPrimeSupportUnit_of_affine
    {S : Finset ℕ} {h u v : ℕ}
    (hsol : IsSUnitAffineSolution S h u v) :
    IsPrimeSupportUnit S (normalizedSUnitA h u) := by
  refine ⟨normalizedSUnitA_pos hsol.1.pos, ?_⟩
  exact (Nat.primeFactors_mono (normalizedSUnitA_dvd_left h u)
    hsol.1.ne_zero).trans hsol.1.2

theorem normalizedSUnitB_isPrimeSupportUnit_of_affine
    {S : Finset ℕ} {h u v : ℕ}
    (hsol : IsSUnitAffineSolution S h u v) :
    IsPrimeSupportUnit S (normalizedSUnitB h u) := by
  have hvEq : v = u + h := hsol.2.2.symm
  subst v
  refine ⟨normalizedSUnitB_pos hsol.1.pos, ?_⟩
  exact (Nat.primeFactors_mono (normalizedSUnitB_dvd_right h u)
    hsol.2.1.ne_zero).trans hsol.2.1.2

/-- Every affine solution normalizes to a primitive equation with `c = h / gcd(u,u+h)`.-/
theorem normalized_isPrimitiveSUnitAffineSolution
    {S : Finset ℕ} {h u v : ℕ}
    (hsol : IsSUnitAffineSolution S h u v) :
    IsPrimitiveSUnitAffineSolution S (normalizedSUnitC h u)
      (normalizedSUnitA h u) (normalizedSUnitB h u) := by
  refine ⟨normalizedSUnitA_isPrimeSupportUnit_of_affine hsol,
    normalizedSUnitB_isPrimeSupportUnit_of_affine hsol,
    normalizedSUnit_coprime hsol.1.pos, normalizedSUnit_affine hsol.1.pos⟩

theorem IsPrimeSupportUnit.mul
    {S : Finset ℕ} {m n : ℕ}
    (hm : IsPrimeSupportUnit S m) (hn : IsPrimeSupportUnit S n) :
    IsPrimeSupportUnit S (m * n) := by
  refine ⟨Nat.mul_pos hm.pos hn.pos, ?_⟩
  change (m * n).primeFactors ⊆ S
  rw [Nat.primeFactors_mul hm.ne_zero hn.ne_zero]
  exact Finset.union_subset hm.2 hn.2

theorem diagonalGCD_mem_shift_divisors {h u : ℕ} (hh : 0 < h) :
    diagonalGCD h u ∈ h.divisors :=
  Nat.mem_divisors.mpr ⟨diagonalGCD_dvd_shift h u, hh.ne'⟩

/-- A family of exact primitive carriers, one for each possible common gcd divisor.-/
def IsPrimitiveDivisorCarrierFamily
    (S : Finset ℕ) (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : Prop :=
  ∀ g ∈ h.divisors,
    IsPrimitiveSUnitAffineCarrier S (h / g) (F g)

/-- Terminal finiteness input for all primitive equations indexed by divisors of `h`.-/
def TerminalPrimitiveDivisorSUnitFiniteness (h : ℕ) : Prop :=
  ∃ F : ℕ → Finset (ℕ × ℕ),
    IsPrimitiveDivisorCarrierFamily (primeSupport h) h F

/-- The irreducible Diophantine statement in type-theoretic form: every primitive equation indexed by a divisor of `h` has finitely many positive solutions.-/
def TerminalPrimitiveDivisorFiniteTypes (h : ℕ) : Prop :=
  ∀ g ∈ h.divisors,
    Finite (PrimitiveAffineSolution (primeSupport h) (h / g))

theorem terminalPrimitiveDivisorSUnitFiniteness_iff_finiteTypes (h : ℕ) :
    TerminalPrimitiveDivisorSUnitFiniteness h ↔
      TerminalPrimitiveDivisorFiniteTypes h := by
  constructor
  · rintro ⟨F, hF⟩ g hg
    exact finite_primitiveAffineSolution_of_carrier (hF g hg)
  · intro hfinite
    classical
    have hExists : ∀ g, ∃ U : Finset (ℕ × ℕ),
        g ∈ h.divisors →
          IsPrimitiveSUnitAffineCarrier (primeSupport h) (h / g) U := by
      intro g
      by_cases hg : g ∈ h.divisors
      · letI : Finite
            (PrimitiveAffineSolution (primeSupport h) (h / g)) :=
          hfinite g hg
        exact ⟨primitiveAffineCarrierOfFinite (primeSupport h) (h / g),
          fun _hg ↦ isPrimitiveSUnitAffineCarrier_of_finite
            (primeSupport h) (h / g)⟩
      · exact ⟨∅, fun hg' ↦ (hg hg').elim⟩
    choose F hF using hExists
    exact ⟨F, fun g hg ↦ hF g hg⟩

theorem divisor_isPrimeSupportUnit
    {h g : ℕ} (hh : 0 < h) (hg : g ∈ h.divisors) :
    IsPrimeSupportUnit (primeSupport h) g := by
  refine ⟨Nat.pos_of_mem_divisors hg, ?_⟩
  exact Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hg) hh.ne'

theorem primitive_reconstruction_isSUnitAffineSolution
    {h g a b : ℕ} (hh : 0 < h) (hg : g ∈ h.divisors)
    (hab : IsPrimitiveSUnitAffineSolution (primeSupport h) (h / g) a b) :
    IsSUnitAffineSolution (primeSupport h) h (g * a) (g * b) := by
  rcases hab with ⟨ha, hb, _hcop, hab⟩
  have hgUnit := divisor_isPrimeSupportUnit hh hg
  refine ⟨IsPrimeSupportUnit.mul hgUnit ha,
    IsPrimeSupportUnit.mul hgUnit hb, ?_⟩
  have hgDvd : g ∣ h := Nat.dvd_of_mem_divisors hg
  calc
    g * a + h = g * a + g * (h / g) := by
      rw [Nat.mul_div_cancel' hgDvd]
    _ = g * (a + h / g) := by ring
    _ = g * b := by rw [hab]

/-- Finiteness of the unnormalized equation implies finiteness of every primitive divisor equation: reconstruction is injective because its divisor `g` is positive.-/
theorem terminalPrimitiveDivisorFiniteTypes_of_terminalEvertse
    {h : ℕ} (hh : 0 < h) (hE : TerminalEvertseSUnitFiniteness h) :
    TerminalPrimitiveDivisorFiniteTypes h := by
  have hfinite : Finite (AffineSolution (primeSupport h) h) :=
    (terminalEvertseSUnitFiniteness_iff_finite h).mp hE
  intro g hg
  let f : PrimitiveAffineSolution (primeSupport h) (h / g) →
      AffineSolution (primeSupport h) h := fun z ↦
    ⟨(g * z.1.1, g * z.1.2),
      primitive_reconstruction_isSUnitAffineSolution hh hg z.2⟩
  letI : Finite (AffineSolution (primeSupport h) h) := hfinite
  apply Finite.of_injective f
  intro z w hzw
  apply Subtype.ext
  apply Prod.ext
  · apply Nat.mul_left_cancel (Nat.pos_of_mem_divisors hg)
    exact congrArg (fun q : AffineSolution (primeSupport h) h ↦ q.1.1) hzw
  · apply Nat.mul_left_cancel (Nat.pos_of_mem_divisors hg)
    exact congrArg (fun q : AffineSolution (primeSupport h) h ↦ q.1.2) hzw

/-- Reconstruct all unnormalized pairs from the finitely many primitive divisor equations.-/
def primitiveReconstruction
    (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact h.divisors.biUnion fun g ↦
    (F g).image fun z ↦ (g * z.1, g * z.2)

/-- Filtering the reconstruction makes soundness definitionally transparent; completeness is the normalization theorem below.-/
def affineCarrierFromPrimitive
    (S : Finset ℕ) (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) := by
  classical
  exact (primitiveReconstruction h F).filter fun z ↦
    IsSUnitAffineSolution S h z.1 z.2

theorem isSUnitAffineCarrier_affineCarrierFromPrimitive
    {S : Finset ℕ} {h : ℕ} (hh : 0 < h)
    {F : ℕ → Finset (ℕ × ℕ)}
    (hF : IsPrimitiveDivisorCarrierFamily S h F) :
    IsSUnitAffineCarrier S h (affineCarrierFromPrimitive S h F) := by
  classical
  intro u v
  constructor
  · intro huv
    exact (Finset.mem_filter.mp huv).2
  · intro hsol
    rw [affineCarrierFromPrimitive, Finset.mem_filter]
    refine ⟨?_, hsol⟩
    let g := diagonalGCD h u
    have hgMem : g ∈ h.divisors := diagonalGCD_mem_shift_divisors hh
    have hprimitive := normalized_isPrimitiveSUnitAffineSolution hsol
    have hnormalizedMem :
        (normalizedSUnitA h u, normalizedSUnitB h u) ∈ F g := by
      apply (hF g hgMem _ _).mpr
      simpa only [g, normalizedSUnitC] using hprimitive
    rw [primitiveReconstruction]
    apply Finset.mem_biUnion.mpr
    refine ⟨g, hgMem, Finset.mem_image.mpr ?_⟩
    refine ⟨(normalizedSUnitA h u, normalizedSUnitB h u),
      hnormalizedMem, ?_⟩
    apply Prod.ext
    · exact diagonalGCD_mul_normalizedSUnitA h u
    · exact (diagonalGCD_mul_normalizedSUnitB h u).trans hsol.2.2

theorem terminalEvertseSUnitFiniteness_of_primitiveDivisors
    {h : ℕ} (hh : 0 < h)
    (hprimitive : TerminalPrimitiveDivisorSUnitFiniteness h) :
    TerminalEvertseSUnitFiniteness h := by
  obtain ⟨F, hF⟩ := hprimitive
  exact ⟨affineCarrierFromPrimitive (primeSupport h) h F,
    isSUnitAffineCarrier_affineCarrierFromPrimitive hh hF⟩

theorem terminalEvertseSUnitFiniteness_of_primitiveFiniteTypes
    {h : ℕ} (hh : 0 < h)
    (hfinite : TerminalPrimitiveDivisorFiniteTypes h) :
    TerminalEvertseSUnitFiniteness h :=
  terminalEvertseSUnitFiniteness_of_primitiveDivisors hh
    ((terminalPrimitiveDivisorSUnitFiniteness_iff_finiteTypes h).mpr hfinite)

/-- For a positive shift, Evertse's terminal input is equivalent to finiteness of the normalized primitive equations.-/
theorem terminalEvertseSUnitFiniteness_iff_primitiveFiniteTypes
    {h : ℕ} (hh : 0 < h) :
    TerminalEvertseSUnitFiniteness h ↔
      TerminalPrimitiveDivisorFiniteTypes h := by
  constructor
  · exact terminalPrimitiveDivisorFiniteTypes_of_terminalEvertse hh
  · exact terminalEvertseSUnitFiniteness_of_primitiveFiniteTypes hh

/-! ## Quantitative specialization -/

/-- The direct quantitative form of the standard S-unit theorem needed here.-/
def TerminalQuantitativeSUnitBound (h : ℕ) : Prop :=
  ∃ U : Finset (ℕ × ℕ),
    IsSUnitAffineCarrier (primeSupport h) h U ∧
      U.card ≤ pptSameSupportBound h

theorem terminalEvertseSUnitFiniteness_of_quantitative
    {h : ℕ} (hquant : TerminalQuantitativeSUnitBound h) :
    TerminalEvertseSUnitFiniteness h := by
  obtain ⟨U, hU, _hcard⟩ := hquant
  exact ⟨U, hU⟩

theorem terminalPPTSameSupportBound_of_quantitative
    {h : ℕ} (hh : 0 < h) (hquant : TerminalQuantitativeSUnitBound h) :
    TerminalPPTSameSupportBound h := by
  obtain ⟨U, hU, hcard⟩ := hquant
  refine ⟨sameSupportCarrierFromSUnit h U,
    isSameSupportCarrier_sameSupportCarrierFromSUnit hh hU, ?_⟩
  exact (card_sameSupportCarrierFromSUnit_le h U).trans hcard

/-- Sum of primitive-carrier cardinalities over all divisors of `h`.-/
def primitiveFamilyCardSum
    (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) : ℕ :=
  h.divisors.sum fun g ↦ (F g).card

theorem card_primitiveReconstruction_le
    (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) :
    (primitiveReconstruction h F).card ≤ primitiveFamilyCardSum h F := by
  classical
  unfold primitiveReconstruction primitiveFamilyCardSum
  calc
    (h.divisors.biUnion fun g ↦
        (F g).image fun z ↦ (g * z.1, g * z.2)).card ≤
        h.divisors.sum fun g ↦
          ((F g).image fun z ↦ (g * z.1, g * z.2)).card :=
      Finset.card_biUnion_le
    _ ≤ h.divisors.sum fun g ↦ (F g).card := by
      apply Finset.sum_le_sum
      intro g _hg
      exact Finset.card_image_le

theorem card_affineCarrierFromPrimitive_le
    (S : Finset ℕ) (h : ℕ) (F : ℕ → Finset (ℕ × ℕ)) :
    (affineCarrierFromPrimitive S h F).card ≤ primitiveFamilyCardSum h F := by
  classical
  exact (Finset.card_filter_le _ _).trans (card_primitiveReconstruction_le h F)

/-- This is the exact quantitative Diophantine input left after normalization: the total number of primitive pairs over all common-gcd divisors has the PPT cardinality.-/
def TerminalPrimitiveDivisorPPTBound (h : ℕ) : Prop :=
  ∃ F : ℕ → Finset (ℕ × ℕ),
    IsPrimitiveDivisorCarrierFamily (primeSupport h) h F ∧
      primitiveFamilyCardSum h F ≤ pptSameSupportBound h

theorem terminalQuantitativeSUnitBound_of_primitivePPT
    {h : ℕ} (hh : 0 < h) (hPPT : TerminalPrimitiveDivisorPPTBound h) :
    TerminalQuantitativeSUnitBound h := by
  obtain ⟨F, hF, hcard⟩ := hPPT
  refine ⟨affineCarrierFromPrimitive (primeSupport h) h F,
    isSUnitAffineCarrier_affineCarrierFromPrimitive hh hF, ?_⟩
  exact (card_affineCarrierFromPrimitive_le (primeSupport h) h F).trans hcard

theorem terminalEvertseSUnitFiniteness_of_primitivePPT
    {h : ℕ} (hh : 0 < h) (hPPT : TerminalPrimitiveDivisorPPTBound h) :
    TerminalEvertseSUnitFiniteness h := by
  obtain ⟨F, hF, _hcard⟩ := hPPT
  exact terminalEvertseSUnitFiniteness_of_primitiveDivisors hh ⟨F, hF⟩

theorem terminalPPTSameSupportBound_of_primitivePPT
    {h : ℕ} (hh : 0 < h) (hPPT : TerminalPrimitiveDivisorPPTBound h) :
    TerminalPPTSameSupportBound h := by
  obtain ⟨F, hF, hcard⟩ := hPPT
  let U := affineCarrierFromPrimitive (primeSupport h) h F
  have hU : IsSUnitAffineCarrier (primeSupport h) h U :=
    isSUnitAffineCarrier_affineCarrierFromPrimitive hh hF
  refine ⟨sameSupportCarrierFromSUnit h U,
    isSameSupportCarrier_sameSupportCarrierFromSUnit hh hU, ?_⟩
  exact (card_sameSupportCarrierFromSUnit_le h U).trans
    ((card_affineCarrierFromPrimitive_le (primeSupport h) h F).trans hcard)

end SUnitTerminal

end

end RankAmplification
