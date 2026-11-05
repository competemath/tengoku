module

public import Tengoku.LanaPi1.Pi1.Orbicurve.SubfieldGalois
public import Tengoku.LanaPi1.Pi1.Orbicurve.GaloisPi1
public import Tengoku.Seed.RingTheory.Valuation.LocalSubring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Valuation-theoretic inertia and inertia of primes of coordinate rings

Let `Ω / K₀` (`K₀ = k(t)`) be a Galois extension and `W` a valuation subring of `Ω` *centered on
the `t`-line*: `k ⊆ W` and `t ∈ W` (`AffOrbicurve.IsCentered`). For an intermediate field `N`,
finite over `K₀`, the coordinate ring `coordRing k t N` is contained in `W`
(`AffOrbicurve.toΩ_mem`), and the center of `W` on it is the prime ideal

  `u_W(N) = {a ∈ coordRing k t N | v_W(a) < 1}` (`AffOrbicurve.centerIdeal`),

maximal when nonzero (`AffOrbicurve.isMaximal_centerIdeal`).

* `AffOrbicurve.restrictNormal_mem_inertia`: for `N / K₀` normal, the restriction to `N` of an
  element of the inertia group `GaloisPi1.inertia W` lies in the inertia group of `u_W(N)`
  (and in `Gal(N / L)` if it fixes `L`: `AffOrbicurve.restrictNormal_mem_fixSub`);
* `AffOrbicurve.exists_mem_inertia_restrictNormal_eq`: conversely, in characteristic `0`, for
  `N / K₀` finite Galois and `u_W(N) ≠ 0`, every element of the inertia group of `u_W(N)` is the
  restriction of an element of `GaloisPi1.inertia W` (surjectivity of inertia). The proof lifts
  compatibly to all finite Galois `M ⊇ N` (by counting: `|I_{u_W(M)}(M / K₀)| = e`, and `e` is
  multiplicative in towers) and concludes by compactness of `Gal(Ω / K₀)`.
-/

@[expose] public section

universe u

open Ideal IntermediateField IntermediateField.algebraAdjoinAdjoin Polynomial

namespace AffOrbicurve

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] {t : Ω}

section Center

variable (k t) in
/-- A valuation subring `W` of `Ω` is **centered on the `t`-line** if it contains `k` and `t`
(equivalently, `k[t] ⊆ W`).-/
def IsCentered (W : ValuationSubring Ω) : Prop :=
  (∀ c : k, algebraMap k Ω c ∈ W) ∧ t ∈ W

variable (t) in
/-- The inclusion of the coordinate ring `coordRing k t L` into `Ω`.-/
def toΩ (L : IntermediateField (K₀ k t) Ω) : coordRing k t L →+* Ω :=
  (L.val : L →+* Ω).comp (coordRing k t L).val.toRingHom

@[simp] lemma toΩ_apply (L : IntermediateField (K₀ k t) Ω) (a : coordRing k t L) :
    toΩ t L a = ((a : L) : Ω) := rfl

lemma toΩ_injective (L : IntermediateField (K₀ k t) Ω) : Function.Injective (toΩ t L) :=
  fun _ _ h => Subtype.val_injective (Subtype.val_injective h)

variable {W : ValuationSubring Ω}

lemma A₀_le (hW : IsCentered k t W) (x : A₀ k t) : (x : Ω) ∈ W := by
  have key : ∀ y ∈ Algebra.adjoin k {t}, y ∈ W := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact hW.2
    | algebraMap c => exact hW.1 c
    | add y z _ _ hy hz => exact W.add_mem _ _ hy hz
    | mul y z _ _ hy hz => exact W.mul_mem _ _ hy hz
  exact key x x.2

/-- Elements of the coordinate ring lie in every valuation subring centered on the `t`-line
(valuation rings are integrally closed).-/
lemma toΩ_mem (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) (a : coordRing k t L) :
    toΩ t L a ∈ W := by
  obtain ⟨p, hp, hpa⟩ := a.2
  let φ : A₀ k t →+* W :=
    { toFun x := ⟨x, A₀_le hW x⟩
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hint : IsIntegral W (toΩ t L a) := by
    refine ⟨p.map φ, hp.map φ, ?_⟩
    have hc : (algebraMap W Ω).comp φ = (L.val : L →+* Ω).comp (algebraMap (A₀ k t) L) :=
      RingHom.ext fun _ => rfl
    rw [Polynomial.eval₂_map, hc, toΩ_apply]
    have := Polynomial.hom_eval₂ p (algebraMap (A₀ k t) L) (L.val : L →+* Ω) (a : L)
    rw [hpa, map_zero] at this
    exact this.symm
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

/-- `coordRing k t L → W`.-/
def toW (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) : coordRing k t L →+* W :=
  (toΩ t L).codRestrict W.toSubring (toΩ_mem hW L)

/-- **The center of `W` on the normalization of the `t`-line in `L`**: the prime ideal
`u_W(L) = {a ∈ coordRing k t L | a ∈ nonunits W}`.-/
def centerIdeal (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) :
    Ideal (coordRing k t L) :=
  (IsLocalRing.maximalIdeal W).comap (toW hW L)

instance (hW : IsCentered k t W) (L : IntermediateField (K₀ k t) Ω) :
    (centerIdeal hW L).IsPrime :=
  Ideal.comap_isPrime _ _

lemma mem_centerIdeal (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    {a : coordRing k t L} : a ∈ centerIdeal hW L ↔ W.valuation (toΩ t L a) < 1 :=
  W.valuation_lt_one_iff (toW hW L a)

lemma mem_centerIdeal_iff_mem_nonunits (hW : IsCentered k t W)
    {L : IntermediateField (K₀ k t) Ω} {a : coordRing k t L} :
    a ∈ centerIdeal hW L ↔ (⟨toΩ t L a, toΩ_mem hW L a⟩ : W) ∈ nonunits W :=
  Iff.rfl

lemma valuation_eq_one_of_notMem (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    {a : coordRing k t L} (ha : a ∉ centerIdeal hW L) : W.valuation (toΩ t L a) = 1 := by
  rw [mem_centerIdeal, not_lt] at ha
  exact le_antisymm ((W.valuation_le_one_iff _).mpr (toΩ_mem hW L a)) ha

lemma valuation_le_one (hW : IsCentered k t W) {L : IntermediateField (K₀ k t) Ω}
    (a : coordRing k t L) : W.valuation (toΩ t L a) ≤ 1 :=
  (W.valuation_le_one_iff _).mpr (toΩ_mem hW L a)

/-- `u_W(L)` is maximal when nonzero.-/
lemma isMaximal_centerIdeal (ht : Transcendental k t) (hW : IsCentered k t W)
    (L : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) L]
    [Algebra.IsSeparable (K₀ k t) L] (h : centerIdeal hW L ≠ ⊥) : (centerIdeal hW L).IsMaximal :=
  haveI := isDedekindDomain_ring t ht L
  Ring.DimensionLEOne.maximalOfPrime h inferInstance

/-- The centers are compatible: `u_W(M) ∩ coordRing k t L = u_W(L)` for `L ⊆ M`.-/
lemma comap_centerIdeal (hW : IsCentered k t W) {L M : IntermediateField (K₀ k t) Ω}
    (h : L ≤ M) : (centerIdeal hW M).comap (ringMap t h) = centerIdeal hW L := by
  ext a
  simp only [Ideal.mem_comap, mem_centerIdeal]
  rfl

lemma centerIdeal_ne_bot_of_le (hW : IsCentered k t W) {L M : IntermediateField (K₀ k t) Ω}
    (h : L ≤ M) (hL : centerIdeal hW L ≠ ⊥) : centerIdeal hW M ≠ ⊥ := by
  intro hM
  apply hL
  rw [← comap_centerIdeal hW h, hM, ← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (ringMap_injective t h)

end Center

section Restriction

variable {W : ValuationSubring Ω}

variable (W) in
/-- `σ` acts trivially modulo the maximal ideal of `W` on the coordinate ring of `M`:
`v_W(σ b - b) < 1` for all `b ∈ coordRing k t M`.-/
def IsInertialOn (M : IntermediateField (K₀ k t) Ω) (σ : Ω ≃ₐ[K₀ k t] Ω) : Prop :=
  ∀ b : coordRing k t M, W.valuation (σ (toΩ t M b) - toΩ t M b) < 1

lemma isInertialOn_of_mem_inertia (hW : IsCentered k t W) (M : IntermediateField (K₀ k t) Ω)
    {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) : IsInertialOn W M σ :=
  fun b => hσ _ (toΩ_mem hW M b)

lemma IsInertialOn.mono {L M : IntermediateField (K₀ k t) Ω} (h : L ≤ M) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : IsInertialOn W M σ) : IsInertialOn W L σ :=
  fun b => hσ (ringMap t h b)

@[simp] lemma coe_restrictNormal_apply (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N]
    (σ : Ω ≃ₐ[K₀ k t] Ω) (x : N) : ((σ.restrictNormal N x : N) : Ω) = σ (x : Ω) :=
  AlgEquiv.restrictNormal_apply N σ x

lemma mem_inertia_centerIdeal_iff (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    (ρ : N ≃ₐ[K₀ k t] N) :
    ρ ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ↔
      ∀ b : coordRing k t N, W.valuation ((ρ (b : N) : Ω) - toΩ t N b) < 1 := by
  simp only [Ideal.inertia, AddSubgroup.mem_inertia]
  refine forall_congr' fun b => ?_
  rw [Submodule.mem_toAddSubgroup, mem_centerIdeal]
  rfl

/-- The restriction of `σ` to `N` lies in the inertia group of `u_W(N)` iff `σ` acts trivially
on `coordRing k t N` modulo the maximal ideal of `W`.-/
lemma restrictNormal_mem_inertia_iff (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    [Normal (K₀ k t) N] (σ : Ω ≃ₐ[K₀ k t] Ω) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ↔ IsInertialOn W N σ := by
  rw [mem_inertia_centerIdeal_iff]
  simp only [coe_restrictNormal_apply]
  rfl

/-- **Restriction of inertia**: the restriction to `N` (normal over `K₀`) of an element of the
inertia group of `W` lies in the inertia group of the center `u_W(N)`.-/
theorem restrictNormal_mem_inertia (hW : IsCentered k t W) (N : IntermediateField (K₀ k t) Ω)
    [Normal (K₀ k t) N] {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) :=
  (restrictNormal_mem_inertia_iff hW N σ).mpr (isInertialOn_of_mem_inertia hW N hσ)

/-- The restriction to `N` of an automorphism fixing `L` lies in `Gal(N / L) = fixSub t N L`.-/
theorem restrictNormal_mem_fixSub (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N]
    {L : IntermediateField (K₀ k t) Ω} {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ L.fixingSubgroup) :
    σ.restrictNormal N ∈ fixSub t N L := by
  intro x hx
  apply Subtype.val_injective
  rw [coe_restrictNormal_apply]
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ hx

/-- **Restriction of inertia** (relative version): for `σ ∈ I_W ∩ Aut(Ω / L)`, the restriction
of `σ` to `N` lies in `I_{u_W(N)}(N / K₀) ∩ Gal(N / L)`.-/
theorem restrictNormal_mem_inertia_inf_fixSub (hW : IsCentered k t W)
    (N : IntermediateField (K₀ k t) Ω) [Normal (K₀ k t) N] {L : IntermediateField (K₀ k t) Ω}
    {σ : Ω ≃ₐ[K₀ k t] Ω} (hσ : σ ∈ GaloisPi1.inertia W) (hσL : σ ∈ L.fixingSubgroup) :
    σ.restrictNormal N ∈ (centerIdeal hW N).inertia (N ≃ₐ[K₀ k t] N) ⊓ fixSub t N L :=
  ⟨restrictNormal_mem_inertia hW N hσ, restrictNormal_mem_fixSub N hσL⟩

end Restriction

section Localization

variable {W : ValuationSubring Ω}

set_option maxHeartbeats 1000000 in
/-- If `u_W(M) ≠ 0`, every element of `W ∩ M` is a quotient `b / s` of elements of the coordinate
ring of `M` with `s ∉ u_W(M)` (`W ∩ M` is the localization of the coordinate ring at `u_W(M)`,
a discrete valuation ring).-/
lemma exists_eq_div (ht : Transcendental k t) (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) M]
    [Algebra.IsSeparable (K₀ k t) M] (hM : centerIdeal hW M ≠ ⊥) {x : Ω} (hxM : x ∈ M)
    (hxW : x ∈ W) : ∃ b s : coordRing k t M, s ∉ centerIdeal hW M ∧
      x = toΩ t M b / toΩ t M s := by
  haveI := isDedekindDomain_ring t ht M
  haveI := isFractionRing_coordRing t M
  set p := centerIdeal hW M
  obtain ⟨b₀, s₀, hs₀, hx⟩ := IsFractionRing.div_surjective (coordRing k t M) (⟨x, hxM⟩ : M)
  have hx' : x = toΩ t M b₀ / toΩ t M s₀ := by
    have := congrArg (fun y : M => (y : Ω)) hx
    simp only [IntermediateField.coe_div] at this
    exact this.symm
  have hs₀' : toΩ t M s₀ ≠ 0 := by
    rw [← map_zero (toΩ t M), (toΩ_injective M).ne_iff]
    exact nonZeroDivisors.ne_zero hs₀
  let R := Localization.AtPrime p
  letI : Algebra (coordRing k t M) R := OreLocalization.instAlgebra
  haveI : IsLocalization.AtPrime R p := Localization.isLocalization
  haveI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hM R
  have hinj : Function.Injective (algebraMap (coordRing k t M) R) :=
    IsLocalization.injective R p.primeCompl_le_nonZeroDivisors
  obtain ⟨z, hz⟩ := ValuationRing.cond (algebraMap _ R b₀) (algebraMap _ R s₀)
  obtain ⟨⟨c, d⟩, hcd⟩ := IsLocalization.surj p.primeCompl z
  simp only at hcd
  have hd : (d : coordRing k t M) ∉ p := d.2
  have hd' : toΩ t M d ≠ 0 := by
    intro h0
    apply hd
    rw [← map_zero (toΩ t M)] at h0
    rw [toΩ_injective M h0]
    exact p.zero_mem
  rcases hz with hz | hz
  · -- `b₀ c = s₀ d`
    have h1 : b₀ * c = s₀ * d := by
      apply hinj
      rw [map_mul, map_mul, ← hcd, ← mul_assoc, hz]
    have h1' := congrArg (toΩ t M) h1
    rw [map_mul, map_mul] at h1'
    have hc' : toΩ t M c ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at h1'
      exact mul_ne_zero hs₀' hd' h1'.symm
    have hxdc : x = toΩ t M d / toΩ t M c := by
      rw [hx', div_eq_div_iff hs₀' hc', h1', mul_comm]
    by_cases hc : c ∈ p
    · exfalso
      have hxc : x * toΩ t M c = toΩ t M d := by rw [hxdc, div_mul_cancel₀ _ hc']
      have h2 := congrArg W.valuation hxc
      rw [map_mul, valuation_eq_one_of_notMem hW hd] at h2
      have hv : W.valuation x ≤ 1 := (W.valuation_le_one_iff x).mpr hxW
      have hvc : W.valuation (toΩ t M c) < 1 := (mem_centerIdeal hW).mp hc
      have : W.valuation x * W.valuation (toΩ t M c) < 1 :=
        lt_of_le_of_lt (by simpa using mul_le_mul_left hv (W.valuation (toΩ t M c))) hvc
      rw [h2] at this
      exact lt_irrefl _ this
    · exact ⟨d, c, hc, hxdc⟩
  · -- `s₀ c = b₀ d`
    have h1 : s₀ * c = b₀ * d := by
      apply hinj
      rw [map_mul, map_mul, ← hcd, ← mul_assoc, hz]
    have h1' := congrArg (toΩ t M) h1
    rw [map_mul, map_mul] at h1'
    refine ⟨c, d, hd, ?_⟩
    rw [hx', div_eq_div_iff hs₀' hd', ← h1', mul_comm]

/-- If `σ` acts trivially on the coordinate ring of `M` modulo the maximal ideal of `W` and
`u_W(M) ≠ 0`, then `σ` acts trivially on `W ∩ M` modulo the maximal ideal of `W`.-/
lemma valuation_sub_lt_one (ht : Transcendental k t) (hW : IsCentered k t W)
    (M : IntermediateField (K₀ k t) Ω) [FiniteDimensional (K₀ k t) M]
    [Algebra.IsSeparable (K₀ k t) M] (hM : centerIdeal hW M ≠ ⊥) {σ : Ω ≃ₐ[K₀ k t] Ω}
    (hσ : IsInertialOn W M σ) {x : Ω} (hxM : x ∈ M) (hxW : x ∈ W) :
    W.valuation (σ x - x) < 1 := by
  obtain ⟨b, s, hs, rfl⟩ := exists_eq_div ht hW M hM hxM hxW
  set B := toΩ t M b
  set S := toΩ t M s
  have hS : W.valuation S = 1 := valuation_eq_one_of_notMem hW hs
  have hS0 : S ≠ 0 := by
    intro h; rw [h, map_zero] at hS; exact zero_ne_one hS
  have hσS : W.valuation (σ S) = 1 := by
    have := Valuation.map_add_eq_of_lt_right W.valuation (x := σ S - S) (y := S)
      (by rw [hS]; exact hσ s)
    rwa [sub_add_cancel, hS] at this
  have hσS0 : σ S ≠ 0 := by
    intro h; rw [h, map_zero] at hσS; exact zero_ne_one hσS
  have heq : σ (B / S) - B / S = (S * (σ B - B) - B * (σ S - S)) / (σ S * S) := by
    rw [map_div₀]
    field_simp
    ring
  rw [heq, map_div₀, map_mul, hS, hσS, mul_one, div_one]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, hS, one_mul]; exact hσ b
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (valuation_le_one hW b)) (hσ s)

end Localization

section Lifting

variable {W : ValuationSubring Ω}

lemma fixSub_bot (N : IntermediateField (K₀ k t) Ω) : fixSub t N ⊥ = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x hx => ?_
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hx
  have : x = algebraMap (K₀ k t) N c := Subtype.ext hc.symm
  rw [this, AlgEquiv.commutes]

variable [CharZero k]

end Lifting

end AffOrbicurve
