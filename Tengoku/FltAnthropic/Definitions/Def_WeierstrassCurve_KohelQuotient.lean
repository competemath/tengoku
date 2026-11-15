import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluQuotientOfSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R]

def rootESymm (h : R[X]) (k : ℕ) : R :=
  if k ≤ h.natDegree then (-1) ^ k * h.coeff (h.natDegree - k) else 0

def rootPowerSumOne (h : R[X]) : R := h.rootESymm 1

def rootPowerSumTwo (h : R[X]) : R := h.rootESymm 1 ^ 2 - 2 * h.rootESymm 2

def rootPowerSumThree (h : R[X]) : R :=
  h.rootESymm 1 ^ 3 - 3 * h.rootESymm 1 * h.rootESymm 2 + 3 * h.rootESymm 3

/--
@isnad1 id=eq.0h2v.s5.0b55b4f263a9 from=translated src=- shape=6993dcff vocab=14bfabe5
-/
@[simp] theorem rootESymm_zero_right (h : R[X]) : h.rootESymm 0 = h.leadingCoeff := by
  simp only [rootESymm, zero_le, ite_true, pow_zero, one_mul, Nat.sub_zero]
  rfl

/--
@isnad1 id=eq.1h3v.s5.08b624df0035 from=translated src=- shape=50e5445d vocab=26636e65
-/
theorem rootESymm_of_lt {h : R[X]} {k : ℕ} (hk : h.natDegree < k) : h.rootESymm k = 0 := by
  simp [rootESymm, not_le.mpr hk]

/--
@isnad1 id=eq.1h3v.s6.808bc5ab237d from=translated src=- shape=0a0f7481 vocab=0d5551e5
-/
theorem rootESymm_of_le {h : R[X]} {k : ℕ} (hk : k ≤ h.natDegree) :
    h.rootESymm k = (-1) ^ k * h.coeff (h.natDegree - k) := by
  simp [rootESymm, hk]

/--
@isnad1 id=eq.0h2v.s6.01ef77486cbe from=translated src=- shape=759c4642 vocab=1557c7af
-/
@[simp] theorem rootESymm_one (k : ℕ) : (1 : R[X]).rootESymm k = if k = 0 then 1 else 0 := by
  rcases k with _ | k
  · simp
  · simp [rootESymm]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

/--
@isnad1 id=eq.1h5v.s7.b552bb318f22 from=translated src=- shape=08dab71e vocab=e8e0fabd
-/
theorem rootESymm_map {h : R[X]} (hh : f h.leadingCoeff ≠ 0) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  simp only [rootESymm, natDegree_map_of_leadingCoeff_ne_zero f hh, coeff_map]
  split_ifs <;> simp

/--
@isnad1 id=eq.1h5v.s6.5fc966ab2e9c from=translated src=- shape=d1410e2a vocab=183736d6
-/
theorem rootESymm_map_of_monic {h : R[X]} (hh : h.Monic) (k : ℕ) :
    (h.map f).rootESymm k = f (h.rootESymm k) := by
  nontriviality S
  exact rootESymm_map f (by rw [hh.leadingCoeff, map_one]; exact one_ne_zero) k

/--
@isnad1 id=eq.1h4v.s6.fa2e27d7c32f from=translated src=- shape=e719184f vocab=c0e107ec
-/
theorem rootPowerSumOne_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumOne = f h.rootPowerSumOne := by
  simp [rootPowerSumOne, rootESymm_map_of_monic f hh]

/--
@isnad1 id=eq.1h4v.s6.deae1774d6fc from=translated src=- shape=e719184f vocab=26d83325
-/
theorem rootPowerSumTwo_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumTwo = f h.rootPowerSumTwo := by
  simp [rootPowerSumTwo, rootESymm_map_of_monic f hh, map_ofNat]

/--
@isnad1 id=eq.1h4v.s6.cd3f6b327bcd from=translated src=- shape=e719184f vocab=7d43446d
-/
theorem rootPowerSumThree_map_of_monic {h : R[X]} (hh : h.Monic) :
    (h.map f).rootPowerSumThree = f h.rootPowerSumThree := by
  simp [rootPowerSumThree, rootESymm_map_of_monic f hh, map_ofNat]

end map

end Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def kohelT (h : R[X]) : R :=
  6 * h.rootPowerSumTwo + W.b₂ * h.rootPowerSumOne + h.natDegree * W.b₄

def kohelW (h : R[X]) : R :=
  10 * h.rootPowerSumThree + 2 * W.b₂ * h.rootPowerSumTwo + 3 * W.b₄ * h.rootPowerSumOne
    + h.natDegree * W.b₆

def kohelQuotient (h : R[X]) : WeierstrassCurve R :=
  W.veluQuotientOfSums (W.kohelT h) (W.kohelW h)

/--
@isnad1 id=eq.0h3v.s4.79ea8ab73eb0 from=translated src=- shape=cc5db9fa vocab=b6ea313d
-/
@[simp] theorem kohelQuotient_a₁ (h : R[X]) : (W.kohelQuotient h).a₁ = W.a₁ := rfl
/--
@isnad1 id=eq.0h3v.s4.61bba991984e from=translated src=- shape=cc5db9fa vocab=d76c0931
-/
@[simp] theorem kohelQuotient_a₂ (h : R[X]) : (W.kohelQuotient h).a₂ = W.a₂ := rfl
/--
@isnad1 id=eq.0h3v.s4.ad72aeb2837a from=translated src=- shape=cc5db9fa vocab=99a7cbf2
-/
@[simp] theorem kohelQuotient_a₃ (h : R[X]) : (W.kohelQuotient h).a₃ = W.a₃ := rfl

/--
@isnad1 id=eq.0h2v.s5.bfbfbbecf518 from=translated src=- shape=b1b49ee2 vocab=e57a16f7
-/
@[simp] theorem kohelT_one : W.kohelT 1 = 0 := by
  simp [kohelT, rootPowerSumOne, rootPowerSumTwo]

/--
@isnad1 id=eq.0h2v.s5.c26b7ebc3dd5 from=translated src=- shape=b1b49ee2 vocab=d575e774
-/
@[simp] theorem kohelW_one : W.kohelW 1 = 0 := by
  simp [kohelW, rootPowerSumOne, rootPowerSumTwo, rootPowerSumThree]

/--
@isnad1 id=eq.0h2v.s5.68f0e3d11814 from=translated src=- shape=78923670 vocab=fe89369d
-/
@[simp] theorem kohelQuotient_one : W.kohelQuotient 1 = W := by
  ext <;> simp [kohelQuotient, veluQuotientOfSums]

section map

variable {S : Type*} [CommRing S] (f : R →+* S)

/--
@isnad1 id=eq.1h5v.s6.4475b69fea5c from=translated src=- shape=df54bb6c vocab=aacd9301
-/
theorem map_kohelT {h : R[X]} (hh : h.Monic) : f (W.kohelT h) = (W.map f).kohelT (h.map f) := by
  nontriviality S
  simp [kohelT, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    hh.natDegree_map, map_ofNat]

/--
@isnad1 id=eq.1h5v.s6.78c03edc5543 from=translated src=- shape=df54bb6c vocab=e929e1dd
-/
theorem map_kohelW {h : R[X]} (hh : h.Monic) : f (W.kohelW h) = (W.map f).kohelW (h.map f) := by
  nontriviality S
  simp [kohelW, rootPowerSumOne_map_of_monic f hh, rootPowerSumTwo_map_of_monic f hh,
    rootPowerSumThree_map_of_monic f hh, hh.natDegree_map, map_ofNat]

/--
@isnad1 id=eq.1h5v.s6.b82d5f194413 from=translated src=- shape=c95c3b90 vocab=248d6105
-/
theorem map_kohelQuotient {h : R[X]} (hh : h.Monic) :
    (W.kohelQuotient h).map f = (W.map f).kohelQuotient (h.map f) := by
  ext
  · rfl
  · rfl
  · rfl
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_ofNat]
  · simp [kohelQuotient, veluQuotientOfSums, map_kohelT W f hh, map_kohelW W f hh, map_ofNat]

/--
@isnad1 id=eq.1h5v.s7.8f76ce702fcb from=translated src=- shape=722df65e vocab=764ae4d0
-/
theorem kohelQuotient_map_j {K L : Type*} [Field K] [Field L] (f : K →+* L) (V : WeierstrassCurve K)
    {h : K[X]} (hh : h.Monic) [(V.kohelQuotient h).IsElliptic]
    [((V.map f).kohelQuotient (h.map f)).IsElliptic] :
    ((V.map f).kohelQuotient (h.map f)).j = f (V.kohelQuotient h).j := by
  have := (V.kohelQuotient h).map_j f
  simp only [map_kohelQuotient V f hh] at this
  convert this using 2

end map

end WeierstrassCurve
