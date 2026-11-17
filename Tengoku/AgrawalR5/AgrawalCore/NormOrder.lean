/-
Nucleo Lean della campagna Agrawal — decomposizione ordine/norma.

Se un elemento `u` di un gruppo finito soddisfa `u ^ m = b`, la formula
classica per l'ordine di una potenza dà

  orderOf b = orderOf u / gcd (orderOf u) m

e quindi

  orderOf u = orderOf b * gcd (orderOf u) m.

Il fattore residuo è a sua volta l'ordine di
`u ^ orderOf b`. Nell'applicazione ciclotomica:

  u = ζ₅ - 1,
  m = 1 + q + q² + q³,
  b = Norm_{F_{q⁴}/F_q}(u) = 5.

Questa unità formalizza soltanto il nucleo gruppale B–C. L'identità di
norma `u ^ m = 5` è un ingresso algebrico separato e non viene assunta come
assioma del progetto.
-/
import Tengoku.Seed.GroupTheory.OrderOfElement
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

variable {G : Type*} [Group G] [Finite G]

/-- L'ordine dell'immagine di una potenza è il quoziente dell'ordine
originario per il gcd con l'esponente.
@isnad1 id=eq.1h4v.s6.bff87a52592c from=translated src=- shape=d450af4d vocab=11849ef9
-/
theorem orderOf_norm_power
    (u b : G) (m : ℕ) (hNorm : u ^ m = b) :
    orderOf b = orderOf u / Nat.gcd (orderOf u) m := by
  subst b
  exact orderOf_pow u

/-- **DECOMPOSIZIONE ORDINE/NORMA.** Se `u ^ m = b`, l'ordine di `u`
si fattorizza esattamente nel prodotto dell'ordine di `b` e del fattore
che rimane nel nucleo della potenza `m`.
@isnad1 id=eq.1h4v.s6.ab8c19e8d088 from=translated src=- shape=5c9cbde2 vocab=3ea48d25
-/
theorem orderOf_norm_decomposition
    (u b : G) (m : ℕ) (hNorm : u ^ m = b) :
    orderOf u = orderOf b * Nat.gcd (orderOf u) m := by
  rw [orderOf_norm_power u b m hNorm]
  exact (Nat.div_mul_cancel (Nat.gcd_dvd_left (orderOf u) m)).symm

/-- Il fattore residuo della decomposizione è esso stesso un ordine:
è l'ordine di `u` elevato all'ordine della sua immagine `b`.
@isnad1 id=eq.1h4v.s6.18a94dc94324 from=translated src=- shape=89e2f00f vocab=d723f84f
-/
theorem orderOf_norm_kernel
    (u b : G) (m : ℕ) (hNorm : u ^ m = b) :
    orderOf (u ^ orderOf b) = Nat.gcd (orderOf u) m := by
  have hu : orderOf u ≠ 0 := Nat.ne_of_gt (orderOf_pos u)
  have hg : Nat.gcd (orderOf u) m ∣ orderOf u :=
    Nat.gcd_dvd_left (orderOf u) m
  rw [orderOf_norm_power u b m hNorm]
  exact orderOf_pow_orderOf_div hu hg

/-- In particolare, l'ordine dell'immagine divide l'ordine originario.
@isnad1 id=dvd.1h4v.s5.8f4c19b8ea47 from=translated src=- shape=a64765dd vocab=f8648084
-/
theorem orderOf_norm_power_dvd
    (u b : G) (m : ℕ) (hNorm : u ^ m = b) :
    orderOf b ∣ orderOf u := by
  rw [orderOf_norm_power u b m hNorm]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left (orderOf u) m)

/-- **Exact threshold in terms of the defect product.**

If `T * I = 10 * (q² - 1)` and `q ≥ 7`, then `T < q²` is equivalent
to `I ≥ 10`.  In the cyclotomic application `I` is the product of the
two odd defect indices.
@isnad1 id=iff.2h3v.s6.6b59566fec35 from=translated src=- shape=84b781f2 vocab=2da69026
-/
theorem defectProduct_threshold {q T I : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1)) :
    T < q ^ 2 ↔ 10 ≤ I := by
  have hq2 : 10 < q ^ 2 := by nlinarith
  constructor
  · intro hT
    by_contra hI
    have hIle : I ≤ 9 := by omega
    have hsub : q ^ 2 - 1 + 1 = q ^ 2 := by omega
    nlinarith
  · intro hI
    have hsub : q ^ 2 - 1 + 1 = q ^ 2 := by omega
    have hIpos : 0 < I := by omega
    nlinarith

/-- Since the two defect indices are odd, the first exceptional value is
`11`, not `10`.
@isnad1 id=iff.3h3v.s6.e2140ba74607 from=translated src=- shape=2c734641 vocab=b38b2e50
-/
theorem odd_defectProduct_threshold {q T I : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1))
    (hodd : Odd I) :
    T < q ^ 2 ↔ 11 ≤ I := by
  rw [defectProduct_threshold hq hexact]
  rcases hodd with ⟨k, rfl⟩
  omega

/-- Complementary normal-range formulation: for an odd defect product,
`T ≥ q²` holds exactly for the finite range `I ≤ 9`.
@isnad1 id=iff.3h3v.s6.c7f5136f2d10 from=translated src=- shape=3bf83620 vocab=a0f4404a
-/
theorem odd_defectProduct_normal_iff {q T I : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1))
    (hodd : Odd I) :
    q ^ 2 ≤ T ↔ I ≤ 9 := by
  have hthreshold := odd_defectProduct_threshold hq hexact hodd
  constructor
  · intro hT
    by_cases hI : I ≤ 9
    · exact hI
    · have h11 : 11 ≤ I := by
        rcases hodd with ⟨k, hk⟩
        omega
      have hlt : T < q ^ 2 := hthreshold.mpr h11
      omega
  · intro hI
    by_cases hT : q ^ 2 ≤ T
    · exact hT
    · have hlt : T < q ^ 2 := by omega
      have h11 : 11 ≤ I := hthreshold.mp hlt
      omega

/-- **Exact multiplier range.** Under the defect-product identity, a positive
multiple `h * T` lies below `q² - 1` exactly when `10h < I`. This is the
arithmetic core of the exact fiber-candidate count.
@isnad1 id=iff.2h4v.s7.5ffc958b3784 from=translated src=- shape=e9917da6 vocab=2da69026
-/
theorem defectMultiplier_iff {q T I h : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1)) :
    h * T < q ^ 2 - 1 ↔ 10 * h < I := by
  have hq2 : 1 < q ^ 2 := by nlinarith
  have hQ : 0 < q ^ 2 - 1 := by omega
  have hI : 0 < I := by
    by_contra h
    have hIz : I = 0 := by omega
    rw [hIz] at hexact
    nlinarith
  constructor
  · intro hlt
    have hm : (10 * h) * (q ^ 2 - 1) < I * (q ^ 2 - 1) := by
      calc
        (10 * h) * (q ^ 2 - 1) = h * (T * I) := by rw [hexact]; ring
        _ = (h * T) * I := by ring
        _ < (q ^ 2 - 1) * I := (Nat.mul_lt_mul_right hI).mpr hlt
        _ = I * (q ^ 2 - 1) := by ring
    exact (Nat.mul_lt_mul_right hQ).mp hm
  · intro hlt
    have hm : (h * T) * I < (q ^ 2 - 1) * I := by
      calc
        (h * T) * I = h * (T * I) := by ring
        _ = h * (10 * (q ^ 2 - 1)) := by rw [hexact]
        _ = (10 * h) * (q ^ 2 - 1) := by ring
        _ < I * (q ^ 2 - 1) := (Nat.mul_lt_mul_right hQ).mpr hlt
        _ = (q ^ 2 - 1) * I := by ring
    exact (Nat.mul_lt_mul_right hI).mp hm

/-- Quotient form of the exact multiplier range. Hence each final-row branch
has exactly `(I - 1) / 10` admissible positive multipliers.
@isnad1 id=iff.2h4v.s7.9a98003c96b8 from=translated src=- shape=734fe746 vocab=ec125bd5
-/
theorem defectMultiplier_le_div_iff {q T I h : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1)) :
    h * T < q ^ 2 - 1 ↔ h ≤ (I - 1) / 10 := by
  have hI : 0 < I := by
    by_contra h
    have hIz : I = 0 := by omega
    rw [hIz] at hexact
    have hq2 : 1 < q ^ 2 := by nlinarith
    omega
  rw [defectMultiplier_iff hq hexact]
  omega

/-- Exact candidate range in the pure branch `P = 1 + hT`.
@isnad1 id=iff.2h4v.s7.9f2c6dfb7d5d from=translated src=- shape=5a7c6153 vocab=b68d0884
-/
theorem pureCandidate_below_sq_iff {q T I h : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1)) :
    1 + h * T < q ^ 2 ↔ h ≤ (I - 1) / 10 := by
  rw [← defectMultiplier_le_div_iff hq hexact]
  omega

/-- Exact candidate range in the twisted branch `P = q² - hT`.
@isnad1 id=iff.2h4v.s7.0273c528942b from=translated src=- shape=48584511 vocab=ec125bd5
-/
theorem twistedCandidate_positive_iff {q T I h : ℕ}
    (hq : 7 ≤ q) (hexact : T * I = 10 * (q ^ 2 - 1)) :
    1 < q ^ 2 - h * T ↔ h ≤ (I - 1) / 10 := by
  rw [← defectMultiplier_le_div_iff hq hexact]
  omega

end AgrawalCore
