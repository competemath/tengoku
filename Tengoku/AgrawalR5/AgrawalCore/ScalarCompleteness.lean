/-
Nucleo Lean della campagna Agrawal — lotto 21: COMPLETEZZA SCALARE.

Obiettivo del modulo: formalizzare la direzione conversa del ponte H4.
Il punto aritmetico di partenza è `p ∣ Hₙ`; il punto locale di arrivo è
l'esistenza di un esponente nella classe `2 mod 5` che realizza la riga
letterale di `S(p,5)`.

La riparazione del difetto negativo è resa costruttiva: se `m = 2n-1`
produce il segno `-1`, si usa

  m' = m + 5 * (m^2 - 1).

Il nuovo addendo è divisibile per 10 e porta simultaneamente ciascun
generatore ciclotomico a `-1`.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.LocalTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

set_option maxHeartbeats 3000000

/-- `Φ₅` è monico nella normalizzazione usata dal progetto.-/
lemma phi5_monic : (phi5 p).Monic := by
  unfold phi5
  have hdeg :
      degree (X ^ 3 + X ^ 2 + X + 1 : Polynomial (ZMod p)) ≤ 3 := by
    compute_degree!
  have hlt :
      degree (X ^ 3 + X ^ 2 + X + 1 : Polynomial (ZMod p)) < 4 := by
    exact hdeg.trans_lt (by norm_num)
  simpa only [add_assoc] using
    (monic_X_pow_add (n := 4) hlt)

/-- L'automorfismo ciclotomico `ζ ↦ ζ²`, inizialmente come endomorfismo.-/
noncomputable def sigmaTwo : Phi5Ring p →+* Phi5Ring p :=
  AdjoinRoot.lift (AdjoinRoot.of (phi5 p)) (zeta5 ^ 2) (by
    simpa [Polynomial.aeval_def, AdjoinRoot.algebraMap_eq'] using
      phi5_aeval_zeta_pow_two (p := p))

@[simp]
lemma sigmaTwo_zeta :
    sigmaTwo (p := p) zeta5 = zeta5 ^ 2 := by
  exact AdjoinRoot.lift_root _

@[simp]
lemma sigmaTwo_base (x : ZMod p) :
    sigmaTwo (p := p) (AdjoinRoot.of (phi5 p) x)
      = AdjoinRoot.of (phi5 p) x := by
  exact AdjoinRoot.lift_of _

/-- Traccia lungo l'orbita `1,2,4,3` di `Gal(Q(ζ₅)/Q)`.-/
noncomputable def cycloTraceFour (x : Phi5Ring p) : Phi5Ring p :=
  x + sigmaTwo x + sigmaTwo (sigmaTwo x)
    + sigmaTwo (sigmaTwo (sigmaTwo x))

lemma cycloTraceFour_add (x y : Phi5Ring p) :
    cycloTraceFour (x + y) = cycloTraceFour x + cycloTraceFour y := by
  simp only [cycloTraceFour, map_add]
  ring

lemma zeta5_orbit_sum (n : ℕ) :
    ∃ c : ZMod p,
      (zeta5 : Phi5Ring p) ^ n + zeta5 ^ (2 * n)
        + zeta5 ^ (4 * n) + zeta5 ^ (3 * n)
          = AdjoinRoot.of (phi5 p) c := by
  have hn : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2
      ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
  rcases hn with hn | hn | hn | hn | hn
  · refine ⟨4, ?_⟩
    rw [zeta5_pow_mod n, zeta5_pow_mod (2 * n),
      zeta5_pow_mod (4 * n), zeta5_pow_mod (3 * n)]
    have h2 : (2 * n) % 5 = 0 := by omega
    have h4 : (4 * n) % 5 = 0 := by omega
    have h3 : (3 * n) % 5 = 0 := by omega
    rw [hn, h2, h4, h3]
    rw [map_ofNat]
    norm_num
  · refine ⟨-1, ?_⟩
    rw [zeta5_pow_mod n, zeta5_pow_mod (2 * n),
      zeta5_pow_mod (4 * n), zeta5_pow_mod (3 * n)]
    have h2 : (2 * n) % 5 = 2 := by omega
    have h4 : (4 * n) % 5 = 4 := by omega
    have h3 : (3 * n) % 5 = 3 := by omega
    rw [hn, h2, h4, h3]
    have hz := zeta5_rel (p := p)
    rw [map_neg, map_one]
    linear_combination hz
  · refine ⟨-1, ?_⟩
    rw [zeta5_pow_mod n, zeta5_pow_mod (2 * n),
      zeta5_pow_mod (4 * n), zeta5_pow_mod (3 * n)]
    have h2 : (2 * n) % 5 = 4 := by omega
    have h4 : (4 * n) % 5 = 3 := by omega
    have h3 : (3 * n) % 5 = 1 := by omega
    rw [hn, h2, h4, h3, pow_one]
    have hz := zeta5_rel (p := p)
    rw [map_neg, map_one]
    linear_combination hz
  · refine ⟨-1, ?_⟩
    rw [zeta5_pow_mod n, zeta5_pow_mod (2 * n),
      zeta5_pow_mod (4 * n), zeta5_pow_mod (3 * n)]
    have h2 : (2 * n) % 5 = 1 := by omega
    have h4 : (4 * n) % 5 = 2 := by omega
    have h3 : (3 * n) % 5 = 4 := by omega
    rw [hn, h2, h4, h3, pow_one]
    have hz := zeta5_rel (p := p)
    rw [map_neg, map_one]
    linear_combination hz
  · refine ⟨-1, ?_⟩
    rw [zeta5_pow_mod n, zeta5_pow_mod (2 * n),
      zeta5_pow_mod (4 * n), zeta5_pow_mod (3 * n)]
    have h2 : (2 * n) % 5 = 3 := by omega
    have h4 : (4 * n) % 5 = 1 := by omega
    have h3 : (3 * n) % 5 = 2 := by omega
    rw [hn, h2, h4, h3, pow_one]
    have hz := zeta5_rel (p := p)
    rw [map_neg, map_one]
    linear_combination hz

omit [Fact p.Prime] in
lemma mk_monomial (n : ℕ) (a : ZMod p) :
    AdjoinRoot.mk (phi5 p) (monomial n a)
      = AdjoinRoot.of (phi5 p) a * (zeta5 : Phi5Ring p) ^ n := by
  rw [← AdjoinRoot.aeval_eq]
  simp [zeta5]

/-- La traccia dell'orbita ciclotomica appartiene sempre all'anello di
base. Questa è la forma elementare del teorema degli invarianti che
serve quando `Φ₅` è spezzato.-/
lemma cycloTraceFour_isBase (x : Phi5Ring p) :
    ∃ c : ZMod p, cycloTraceFour x = AdjoinRoot.of (phi5 p) c := by
  induction x using AdjoinRoot.induction_on with
  | ih f =>
      induction f using Polynomial.induction_on' with
      | add f g hf hg =>
          rcases hf with ⟨a, ha⟩
          rcases hg with ⟨b, hb⟩
          refine ⟨a + b, ?_⟩
          rw [map_add, cycloTraceFour_add, ha, hb, map_add]
      | monomial n a =>
          rcases zeta5_orbit_sum (p := p) n with ⟨c, hc⟩
          refine ⟨a * c, ?_⟩
          rw [mk_monomial]
          simp only [cycloTraceFour, map_mul, map_pow, sigmaTwo_base,
            sigmaTwo_zeta]
          have h8 :
              (zeta5 : Phi5Ring p) ^ (8 * n) = zeta5 ^ (3 * n) := by
            rw [zeta5_pow_mod (8 * n), zeta5_pow_mod (3 * n)]
            congr 1
            omega
          have h2nested :
              ((zeta5 : Phi5Ring p) ^ 2) ^ n = zeta5 ^ (2 * n) := by
            exact (pow_mul zeta5 2 n).symm
          have h4nested :
              (((zeta5 : Phi5Ring p) ^ 2) ^ 2) ^ n
                = zeta5 ^ (4 * n) := by
            simp only [← pow_mul]
          have h8pow :
              ((((zeta5 : Phi5Ring p) ^ 2) ^ 2) ^ 2) ^ n
                = zeta5 ^ (8 * n) := by
            simp only [← pow_mul]
          rw [h2nested, h4nested, h8pow, h8]
          calc
            AdjoinRoot.of (phi5 p) a * zeta5 ^ n
                  + AdjoinRoot.of (phi5 p) a * zeta5 ^ (2 * n)
                  + AdjoinRoot.of (phi5 p) a * zeta5 ^ (4 * n)
                  + AdjoinRoot.of (phi5 p) a * zeta5 ^ (3 * n)
                = AdjoinRoot.of (phi5 p) a
                    * (zeta5 ^ n + zeta5 ^ (2 * n)
                      + zeta5 ^ (4 * n) + zeta5 ^ (3 * n)) := by ring
            _ = AdjoinRoot.of (phi5 p) a * AdjoinRoot.of (phi5 p) c := by
                  rw [hc]
            _ = AdjoinRoot.of (phi5 p) (a * c) :=
              (map_mul (AdjoinRoot.of (phi5 p)) a c).symm
          all_goals
            exact map_mul (AdjoinRoot.of (phi5 p)) a c

/-- Un elemento fissato da `ζ ↦ ζ²` e di quadrato uno non può avere
segni diversi sulle componenti spezzate: è globalmente `1` oppure `-1`.-/
lemma fixedBySigmaTwo_sq_one (hp2 : p ≠ 2) {x : Phi5Ring p}
    (hfix : sigmaTwo x = x) (hsq : x ^ 2 = 1) :
    x = 1 ∨ x = -1 := by
  rcases cycloTraceFour_isBase (p := p) x with ⟨c, hc⟩
  have htrace : cycloTraceFour x = 4 * x := by
    simp only [cycloTraceFour, hfix]
    ring
  have hbase : (4 : Phi5Ring p) * x = AdjoinRoot.of (phi5 p) c := by
    rw [← hc, htrace]
  have hc2map :
      AdjoinRoot.of (phi5 p) (c ^ 2)
        = AdjoinRoot.of (phi5 p) ((4 : ZMod p) ^ 2) := by
    rw [map_pow, map_pow, map_ofNat]
    have hsquare := congrArg (fun y : Phi5Ring p => y ^ 2) hbase
    calc
      (AdjoinRoot.of (phi5 p) c) ^ 2
          = ((4 : Phi5Ring p) * x) ^ 2 := hsquare.symm
      _ = (4 : Phi5Ring p) ^ 2 := by rw [mul_pow, hsq, mul_one]
  have hc2 : c ^ 2 = (4 : ZMod p) ^ 2 :=
    phi5_of_injective hc2map
  have hc : c = 4 ∨ c = -4 :=
    eq_or_eq_neg_of_sq_eq_sq c 4 hc2
  have h2z : IsUnit (2 : ZMod p) :=
    isUnit_iff_ne_zero.mpr (two_ne_zero' hp2)
  have h4u : IsUnit (4 : Phi5Ring p) := by
    have h := (h2z.pow 2).map (AdjoinRoot.of (phi5 p))
    simpa [map_ofNat, show (4 : Phi5Ring p) = 2 ^ 2 by norm_num] using h
  rcases hc with rfl | rfl
  · left
    apply h4u.mul_left_cancel
    simpa [map_ofNat] using hbase
  · right
    apply h4u.mul_left_cancel
    simpa [map_neg, map_ofNat] using hbase

/-- Inclusione del nucleo aureo nel quoziente ciclotomico.-/
noncomputable def goldenToCyclo : GoldenRing p →+* Phi5Ring p :=
  AdjoinRoot.lift (AdjoinRoot.of (phi5 p)) (cycloEps p) (by
    simp only [goldenPoly, eval₂_sub, eval₂_pow, eval₂_X, eval₂_one]
    linear_combination cycloEps_sq (p := p))

@[simp]
lemma goldenToCyclo_eps :
    goldenToCyclo (p := p) eps = cycloEps p := by
  exact AdjoinRoot.lift_root _

@[simp]
lemma goldenToCyclo_base (x : ZMod p) :
    goldenToCyclo (p := p) (AdjoinRoot.of (goldenPoly p) x)
      = AdjoinRoot.of (phi5 p) x := by
  exact AdjoinRoot.lift_of _

/-- Il profilo aritmetico `p ∣ Hₙ` si trasporta nel vero anello
ciclotomico.-/
lemma dvd_goldenH_imp_cyclo_scalar {n : ℕ} (hn : 1 ≤ n)
    (hp5 : p ≠ 5) (hH : p ∣ goldenH n) :
    (cycloEps p) ^ (2 * n) = -1
      ∧ (5 : Phi5Ring p) ^ (n - 1) = -1 := by
  have hs :=
    (dvd_goldenH_iff_scalar_profile (p := p) hn hp5).mp hH
  constructor
  · have hm := congrArg (goldenToCyclo (p := p)) hs.1
    simpa using hm
  · have hm := congrArg (AdjoinRoot.of (phi5 p)) hs.2
    calc
      (5 : Phi5Ring p) ^ (n - 1)
          = AdjoinRoot.of (phi5 p) ((5 : ZMod p) ^ (n - 1)) := by
              rw [map_pow, map_ofNat]
      _ = AdjoinRoot.of (phi5 p) (-1 : ZMod p) := hm
      _ = -1 := by rw [map_neg, map_one]

/-- Le altre due relazioni di rapporto fra i generatori ciclotomici.-/
lemma u3_eq_cyclo_factor :
    (zeta5 : Phi5Ring p) ^ 3 - 1
      = (zeta5 * cycloEps p) * (zeta5 - 1) := by
  have hz5 := zeta5_pow_five (p := p)
  have hz6 : (zeta5 : Phi5Ring p) ^ 6 = zeta5 := by
    calc
      (zeta5 : Phi5Ring p) ^ 6 = zeta5 ^ 5 * zeta5 := by
        rw [show 6 = 5 + 1 by norm_num, pow_succ]
      _ = zeta5 := by rw [hz5, one_mul]
  calc
    (zeta5 : Phi5Ring p) ^ 3 - 1
        = zeta5 ^ 3 - zeta5 + zeta5 ^ 6 - zeta5 ^ 5 := by
            rw [hz6, hz5]
            ring
    _ = (zeta5 * cycloEps p) * (zeta5 - 1) := by
            unfold cycloEps
            ring

lemma u4_eq_cyclo_factor :
    (zeta5 : Phi5Ring p) ^ 4 - 1
      = (-(zeta5 ^ 4)) * (zeta5 - 1) := by
  have hz5 := zeta5_pow_five (p := p)
  calc
    (zeta5 : Phi5Ring p) ^ 4 - 1
        = -(zeta5 ^ 5) + zeta5 ^ 4 := by rw [hz5]; ring
    _ = (-(zeta5 ^ 4)) * (zeta5 - 1) := by ring

lemma u3_isUnit (hp5 : p ≠ 5) :
    IsUnit ((zeta5 : Phi5Ring p) ^ 3 - 1) := by
  rw [u3_eq_cyclo_factor]
  exact (zeta5_isUnit.mul cycloEps_isUnit).mul
    (zeta_sub_one_isUnit hp5)

lemma u4_isUnit (hp5 : p ≠ 5) :
    IsUnit ((zeta5 : Phi5Ring p) ^ 4 - 1) := by
  rw [u4_eq_cyclo_factor]
  exact (zeta5_isUnit.pow 4).neg.mul (zeta_sub_one_isUnit hp5)

/-- Le congruenze scalari rendono uguali, per moltiplicazione incrociata,
i quattro difetti del trasporto.-/
lemma scalar_common_defect_cross {n : ℕ} (hn : 1 ≤ n)
    (hn5 : n % 5 = 4)
    (he : (cycloEps p) ^ (2 * n) = -1) :
    let z : Phi5Ring p := zeta5
    let m := 2 * n - 1
    let u1 := z - 1
    let u2 := z ^ 2 - 1
    let u3 := z ^ 3 - 1
    let u4 := z ^ 4 - 1
    u2 ^ m * u2 = u1 ^ m * u4
      ∧ u4 ^ m * u2 = u1 ^ m * u3
      ∧ u3 ^ m * u2 = u1 ^ m * u1 := by
  dsimp only
  let z : Phi5Ring p := zeta5
  let e : Phi5Ring p := cycloEps p
  let u1 : Phi5Ring p := z - 1
  let u2 : Phi5Ring p := z ^ 2 - 1
  let u3 : Phi5Ring p := z ^ 3 - 1
  let u4 : Phi5Ring p := z ^ 4 - 1
  let c : Phi5Ring p := -(z ^ 3) * e
  let d : Phi5Ring p := z * e
  let f : Phi5Ring p := -(z ^ 4)
  let m : ℕ := 2 * n - 1
  have hm : m = 2 * n - 1 := rfl
  have hm1 : m + 1 = 2 * n := by dsimp [m]; omega
  have hmodd : Odd m := by
    refine ⟨n - 1, ?_⟩
    dsimp [m]
    omega
  have hm5 : m % 5 = 2 := by dsimp [m]; omega
  have hu2 : u2 = c * u1 := by
    dsimp [u2, c, u1, z, e]
    exact u2_eq_cyclo_factor
  have hu3 : u3 = d * u1 := by
    dsimp [u3, d, u1, z, e]
    exact u3_eq_cyclo_factor
  have hu4 : u4 = f * u1 := by
    dsimp [u4, f, u1, z]
    exact u4_eq_cyclo_factor
  have hz5 : z ^ 5 = 1 := by
    simpa [z] using zeta5_pow_five (p := p)
  have hz6 : z ^ 6 = z := by
    calc
      z ^ 6 = z ^ 5 * z := by
        rw [show 6 = 5 + 1 by norm_num, pow_succ]
      _ = z := by rw [hz5, one_mul]
  have hcstep : c ^ (m + 1) = f := by
    have hzexp : z ^ (3 * (2 * n)) = z ^ 4 := by
      rw [zeta5_pow_mod, zeta5_pow_mod]
      congr 1
      omega
    calc
      c ^ (m + 1) = (-(z ^ 3) * e) ^ (2 * n) := by rw [hm1]
      _ = (-(z ^ 3)) ^ (2 * n) * e ^ (2 * n) := by rw [mul_pow]
      _ = z ^ (3 * (2 * n)) * (-1) := by
            rw [Even.neg_pow (even_two_mul n), ← pow_mul, he]
      _ = -(z ^ 4) := by rw [hzexp]; ring
      _ = f := rfl
  have hfstep : f ^ m * c = d := by
    have hzexp : z ^ (4 * m) = z ^ 3 := by
      rw [zeta5_pow_mod, zeta5_pow_mod]
      congr 1
      omega
    calc
      f ^ m * c = (-(z ^ 4)) ^ m * (-(z ^ 3) * e) := rfl
      _ = (-(z ^ (4 * m))) * (-(z ^ 3) * e) := by
            rw [hmodd.neg_pow, ← pow_mul]
      _ = d := by
            rw [hzexp]
            dsimp [d]
            calc
              -(z ^ 3) * (-(z ^ 3) * e) = z ^ 6 * e := by ring
              _ = z * e := by rw [hz6]
  have hdstep : d ^ m * c = 1 := by
    have hzexp : z ^ m * z ^ 3 = 1 := by
      rw [← pow_add, zeta5_pow_mod]
      have hh : (m + 3) % 5 = 0 := by omega
      rw [hh, pow_zero]
    calc
      d ^ m * c = (z * e) ^ m * (-(z ^ 3) * e) := rfl
      _ = -(z ^ m * z ^ 3 * e ^ (m + 1)) := by
            rw [mul_pow, pow_succ]
            ring
      _ = 1 := by rw [hm1, he, hzexp]; ring
  constructor
  · change u2 ^ m * u2 = u1 ^ m * u4
    rw [hu2, hu4]
    calc
      (c * u1) ^ m * (c * u1)
          = c ^ (m + 1) * u1 ^ (m + 1) := by
              rw [mul_pow, pow_succ, pow_succ]
              ring
      _ = u1 ^ m * (f * u1) := by rw [hcstep, pow_succ]; ring
  constructor
  · change u4 ^ m * u2 = u1 ^ m * u3
    rw [hu4, hu2, hu3]
    calc
      (f * u1) ^ m * (c * u1)
          = u1 ^ m * ((f ^ m * c) * u1) := by rw [mul_pow]; ring
      _ = u1 ^ m * (d * u1) := by rw [hfstep]
  · change u3 ^ m * u2 = u1 ^ m * u1
    rw [hu3, hu2]
    calc
      (d * u1) ^ m * (c * u1)
          = u1 ^ m * ((d ^ m * c) * u1) := by rw [mul_pow]; ring
      _ = u1 ^ m * u1 := by rw [hdstep, one_mul]

/-- Il difetto universale, normalizzato sulla prima riga.-/
noncomputable def commonDefect (hp5 : p ≠ 5) (m : ℕ) : Phi5Ring p :=
  ((zeta5 : Phi5Ring p) - 1) ^ m
    * ↑((u2_isUnit (p := p) hp5).unit⁻¹)

lemma commonDefect_mul_u2 (hp5 : p ≠ 5) (m : ℕ) :
    commonDefect (p := p) hp5 m * (zeta5 ^ 2 - 1)
      = (zeta5 - 1) ^ m := by
  have hus :
      (↑((u2_isUnit (p := p) hp5).unit) : Phi5Ring p)
        = zeta5 ^ 2 - 1 :=
    (u2_isUnit (p := p) hp5).unit_spec
  unfold commonDefect
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ m
          * (↑((u2_isUnit (p := p) hp5).unit⁻¹) : Phi5Ring p)
          * ((zeta5 : Phi5Ring p) ^ 2 - 1)
        =
        ((zeta5 : Phi5Ring p) - 1) ^ m
          * (↑((u2_isUnit (p := p) hp5).unit⁻¹) : Phi5Ring p)
          * (↑((u2_isUnit (p := p) hp5).unit) : Phi5Ring p) := by
            exact congrArg
              (fun x : Phi5Ring p =>
                ((zeta5 : Phi5Ring p) - 1) ^ m
                  * (↑((u2_isUnit (p := p) hp5).unit⁻¹) : Phi5Ring p) * x)
              hus.symm
    _ = ((zeta5 : Phi5Ring p) - 1) ^ m :=
      ((u2_isUnit (p := p) hp5).unit.inv_mul_cancel_right
        (((zeta5 : Phi5Ring p) - 1) ^ m))

lemma sigmaTwo_u1 :
    sigmaTwo (p := p) (zeta5 - 1) = zeta5 ^ 2 - 1 := by
  simp

lemma sigmaTwo_u2 :
    sigmaTwo (p := p) (zeta5 ^ 2 - 1) = zeta5 ^ 4 - 1 := by
  simp only [map_sub, map_pow, map_one, sigmaTwo_zeta]
  rw [← pow_mul]

lemma commonDefect_fixed {n : ℕ} (hn : 1 ≤ n) (hn5 : n % 5 = 4)
    (hp5 : p ≠ 5) (he : (cycloEps p) ^ (2 * n) = -1) :
    sigmaTwo (commonDefect (p := p) hp5 (2 * n - 1))
      = commonDefect (p := p) hp5 (2 * n - 1) := by
  let w := commonDefect (p := p) hp5 (2 * n - 1)
  let u1 : Phi5Ring p := zeta5 - 1
  let u2 : Phi5Ring p := zeta5 ^ 2 - 1
  let u4 : Phi5Ring p := zeta5 ^ 4 - 1
  let m := 2 * n - 1
  have hcross :=
    (scalar_common_defect_cross (p := p) hn hn5 he).1
  change u2 ^ m * u2 = u1 ^ m * u4 at hcross
  have hwu2 : w * u2 = u1 ^ m := by
    simpa [w, u1, u2, m] using
      commonDefect_mul_u2 (p := p) hp5 (2 * n - 1)
  have hsig : sigmaTwo w * u4 = u2 ^ m := by
    have hmap := congrArg (sigmaTwo (p := p)) hwu2
    simpa [u1, u2, u4, m, map_mul, map_pow, sigmaTwo_u1,
      sigmaTwo_u2] using hmap
  have hwu4 : w * u4 = u2 ^ m := by
    apply (u2_isUnit (p := p) hp5).mul_right_cancel
    calc
      (w * u4) * u2 = (w * u2) * u4 := by ring
      _ = u1 ^ m * u4 := by rw [hwu2]
      _ = u2 ^ m * u2 := hcross.symm
  apply (u4_isUnit (p := p) hp5).mul_right_cancel
  rw [hsig, hwu4]

lemma cyclo_factor_sq :
    (-(zeta5 ^ 3) * cycloEps p : Phi5Ring p) ^ 2
      = zeta5 * (cycloEps p) ^ 2 := by
  have hz5 := zeta5_pow_five (p := p)
  have hz6 : (zeta5 : Phi5Ring p) ^ 6 = zeta5 := by
    calc
      (zeta5 : Phi5Ring p) ^ 6 = zeta5 ^ 5 * zeta5 := by
        rw [show 6 = 5 + 1 by norm_num, pow_succ]
      _ = zeta5 := by rw [hz5, one_mul]
  calc
    (-(zeta5 ^ 3) * cycloEps p : Phi5Ring p) ^ 2
        = zeta5 ^ 6 * (cycloEps p) ^ 2 := by ring
    _ = zeta5 * (cycloEps p) ^ 2 := by rw [hz6]

lemma commonDefect_sq_one {n : ℕ} (hn : 1 ≤ n) (hn5 : n % 5 = 4)
    (hp5 : p ≠ 5)
    (hs : (cycloEps p) ^ (2 * n) = -1
      ∧ (5 : Phi5Ring p) ^ (n - 1) = -1) :
    (commonDefect (p := p) hp5 (2 * n - 1)) ^ 2 = 1 := by
  let z : Phi5Ring p := zeta5
  let e : Phi5Ring p := cycloEps p
  let u1 : Phi5Ring p := z - 1
  let u2 : Phi5Ring p := z ^ 2 - 1
  let c : Phi5Ring p := -(z ^ 3) * e
  let m := 2 * n - 1
  let w := commonDefect (p := p) hp5 m
  have hm : m = 2 * n - 1 := rfl
  have hu2 : u2 = c * u1 := by
    dsimp [u2, c, u1, z, e]
    exact u2_eq_cyclo_factor
  have hwu2 : w * u2 = u1 ^ m := by
    simpa [w, u1, u2, m, z] using
      commonDefect_mul_u2 (p := p) hp5 (2 * n - 1)
  have hent : z ^ 3 * e ^ 2 * u1 ^ 4 = 5 := by
    dsimp [z, e, u1]
    exact entanglement zeta5_rel
  have hzexp : z ^ (3 * (n - 1) + 1) = 1 := by
    rw [zeta5_pow_mod]
    have hh : (3 * (n - 1) + 1) % 5 = 0 := by omega
    rw [hh, pow_zero]
  have hq : IsUnit (z ^ (3 * (n - 1)) * e ^ (2 * (n - 1))) :=
    ((zeta5_isUnit (p := p).pow _).mul
      (cycloEps_isUnit (p := p).pow _))
  have hu1four : u1 ^ (4 * (n - 1)) = z * e ^ 2 := by
    have heexp :
        e ^ (2 * n) = e ^ (2 * (n - 1)) * e ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    apply hq.mul_left_cancel
    calc
      (z ^ (3 * (n - 1)) * e ^ (2 * (n - 1)))
            * u1 ^ (4 * (n - 1))
          = (z ^ 3 * e ^ 2 * u1 ^ 4) ^ (n - 1) := by
              repeat' rw [mul_pow, ← pow_mul]
              ring
      _ = (5 : Phi5Ring p) ^ (n - 1) := by rw [hent]
      _ = -1 := hs.2
      _ = (z ^ (3 * (n - 1)) * e ^ (2 * (n - 1)))
            * (z * e ^ 2) := by
              calc
                -1 = z ^ (3 * (n - 1) + 1) * e ^ (2 * n) := by
                  rw [hzexp, one_mul, hs.1]
                _ = (z ^ (3 * (n - 1)) * z)
                      * (e ^ (2 * (n - 1)) * e ^ 2) := by
                        rw [pow_succ, heexp]
                _ = (z ^ (3 * (n - 1)) * e ^ (2 * (n - 1)))
                      * (z * e ^ 2) := by ring
  have hc2 : c ^ 2 = z * e ^ 2 := by
    dsimp [c, z, e]
    exact cyclo_factor_sq (p := p)
  have hexp : u1 ^ (2 * (m - 1)) = c ^ 2 := by
    rw [show 2 * (m - 1) = 4 * (n - 1) by dsimp [m]; omega,
      hu1four, hc2]
  apply (u2_isUnit (p := p) hp5).pow 2 |>.mul_right_cancel
  calc
    w ^ 2 * u2 ^ 2 = (w * u2) ^ 2 := by rw [mul_pow]
    _ = (u1 ^ m) ^ 2 := by rw [hwu2]
    _ = u1 ^ (2 * m) := by rw [← pow_mul, mul_comm]
    _ = u1 ^ (2 * (m - 1)) * u1 ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    _ = c ^ 2 * u1 ^ 2 := by rw [hexp]
    _ = u2 ^ 2 := by
      rw [hu2, mul_pow]
      dsimp [c]
      ring
    _ = 1 * u2 ^ 2 := by rw [one_mul]

/-- Il profilo scalare divide il problema ciclotomico in esattamente
due rami globali: difetto `+1` oppure difetto `-1`.-/
theorem commonDefect_eq_one_or_neg_one {n : ℕ}
    (hn : 1 ≤ n) (hn5 : n % 5 = 4)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hH : p ∣ goldenH n) :
    commonDefect (p := p) hp5 (2 * n - 1) = 1
      ∨ commonDefect (p := p) hp5 (2 * n - 1) = -1 := by
  have hs := dvd_goldenH_imp_cyclo_scalar (p := p) hn hp5 hH
  exact fixedBySigmaTwo_sq_one (p := p) hp2
    (commonDefect_fixed (p := p) hn hn5 hp5 hs.1)
    (commonDefect_sq_one (p := p) hn hn5 hp5 hs)

/-- Nel ramo di difetto positivo l'indice scalare originale è già un
testimone letterale di `S(p,5)`.-/
lemma localS5_of_commonDefect_eq_one {n : ℕ}
    (hn : 1 ≤ n) (hn5 : n % 5 = 4) (hp5 : p ≠ 5)
    (hw : commonDefect (p := p) hp5 (2 * n - 1) = 1) :
    LocalS5 p (2 * n - 1) := by
  have hmul :=
    commonDefect_mul_u2 (p := p) hp5 (2 * n - 1)
  have hm5 : (2 * n - 1) % 5 = 2 := by omega
  unfold LocalS5
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ (2 * n - 1)
        = commonDefect (p := p) hp5 (2 * n - 1)
            * (zeta5 ^ 2 - 1) := hmul.symm
    _ = zeta5 ^ 2 - 1 := by rw [hw, one_mul]
    _ = zeta5 ^ (2 * n - 1) - 1 := by
      rw [zeta5_pow_mod (2 * n - 1), hm5]

/-- Nel ramo negativo il difetto si ripara costruttivamente. Se
`m = 2n-1`, si pone `d = ⌊m²/2⌋ = (m²-1)/2` e si usa l'indice
`n' = n + 5d`; il nuovo esponente è `m' = m + 10d`.-/
lemma localS5_sign_repair {n : ℕ}
    (hn : 1 ≤ n) (hn5 : n % 5 = 4) (hp5 : p ≠ 5)
    (he : (cycloEps p) ^ (2 * n) = -1)
    (hw : commonDefect (p := p) hp5 (2 * n - 1) = -1) :
    let m := 2 * n - 1
    let d := (m * m) / 2
    LocalS5 p (2 * (n + 5 * d) - 1) := by
  let z : Phi5Ring p := zeta5
  let u1 : Phi5Ring p := z - 1
  let u2 : Phi5Ring p := z ^ 2 - 1
  let u4 : Phi5Ring p := z ^ 4 - 1
  let m := 2 * n - 1
  let d := (m * m) / 2
  have hmodd : Odd m := by
    use n - 1
    dsimp [m]
    omega
  have hmpos : 1 ≤ m := by
    dsimp [m]
    omega
  have hmmpos : 1 ≤ m * m := Nat.mul_pos hmpos hmpos
  have hhalf : 2 * d = m * m - 1 := by
    dsimp [d]
    exact Nat.two_mul_odd_div_two
      (Nat.odd_iff.mp (hmodd.mul hmodd))
  have hwu2 :
      commonDefect (p := p) hp5 m * u2 = u1 ^ m := by
    simpa [m, u1, u2, z] using
      commonDefect_mul_u2 (p := p) hp5 (2 * n - 1)
  have hu1m : u1 ^ m = -u2 := by
    rw [hw] at hwu2
    simpa using hwu2.symm
  have hcross :=
    (scalar_common_defect_cross (p := p) hn hn5 he).1
  change u2 ^ m * u2 = u1 ^ m * u4 at hcross
  have hu2m : u2 ^ m = -u4 := by
    apply (u2_isUnit (p := p) hp5).mul_right_cancel
    calc
      u2 ^ m * u2 = u1 ^ m * u4 := hcross
      _ = (-u4) * u2 := by rw [hu1m]; ring
  have hiterate : u1 ^ (m * m) = u4 := by
    calc
      u1 ^ (m * m) = (u1 ^ m) ^ m := by rw [pow_mul]
      _ = (-u2) ^ m := by rw [hu1m]
      _ = -(u2 ^ m) := hmodd.neg_pow u2
      _ = u4 := by rw [hu2m]; ring
  have hquotient : u1 ^ (m * m - 1) = -(z ^ 4) := by
    apply (zeta_sub_one_isUnit (p := p) hp5).mul_right_cancel
    calc
      u1 ^ (m * m - 1) * u1 = u1 ^ (m * m) := by
        rw [← pow_succ]
        congr 1
        omega
      _ = u4 := hiterate
      _ = (-(z ^ 4)) * u1 := by
        dsimp [u4, u1, z]
        exact u4_eq_cyclo_factor (p := p)
  have hz20 : z ^ 20 = 1 := by
    calc
      z ^ 20 = (z ^ 5) ^ 4 := by norm_num [← pow_mul]
      _ = 1 := by rw [zeta5_pow_five, one_pow]
  have hshift0 : u1 ^ (5 * (m * m - 1)) = -1 := by
    calc
      u1 ^ (5 * (m * m - 1))
          = (u1 ^ (m * m - 1)) ^ 5 := by
              rw [mul_comm, pow_mul]
      _ = (-(z ^ 4)) ^ 5 := by rw [hquotient]
      _ = -(z ^ 20) := by
        rw [(show Odd 5 by decide).neg_pow, ← pow_mul]
      _ = -1 := by rw [hz20]
  have hshift : u1 ^ (10 * d) = -1 := by
    rw [show 10 * d = 5 * (m * m - 1) by omega]
    exact hshift0
  have hm' :
      2 * (n + 5 * d) - 1 = m + 10 * d := by
    dsimp [m]
    omega
  have hm'5 : (2 * (n + 5 * d) - 1) % 5 = 2 := by omega
  unfold LocalS5
  calc
    ((zeta5 : Phi5Ring p) - 1) ^ (2 * (n + 5 * d) - 1)
        = u1 ^ (m + 10 * d) := by rw [hm']
    _ = u1 ^ m * u1 ^ (10 * d) := by rw [pow_add]
    _ = (-u2) * (-1) := by rw [hu1m, hshift]
    _ = z ^ 2 - 1 := by dsimp [u2]; ring
    _ = zeta5 ^ (2 * (n + 5 * d) - 1) - 1 := by
      rw [zeta5_pow_mod (2 * (n + 5 * d) - 1), hm'5]

/-- **Completezza scalare, direzione conversa.**
Ogni divisore primo di un termine critico `Hₙ` produce un vero
trasporto locale di ordine quattro. L'indice resta `n` nel ramo
positivo; nel ramo negativo viene sostituito dall'indice costruttivo
`n + 5⌊(2n-1)²/2⌋`.-/
theorem dvd_goldenH_imp_hasOrderFourTransport {n : ℕ}
    (hn : 1 ≤ n) (hn5 : n % 5 = 4)
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) (hH : p ∣ goldenH n) :
    HasOrderFourTransport p := by
  rcases commonDefect_eq_one_or_neg_one (p := p)
      hn hn5 hp2 hp5 hH with hw | hw
  · exact ⟨n, hn, hn5, localS5_of_commonDefect_eq_one
      (p := p) hn hn5 hp5 hw⟩
  · let m := 2 * n - 1
    let d := (m * m) / 2
    have hs := dvd_goldenH_imp_cyclo_scalar (p := p) hn hp5 hH
    refine ⟨n + 5 * d, ?_, ?_, ?_⟩
    · omega
    · omega
    · simpa [m, d] using
        localS5_sign_repair (p := p) hn hn5 hp5 hs.1 hw

/-- **Ponte locale H4, equivalenza completa verificata dal kernel.**
Per `p ≠ 2,5`, l'esistenza di un trasporto locale nella classe
d'ordine quattro equivale esattamente alla presenza di `p` nel
supporto della successione aurea `Hₙ`, su un indice `n ≡ 4 (mod 5)`.-/
theorem hasOrderFourTransport_iff_goldenH_support
    (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    HasOrderFourTransport p ↔
      ∃ n, 1 ≤ n ∧ n % 5 = 4 ∧ p ∣ goldenH n := by
  constructor
  · exact hasOrderFourTransport_imp_goldenH_support (p := p) hp5
  · rintro ⟨n, hn, hn5, hH⟩
    exact dvd_goldenH_imp_hasOrderFourTransport
      (p := p) hn hn5 hp2 hp5 hH

end AgrawalCore
