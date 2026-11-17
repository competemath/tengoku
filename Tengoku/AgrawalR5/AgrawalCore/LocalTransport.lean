/-
Nucleo Lean della campagna Agrawal — lotto 20: IL TRASPORTO LOCALE H4.

Questo modulo introduce nel kernel la vera riga locale

  (ζ - 1)^m = ζ^m - 1  in  (Z/p)[X]/Φ₅,

e non un suo surrogato scalare. Per un esponente di trasporto
`m = 2n - 1`, `n ≡ 4 (mod 5)`, dimostra la direzione necessaria

  trasporto locale di ordine quattro  ->  p ∣ Hₙ.

Le quattro righe etichettate sono ottenute dalla divisibilità per Φ₅
e dalla valutazione nelle quattro radici ζ^a. La direzione conversa
`p ∣ Hₙ -> esistenza di un trasporto locale` non è affermata qui:
è precisamente il gate di completezza scalare ancora da formalizzare.

Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.H4Core
import Tengoku.AgrawalR5.AgrawalCore.LocalGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

variable {p : ℕ} [Fact p.Prime]

-- Le normalizzazioni di `aeval` nelle radici coniugate espandono potenze
-- fino al grado 16; il margine evita timeout dipendenti dalla macchina.
set_option maxHeartbeats 2000000

/-- L'unità aurea nella coordinata ciclotomica: `ε = 1 + ζ + ζ⁴`.-/
noncomputable def cycloEps (p : ℕ) [Fact p.Prime] : Phi5Ring p :=
  1 + zeta5 + zeta5 ^ 4

/-- La relazione aurea nella coordinata ciclotomica.
@isnad1 id=eq.0h1v.s6.800789272f9a from=translated src=- shape=e9ab50b8 vocab=3414b54e
-/
lemma cycloEps_sq :
    (cycloEps p) ^ 2 = cycloEps p + 1 := by
  have hz := zeta5_rel (p := p)
  unfold cycloEps
  linear_combination
    (zeta5 ^ 4 - zeta5 ^ 3 + 2 * zeta5 - 1) * hz

/-- L'altra radice aurea nella coordinata ciclotomica.-/
noncomputable def cycloEps' (p : ℕ) [Fact p.Prime] : Phi5Ring p :=
  1 - cycloEps p

/--
@isnad1 id=eq.0h1v.s6.bd13ca85ea13 from=translated src=- shape=e9ab50b8 vocab=321ffc7c
-/
lemma cycloEps'_sq :
    (cycloEps' p) ^ 2 = cycloEps' p + 1 := by
  have h := cycloEps_sq (p := p)
  unfold cycloEps'
  linear_combination h

/--
@isnad1 id=eq.0h1v.s6.b3723556cb00 from=translated src=- shape=4dba446d vocab=e7eaf565
-/
lemma cycloEps_mul_conj :
    cycloEps p * cycloEps' p = -1 := by
  have h := cycloEps_sq (p := p)
  unfold cycloEps'
  linear_combination -h

/--
@isnad1 id=isunit.0h1v.s4.d254c53c2c50 from=translated src=- shape=7e6de1f7 vocab=a1610594
-/
lemma cycloEps_isUnit : IsUnit (cycloEps p) :=
  IsUnit.of_mul_eq_one (cycloEps p - 1) (by
    have h := cycloEps_sq (p := p)
    linear_combination h)

/-- La radice quadrata di `5` nella coordinata ciclotomica.-/
noncomputable def cycloSqrt5 (p : ℕ) [Fact p.Prime] : Phi5Ring p :=
  2 * cycloEps p - 1

/--
@isnad1 id=eq.0h1v.s6.4e7b91e9cdec from=translated src=- shape=3101749e vocab=b74fde1a
-/
lemma cycloSqrt5_sq :
    (cycloSqrt5 p) ^ 2 = 5 := by
  have h := cycloEps_sq (p := p)
  unfold cycloSqrt5
  linear_combination 4 * h

/-- La vera congruenza locale che definisce `S(p,5)` nella componente
`Φ₅`.-/
def LocalS5 (p m : ℕ) [Fact p.Prime] : Prop :=
  ((zeta5 : Phi5Ring p) - 1) ^ m = zeta5 ^ m - 1

/-- Un testimone parametrizzato del residuo `2 mod 5`: l'esponente locale
è `m = 2n-1`, quindi è dispari e induce il ciclo `1 -> 2 -> 4 -> 3 -> 1`.-/
def OrderFourTransportWitness (p n : ℕ) [Fact p.Prime] : Prop :=
  1 ≤ n ∧ n % 5 = 4 ∧ LocalS5 p (2 * n - 1)

/-- Esistenza di un trasporto locale nella classe `2 mod 5`.-/
def HasOrderFourTransport (p : ℕ) [Fact p.Prime] : Prop :=
  ∃ n, OrderFourTransportWitness p n

/-- `ζ` è radice di `Φ₅`.
@isnad1 id=eq.0h1v.s8.023061ba0fa6 from=translated src=- shape=e6e35077 vocab=b2018d22
-/
lemma phi5_aeval_zeta :
    Polynomial.aeval (zeta5 : Phi5Ring p) (phi5 p) = 0 := by
  simpa [phi5, map_add, map_pow, map_one, Polynomial.aeval_X]
    using zeta5_rel (p := p)

/-- `ζ²` è radice di `Φ₅`.
@isnad1 id=eq.0h1v.s8.c3da0c4b5d74 from=translated src=- shape=2aae0fcb vocab=d5377041
-/
lemma phi5_aeval_zeta_pow_two :
    Polynomial.aeval ((zeta5 : Phi5Ring p) ^ 2) (phi5 p) = 0 := by
  simp only [phi5, map_add, map_pow, map_one, Polynomial.aeval_X]
  have hz := zeta5_rel (p := p)
  linear_combination
    (zeta5 ^ 4 - zeta5 ^ 3 + zeta5 ^ 2 - zeta5 + 1) * hz

/-- `ζ³` è radice di `Φ₅`.
@isnad1 id=eq.0h1v.s8.a3d0df658c96 from=translated src=- shape=2aae0fcb vocab=d5377041
-/
lemma phi5_aeval_zeta_pow_three :
    Polynomial.aeval ((zeta5 : Phi5Ring p) ^ 3) (phi5 p) = 0 := by
  simp only [phi5, map_add, map_pow, map_one, Polynomial.aeval_X]
  have hz := zeta5_rel (p := p)
  linear_combination
    (zeta5 ^ 8 - zeta5 ^ 7 + zeta5 ^ 5 - zeta5 ^ 4
      + zeta5 ^ 3 - zeta5 + 1) * hz

/-- `ζ⁴` è radice di `Φ₅`.
@isnad1 id=eq.0h1v.s8.df7bf893ae5d from=translated src=- shape=2aae0fcb vocab=d5377041
-/
lemma phi5_aeval_zeta_pow_four :
    Polynomial.aeval ((zeta5 : Phi5Ring p) ^ 4) (phi5 p) = 0 := by
  simp only [phi5, map_add, map_pow, map_one, Polynomial.aeval_X]
  have hz := zeta5_rel (p := p)
  linear_combination
    (zeta5 ^ 12 - zeta5 ^ 11 + zeta5 ^ 8 - zeta5 ^ 6
      + zeta5 ^ 4 - zeta5 + 1) * hz

/-- T5 in forma etichettata: una riga locale nella radice universale
si trasporta a ciascuna radice `ζ^a`.
@isnad1 id=eq.2h3v.s9.c4e93c73fb5b from=translated src=- shape=078b3975 vocab=0a9efc65
-/
lemma localS5_row {m a : ℕ} (h : LocalS5 p m)
    (ha : Polynomial.aeval ((zeta5 : Phi5Ring p) ^ a) (phi5 p) = 0) :
    ((zeta5 : Phi5Ring p) ^ a - 1) ^ m = zeta5 ^ (a * m) - 1 := by
  have hd : phi5 p ∣
      ((X - 1) ^ m - (X ^ m - 1) : Polynomial (ZMod p)) :=
    phi5_dvd_of_local h
  obtain ⟨g, hg⟩ := hd
  have heval := congrArg
    (Polynomial.aeval ((zeta5 : Phi5Ring p) ^ a)) hg
  simp only [map_sub, map_pow, map_one, Polynomial.aeval_X, map_mul] at heval
  rw [ha, zero_mul] at heval
  rw [pow_mul]
  linear_combination heval

/-- Le quattro righe del ciclo etichettato di ordine quattro.
@isnad1 id=other.1h2v.s9.876e0f6f320f from=translated src=- shape=1bb0fc9e vocab=2ad32ab5
-/
lemma orderFourTransport_rows {n : ℕ}
    (h : OrderFourTransportWitness p n) :
    let z : Phi5Ring p := zeta5
    (z - 1) ^ (2 * n - 1) = z ^ 2 - 1
      ∧ (z ^ 2 - 1) ^ (2 * n - 1) = z ^ 4 - 1
      ∧ (z ^ 4 - 1) ^ (2 * n - 1) = z ^ 3 - 1
      ∧ (z ^ 3 - 1) ^ (2 * n - 1) = z - 1 := by
  rcases h with ⟨hn, hn5, hloc⟩
  dsimp only
  have hm5 : (2 * n - 1) % 5 = 2 := by omega
  have h1 := localS5_row (p := p) hloc (a := 1) (by
    simpa [pow_one] using phi5_aeval_zeta (p := p))
  have h2 := localS5_row (p := p) hloc (a := 2)
    (phi5_aeval_zeta_pow_two (p := p))
  have h4 := localS5_row (p := p) hloc (a := 4)
    (phi5_aeval_zeta_pow_four (p := p))
  have h3 := localS5_row (p := p) hloc (a := 3)
    (phi5_aeval_zeta_pow_three (p := p))
  have e1 : 1 * (2 * n - 1) % 5 = 2 := by omega
  have e2 : 2 * (2 * n - 1) % 5 = 4 := by omega
  have e4 : 4 * (2 * n - 1) % 5 = 3 := by omega
  have e3 : 3 * (2 * n - 1) % 5 = 1 := by omega
  have hp1 : (zeta5 : Phi5Ring p) ^ (1 * (2 * n - 1)) = zeta5 ^ 2 := by
    rw [zeta5_pow_mod, e1]
  have hp2 : (zeta5 : Phi5Ring p) ^ (2 * (2 * n - 1)) = zeta5 ^ 4 := by
    rw [zeta5_pow_mod, e2]
  have hp4 : (zeta5 : Phi5Ring p) ^ (4 * (2 * n - 1)) = zeta5 ^ 3 := by
    rw [zeta5_pow_mod, e4]
  have hp3 : (zeta5 : Phi5Ring p) ^ (3 * (2 * n - 1)) = zeta5 := by
    rw [zeta5_pow_mod, e3, pow_one]
  have h1' : ((zeta5 : Phi5Ring p) - 1) ^ (2 * n - 1)
      = zeta5 ^ 2 - 1 := by
    calc
      ((zeta5 : Phi5Ring p) - 1) ^ (2 * n - 1)
          = zeta5 ^ (1 * (2 * n - 1)) - (1 : Phi5Ring p) := by
              simpa [pow_one] using h1
      _ = zeta5 ^ 2 - 1 := by rw [hp1]
  have h2' : ((zeta5 : Phi5Ring p) ^ 2 - 1) ^ (2 * n - 1)
      = zeta5 ^ 4 - 1 := by
    calc
      ((zeta5 : Phi5Ring p) ^ 2 - 1) ^ (2 * n - 1)
          = zeta5 ^ (2 * (2 * n - 1)) - (1 : Phi5Ring p) := h2
      _ = zeta5 ^ 4 - 1 := by rw [hp2]
  have h4' : ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ (2 * n - 1)
      = zeta5 ^ 3 - 1 := by
    calc
      ((zeta5 : Phi5Ring p) ^ 4 - 1) ^ (2 * n - 1)
          = zeta5 ^ (4 * (2 * n - 1)) - (1 : Phi5Ring p) := h4
      _ = zeta5 ^ 3 - 1 := by rw [hp4]
  have h3' : ((zeta5 : Phi5Ring p) ^ 3 - 1) ^ (2 * n - 1)
      = zeta5 - 1 := by
    calc
      ((zeta5 : Phi5Ring p) ^ 3 - 1) ^ (2 * n - 1)
          = zeta5 ^ (3 * (2 * n - 1)) - (1 : Phi5Ring p) := h3
      _ = zeta5 - 1 := by rw [hp3]
  exact ⟨h1', h2', h4', h3'⟩

/-- La prima relazione etichettata fra i generatori ciclotomici.
@isnad1 id=eq.0h1v.s8.45c3b56a58f2 from=translated src=- shape=c1796205 vocab=96fe8dd5
-/
lemma u2_eq_cyclo_factor :
    (zeta5 : Phi5Ring p) ^ 2 - 1
      = (-(zeta5 ^ 3) * cycloEps p) * (zeta5 - 1) := by
  have hz := zeta5_rel (p := p)
  unfold cycloEps
  linear_combination
    (zeta5 ^ 4 - 2 * zeta5 ^ 3 + zeta5 ^ 2 + zeta5 - 1) * hz

/-- La seconda relazione di rapporto, scritta senza divisioni.
@isnad1 id=eq.0h1v.s8.d2067998f5f1 from=translated src=- shape=879e298c vocab=296d956b
-/
lemma u4_mul_cycloEps :
    ((zeta5 : Phi5Ring p) ^ 4 - 1) * cycloEps p
      = zeta5 * (zeta5 ^ 2 - 1) := by
  have hz := zeta5_rel (p := p)
  unfold cycloEps
  linear_combination
    (zeta5 ^ 4 - zeta5 ^ 3 + zeta5 - 1) * hz

/--
@isnad1 id=isunit.0h1v.s4.f3584cf8b9a0 from=translated src=- shape=7e6de1f7 vocab=256722d8
-/
lemma zeta5_isUnit : IsUnit (zeta5 : Phi5Ring p) :=
  IsUnit.of_mul_eq_one (zeta5 ^ 4) (by
    calc
      (zeta5 : Phi5Ring p) * zeta5 ^ 4 = zeta5 ^ 5 := by ring
      _ = 1 := zeta5_pow_five)

/--
@isnad1 id=isunit.1h1v.s7.b448d2568cdb from=translated src=- shape=ec651eeb vocab=e41fe94c
-/
lemma u2_isUnit (hp5 : p ≠ 5) :
    IsUnit ((zeta5 : Phi5Ring p) ^ 2 - 1) := by
  rw [u2_eq_cyclo_factor]
  exact (((zeta5_isUnit.pow 3).neg.mul cycloEps_isUnit).mul
    (zeta_sub_one_isUnit hp5))

/-- **Compressione aurea direttamente dalla riga locale.**
Il trasporto etichettato completo forza le due congruenze scalari
negative nello stesso anello ciclotomico.
@isnad1 id=and.2h2v.s8.e58b8115b4b0 from=translated src=- shape=a6fad91e vocab=33645138
-/
theorem orderFourTransport_cyclo_scalar {n : ℕ} (hp5 : p ≠ 5)
    (h : OrderFourTransportWitness p n) :
    (cycloEps p) ^ (2 * n) = -1
      ∧ (5 : Phi5Ring p) ^ (n - 1) = -1 := by
  rcases h with ⟨hn, hn5, hloc⟩
  have hrows := orderFourTransport_rows (p := p) ⟨hn, hn5, hloc⟩
  dsimp only at hrows
  rcases hrows with ⟨h1, h2, h4, h3⟩
  let z : Phi5Ring p := zeta5
  let e : Phi5Ring p := cycloEps p
  let u1 : Phi5Ring p := z - 1
  let u2 : Phi5Ring p := z ^ 2 - 1
  let u4 : Phi5Ring p := z ^ 4 - 1
  let c : Phi5Ring p := -(z ^ 3) * e
  let m : ℕ := 2 * n - 1
  have hm : m = 2 * n - 1 := rfl
  have hm5 : m % 5 = 2 := by
    dsimp [m]
    omega
  have hmodd : Odd m := by
    refine ⟨n - 1, ?_⟩
    dsimp [m]
    omega
  have hcu : u2 = c * u1 := by
    dsimp [u2, c, u1, z, e]
    exact u2_eq_cyclo_factor
  have h4e : u4 * e = z * u2 := by
    dsimp [u4, e, z, u2]
    exact u4_mul_cycloEps
  have h1' : u1 ^ m = u2 := by simpa [u1, u2, z, m] using h1
  have h2' : u2 ^ m = u4 := by simpa [u2, u4, z, m] using h2
  have hu2 : IsUnit u2 := by
    simpa [u2, z] using u2_isUnit (p := p) hp5
  have hz : IsUnit z := by simpa [z] using zeta5_isUnit (p := p)
  have hcstep : c ^ m * u2 = u4 := by
    calc
      c ^ m * u2 = c ^ m * u1 ^ m := by rw [h1']
      _ = (c * u1) ^ m := (mul_pow c u1 m).symm
      _ = u2 ^ m := by rw [← hcu]
      _ = u4 := h2'
  have hce : c ^ m * e = z := by
    apply hu2.mul_left_cancel
    calc
      u2 * (c ^ m * e) = (c ^ m * u2) * e := by ring
      _ = u4 * e := by rw [hcstep]
      _ = z * u2 := h4e
      _ = u2 * z := by ring
  have hz3m : (z ^ 3) ^ m = z := by
    rw [← pow_mul, zeta5_pow_mod]
    have he : (3 * m) % 5 = 1 := by omega
    rw [he, pow_one]
  have hcm : c ^ m = -(z * e ^ m) := by
    dsimp [c]
    rw [mul_pow, neg_pow, hmodd.neg_one_pow, hz3m]
    ring
  have hepow : e ^ (m + 1) = -1 := by
    have hze : -(z * e ^ m) * e = z := by rwa [← hcm]
    apply hz.mul_left_cancel
    calc
      z * e ^ (m + 1) = z * (e ^ m * e) := by rw [pow_succ]
      _ = z * -1 := by linear_combination -hze
  have he2n : e ^ (2 * n) = -1 := by
    have harith : m + 1 = 2 * n := by
      dsimp [m]
      omega
    rwa [harith] at hepow
  have hu1 : IsUnit u1 := by
    simpa [u1, z] using zeta_sub_one_isUnit (p := p) hp5
  have hmexpand : m = 2 * (n - 1) + 1 := by
    dsimp [m]
    omega
  have hu1half : u1 ^ (2 * (n - 1)) = c := by
    apply hu1.mul_right_cancel
    calc
      u1 ^ (2 * (n - 1)) * u1 = u1 ^ m := by
        rw [← pow_succ, hmexpand]
      _ = u2 := h1'
      _ = c * u1 := hcu
  have hc2 : c ^ 2 = z * e ^ 2 := by
    have hz6 : z ^ 6 = z := by
      have hz5 : z ^ 5 = 1 := by
        simpa [z] using zeta5_pow_five (p := p)
      calc
        z ^ 6 = z ^ 5 * z := by rw [show 6 = 5 + 1 by norm_num, pow_succ]
        _ = z := by rw [hz5, one_mul]
    dsimp [c]
    calc
      (-z ^ 3 * e) ^ 2 = z ^ 6 * e ^ 2 := by ring
      _ = z * e ^ 2 := by rw [hz6]
  have hu1four : u1 ^ (4 * (n - 1)) = z * e ^ 2 := by
    calc
      u1 ^ (4 * (n - 1)) = (u1 ^ (2 * (n - 1))) ^ 2 := by
        rw [← pow_mul]
        congr 1
        ring
      _ = c ^ 2 := by rw [hu1half]
      _ = z * e ^ 2 := hc2
  have hent : z ^ 3 * e ^ 2 * u1 ^ 4 = 5 := by
    dsimp [z, e, u1]
    exact entanglement zeta5_rel
  have hzexp : z ^ (3 * (n - 1) + 1) = 1 := by
    rw [zeta5_pow_mod]
    have he : (3 * (n - 1) + 1) % 5 = 0 := by omega
    rw [he, pow_zero]
  have hfive : (5 : Phi5Ring p) ^ (n - 1) = -1 := by
    calc
      (5 : Phi5Ring p) ^ (n - 1)
          = (z ^ 3 * e ^ 2 * u1 ^ 4) ^ (n - 1) := by rw [hent]
      _ = z ^ (3 * (n - 1)) * e ^ (2 * (n - 1))
          * u1 ^ (4 * (n - 1)) := by
            repeat' rw [mul_pow, ← pow_mul]
            ring
      _ = z ^ (3 * (n - 1) + 1) * e ^ (2 * n) := by
            rw [hu1four]
            calc
              z ^ (3 * (n - 1)) * e ^ (2 * (n - 1)) * (z * e ^ 2)
                  = (z ^ (3 * (n - 1)) * z)
                    * (e ^ (2 * (n - 1)) * e ^ 2) := by ring
              _ = z ^ (3 * (n - 1) + 1)
                    * e ^ (2 * (n - 1) + 2) := by
                      have hzprod : z ^ (3 * (n - 1)) * z
                          = z ^ (3 * (n - 1) + 1) := by
                            exact (pow_succ z (3 * (n - 1))).symm
                      have heprod : e ^ (2 * (n - 1)) * e ^ 2
                          = e ^ (2 * (n - 1) + 2) :=
                            (pow_add e (2 * (n - 1)) 2).symm
                      rw [hzprod, heprod]
              _ = z ^ (3 * (n - 1) + 1) * e ^ (2 * n) := by
                      congr 2
                      omega
      _ = -1 := by rw [hzexp, one_mul, he2n]
  simpa [e] using ⟨he2n, hfive⟩

omit [Fact p.Prime] in
/-- Potenze di una radice dell'equazione aurea, ora nel quoziente
ciclotomico.
@isnad1 id=eq.1h3v.s8.da487ed3f38e from=translated src=- shape=1d44e0ad vocab=d813c127
-/
lemma cyclo_golden_pow_of_sq {x : Phi5Ring p} (hx : x ^ 2 = x + 1) :
    ∀ n : ℕ, x ^ (n + 1)
      = (Nat.fib (n + 1) : Phi5Ring p) * x
        + (Nat.fib n : Phi5Ring p)
  | 0 => by simp
  | n + 1 => by
    have ih := cyclo_golden_pow_of_sq hx n
    rw [pow_succ, ih, Nat.fib_add_two]
    push_cast
    linear_combination (Nat.fib (n + 1) : Phi5Ring p) * hx

omit [Fact p.Prime] in
/--
@isnad1 id=eq.2h3v.s8.8bd1d2418471 from=translated src=- shape=330956e9 vocab=ac9e372e
-/
lemma cyclo_golden_pow_pred {x : Phi5Ring p} (hx : x ^ 2 = x + 1)
    {n : ℕ} (hn : 1 ≤ n) :
    x ^ n = (Nat.fib n : Phi5Ring p) * x
      + (Nat.fib (n - 1) : Phi5Ring p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simpa using cyclo_golden_pow_of_sq hx m

/-- Formula di Lucas nella coordinata ciclotomica.
@isnad1 id=eq.1h2v.s7.99b66b35e7ae from=translated src=- shape=76a3acb3 vocab=2a5132fd
-/
lemma cycloEps_pow_add_conj_pow {n : ℕ} (hn : 1 ≤ n) :
    (cycloEps p) ^ n + (cycloEps' p) ^ n
      = (lucas n : Phi5Ring p) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [cyclo_golden_pow_pred (cycloEps_sq (p := p)) hn,
      cyclo_golden_pow_pred (cycloEps'_sq (p := p)) hn]
  unfold lucas cycloEps'
  push_cast [Nat.fib_add_two]
  ring

/-- Cast a zero verso il basso dal quoziente ciclotomico.
@isnad1 id=dvd.1h2v.s6.3c1e06e97af3 from=translated src=- shape=78acb0bb vocab=201c02b3
-/
lemma dvd_of_phi5_natCast_eq_zero {a : ℕ}
    (h : ((a : ℕ) : Phi5Ring p) = 0) : p ∣ a := by
  have h1 : AdjoinRoot.of (phi5 p) ((a : ℕ) : ZMod p)
      = AdjoinRoot.of (phi5 p) 0 := by
    rw [map_natCast, map_zero]
    exact h
  exact (CharP.cast_eq_zero_iff (ZMod p) p _).mp (phi5_of_injective h1)

/--
@isnad1 id=isunit.1h1v.s5.ec78d3ac3013 from=translated src=- shape=4e7691ea vocab=96ad97f6
-/
lemma cycloSqrt5_isUnit (hp5 : p ≠ 5) :
    IsUnit (cycloSqrt5 p) := by
  refine IsUnit.of_mul_eq_one
    (cycloSqrt5 p * AdjoinRoot.of (phi5 p) (5 : ZMod p)⁻¹) ?_
  have h1 : cycloSqrt5 p
      * (cycloSqrt5 p * AdjoinRoot.of (phi5 p) (5 : ZMod p)⁻¹)
      = (5 : Phi5Ring p) * AdjoinRoot.of (phi5 p) (5 : ZMod p)⁻¹ := by
    have h := cycloSqrt5_sq (p := p)
    linear_combination
      (AdjoinRoot.of (phi5 p) (5 : ZMod p)⁻¹) * h
  rw [h1, show (5 : Phi5Ring p) = AdjoinRoot.of (phi5 p) (5 : ZMod p)
      from (map_ofNat _ 5).symm, ← map_mul,
      mul_inv_cancel₀ (five_ne_zero hp5), map_one]

/-- La congruenza aurea negativa nel quoziente ciclotomico forza
la divisibilità del termine misto `Aₙ`.
@isnad1 id=dvd.3h2v.s7.e192144a5744 from=translated src=- shape=1be635b2 vocab=02b17491
-/
lemma dvd_goldenA_of_cyclo_pow_eq_neg_one {n : ℕ} (hn : 1 ≤ n)
    (hp5 : p ≠ 5) (h : (cycloEps p) ^ (2 * n) = -1) :
    p ∣ goldenA n := by
  rcases Nat.even_or_odd n with hev | hodd
  · rw [goldenA_of_even hev]
    have hm : (cycloEps p * cycloEps' p) ^ n = 1 := by
      rw [cycloEps_mul_conj]
      exact hev.neg_one_pow
    have hsum := cycloEps_pow_add_conj_pow (p := p) hn
    have key : ((lucas n : ℕ) : Phi5Ring p) * (cycloEps p) ^ n = 0 := by
      calc
        ((lucas n : ℕ) : Phi5Ring p) * (cycloEps p) ^ n
            = ((cycloEps p) ^ n + (cycloEps' p) ^ n)
              * (cycloEps p) ^ n := by rw [hsum]
        _ = (cycloEps p) ^ (2 * n)
              + (cycloEps p * cycloEps' p) ^ n := by
                rw [two_mul, pow_add, mul_pow]
                ring
        _ = -1 + 1 := by rw [h, hm]
        _ = 0 := by ring
    exact dvd_of_phi5_natCast_eq_zero
      (((cycloEps_isUnit (p := p).pow n).mul_left_eq_zero).mp key)
  · rw [goldenA_of_odd hodd]
    have hm : (cycloEps p * cycloEps' p) ^ n = -1 := by
      rw [cycloEps_mul_conj]
      exact hodd.neg_one_pow
    have hdiff : (cycloEps p) ^ n - (cycloEps' p) ^ n
        = (Nat.fib n : Phi5Ring p) * cycloSqrt5 p := by
      rw [cyclo_golden_pow_pred (cycloEps_sq (p := p)) hn,
          cyclo_golden_pow_pred (cycloEps'_sq (p := p)) hn]
      unfold cycloEps' cycloSqrt5
      ring
    have key : ((Nat.fib n : ℕ) : Phi5Ring p)
        * (cycloSqrt5 p * (cycloEps p) ^ n) = 0 := by
      calc
        ((Nat.fib n : ℕ) : Phi5Ring p)
              * (cycloSqrt5 p * (cycloEps p) ^ n)
            = ((Nat.fib n : Phi5Ring p) * cycloSqrt5 p)
              * (cycloEps p) ^ n := by ring
        _ = ((cycloEps p) ^ n - (cycloEps' p) ^ n)
              * (cycloEps p) ^ n := by rw [hdiff]
        _ = (cycloEps p) ^ (2 * n)
              - (cycloEps p * cycloEps' p) ^ n := by
                rw [two_mul, pow_add, mul_pow]
                ring
        _ = -1 - -1 := by rw [h, hm]
        _ = 0 := by ring
    exact dvd_of_phi5_natCast_eq_zero
      (((cycloSqrt5_isUnit (p := p) hp5).mul
        (cycloEps_isUnit (p := p).pow n)).mul_left_eq_zero.mp key)

/-- **Ponte locale H4, direzione formalizzata.**
Un vero trasporto locale di residuo `2 mod 5`, espresso nella definizione
di `S(p,5)`, produce un divisore primo di `Hₙ`.
@isnad1 id=dvd.2h2v.s4.5a75328a2ebf from=translated src=- shape=8cd89471 vocab=1a4f58ee
-/
theorem orderFourTransport_dvd_goldenH {n : ℕ} (hp5 : p ≠ 5)
    (h : OrderFourTransportWitness p n) :
    p ∣ goldenH n := by
  have hs := orderFourTransport_cyclo_scalar (p := p) hp5 h
  rw [dvd_goldenH_iff]
  refine ⟨dvd_goldenA_of_cyclo_pow_eq_neg_one h.1 hp5 hs.1, ?_⟩
  apply dvd_of_phi5_natCast_eq_zero
  push_cast
  rw [hs.2]
  ring

/-- Forma esistenziale del ponte locale: ogni trasporto di residuo `2`
produce un indice critico e un divisore primo di `Hₙ`.
@isnad1 id=ex.2h1v.s5.904630e1955e from=translated src=- shape=8877ddcd vocab=967bda8a
-/
theorem hasOrderFourTransport_imp_goldenH_support (hp5 : p ≠ 5)
    (h : HasOrderFourTransport p) :
    ∃ n, 1 ≤ n ∧ n % 5 = 4 ∧ p ∣ goldenH n := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, hn.1, hn.2.1, orderFourTransport_dvd_goldenH hp5 hn⟩

end AgrawalCore
