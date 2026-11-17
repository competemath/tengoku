/-
Nucleo Lean della campagna Agrawal — IL PONTE INVERSO: da locale a globale.
`AgrawalBridge.lean` (teorema `agrawal_fermat_shadow`) riduce la congruenza
di Agrawal da `(Z/n)[X]` a `(Z/p)[X]` per ogni fattore primo `p` di `n`
(squarefree). Qui si fa il percorso opposto: dalla congruenza locale in
`(Z/p)[X]`, per ogni `p ∣ n`, si RICOSTRUISCE la congruenza globale in
`(Z/n)[X]`.

La tecnica (variante della strategia a coefficienti, `FermatShadow`-style):
si solleva tutto a `ℤ[X]`. Sia `F = (X-1)^n - (X^n-1)` e `D = X^5-1`
(monico, grado 5). La divisione euclidea su `ℤ` dà `F = D·Q + R` con
`deg R < 5`. L'ipotesi locale mod `p` dice che il resto della divisione di
`F.map φ_p` per `D.map φ_p` è nullo; per l'UNICITÀ della divisione
euclidea (`Polynomial.div_modByMonic_unique`, dato che `D.map φ_p` è
monico) questo resto coincide con `R.map φ_p`. Dunque ogni coefficiente
di `R` è divisibile per ogni fattore primo di `n`; siccome `n` è
squarefree, `n = ∏ p`, e la stessa aritmetica di incollaggio usata in
`AgrawalBridge`/`FermatShadow` (`Nat.prod_primeFactors_of_squarefree` +
`Finset.prod_primes_dvd`, qui applicata ai coefficienti invece che alla
potenza di Fermat) dà che `n` divide ogni coefficiente di `R`. Quindi
`R.map φ_n = 0`, e mappando la decomposizione `F = D·Q+R` modulo `n` si
ottiene la congruenza globale con testimone `Q.map φ_n`. Il lavoro pesante
è isolato in `coeff_dvd_of_local` (una dichiarazione a parte, per non far
esplodere gli heartbeat di un unico teorema monolitico).
Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.AgrawalR5.AgrawalCore.FermatShadow
import Tengoku.Seed.Algebra.Polynomial.Div

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial

namespace AgrawalCore

/-- **Colla aritmetica sui coefficienti.** Se un intero `r` è divisibile
per ogni fattore primo di `n` (squarefree), allora `r` è divisibile per
`n`. Stessa aritmetica di `agrawal_fermat_shadow`/`fermat_shadow`
(`Nat.prod_primeFactors_of_squarefree` + `Finset.prod_primes_dvd`),
applicata a un coefficiente intero invece che a `5^(n-1)-1`.-/
theorem dvd_of_forall_primeFactors_dvd {n : ℕ} (hsq : Squarefree n) {r : ℤ}
    (H : ∀ p ∈ n.primeFactors, (p : ℤ) ∣ r) : (n : ℤ) ∣ r := by
  have key : ∀ p ∈ n.primeFactors, p ∣ r.natAbs := by
    intro p hp
    have h1 : (p : ℤ) ∣ (r.natAbs : ℤ) := Int.dvd_natAbs.mpr (H p hp)
    exact_mod_cast h1
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  have hdvd : (∏ p ∈ n.primeFactors, p) ∣ r.natAbs :=
    Finset.prod_primes_dvd r.natAbs
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).prime) key
  rw [hprod] at hdvd
  have h2 : (n : ℤ) ∣ (r.natAbs : ℤ) := by exact_mod_cast hdvd
  exact Int.dvd_natAbs.mp h2

/-- **Il passo locale, isolato.** Sia `F = (X-1)^n - (X^n-1)` sollevato a
`ℤ[X]`, diviso euclideamente per il monico `D = X^5-1`: `F = D·Q + R` con
`deg R < deg D`. Se la congruenza di Agrawal vale in `(Z/p)[X]` (`p`
primo), allora ogni coefficiente di `R` è divisibile per `p`: il resto
della divisione di `F.map φ_p` per `D.map φ_p` è, per unicità della
divisione euclidea, sia `0` (dalla congruenza locale) sia `R.map φ_p`
(dalla divisione sollevata da `ℤ`).-/
theorem coeff_dvd_of_local {n : ℕ} {Q R : Polynomial ℤ}
    (hdecomp : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ) = (X ^ 5 - 1) * Q + R)
    (_hDmonic : (X ^ 5 - 1 : Polynomial ℤ).Monic)
    (hDdeg : (X ^ 5 - 1 : Polynomial ℤ).degree = (5 : ℕ))
    (hRdeg : R.degree < (X ^ 5 - 1 : Polynomial ℤ).degree)
    {p : ℕ} [Fact p.Prime] (gp : Polynomial (ZMod p))
    (hgp : (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * gp) (i : ℕ) :
    (p : ℤ) ∣ R.coeff i := by
  set φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hφdef
  have hFmap : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map φ
      = (X - 1) ^ n - (X ^ n - 1) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
  have hDmap : (X ^ 5 - 1 : Polynomial ℤ).map φ
      = (X ^ 5 - 1 : Polynomial (ZMod p)) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
  have hDmap_monic : ((X ^ 5 - 1 : Polynomial ℤ).map φ).Monic := by
    rw [hDmap]
    have hm := Polynomial.monic_X_pow_sub_C (1 : ZMod p) (n := 5) (by norm_num)
    rwa [Polynomial.C_1] at hm
  have hDmap_deg : ((X ^ 5 - 1 : Polynomial ℤ).map φ).degree = (5 : ℕ) := by
    rw [hDmap]
    have hd := Polynomial.degree_X_pow_sub_C (R := ZMod p) (n := 5) (by norm_num) 1
    rwa [Polynomial.C_1] at hd
  have hlocal : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map φ
      = (X ^ 5 - 1 : Polynomial ℤ).map φ * gp := by
    rw [hFmap, hDmap]; linear_combination hgp
  have hdecomp_map : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map φ
      = (X ^ 5 - 1 : Polynomial ℤ).map φ * Q.map φ + R.map φ := by
    rw [hdecomp]; simp [Polynomial.map_add, Polynomial.map_mul]
  have hRmap_deg : (R.map φ).degree < ((X ^ 5 - 1 : Polynomial ℤ).map φ).degree := by
    rw [hDmap_deg]
    calc (R.map φ).degree ≤ R.degree := Polynomial.degree_map_le
      _ < (X ^ 5 - 1 : Polynomial ℤ).degree := hRdeg
      _ = (5 : ℕ) := hDdeg
  have hzero_deg : (0 : Polynomial (ZMod p)).degree
      < ((X ^ 5 - 1 : Polynomial ℤ).map φ).degree := by
    rw [Polynomial.degree_zero, hDmap_deg]
    exact WithBot.bot_lt_coe 5
  have proof_eq1 : R.map φ + (X ^ 5 - 1 : Polynomial ℤ).map φ * Q.map φ
      = ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map φ := by
    linear_combination -hdecomp_map
  have proof_eq2 : (0 : Polynomial (ZMod p))
      + (X ^ 5 - 1 : Polynomial ℤ).map φ * gp
      = ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map φ := by
    linear_combination -hlocal
  have huniq1 := Polynomial.div_modByMonic_unique (Q.map φ) (R.map φ)
    hDmap_monic ⟨proof_eq1, hRmap_deg⟩
  have huniq2 := Polynomial.div_modByMonic_unique gp 0
    hDmap_monic ⟨proof_eq2, hzero_deg⟩
  have hRmap0 : R.map φ = 0 := huniq1.2.symm.trans huniq2.2
  have hcoe0 : (R.coeff i : ZMod p) = 0 := by
    have hco := congrArg (fun q : Polynomial (ZMod p) => q.coeff i) hRmap0
    simpa [Polynomial.coeff_map, hφdef] using hco
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd (R.coeff i) p).mp hcoe0

/-- **IL PONTE, da locale a globale.** Sia `n` squarefree. Se per ogni
fattore primo `p` di `n` la congruenza di Agrawal a `r = 5` vale in
`(Z/p)[X]`, allora vale in `(Z/n)[X]`. È il passaggio inverso rispetto
alla riduzione `agrawal_fermat_shadow`/`agrawal_local`: qui si incollano
i pezzi locali invece di scomporre il pezzo globale.-/
theorem congruence_of_local {n : ℕ} (hn : Squarefree n) (_hn1 : 0 < n)
    (h : ∀ p ∈ n.primeFactors, ∃ g : Polynomial (ZMod p),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g) :
    ∃ g : Polynomial (ZMod n),
      (X - 1) ^ n = X ^ n - 1 + (X ^ 5 - 1) * g := by
  -- Il divisore, su ℤ: monico, grado 5.
  have hDmonic : (X ^ 5 - 1 : Polynomial ℤ).Monic := by
    have hm := Polynomial.monic_X_pow_sub_C (1 : ℤ) (n := 5) (by norm_num)
    rwa [Polynomial.C_1] at hm
  have hDdeg : (X ^ 5 - 1 : Polynomial ℤ).degree = (5 : ℕ) := by
    have hd := Polynomial.degree_X_pow_sub_C (R := ℤ) (n := 5) (by norm_num) 1
    rwa [Polynomial.C_1] at hd
  -- Divisione euclidea su ℤ: F = D·Q + R, deg R < 5.
  obtain ⟨Q, R, hdecomp, hRdeg⟩ :
      ∃ Q R : Polynomial ℤ,
        ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ) = (X ^ 5 - 1) * Q + R ∧
          R.degree < (X ^ 5 - 1 : Polynomial ℤ).degree :=
    ⟨((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ) /ₘ (X ^ 5 - 1),
      ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ) %ₘ (X ^ 5 - 1),
      by
        have hb := Polynomial.modByMonic_add_div
          (((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ)) (X ^ 5 - 1 : Polynomial ℤ)
        linear_combination -hb,
      Polynomial.degree_modByMonic_lt
        ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ) hDmonic⟩
  -- Incollaggio: n divide ogni coefficiente di R.
  have hcoeff_n : ∀ i : ℕ, (n : ℤ) ∣ R.coeff i := by
    intro i
    apply dvd_of_forall_primeFactors_dvd hn
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    obtain ⟨gp, hgp⟩ := h p hp
    exact coeff_dvd_of_local hdecomp hDmonic hDdeg hRdeg gp hgp i
  have hRmapn : R.map (Int.castRingHom (ZMod n)) = 0 := by
    ext i
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (R.coeff i) n).mpr (hcoeff_n i)
  -- Ricostruzione della congruenza modulo n.
  refine ⟨Q.map (Int.castRingHom (ZMod n)), ?_⟩
  have hFmapn : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map
      (Int.castRingHom (ZMod n)) = (X - 1) ^ n - (X ^ n - 1) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X]
  have hDmapn : (X ^ 5 - 1 : Polynomial ℤ).map (Int.castRingHom (ZMod n))
      = (X ^ 5 - 1 : Polynomial (ZMod n)) := by
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_one]
  have hdecomp_mapn : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map
      (Int.castRingHom (ZMod n))
      = (X ^ 5 - 1 : Polynomial (ZMod n)) * Q.map (Int.castRingHom (ZMod n)) := by
    have hstep : ((X - 1) ^ n - (X ^ n - 1) : Polynomial ℤ).map (Int.castRingHom (ZMod n))
        = (X ^ 5 - 1 : Polynomial ℤ).map (Int.castRingHom (ZMod n))
          * Q.map (Int.castRingHom (ZMod n)) + R.map (Int.castRingHom (ZMod n)) := by
      rw [hdecomp]; simp [Polynomial.map_add, Polynomial.map_mul]
    rw [hRmapn, add_zero] at hstep
    rw [hstep, hDmapn]
  have key : (X - 1) ^ n - (X ^ n - 1)
      = (X ^ 5 - 1 : Polynomial (ZMod n)) * Q.map (Int.castRingHom (ZMod n)) :=
    hFmapn.symm.trans hdecomp_mapn
  linear_combination key

end AgrawalCore
