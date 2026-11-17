/-
Nucleo Lean della campagna Agrawal — l'aritmetica delle classi mod 80 che
serve alla proposizione di Lenstra.

Il fatto centrale: `3` ha ordine `4` modulo `80` (`3^4 = 81 ≡ 1`), quindi il
prodotto di `k` numeri tutti `≡ 3 mod 80` dipende, modulo `80`, solo da
`k mod 4`. Quando `k ≡ 1 mod 4` il prodotto resta `≡ 3 mod 80`.

  · `pow_three_mod_eighty`   : `3^k mod 80` dipende solo da `k mod 4`
  · `prod_mod_eighty`        : il prodotto di una lista di classe `3`
                               vale `3^(lunghezza) mod 80`
  · `prod_class_mod_eighty`  : se la lunghezza è `≡ 1 mod 4`, il prodotto
                               resta nella classe `3 mod 80`
  · `mod_five_of_mod_eighty`, `sq_not_one_mod_five` : la scappatoia
    `n² ≡ 1 mod 5` resta chiusa per ogni `n ≡ 3 mod 80` (dato che `5 ∣ 80`)
  · variante per la classe `67 mod 80` (`67` ha anch'esso ordine `4`,
    `67² ≡ 9`, `67³ ≡ 43`, `67⁴ ≡ 1`): per lunghezza dispari il prodotto
    cade nella classe `67` o `43`, ed entrambe chiudono comunque la
    scappatoia `n² ≡ 1 mod 5`.

Nella congettura di Agrawal la conclusione è «`n` primo OPPURE `n² ≡ 1 mod
r`»: questi lemmi chiudono la seconda via per `r = 5` sulle classi `3` e
`67` mod `80`, quindi un `n` con queste proprietà sarebbe un controesempio
genuino solo se falsifica anche la prima. Campagna UNICO, 26 luglio 2026.
-/
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Algebra.Ring.Parity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace AgrawalCore

/-! ### La classe `3 mod 80` (ordine `4`) -/

/-- **Periodicità di `3^k` modulo `80`.** Poiché `3^4 = 81 ≡ 1 (mod 80)`,
il resto di `3^k` modulo `80` dipende solo da `k mod 4`.
@isnad1 id=eq.0h1v.s6.e4bbbd81fe52 from=translated src=- shape=0fd08476 vocab=df461349
-/
lemma pow_three_mod_eighty (k : ℕ) : 3 ^ k % 80 = 3 ^ (k % 4) % 80 := by
  have h81 : (3 : ℕ) ^ 4 ≡ 1 [MOD 80] := by decide
  have hk : (3 : ℕ) ^ k ≡ 3 ^ (k % 4) [MOD 80] := by
    conv_lhs => rw [← Nat.div_add_mod k 4]
    rw [pow_add, pow_mul]
    have hstep := (h81.pow (k / 4)).mul_right (3 ^ (k % 4))
    simpa using hstep
  exact hk

/-- **Il prodotto di una lista di classe `3` mod `80`** vale, modulo `80`,
`3` elevato alla lunghezza della lista.
@isnad1 id=eq.1h1v.s6.1ab31902bbad from=translated src=- shape=ccd03e3a vocab=b23b0f16
-/
lemma prod_mod_eighty {L : List ℕ} (h : ∀ x ∈ L, x % 80 = 3) :
    L.prod % 80 = 3 ^ L.length % 80 := by
  have hmod : L.prod ≡ 3 ^ L.length [MOD 80] := by
    induction L with
    | nil => simp [Nat.ModEq.refl]
    | cons a l ih =>
      have ha : a ≡ 3 [MOD 80] := h a List.mem_cons_self
      have hl : l.prod ≡ 3 ^ l.length [MOD 80] :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      have hstep := ha.mul hl
      simpa [List.prod_cons, List.length_cons, pow_succ'] using hstep
  exact hmod

/-- **Il prodotto sta nella classe `3` mod `80`.** Se ogni fattore è
`≡ 3 (mod 80)` e la lunghezza della lista è `≡ 1 (mod 4)`, allora il
prodotto è ancora `≡ 3 (mod 80)`.
@isnad1 id=eq.2h1v.s6.fcf47755b3d3 from=translated src=- shape=812f7707 vocab=c27b3e27
-/
theorem prod_class_mod_eighty {L : List ℕ} (h : ∀ x ∈ L, x % 80 = 3)
    (hk : L.length % 4 = 1) : L.prod % 80 = 3 := by
  rw [prod_mod_eighty h, pow_three_mod_eighty, hk]
  decide

/-! ### La scappatoia mod `5` resta chiusa -/

/-- Passaggio da `mod 80` a `mod 5` per un residuo qualunque, dato che
`5 ∣ 80`.-/
private lemma mod_eighty_to_five {n a : ℕ} (h : n % 80 = a) : n % 5 = a % 5 := by
  have hd : (5 : ℕ) ∣ 80 := ⟨16, rfl⟩
  have key := Nat.mod_mod_of_dvd n hd
  rw [h] at key
  exact key.symm

/-- Se `n ≡ 3 (mod 80)` allora `n ≡ 3 (mod 5)`.
@isnad1 id=eq.1h1v.s5.91cc5109026b from=translated src=- shape=5643c472 vocab=b6301362
-/
lemma mod_five_of_mod_eighty {n : ℕ} (h : n % 80 = 3) : n % 5 = 3 := by
  have h5 := mod_eighty_to_five h
  omega

/-- **La scappatoia resta chiusa** per la classe `3`: se `n ≡ 3 (mod 80)`
allora `n² % 5 = 4 ≠ 1`.
@isnad1 id=ne.1h1v.s5.e9562f6b1476 from=translated src=- shape=a8e2a8c4 vocab=df461349
-/
theorem sq_not_one_mod_five {n : ℕ} (h : n % 80 = 3) : n ^ 2 % 5 ≠ 1 := by
  have h5 := mod_five_of_mod_eighty h
  have hsq : n ^ 2 % 5 = (n % 5) ^ 2 % 5 := by rw [Nat.pow_mod]
  rw [hsq, h5]
  decide

/-- Forma generale, riutilizzata per la variante `67`: se `n ≡ a (mod 80)`
e `a² % 5 ≠ 1`, allora `n² % 5 ≠ 1`.-/
private lemma sq_not_one_mod_five_of_class {n a : ℕ} (h : n % 80 = a)
    (ha : a ^ 2 % 5 ≠ 1) : n ^ 2 % 5 ≠ 1 := by
  have h5 := mod_eighty_to_five h
  have hsq : n ^ 2 % 5 = a ^ 2 % 5 := by
    rw [Nat.pow_mod, h5, ← Nat.pow_mod]
  rw [hsq]
  exact ha

/-! ### Variante: la classe `67 mod 80` (ordine `4` anch'essa) -/

/-- **Periodicità di `67^k` modulo `80`.** Poiché `67^4 ≡ 1 (mod 80)`
(`67² ≡ 9`, `67³ ≡ 43`, `67⁴ ≡ 1`), il resto di `67^k` modulo `80` dipende
solo da `k mod 4`.
@isnad1 id=eq.0h1v.s6.9185813aeb3f from=translated src=- shape=0fd08476 vocab=df461349
-/
lemma pow_sixtyseven_mod_eighty (k : ℕ) : 67 ^ k % 80 = 67 ^ (k % 4) % 80 := by
  have h67 : (67 : ℕ) ^ 4 ≡ 1 [MOD 80] := by decide
  have hk : (67 : ℕ) ^ k ≡ 67 ^ (k % 4) [MOD 80] := by
    conv_lhs => rw [← Nat.div_add_mod k 4]
    rw [pow_add, pow_mul]
    have hstep := (h67.pow (k / 4)).mul_right (67 ^ (k % 4))
    simpa using hstep
  exact hk

/-- **Il prodotto di una lista di classe `67` mod `80`** vale, modulo `80`,
`67` elevato alla lunghezza della lista.
@isnad1 id=eq.1h1v.s6.143179a94e73 from=translated src=- shape=ccd03e3a vocab=b23b0f16
-/
lemma prod_mod_eighty_67 {L : List ℕ} (h : ∀ x ∈ L, x % 80 = 67) :
    L.prod % 80 = 67 ^ L.length % 80 := by
  have hmod : L.prod ≡ 67 ^ L.length [MOD 80] := by
    induction L with
    | nil => simp [Nat.ModEq.refl]
    | cons a l ih =>
      have ha : a ≡ 67 [MOD 80] := h a List.mem_cons_self
      have hl : l.prod ≡ 67 ^ l.length [MOD 80] :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      have hstep := ha.mul hl
      simpa [List.prod_cons, List.length_cons, pow_succ'] using hstep
  exact hmod

/-- **Il prodotto sta nella classe `67` o `43` mod `80`.** Se ogni fattore
è `≡ 67 (mod 80)` e la lista ha lunghezza dispari, il prodotto è
`≡ 67 (mod 80)` (lunghezza `≡ 1 mod 4`) oppure `≡ 43 (mod 80)` (lunghezza
`≡ 3 mod 4`).
@isnad1 id=or.2h1v.s6.327b493a9407 from=translated src=- shape=b4e4ff6e vocab=d3208a03
-/
theorem prod_class_mod_eighty_67 {L : List ℕ} (h : ∀ x ∈ L, x % 80 = 67)
    (hk : Odd L.length) : L.prod % 80 = 67 ∨ L.prod % 80 = 43 := by
  have hmod : L.length % 4 = 1 ∨ L.length % 4 = 3 := by
    obtain ⟨m, hm⟩ := hk
    omega
  rw [prod_mod_eighty_67 h, pow_sixtyseven_mod_eighty]
  rcases hmod with h1 | h3
  · left; rw [h1]; decide
  · right; rw [h3]; decide

/-- **La scappatoia resta chiusa anche per la classe `67`**: se ogni
fattore è `≡ 67 (mod 80)` e la lista ha lunghezza dispari, il quadrato del
prodotto non è mai `≡ 1 (mod 5)`.
@isnad1 id=ne.2h1v.s6.5c1ee4a407e0 from=translated src=- shape=e1dac737 vocab=288d59e1
-/
theorem sq_not_one_mod_five_of_prod_67 {L : List ℕ} (h : ∀ x ∈ L, x % 80 = 67)
    (hk : Odd L.length) : L.prod ^ 2 % 5 ≠ 1 := by
  rcases prod_class_mod_eighty_67 h hk with h67 | h43
  · exact sq_not_one_mod_five_of_class h67 (by decide)
  · exact sq_not_one_mod_five_of_class h43 (by decide)

end AgrawalCore
