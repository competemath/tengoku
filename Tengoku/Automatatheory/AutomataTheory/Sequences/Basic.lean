/-
Copyright (c) 2025-present Ching-Tsun Chou All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

import Tengoku.Automatatheory.AutomataTheory.Mathlib.Imports

/-!
This file contains some definitions and theorems about finite and infinite sequences,
which are modeled by types `List X` and `Stream' X` respectively (X being an arbitrary type).
It is imported directly or indirectly by all other files in AutomataTheory except those
in AutomataTheory.Mathlib.
-/

open Function Set Option Stream'

section List

/-- Pad a finite sequence into an infinite sequence using `default`.
-/
def List.padDefault [Inhabited X] (xl : List X) : Stream' X :=
  fun k ↦ if h : k < xl.length then xl[k] else default

end List

section Stream'

namespace Stream'

variable {X : Type*}

/-- Get the list containing the elements of `xs` from position `m` to `n - 1`.
-/
def extract (xs : Stream' X) (m n : ℕ) : List X :=
  take (n - m) (xs.drop m)

/-- Fix all elements of `xs` to `x` from position `n` onward.
-/
def fixSuffix (xs : Stream' X) (n : ℕ) (x : X) : Stream' X :=
  fun k ↦ if k < n then xs k else x

/- Some miscellaneous theorems are proved below. -/

/--
@isnad1 id=eq.0h2v.s4.f71befd9d0ef from=translated src=- shape=f13515ef vocab=139e8895
-/
theorem take_one {xs : Stream' X} :
    xs.take 1 = [xs.get 0] := by
  simp only [take_succ, take_zero]

/--
@isnad1 id=eq.0h2v.s4.72e1fa06d3f4 from=translated src=- shape=0cfc8341 vocab=d7894452
-/
theorem take_one' {xs : Stream' X} :
    xs.take 1 = [xs 0] := by
  apply take_one

/--
@isnad1 id=eq.0h4v.s4.1c3b9163cc97 from=translated src=- shape=cd89e517 vocab=a3b1fc85
-/
theorem get_drop' {xs : Stream' X} {n k : ℕ} :
    (xs.drop n) k = xs (n + k) := by
  apply get_drop

/--
@isnad1 id=eq.1h4v.s5.a95c35739690 from=translated src=- shape=c35080b1 vocab=2bc2b90d
-/
theorem get_append_left' {xl : List X} {xs : Stream' X} {k : ℕ} (h : k < xl.length) :
    (xl ++ₛ xs) k = xl[k] := by
  apply get_append_left

/--
@isnad1 id=eq.1h4v.s5.d5f258e94b37 from=translated src=- shape=e3a22e0b vocab=c4ddf82e
-/
theorem get_append_right' {xl : List X} {xs : Stream' X} {k : ℕ} (h : xl.length ≤ k) :
    (xl ++ₛ xs) k = xs (k - xl.length) := by
  obtain ⟨n, rfl⟩ := show ∃ n, k = xl.length + n by use (k - xl.length) ; omega
  simp ; apply get_append_right

/--
@isnad1 id=eq.1h4v.s5.223d290d2e08 from=translated src=- shape=01fd1696 vocab=87dd5df0
-/
theorem drop_append_of_ge_length {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).drop n = xs.drop (n - xl.length) := by
  ext k ; simp (disch := omega) only [get.eq_1, get_drop', get_append_right']
  congr ; omega

/--
@isnad1 id=eq.0h4v.s5.40e3d131df88 from=translated src=- shape=1bd1be3b vocab=cdfdc89b
-/
theorem extract_eq_drop_take {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = take (n - m) (xs.drop m) := by
  rfl

/--
@isnad1 id=eq.0h4v.s5.01ee85e7a249 from=translated src=- shape=af907914 vocab=d832ef15
-/
theorem extract_eq_ofFn {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = List.ofFn (fun k : Fin (n - m) ↦ xs (m + k)) := by
  ext k x ; rcases (show k < n - m ∨ ¬ k < n - m by omega) with h_k | h_k
    <;> simp (disch := omega) [extract_eq_drop_take, get.eq_1, getElem?_take, get_drop']
    <;> aesop

/--
@isnad1 id=and.1h7v.s6.619bbe26f5f6 from=translated src=- shape=75b799a4 vocab=b679d70e
-/
theorem extract_eq_extract {xs xs' : Stream' X} {m n m' n' : ℕ}
    (h : xs.extract m n = xs'.extract m' n') :
    n - m = n' - m' ∧ ∀ k < n - m, xs (m + k) = xs' (m' + k) := by
  simp only [extract_eq_ofFn, List.ofFn_inj', Sigma.mk.injEq] at h
  obtain ⟨h_eq, h_fun⟩ := h
  rw [← h_eq] at h_fun ; simp only [heq_eq_eq, funext_iff, Fin.forall_iff] at h_fun
  simp only [← h_eq, true_and] ; intro k h_k ; simp only [h_fun k h_k]

/--
@isnad1 id=eq.0h3v.s4.c94755238d84 from=translated src=- shape=970ff832 vocab=3af6700c
-/
theorem extract_eq_take {xs : Stream' X} {n : ℕ} :
    xs.extract 0 n = xs.take n := by
  simp only [extract_eq_drop_take, tsub_zero, drop_zero]

/--
@isnad1 id=eq.0h3v.s4.d0b8a9748921 from=translated src=- shape=f466e6cb vocab=012b3870
-/
theorem append_extract_drop {xs : Stream' X} {n : ℕ} :
    (xs.extract 0 n) ++ₛ (xs.drop n) = xs := by
  simp only [extract_eq_take, append_take_drop]

/--
@isnad1 id=eq.1h5v.s5.a01933ec03a8 from=translated src=- shape=e77ca61c vocab=eed0418d
-/
theorem extract_apppend_right_right {xl : List X} {xs : Stream' X} {m n : ℕ} (h : xl.length ≤ m) :
    (xl ++ₛ xs).extract m n = xs.extract (m - xl.length) (n - xl.length) := by
  have h1 : n - xl.length - (m - xl.length) = n - m := by omega
  simp (disch := omega) only [extract_eq_drop_take, drop_append_of_ge_length, h1]

/--
@isnad1 id=eq.1h4v.s6.6bcadf9a2960 from=translated src=- shape=24e3c265 vocab=ac1a2092
-/
theorem extract_append_zero_right {xl : List X} {xs : Stream' X} {n : ℕ} (h : xl.length ≤ n) :
    (xl ++ₛ xs).extract 0 n = xl ++ (xs.extract 0 (n - xl.length)) := by
  obtain ⟨k, rfl⟩ := show ∃ k, n = xl.length + k by use (n - xl.length) ; omega
  simp only [extract_eq_take, ← append_take, add_tsub_cancel_left]

/--
@isnad1 id=eq.0h5v.s5.c2827680da74 from=translated src=- shape=43820382 vocab=ebef3f92
-/
theorem extract_drop {xs : Stream' X} {k m n : ℕ} :
    (xs.drop k).extract m n = xs.extract (k + m) (k + n) := by
  have h1 : k + n - (k + m) = n - m := by omega
  simp only [extract_eq_drop_take, drop_drop, h1]

/--
@isnad1 id=eq.0h4v.s4.e5f0863ceb28 from=translated src=- shape=f3df0c0c vocab=de5f70f4
-/
theorem length_extract {xs : Stream' X} {m n : ℕ} :
    (xs.extract m n).length = n - m := by
  simp only [extract_eq_drop_take, length_take]

/--
@isnad1 id=eq.0h3v.s4.2dd66f62a7cc from=translated src=- shape=be8610ab vocab=24b470a7
-/
theorem extract_eq_nil {xs : Stream' X} {n : ℕ} :
    xs.extract n n = [] := by
  simp only [extract_eq_drop_take, tsub_self, take_zero]

/--
@isnad1 id=iff.0h4v.s4.6f558b4622e7 from=translated src=- shape=8803790c vocab=25d23d5e
-/
theorem extract_eq_nil_iff {xs : Stream' X} {m n : ℕ} :
    xs.extract m n = [] ↔ m ≥ n := by
  simp only [extract_eq_drop_take, ← List.length_eq_zero_iff, length_take, ge_iff_le]
  omega

/--
@isnad1 id=eq.1h5v.s6.caa1baadd9b9 from=translated src=- shape=f90b569a vocab=76f42e81
-/
theorem get_extract {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs.get (m + k) := by
  simp only [extract_eq_drop_take, take_get, get_drop]

/--
@isnad1 id=eq.1h5v.s6.759e9de54014 from=translated src=- shape=f078875b vocab=b201be19
-/
theorem get_extract' {xs : Stream' X} {m n k : ℕ} (h : k < n - m) :
    (xs.extract m n)[k]'(by simp only [length_extract, h]) = xs (m + k) := by
  apply get_extract h

/--
@isnad1 id=eq.2h5v.s5.4f7f7440a2f1 from=translated src=- shape=14081803 vocab=9fbe00b2
-/
theorem append_extract_extract {xs : Stream' X} {k m n : ℕ} (h_km : k ≤ m) (h_mn : m ≤ n) :
    (xs.extract k m) ++ (xs.extract m n) = xs.extract k n := by
  have h1 : n - k = (m - k) + (n - m) := by omega
  have h2 : k + (m - k) = m := by omega
  simp only [extract_eq_drop_take, h1, take_add, drop_drop, h2]

/--
@isnad1 id=eq.1h4v.s5.d163d6508cab from=translated src=- shape=efc754a5 vocab=a0b6756c
-/
theorem extract_succ_right {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs.get n] := by
  rw [← append_extract_extract h_mn (show n ≤ n + 1 by omega)] ; congr
  simp only [extract_eq_drop_take, add_tsub_cancel_left, take_one, get_drop, add_zero]

/--
@isnad1 id=eq.1h4v.s5.7e6bd8b77273 from=translated src=- shape=d5fcedea vocab=8ebc7b3e
-/
theorem extract_succ_right' {xs : Stream' X} {m n : ℕ} (h_mn : m ≤ n) :
    xs.extract m (n + 1) = xs.extract m n ++ [xs n] := by
  apply extract_succ_right ; exact h_mn

/--
@isnad1 id=eq.1h6v.s5.973195b1042e from=translated src=- shape=30dfcc74 vocab=35daa3ba
-/
theorem extract_extract2' {xs : Stream' X} {m n i j : ℕ} (h : j ≤ n - m) :
    (xs.extract m n).extract i j = xs.extract (m + i) (m + j) := by
  ext k x ; rcases (show k < j - i ∨ ¬ k < j - i by omega) with h_k | h_k
    <;> simp [extract_eq_ofFn, h_k]
  · simp only [(show i + k < n - m by omega), (show k < m + j - (m + i) by omega), add_assoc]
  · simp only [(show ¬k < m + j - (m + i) by omega), IsEmpty.forall_iff]

/--
@isnad1 id=eq.1h5v.s5.f7672c71389b from=translated src=- shape=39b643eb vocab=4f5f1f50
-/
theorem extract_extract2 {xs : Stream' X} {n i j : ℕ} (h : j ≤ n) :
    (xs.extract 0 n).extract i j = xs.extract i j := by
  simp only [extract_extract2' (show j ≤ n - 0 by omega), zero_add]

/--
@isnad1 id=eq.0h4v.s5.aa23843128dd from=translated src=- shape=f9017ad7 vocab=7835d8af
-/
theorem extract_extract1 {xs : Stream' X} {n i : ℕ} :
    (xs.extract 0 n).extract i = xs.extract i n := by
  simp only [length_extract, extract_extract2 (show n ≤ n by omega), tsub_zero]

/--
@isnad1 id=eq.0h2v.s4.e9cf096805e5 from=translated src=- shape=c1c35b87 vocab=ce96bf6e
-/
theorem extract_padDefault [Inhabited X] {xl : List X} :
    xl.padDefault.extract 0 xl.length = xl := by
  simp [List.padDefault, extract_eq_ofFn]

/--
@isnad1 id=eq.1h3v.s5.41fd84fb01e7 from=translated src=- shape=3bf2e446 vocab=944b3f5b
-/
theorem padDefault_elt_left [Inhabited X] {xl : List X} {k : ℕ} (h : k < xl.length) :
    xl.padDefault k = xl[k] := by
  simp [List.padDefault, h]

end Stream'

section Misc

/--
@isnad1 id=ex.1h2v.s5.60695a6b2d37 from=translated src=- shape=42c974fe vocab=20988ed0
-/
theorem antitone_fin_eventually {n : ℕ} {f : ℕ → Fin n} (h : Antitone f) :
    ∃ i : Fin n, ∃ m, ∀ k ≥ m, f k = i := by
  have h_fin : (range f).Finite := toFinite (range f)
  have h_ne : (range f).Nonempty := by use (f 0) ; simp
  obtain ⟨i, ⟨m, rfl⟩, h_min⟩ := Finite.exists_minimal h_fin h_ne
  use (f m), m ; intro k h_k
  have h_k_m := h h_k
  have h_m_k := h_min (show f k ∈ range f by simp) h_k_m
  exact Fin.le_antisymm h_k_m h_m_k

/--
@isnad1 id=ex.1h3v.s6.a41053ff32eb from=translated src=- shape=58333780 vocab=ca6fe735
-/
theorem option_some_pigeonhole {X : Type*} [Finite X] {n : ℕ} (f : Fin n → Option X)
    (h : {j | (f j).isSome}.ncard > Nat.card X) :
    ∃ j1 j2, j1 ≠ j2 ∧ ∃ x, f j1 = some x ∧ f j2 = some x := by
  have ht : (some '' (univ : Set X)).Finite := by exact toFinite (some '' univ)
  have : (some '' (univ : Set X)).ncard = Nat.card X := by
    rw [ncard_image_of_injective (univ : Set X) (some_injective X)] ; exact ncard_univ X
  have hc : (some '' (univ : Set X)).ncard < {j | (f j).isSome}.ncard := by omega
  have hf : ∀ j ∈ {j | (f j).isSome}, f j ∈ some '' (univ : Set X) := by
    intro j ; simp ; rw [isSome_iff_exists] ; tauto
  obtain ⟨j1, h_j1, j2, h_j2, h_ne, h_eq⟩ := exists_ne_map_eq_of_ncard_lt_of_maps_to hc hf ht
  obtain ⟨s1, h_s1⟩ := isSome_iff_exists.mp h_j1
  obtain ⟨s2, h_s2⟩ := isSome_iff_exists.mp h_j2
  simp [h_s1, h_s2] at h_eq ; obtain ⟨rfl⟩ := h_eq
  use j1, j2 ; simp [h_ne] ; use s1

end Misc
