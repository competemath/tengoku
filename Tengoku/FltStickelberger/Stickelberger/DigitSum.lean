module
public import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
@[expose] public section

/-!
# Base-`p` digit sums

Development following L. C. Washington, *Introduction to Cyclotomic
Fields* (2nd ed.), §6.2 (Proposition 6.13 and Lemma 6.14). The valuation
`s(α) = v_𝒫̄(g(ω^{-α}))` of a Gauss sum turns out to be the **base-`p` digit
sum** of `α`. This file isolates the purely arithmetic facts about digit sums
that the valuation computation needs; nothing here depends on Gauss sums or
valuations.

Built only on Mathlib's `Nat.digits` API; no other formalization is consulted.
-/

namespace Stickelberger

open Finset

/-- Helper: the mixed-radix decomposition of a `mod` by a product.
@isnad1 id=eq.2h3v.s6.7c85f42e8032 from=translated src=- shape=e7cc44fe vocab=1ec7a304
-/
theorem mod_mul' (a : ℕ) {b c : ℕ} (hb : 0 < b) (hc : 0 < c) :
    a % (b * c) = a % b + b * (a / b % c) := by
  have h1 : a = (a % b + b * (a / b % c)) + b * c * (a / b / c) := by
    have e2 := Nat.div_add_mod (a / b) c
    calc a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
      _ = b * (c * (a / b / c) + a / b % c) + a % b := by rw [e2]
      _ = (a % b + b * (a / b % c)) + b * c * (a / b / c) := by ring
  have hr : a % b < b := Nat.mod_lt _ hb
  have hbc : b * (a / b % c + 1) ≤ b * c := by gcongr; exact Nat.mod_lt _ hc
  have hb2 : b * (a / b % c) + b ≤ b * c := by rw [← Nat.mul_succ]; exact hbc
  have h2 : a % b + b * (a / b % c) < b * c := by omega
  nth_rewrite 1 [h1]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]

/-- **Rotation invariance.** Summing `g` over the cyclic rotation `i ↦ (k + i) % f`
of `range f` gives the same result as summing `g` over `range f`. This is what lets
the digit-rotation double sum in Lemma 6.14 be reindexed.
@isnad1 id=eq.0h4v.s5.193ca2a2b93e from=translated src=- shape=3d92bc10 vocab=9b083cc3
-/
theorem sum_range_rotate {M : Type*} [AddCommMonoid M] (g : ℕ → M) (f k : ℕ) :
    ∑ i ∈ range f, g ((k + i) % f) = ∑ i ∈ range f, g i := by
  rcases Nat.eq_zero_or_pos f with hf | hf
  · simp [hf]
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  rw [← Fin.sum_univ_eq_sum_range (fun i => g i),
    ← Fin.sum_univ_eq_sum_range (fun i => g ((k + i) % (n + 1)))]
  refine Fintype.sum_equiv (Equiv.addLeft (⟨k % (n + 1), Nat.mod_lt k n.succ_pos⟩ : Fin (n + 1)))
    (fun x : Fin (n + 1) => g ((k + x.val) % (n + 1)))
    (fun x : Fin (n + 1) => g x.val) (fun x => ?_)
  simp only [Equiv.coe_addLeft, Fin.val_add]
  congr 1
  exact ((Nat.mod_modEq k (n + 1)).add_right x.val).symm

/-- A finite sum of `Nat.ModEq`s is a `Nat.ModEq`.
@isnad1 id=modeq.1h5v.s5.0915cbcac0db from=translated src=- shape=fd08eb72 vocab=88d146c4
-/
theorem modEq_sum {α : Type*} {n : ℕ} {F G : α → ℕ} {s : Finset α}
    (h : ∀ a ∈ s, F a ≡ G a [MOD n]) : ∑ a ∈ s, F a ≡ ∑ a ∈ s, G a [MOD n] := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- The base-`p` digit sum of `h` truncated to its first `f` digits, in closed form
`∑_{i<f} h/p^i%p`. For `h < p^f` this is the full digit sum (Proposition 6.13).-/
def digitSumF (p f h : ℕ) : ℕ := ∑ i ∈ range f, h / p ^ i % p

/-- **Floor split for `(ZMod m)ˣ` representatives.** With `a.val` the canonical unit
representative, `c·a.val = (a·c).val + m·⌊c·a.val/m⌋` — the bridge between the
`stickelbergerProd` exponent `⌊c·a/m⌋` and the `σ_c`-twist multiplicity bookkeeping.
@isnad1 id=eq.0h3v.s7.3f76c67766f0 from=translated src=- shape=55c46b4e vocab=fa494338
-/
theorem mul_units_val_eq_floor {m : ℕ} [NeZero m] (a : (ZMod m)ˣ) (c : ℕ) :
    c * (a : ZMod m).val = ((a : ZMod m) * (c : ZMod m)).val + m * (c * (a : ZMod m).val / m) := by
  have hdiv := (Nat.div_add_mod (c * (a : ZMod m).val) m).symm
  have hmod : c * (a : ZMod m).val % m = ((a : ZMod m) * (c : ZMod m)).val := by
    rw [ZMod.val_mul, ZMod.val_natCast, ← Nat.mod_mul_mod, mul_comm (c % m),
      mul_comm (a : ZMod m).val]
  rw [hmod, add_comm] at hdiv
  exact hdiv

/-- **Per-fiber exponent constancy (`f = 1`).** With `d = (ℓ-1)/r` and `a < r` (and `r ∣ ℓ-1`),
the shifted exponent `d·a·(1+r·j)` reduces mod `ℓ-1` to `d·a` for every `j` — because
`d·a·(1+r·j) = d·a + (ℓ-1)·(a·j)` and `d·a < ℓ-1`. This is the arithmetic core of the totally-split
fiber sum (Washington 6.9): for the character `ω^{-d}` of exact order `r`, every prime in the
`Gal(L/K)`-fiber over `𝔭_a` (indexed by `j`, with `galEquivZMod` exponent `k = 1+r·j ≡ 1 mod r`)
carries the *same* base-`ℓ` digit `d·a`.
@isnad1 id=eq.4h4v.s7.2313bb85c834 from=translated src=- shape=6a0acc50 vocab=4496d307
-/
theorem div_mul_one_add_mul_mod {r ℓ a j : ℕ} (hr0 : 0 < r) (hrdvd : r ∣ ℓ - 1)
    (hℓ : 0 < ℓ - 1) (ha : a < r) :
    ((ℓ - 1) / r * a * (1 + r * j)) % (ℓ - 1) = (ℓ - 1) / r * a := by
  obtain ⟨k, hk⟩ := hrdvd
  have hd : (ℓ - 1) / r = k := by rw [hk, Nat.mul_div_cancel_left _ hr0]
  have hk0 : 0 < k := by
    rw [hk] at hℓ
    rcases Nat.eq_zero_or_pos k with rfl | h
    · simp at hℓ
    · exact h
  rw [hd]
  have hrw : k * a * (1 + r * j) = k * a + (ℓ - 1) * (a * j) := by rw [hk]; ring
  rw [hrw, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  rw [hk]
  calc k * a < k * r := (Nat.mul_lt_mul_left hk0).mpr ha
    _ = r * k := Nat.mul_comm k r

/-- **Exponent shift-invariance from `k ≡ 1 (mod r)`.** The `k % r = 1` form of
`div_mul_one_add_mul_mod` (`k = 1 + r·(k/r)`): if `k ≡ 1 (mod r)` then `(d·a·k) mod (ℓ-1) = d·a`
(`d = (ℓ-1)/r`, `a < r`). This is the arithmetic that makes `α·k ≡ α (mod q-1)` for the Gauss-sum
eigenvector hypothesis when `σ` fixes `ℚ(ζ_r)` (so its cyclotomic exponent `k ≡ 1 mod r`).
@isnad1 id=eq.5h4v.s7.eac3445b55d4 from=translated src=- shape=b0aada32 vocab=66b6a2fd
-/
theorem div_mul_mod_of_mod_eq_one {r ℓ a k : ℕ} (hr0 : 0 < r) (hrdvd : r ∣ ℓ - 1) (hℓ : 0 < ℓ - 1)
    (ha : a < r) (hk : k % r = 1) :
    ((ℓ - 1) / r * a * k) % (ℓ - 1) = (ℓ - 1) / r * a := by
  have hdm := Nat.div_add_mod k r
  rw [hk] at hdm
  have hke : k = 1 + r * (k / r) := by omega
  rw [hke]
  exact div_mul_one_add_mul_mod hr0 hrdvd hℓ ha

/-- Reduce a scaled residue: `((ℓ-1)/m · k) mod (ℓ-1) = (ℓ-1)/m · (k mod m)` when `m ∣ ℓ-1`.
@isnad1 id=eq.2h3v.s6.d866c33a6fe5 from=translated src=- shape=8ceee075 vocab=66b6a2fd
-/
theorem div_mul_mod_eq {ℓ m k : ℕ} (hm0 : 0 < m) (hmdvd : m ∣ ℓ - 1) :
    (ℓ - 1) / m * k % (ℓ - 1) = (ℓ - 1) / m * (k % m) := by
  rcases Nat.eq_zero_or_pos (ℓ - 1) with hℓ0 | hℓpos
  · simp [hℓ0]
  have hcancel : (ℓ - 1) / m * m = ℓ - 1 := Nat.div_mul_cancel hmdvd
  have hmod : (ℓ - 1) / m * k % (ℓ - 1) = (ℓ - 1) / m * (k % m) % (ℓ - 1) := by
    conv_lhs => rw [← Nat.div_add_mod k m, Nat.mul_add]
    conv_lhs => lhs; lhs; rw [← Nat.mul_assoc, hcancel]
    rw [Nat.mul_add_mod_self_left]
  rw [hmod]
  rcases Nat.eq_zero_or_pos ((ℓ - 1) / m) with hq0 | hqpos
  · simp [hq0]
  have hkmod : k % m < m := Nat.mod_lt k hm0
  have hlt : (ℓ - 1) / m * (k % m) < ℓ - 1 :=
    calc (ℓ - 1) / m * (k % m) < (ℓ - 1) / m * m := (Nat.mul_lt_mul_left hqpos).mpr hkmod
      _ = ℓ - 1 := hcancel
  exact Nat.mod_eq_of_lt hlt

/-- Scaling a digit-position sum: as `h` ranges over `[0, a·m)`, `h / a` takes each value in
`[0, m)` exactly `a` times, so `∑ (h / a % p) = a · ∑ (k % p)`.
@isnad1 id=eq.1h3v.s6.f1102c6b8c82 from=translated src=- shape=822d56c6 vocab=05d5cd05
-/
theorem sum_range_div_mod (p a m : ℕ) (ha : 0 < a) :
    ∑ h ∈ range (a * m), (h / a % p) = a * ∑ k ∈ range m, (k % p) := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    have hconst : ∀ x ∈ range a, (a * n + x) / a % p = n % p := fun x hx => by
      rw [Nat.mul_add_div ha, Nat.div_eq_of_lt (Finset.mem_range.mp hx), add_zero]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- Periodicity of `· % p`: as `k` ranges over `[0, p·c)`, the residue `k % p` runs through
`0, …, p-1` exactly `c` times, so `∑ (k % p) = c · ∑_{d<p} d`.
@isnad1 id=eq.0h2v.s5.c987bca318d7 from=translated src=- shape=1e5b814e vocab=a4fcbb85
-/
theorem sum_range_mod (p c : ℕ) :
    ∑ k ∈ range (p * c), (k % p) = c * ∑ d ∈ range p, d := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    have hblk : ∑ x ∈ range p, ((p * n + x) % p) = ∑ d ∈ range p, d :=
      Finset.sum_congr rfl (fun x hx => by
        rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.mp hx)])
    rw [hblk, add_one_mul]

end Stickelberger
