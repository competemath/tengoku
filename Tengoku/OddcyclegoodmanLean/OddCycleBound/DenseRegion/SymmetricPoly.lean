import Tengoku.Seed.Data.Nat.Choose.Sum
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace OddCycleBound.DenseRegion

def hsym : List ℝ → ℕ → ℝ
  | [], 0 => 1
  | [], (_ + 1) => 0
  | (x :: xs), d => ∑ j ∈ Finset.range (d + 1), x ^ j * hsym xs (d - j)

/--
@isnad1 id=eq.0h3v.s6.20437b9db65e from=translated src=- shape=ce0ab58b vocab=28aeddfa
-/
lemma hsym_cons (x : ℝ) (xs : List ℝ) (d : ℕ) :
    hsym (x :: xs) d = ∑ j ∈ Finset.range (d + 1), x ^ j * hsym xs (d - j) := rfl

/--
@isnad1 id=eq.0h1v.s5.977ab61a199f from=translated src=- shape=c379ec76 vocab=bfd789b7
-/
@[simp] lemma hsym_nil (d : ℕ) : hsym [] d = if d = 0 then 1 else 0 := by
  cases d <;> rfl

/--
@isnad1 id=eq.0h3v.s6.27b3fab0d6b5 from=translated src=- shape=969340aa vocab=3fae4fcb
-/
lemma hsym_append (ys : List ℝ) : ∀ (xs : List ℝ) (d : ℕ),
    hsym (xs ++ ys) d = ∑ j ∈ Finset.range (d + 1), hsym xs j * hsym ys (d - j)
  | [], d => by
      simp only [List.nil_append]
      rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.2 (Nat.succ_pos d))]
      · simp
      · intro j _ hj
        rw [hsym_nil, ite_eq_right hj, zero_mul]
  | (x :: xs), d => by
      rw [List.cons_append, hsym_cons]
      simp_rw [hsym_append ys xs, Finset.mul_sum]
      simp_rw [hsym_cons, Finset.sum_mul]
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (fun p => ⟨p.1 + p.2, p.1⟩) (fun p => ⟨p.2, p.1 - p.2⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
        omega
      · rintro ⟨J, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
        omega
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        show (⟨j, j + i - j⟩ : Σ _ : ℕ, ℕ) = ⟨j, i⟩
        rw [show j + i - j = i from by omega]
      · rintro ⟨J, j⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        show (⟨j + (J - j), j⟩ : Σ _ : ℕ, ℕ) = ⟨J, j⟩
        rw [show j + (J - j) = J from by omega]
      · rintro ⟨j, i⟩ hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        rw [show j + i - j = i from by omega, show d - j - i = d - (j + i) from by omega]
        ring

/--
@isnad1 id=eq.0h2v.s6.53718e09c8de from=translated src=- shape=653aa462 vocab=7a05e5cf
-/
lemma sum_choose_hockey (k : ℕ) : ∀ d,
    ∑ i ∈ Finset.range (d + 1), Nat.choose (i + k) k = Nat.choose (d + k + 1) (k + 1)
  | 0 => by simp
  | (d + 1) => by
      rw [Finset.sum_range_succ, sum_choose_hockey k d]
      rw [show d + 1 + k + 1 = (d + k + 1) + 1 from by omega,
        Nat.choose_succ_succ (d + k + 1) k, show d + 1 + k = d + k + 1 from by omega]
      ring

/--
@isnad1 id=eq.0h3v.s5.dacef10c5d5f from=translated src=- shape=d0322318 vocab=6a0aedbf
-/
lemma hsym_replicate (a : ℝ) : ∀ (k d : ℕ),
    hsym (List.replicate (k + 1) a) d = (Nat.choose (d + k) k : ℝ) * a ^ d
  | 0, d => by
      rw [Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, one_mul]
      show hsym [a] d = a ^ d
      rw [hsym_cons, Finset.sum_eq_single_of_mem d (Finset.self_mem_range_succ d)]
      · simp
      · intro j hj hjd
        rw [Finset.mem_range] at hj
        rw [hsym_nil, ite_eq_right (by omega), mul_zero]
  | (k + 1), d => by
      show hsym (a :: List.replicate (k + 1) a) d = _
      rw [hsym_cons]
      simp_rw [hsym_replicate a k]
      have hterm : ∀ j ∈ Finset.range (d + 1),
          a ^ j * ((Nat.choose (d - j + k) k : ℝ) * a ^ (d - j))
            = (Nat.choose (d - j + k) k : ℝ) * a ^ d := by
        intro j hj
        rw [Finset.mem_range] at hj
        have hpow : a ^ j * a ^ (d - j) = a ^ d := by
          rw [← pow_add, show j + (d - j) = d from by omega]
        rw [← hpow]; ring
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
      have hcast : ∑ j ∈ Finset.range (d + 1), (Nat.choose (d - j + k) k : ℝ)
          = (Nat.choose (d + (k + 1)) (k + 1) : ℝ) := by
        have hreindex : ∑ j ∈ Finset.range (d + 1), Nat.choose (d - j + k) k
            = ∑ i ∈ Finset.range (d + 1), Nat.choose (i + k) k :=
          Finset.sum_nbij' (fun j => d - j) (fun i => d - i)
            (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
            (by intro i hi; simp only [Finset.mem_range] at hi ⊢; omega)
            (by intro j hj; simp only [Finset.mem_range] at hj; omega)
            (by intro i hi; simp only [Finset.mem_range] at hi; omega)
            (by intro j _; rfl)
        rw [← Nat.cast_sum, hreindex, sum_choose_hockey k d,
          show d + (k + 1) = d + k + 1 from by omega]
      rw [hcast]

/--
@isnad1 id=eq.0h4v.s6.509963131acb from=translated src=- shape=03a045fb vocab=2910dd5c
-/
lemma hsym_replicate_append (a : ℝ) (ys : List ℝ) (k d : ℕ) :
    hsym (List.replicate (k + 1) a ++ ys) d
      = ∑ j ∈ Finset.range (d + 1),
          (Nat.choose (d - j + k) k : ℝ) * a ^ (d - j) * hsym ys j := by
  rw [hsym_append]
  refine Finset.sum_nbij' (fun j => d - j) (fun j => d - j)
    (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj ⊢; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj; omega)
    (by intro j hj; simp only [Finset.mem_range] at hj; omega)
    ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [hsym_replicate a k, show d - (d - j) = j from by omega]

/--
@isnad1 id=eq.0h2v.s4.63785fbeca5e from=translated src=- shape=a7ed394e vocab=942640ce
-/
@[simp] lemma hsym_singleton (a : ℝ) (d : ℕ) : hsym [a] d = a ^ d := by
  simpa using hsym_replicate a 0 d

/--
@isnad1 id=eq.0h2v.s5.bbfc17674dcb from=translated src=- shape=4eaf76e3 vocab=23eecd02
-/
lemma hsym_map_neg : ∀ (xs : List ℝ) (d : ℕ),
    hsym (xs.map (fun x => -x)) d = (-1 : ℝ) ^ d * hsym xs d
  | [], d => by cases d <;> simp
  | (x :: xs), d => by
      rw [List.map_cons, hsym_cons, hsym_cons, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      rw [hsym_map_neg xs (d - j), neg_pow,
        show (-1 : ℝ) ^ d = (-1) ^ j * (-1) ^ (d - j) from by
          rw [← pow_add, show j + (d - j) = d from by omega]]
      ring

/--
@isnad1 id=eq.0h5v.s7.c6f0b5d41430 from=translated src=- shape=822f2a03 vocab=2910dd5c
-/
lemma hsym_replicate_append_replicate (a ℓ : ℝ) (s k d : ℕ) :
    hsym (List.replicate (k + 1) a ++ List.replicate (s + 1) ℓ) d
      = ∑ j ∈ Finset.range (d + 1),
          (Nat.choose (d - j + k) k : ℝ) * a ^ (d - j) * ((Nat.choose (j + s) s : ℝ) * ℓ ^ j) := by
  rw [hsym_replicate_append]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym_replicate]

noncomputable def diagKernel (m r : ℕ) (q ℓ : ℝ) : ℝ :=
  (m / r : ℝ)
      * (hsym (List.replicate r (1 - q) ++ List.replicate r (-ℓ)) (m - 2 * r)
        + hsym (List.replicate r q ++ List.replicate r ℓ) (m - 2 * r))
    - hsym (List.replicate (r + 1) q ++ List.replicate r ℓ) (m - 2 * r - 1)

noncomputable def multiKernel (m r : ℕ) (q : ℝ) (L : List ℝ) : ℝ :=
  (m / r : ℝ)
      * (hsym (List.replicate r (1 - q) ++ L.map (fun x => -x)) (m - 2 * r)
        + hsym (List.replicate r q ++ L) (m - 2 * r))
    - hsym (List.replicate (r + 1) q ++ L) (m - 2 * r - 1)

/--
@isnad1 id=eq.0h4v.s4.2b31662417ca from=translated src=- shape=1185161c vocab=402b8e42
-/
lemma diagKernel_eq_multiKernel (m r : ℕ) (q ℓ : ℝ) :
    diagKernel m r q ℓ = multiKernel m r q (List.replicate r ℓ) := by
  unfold diagKernel multiKernel
  rw [List.map_replicate]

/--
@isnad1 id=eq.1h3v.s6.248cdb5371e3 from=translated src=- shape=3908b99f vocab=34bf9662
-/
lemma hsym_replicate' (a : ℝ) {r : ℕ} (hr : r ≠ 0) (d : ℕ) :
    hsym (List.replicate r a) d = (Nat.choose (d + (r - 1)) (r - 1) : ℝ) * a ^ d := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  simpa using hsym_replicate a s d

/--
@isnad1 id=eq.1h4v.s7.4d5dd34ec856 from=translated src=- shape=a90a2ca7 vocab=2910dd5c
-/
lemma hsym_replicate_append' (a : ℝ) {r : ℕ} (hr : r ≠ 0) (ys : List ℝ) (d : ℕ) :
    hsym (List.replicate r a ++ ys) d
      = ∑ j ∈ Finset.range (d + 1),
          (Nat.choose (d - j + (r - 1)) (r - 1) : ℝ) * a ^ (d - j) * hsym ys j := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  simpa using hsym_replicate_append a ys s d

noncomputable def kerB (m r : ℕ) (q : ℝ) (j : ℕ) : ℝ :=
  (m / r : ℝ)
      * ((Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) * (1 - q) ^ (m - 2 * r - j) * (-1) ^ j
        + (Nat.choose (m - 2 * r - j + (r - 1)) (r - 1) : ℝ) * q ^ (m - 2 * r - j))
    - (if j < m - 2 * r then
        (Nat.choose (m - 2 * r - 1 - j + r) r : ℝ) * q ^ (m - 2 * r - 1 - j) else 0)

/--
@isnad1 id=eq.2h4v.s6.5050834abc11 from=translated src=- shape=ed086f55 vocab=1c88cd65
-/
lemma multiKernel_expand {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q : ℝ) (L : List ℝ) :
    multiKernel m r q L
      = ∑ j ∈ Finset.range (m - 2 * r + 1), kerB m r q j * hsym L j := by
  set n := m - 2 * r with hndef
  unfold multiKernel
  rw [← hndef, hsym_replicate_append' (1 - q) hr, hsym_replicate_append' q hr,
    hsym_replicate_append' q (by omega : r + 1 ≠ 0)]
  simp_rw [hsym_map_neg L, show (r + 1) - 1 = r from rfl]

  have hT3 : ∑ j ∈ Finset.range (n - 1 + 1),
        (Nat.choose (n - 1 - j + r) r : ℝ) * q ^ (n - 1 - j) * hsym L j
      = ∑ j ∈ Finset.range (n + 1),
        (if j < n then (Nat.choose (n - 1 - j + r) r : ℝ) * q ^ (n - 1 - j) else 0) * hsym L j := by
    rw [show n - 1 + 1 = n from by omega, Finset.sum_range_succ, ite_eq_right (lt_irrefl n), zero_mul,
      add_zero]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [ite_eq_left hj]
  rw [hT3, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [kerB, ← hndef]
  ring

/--
@isnad1 id=eq.2h4v.s7.cbcd078ef377 from=translated src=- shape=1a0a7a84 vocab=a7097321
-/
lemma diagKernel_expand {m r : ℕ} (hr : r ≠ 0) (hn : 1 ≤ m - 2 * r) (q ℓ : ℝ) :
    diagKernel m r q ℓ
      = ∑ j ∈ Finset.range (m - 2 * r + 1),
          kerB m r q j * ((Nat.choose (j + (r - 1)) (r - 1) : ℝ) * ℓ ^ j) := by
  rw [diagKernel_eq_multiKernel, multiKernel_expand hr hn]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym_replicate' ℓ hr]

end OddCycleBound.DenseRegion
