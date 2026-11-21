import Tengoku.EocLeanVerification.EOC.CompositionCounting
import Tengoku.Seed.Data.List.Rotate

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace EOC

namespace FiniteValuationWord

/-- Turn a list with certified length `N` into a finite word.-/
def ofList (l : List ℕ) (hl : l.length = N) : FiniteValuationWord N :=
  fun i ↦ l.get ⟨i, by omega⟩

/--
@isnad1 id=eq.1h2v.s4.ba90fd28e2b3 from=translated src=- shape=8cd236cc vocab=141ea6cf
-/
@[simp] theorem ofFn_ofList (l : List ℕ) (hl : l.length = N) :
    List.ofFn (ofList l hl) = l := by
  subst N
  exact List.ofFn_get l

/-- Cyclic left rotation of a finite word.-/
def rotate (w : FiniteValuationWord N) (r : ℕ) : FiniteValuationWord N :=
  ofList ((List.ofFn w).rotate r) (by simp)

/--
@isnad1 id=eq.0h3v.s4.a99c59b8ac8a from=translated src=- shape=5211be90 vocab=4ffaa1a6
-/
@[simp] theorem ofFn_rotate (w : FiniteValuationWord N) (r : ℕ) :
    List.ofFn (w.rotate r) = (List.ofFn w).rotate r := by
  simp [rotate]

/--
@isnad1 id=eq.0h2v.s4.ee88252f4f6d from=translated src=- shape=5bdfd7f1 vocab=7ef671e0
-/
@[simp] theorem rotate_zero (w : FiniteValuationWord N) : w.rotate 0 = w := by
  apply_fun List.ofFn using List.ofFn_injective
  simp

/--
@isnad1 id=injectiv.0h2v.s4.db526ea3521c from=translated src=- shape=3b54d3f4 vocab=c4d342da
-/
theorem rotate_injective (r : ℕ) :
    Function.Injective (fun w : FiniteValuationWord N ↦ w.rotate r) := by
  intro w v h
  have h' := congrArg List.ofFn h
  simp only [ofFn_rotate] at h'
  exact List.ofFn_injective (List.rotate_injective r h')

/--
@isnad1 id=iff.0h3v.s4.9e5a8000704f from=translated src=- shape=91943eac vocab=c4afb8a1
-/
@[simp] theorem rotate_positive (w : FiniteValuationWord N) (r : ℕ) :
    (w.rotate r).Positive ↔ w.Positive := by
  constructor <;> intro h
  · intro i
    have hm : w i ∈ List.ofFn w := by simp
    have hm' : w i ∈ List.ofFn (w.rotate r) := by
      rw [ofFn_rotate, List.mem_rotate]
      exact hm
    simp only [List.mem_ofFn] at hm'
    obtain ⟨k, hk⟩ := hm'
    rw [← hk]
    exact h k
  · intro i
    have hm : (w.rotate r) i ∈ List.ofFn (w.rotate r) := List.mem_ofFn.mpr ⟨i, rfl⟩
    rw [ofFn_rotate, List.mem_rotate] at hm
    simp only [List.mem_ofFn] at hm
    obtain ⟨k, hk⟩ := hm
    rw [← hk]
    exact h k

/--
@isnad1 id=eq.0h3v.s4.61ccaa7048da from=translated src=- shape=0d268503 vocab=7140a45c
-/
@[simp] theorem rotate_total (w : FiniteValuationWord N) (r : ℕ) :
    (w.rotate r).total = w.total := by
  simp only [total, prefixSum, ofFn_rotate]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  exact (List.rotate_perm _ r).sum_eq

end FiniteValuationWord

namespace ValuationShell

/-- Rotation stays inside a fixed-sum shell.-/
def rotate {s : ℕ} (q : ValuationShell N s) (r : ℕ) : ValuationShell N s :=
  ⟨{ blocks := q.1.blocks.rotate r
     blocks_pos := by
       intro i hi
       exact q.1.blocks_pos (List.mem_rotate.mp hi)
     blocks_sum := by
       exact (List.rotate_perm q.1.blocks r).sum_eq.trans q.1.blocks_sum }, by
    show (q.1.blocks.rotate r).length = N
    rw [List.length_rotate]
    exact q.2⟩

/--
@isnad1 id=eq.0h4v.s4.b696a8e714ed from=translated src=- shape=66e81d03 vocab=9a905e61
-/
@[simp] theorem rotate_toWord {s : ℕ} (q : ValuationShell N s) (r : ℕ) :
    (q.rotate r).toWord = q.toWord.rotate r := by
  apply_fun List.ofFn using List.ofFn_injective
  simp [ValuationShell.ofFn_toWord, FiniteValuationWord.ofFn_rotate, rotate]

/--
@isnad1 id=injectiv.0h3v.s4.f0adea0c291a from=translated src=- shape=b27cfcf0 vocab=b90d5de1
-/
theorem rotate_injective {s : ℕ} (r : ℕ) :
    Function.Injective (fun q : ValuationShell N s ↦ q.rotate r) := by
  intro q t h
  apply Subtype.ext
  apply Composition.ext
  have hblocks := congrArg (fun z : ValuationShell N s ↦ z.1.blocks) h
  exact List.rotate_injective r hblocks

end ValuationShell

namespace ChordRotation

private def intPrefix (l : List ℤ) (j : ℕ) : ℤ := (l.take j).sum

/-- Zero-sum cyclic-list lemma underlying the chord rotation argument.  A maximizing prefix is
chosen from all proper prefixes; no uniqueness is required.-/
private theorem exists_rotate_int_prefix_nonpos (l : List ℤ) (hl : 0 < l.length)
    (hsum : l.sum = 0) :
    ∃ r < l.length, ∀ j ≤ l.length, intPrefix (l.rotate r) j ≤ 0 := by
  let indices := List.range l.length
  have hindices : indices ≠ [] := by simp [indices, hl.ne']
  let p : ℕ → ℤ := fun j ↦ intPrefix l j
  let r : ℕ := indices.maxOn p hindices
  have hrmem : r ∈ indices := by
    exact List.maxOn_mem (f := p) (h := hindices)
  have hr : r < l.length := by simpa [indices] using hrmem
  have hmax : ∀ {k : ℕ}, k < l.length → p k ≤ p r := by
    intro k hk
    exact List.le_apply_maxOn_of_mem (f := p) (by simp [indices, hk])
  have hpzero : 0 ≤ p r := by
    have := hmax (k := 0) hl
    simpa [p, intPrefix] using this
  refine ⟨r, hr, ?_⟩
  intro j hj
  rw [List.rotate_eq_drop_append_take hr.le]
  let u := l.take r
  let v := l.drop r
  have huv : u ++ v = l := by simpa [u, v] using List.take_append_drop r l
  have huvsum : u.sum + v.sum = 0 := by
    rw [← List.sum_append, huv, hsum]
  have hvlen : v.length = l.length - r := by simp [v]
  show ((v ++ u).take j).sum ≤ 0
  by_cases hjv : j ≤ v.length
  · rw [List.take_append_of_le_length hjv]
    have hadd : p (r + j) = p r + (v.take j).sum := by
      simp [p, intPrefix, v, List.take_add, List.sum_append]
    have hbound : p (r + j) ≤ p r := by
      rcases lt_or_eq_of_le (by omega : r + j ≤ l.length) with hlt | heq
      · exact hmax hlt
      · rw [heq]
        have : p l.length = 0 := by simp [p, intPrefix, hsum]
        linarith
    linarith
  · rw [List.take_append]
    have hvj : v.length ≤ j := by omega
    rw [List.take_of_length_le hvj, List.sum_append]
    let k := j - v.length
    have hk : k ≤ r := by simp [k, hvlen]; omega
    have hklt : k < l.length := lt_of_le_of_lt hk hr
    have htake : (u.take k).sum = p k := by
      simp [u, p, intPrefix, List.take_take, Nat.min_eq_left hk]
    have hbound : p k ≤ p r := hmax hklt
    have hu : u.sum = p r := by simp [u, p, intPrefix]
    rw [show j - v.length = k from rfl, htake]
    linarith

/-- Zero-sum cyclic-list lemma: some rotation of a nonempty integer list with sum `0` has every
prefix sum `≤ 0`.  Public form of the internal helper above, with `intPrefix` unfolded.
@isnad1 id=ex.2h1v.s6.c6990bdd5589 from=translated src=- shape=5a075c7c vocab=d10ad332
-/
theorem exists_rotate_take_sum_nonpos (l : List ℤ) (hl : 0 < l.length) (hsum : l.sum = 0) :
    ∃ r < l.length, ∀ j ≤ l.length, ((l.rotate r).take j).sum ≤ 0 :=
  exists_rotate_int_prefix_nonpos l hl hsum

private theorem sum_centered (l : List ℕ) (N s : ℕ) :
    (l.map (fun d ↦ (N : ℤ) * (d : ℤ) - (s : ℤ))).sum =
      (N : ℤ) * (l.sum : ℤ) - (l.length : ℤ) * (s : ℤ) := by
  induction l with
  | nil => simp
  | cons d l ih =>
      simp [List.sum_cons] at ih ⊢
      linarith

/-- Rotation-below-the-chord lemma, division-free form.  There is a cyclic rotation lying below
the chord joining `(0,0)` to `(N,s)`.
@isnad1 id=ex.2h3v.s6.c59d82a825c0 from=translated src=- shape=92079b41 vocab=13f6fa17
-/
theorem chord_rotation_nat (hN : 0 < N) (w : FiniteValuationWord N) (s : ℕ)
    (htotal : w.total = s) :
    ∃ r < N, ∀ j ≤ N, N * (w.rotate r).prefixSum j ≤ j * s := by
  let l : List ℕ := List.ofFn w
  let x : List ℤ := l.map (fun d ↦ (N : ℤ) * (d : ℤ) - (s : ℤ))
  have hllen : l.length = N := by simp [l]
  have hxlen : x.length = N := by simp [x, hllen]
  have hlsum : l.sum = s := by
    simpa [l, FiniteValuationWord.total_eq_sum_univ, List.sum_ofFn] using htotal
  have hxsum : x.sum = 0 := by
    rw [sum_centered, hlsum, hllen]
    ring
  obtain ⟨r, hr, hgood⟩ := exists_rotate_int_prefix_nonpos x (by simpa [hxlen] using hN) hxsum
  refine ⟨r, by simpa [hxlen] using hr, ?_⟩
  intro j hj
  have hgj := hgood j (by simpa [hxlen] using hj)
  have hlen_take : ((l.rotate r).take j).length = j := by
    rw [List.length_take, List.length_rotate, hllen, Nat.min_eq_left hj]
  have hcenter :
      ((l.rotate r).take j |>.map
          (fun d ↦ (N : ℤ) * (d : ℤ) - (s : ℤ))).sum =
        (N : ℤ) * (((l.rotate r).take j).sum : ℤ) - (j : ℤ) * (s : ℤ) := by
    rw [sum_centered, hlen_take]
  have hgj' :
      (N : ℤ) * (((l.rotate r).take j).sum : ℤ) - (j : ℤ) * (s : ℤ) ≤ 0 := by
    rw [← hcenter]
    simpa [intPrefix, x, l, List.map_rotate, List.map_take, List.map_map,
      ← List.map_eq_flatMap] using hgj
  have hpref : (w.rotate r).prefixSum j = ((l.rotate r).take j).sum := by
    simp [FiniteValuationWord.prefixSum, l]
  rw [hpref]
  exact_mod_cast (show
    (N : ℤ) * (((l.rotate r).take j).sum : ℤ) ≤ (j : ℤ) * (s : ℤ) by linarith)

/-- Rotation-below-the-chord lemma, real-valued chord form.
@isnad1 id=ex.2h3v.s6.cb4ffc588fc4 from=translated src=- shape=df2bbe51 vocab=987a8b61
-/
theorem chord_rotation_real (hN : 0 < N) (w : FiniteValuationWord N) (s : ℕ)
    (htotal : w.total = s) :
    ∃ r < N, ∀ j ≤ N,
      ((w.rotate r).prefixSum j : ℝ) ≤ (j : ℝ) * (s : ℝ) / (N : ℝ) := by
  obtain ⟨r, hr, h⟩ := chord_rotation_nat hN w s htotal
  refine ⟨r, hr, ?_⟩
  intro j hj
  have h' : (N : ℝ) * ((w.rotate r).prefixSum j : ℝ) ≤
      (j : ℝ) * (s : ℝ) := by exact_mod_cast h j hj
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ hNr).mpr
  simpa [mul_comm] using h'

end ChordRotation

end EOC
