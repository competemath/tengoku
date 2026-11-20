import Tengoku.Cliffordchain.Clifford.General

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A counterexample to `CliffordChain 6`

See `GENERAL_REPORT.md`. For the six centres `cx` below (exact Gaussian integers) `GenPosN cx`
holds, every level-4 point is forced to be the classical Miquel point, the six level-5 objects
are forced to be lines (five distinct collinear Miquel points each), and three of these lines
are not concurrent, so no level-6 point exists.
-/

namespace Clifford

open Complex ComplexConjugate

namespace Counter6

/-- Six centres in general position (`GenPosN`) without a level-6 Clifford object.-/
def cx : Fin 6 → ℂ := ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩]

/--
@isnad1 id=transver.1h2v.s4.bee18bf18c1c from=translated src=- shape=44491685 vocab=efd56231
-/
theorem cx_transversal (i j : Fin 6) (h : i ≠ j) : Transversal (cx i) (cx j) := by
  fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl h
    | (intro h; have := congrArg Complex.im h; simp [cx] at this; norm_num at this)

/--
@isnad1 id=gentripl.2h3v.s5.17ed7415700d from=translated src=- shape=97f24203 vocab=fe373299
-/
theorem cx_genTriple (i j k : Fin 6) (h1 : i < j) (h2 : j < k) :
    GenTriple (cx i) (cx j) (cx k) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at h1 h2 <;>
    refine ⟨fun h => ?_, fun h => ?_⟩ <;> have := congrArg Complex.im h <;>
    simp [cx, triP, cycP, det3] at this <;> norm_num at this

/--
@isnad1 id=genposn.0h0v.s2.5f90bb983c66 from=translated src=- shape=cef8a6bf vocab=f04d2692
-/
theorem cx_genPosN : GenPosN cx := ⟨cx_transversal, cx_genTriple⟩

/--
@isnad1 id=eq.0h0v.s5.1b81a8df06bf from=translated src=- shape=fe54bc82 vocab=2fac82b3
-/
theorem s01 : second ⟨3, -6⟩ ⟨6, -3⟩ = ⟨9, -9⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.84f0c34c7a2c from=translated src=- shape=ba51fdf6 vocab=97d68fa4
-/
theorem s02 : second ⟨3, -6⟩ ⟨1, 2⟩ = ⟨48/17, 12/17⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.e0bc0d5978b4 from=translated src=- shape=aa625add vocab=2fac82b3
-/
theorem s03 : second ⟨3, -6⟩ ⟨-2, -1⟩ = ⟨-3, -3⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.1ce659237379 from=translated src=- shape=4ac7534e vocab=97d68fa4
-/
theorem s04 : second ⟨3, -6⟩ ⟨0, -4⟩ = ⟨-48/13, -72/13⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.984f120d11ba from=translated src=- shape=24bbced0 vocab=97d68fa4
-/
theorem s05 : second ⟨3, -6⟩ ⟨4, 0⟩ = ⟨288/37, -48/37⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s5.169bbbbcac93 from=translated src=- shape=52a5da92 vocab=2fac82b3
-/
theorem s12 : second ⟨6, -3⟩ ⟨1, 2⟩ = ⟨3, 3⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.55221b4c1d95 from=translated src=- shape=ad364f57 vocab=97d68fa4
-/
theorem s13 : second ⟨6, -3⟩ ⟨-2, -1⟩ = ⟨-12/17, -48/17⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.a29167f4d78d from=translated src=- shape=f3f26bf6 vocab=97d68fa4
-/
theorem s14 : second ⟨6, -3⟩ ⟨0, -4⟩ = ⟨48/37, -288/37⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.d736a8f801aa from=translated src=- shape=ba51fdf6 vocab=97d68fa4
-/
theorem s15 : second ⟨6, -3⟩ ⟨4, 0⟩ = ⟨72/13, 48/13⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s5.fe3074fb12d0 from=translated src=- shape=f44edf62 vocab=2fac82b3
-/
theorem s23 : second ⟨1, 2⟩ ⟨-2, -1⟩ = ⟨-1, 1⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.a14e517a5c17 from=translated src=- shape=95f6d4b5 vocab=97d68fa4
-/
theorem s24 : second ⟨1, 2⟩ ⟨0, -4⟩ = ⟨48/37, -8/37⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.461e36492bb7 from=translated src=- shape=e4bec74f vocab=b01ac763
-/
theorem s25 : second ⟨1, 2⟩ ⟨4, 0⟩ = ⟨32/13, 48/13⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.df8384e462ba from=translated src=- shape=440651f3 vocab=97d68fa4
-/
theorem s34 : second ⟨-2, -1⟩ ⟨0, -4⟩ = ⟨-48/13, -32/13⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s6.e2c3257435c5 from=translated src=- shape=e27a0e0d vocab=97d68fa4
-/
theorem s35 : second ⟨-2, -1⟩ ⟨4, 0⟩ = ⟨8/37, -48/37⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.0h0v.s5.180a1e03d3aa from=translated src=- shape=b6022e87 vocab=2fac82b3
-/
theorem s45 : second ⟨0, -4⟩ ⟨4, 0⟩ = ⟨4, -4⟩ := by
  apply second_eq
  · intro h; have h1 := congrArg Complex.re h; norm_num at h1
  · apply Complex.ext <;> norm_num

/--
@isnad1 id=eq.1h1v.s7.9ae6e44f7895 from=translated src=- shape=4b96a38f vocab=0df94b20
-/
theorem q0134 {q : ℂ} (h : Chain 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) : q = ⟨-6, -4⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s01, s03, s04, s13, s14, s34] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (8177/768000) * h1 + (-507/6400) * h2 + (-481/288000) * h3
  · linear_combination (-8177/1152000) * h1 + (1183/28800) * h2 + (-481/432000) * h3

/--
@isnad1 id=eq.1h1v.s7.0c644037e015 from=translated src=- shape=a5031a3b vocab=0df94b20
-/
theorem q0135 {q : ℂ} (h : Chain 4 ![⟨3, -6⟩, ⟨6, -3⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) : q = ⟨4, -24⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s01, s03, s05, s13, s15, s35] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-8177/1152000) * h1 + (1369/1411200) * h2 + (481/432000) * h3
  · linear_combination (-8177/192000) * h1 + (1369/78400) * h2 + (-481/72000) * h3

/--
@isnad1 id=eq.1h1v.s7.6d3866bb424a from=translated src=- shape=545f8d4a vocab=3eadcca3
-/
theorem q0234 {q : ℂ} (h : Chain 4 ![⟨3, -6⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) : q = ⟨-8/3, -4⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s02, s03, s04, s23, s24, s34] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (481/72000) * h1 + (-1859/43200) * h2 + (8177/1728000) * h3
  · linear_combination (481/48000) * h1 + (-1183/28800) * h2 + (-8177/1152000) * h3

/--
@isnad1 id=eq.1h1v.s7.0785f70d742d from=translated src=- shape=68991853 vocab=3eadcca3
-/
theorem q0235 {q : ℂ} (h : Chain 4 ![⟨3, -6⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) : q = ⟨4, -2/3⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s02, s03, s05, s23, s25, s35] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-481/48000) * h1 + (-1369/1411200) * h2 + (-8177/1152000) * h3
  · linear_combination (481/288000) * h1 + (23273/8467200) * h2 + (-8177/6912000) * h3

/--
@isnad1 id=eq.1h1v.s7.41aebb02d948 from=translated src=- shape=9fde434f vocab=3eadcca3
-/
theorem q1234 {q : ℂ} (h : Chain 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩] {q}) : q = ⟨2/3, -4⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s12, s13, s14, s23, s24, s34] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-481/288000) * h1 + (-8177/6912000) * h2 + (23273/8467200) * h3
  · linear_combination (481/48000) * h1 + (-8177/1152000) * h2 + (-1369/1411200) * h3

/--
@isnad1 id=eq.1h1v.s7.6a51c682e569 from=translated src=- shape=8a1db714 vocab=3eadcca3
-/
theorem q1235 {q : ℂ} (h : Chain 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨4, 0⟩] {q}) : q = ⟨4, 8/3⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s12, s13, s15, s23, s25, s35] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-481/48000) * h1 + (-8177/1152000) * h2 + (-1183/28800) * h3
  · linear_combination (-481/72000) * h1 + (8177/1728000) * h2 + (-1859/43200) * h3

/--
@isnad1 id=eq.1h1v.s7.9c64fe964a68 from=translated src=- shape=b3fbdbcc vocab=3eadcca3
-/
theorem q1245 {q : ℂ} (h : Chain 4 ![⟨6, -3⟩, ⟨1, 2⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) : q = ⟨16/3, 16/3⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s12, s14, s15, s24, s25, s45] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (481/480000) * h1 + (-3367/1440000) * h2 + (-169/18000) * h3
  · linear_combination (-481/60000) * h1 + (-481/360000) * h2 + (-1183/18000) * h3

/--
@isnad1 id=eq.1h1v.s7.accd1202c4e7 from=translated src=- shape=f5b200ac vocab=3eadcca3
-/
theorem q1345 {q : ℂ} (h : Chain 4 ![⟨6, -3⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) : q = ⟨-8/3, -32/3⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s13, s14, s15, s34, s35, s45] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-481/96000) * h1 + (481/288000) * h2 + (-8177/576000) * h3
  · linear_combination (-3367/384000) * h1 + (6253/1152000) * h2 + (-8177/576000) * h3

/--
@isnad1 id=eq.1h1v.s7.ac46ea705858 from=translated src=- shape=e900765b vocab=3eadcca3
-/
theorem q2345 {q : ℂ} (h : Chain 4 ![⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] {q}) : q = ⟨16/9, -16/9⟩ := by
  obtain ⟨h1, h2, h3, -⟩ := chain4_cD h
  simp only [s23, s24, s25, s34, s35, s45] at h1 h2 h3
  simp only [cD, det4, det3] at h1 h2 h3
  apply Complex.ext
  · linear_combination (-481/864000) * h1 + (6253/864000) * h2 + (-481/54000) * h3
  · linear_combination (-481/108000) * h1 + (-481/216000) * h2 + (481/54000) * h3

/--
@isnad1 id=not.0h1v.s3.0fbd50350fc1 from=translated src=- shape=577ba648 vocab=099c4135
-/
theorem not_chain6 {X : Set ℂ} : ¬ Chain 6 cx X := by
  intro h
  obtain ⟨p, -, h⟩ := (h : ∃ p, X = {p} ∧ ∀ i : Fin 6, ∃ Y, Chain 5 (cx ∘ i.succAbove) Y ∧ p ∈ Y)
  have e4 : cx ∘ Fin.succAbove 4 = ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨4, 0⟩] := by funext k; fin_cases k <;> rfl
  obtain ⟨Y4, hY4, p4⟩ := h 4
  rw [e4] at hY4
  obtain ⟨g4, a4, b4, c4⟩ := chain5_mem hY4
  obtain ⟨r4a, hr4a, m4a⟩ := a4
  rw [q1235 hr4a] at m4a
  obtain ⟨r4b, hr4b, m4b⟩ := b4
  rw [q0235 hr4b] at m4b
  obtain ⟨r4c, hr4c, m4c⟩ := c4
  rw [q0135 hr4c] at m4c
  have l4 := cD_eq_zero g4 m4a m4b m4c p4
  simp only [cD, det4, det3] at l4
  have e5 : cx ∘ Fin.succAbove 5 = ![⟨3, -6⟩, ⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩] := by funext k; fin_cases k <;> rfl
  obtain ⟨Y5, hY5, p5⟩ := h 5
  rw [e5] at hY5
  obtain ⟨g5, a5, b5, c5⟩ := chain5_mem hY5
  obtain ⟨r5a, hr5a, m5a⟩ := a5
  rw [q1234 hr5a] at m5a
  obtain ⟨r5b, hr5b, m5b⟩ := b5
  rw [q0234 hr5b] at m5b
  obtain ⟨r5c, hr5c, m5c⟩ := c5
  rw [q0134 hr5c] at m5c
  have l5 := cD_eq_zero g5 m5a m5b m5c p5
  simp only [cD, det4, det3] at l5
  have e0 : cx ∘ Fin.succAbove 0 = ![⟨6, -3⟩, ⟨1, 2⟩, ⟨-2, -1⟩, ⟨0, -4⟩, ⟨4, 0⟩] := by funext k; fin_cases k <;> rfl
  obtain ⟨Y0, hY0, p0⟩ := h 0
  rw [e0] at hY0
  obtain ⟨g0, a0, b0, c0⟩ := chain5_mem hY0
  obtain ⟨r0a, hr0a, m0a⟩ := a0
  rw [q2345 hr0a] at m0a
  obtain ⟨r0b, hr0b, m0b⟩ := b0
  rw [q1345 hr0b] at m0b
  obtain ⟨r0c, hr0c, m0c⟩ := c0
  rw [q1245 hr0c] at m0c
  have l0 := cD_eq_zero g0 m0a m0b m0c p0
  simp only [cD, det4, det3] at l0
  have : (1 : ℝ) = 0 := by
    linear_combination (-81/560000) * l4 + (-81/40000) * l5 + (243/1024000) * l0
  norm_num at this

/-- **`CliffordChain 6` is false**: the centres `cx` are in general position (`GenPosN`) but have
no level-6 Clifford object.
@isnad1 id=not.0h0v.s2.b0b82a0ed4f8 from=translated src=- shape=8d7dbbf6 vocab=5675b229
-/
theorem not_cliffordChain_six : ¬ CliffordChain 6 := fun H =>
  let ⟨_, hX⟩ := H cx cx_genPosN
  not_chain6 hX

end Counter6

end Clifford
