import Tengoku.ClosureResidueP3Lean.P3.Closure
import Tengoku.ClosureResidueP3Lean.P3.QuadraticReturn

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open scoped BigOperators

namespace P3

section Filtration

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The depth-`k` quadratic residue space from §5:
the complex span of all quadratic returns with total hidden depth `i + j ≤ k`.

This is defined independently of `hiddenFlow`; Corollary 6.2 is proved below.-/
def residue (φ : Dynamics V) (k : ℕ) : Submodule ℂ (DiagZero (V := V)) :=
  Submodule.span ℂ
    {r | ∃ i j : ℕ, i + j ≤ k ∧
      ∃ z w : OffDiag (V := V),
        z.1 ∈ hidden φ i ∧
        w.1 ∈ hidden φ j ∧
        quadraticReturn (V := V) z w = r}

/--
The depth-`k` hidden flow space from §6:
the complex span of all Hadamard flows with total hidden depth `i + j ≤ k`.-/
def hiddenFlow (φ : Dynamics V) (k : ℕ) : Submodule ℂ (EdgeSpace V) :=
  Submodule.span ℂ
    {f | ∃ i j : ℕ, i + j ≤ k ∧
      ∃ z w : OffDiag (V := V),
        z.1 ∈ hidden φ i ∧
        w.1 ∈ hidden φ j ∧
        hadamardFlow (V := V) z w = f}

/-- A single admissible quadratic return belongs to `R_k`.-/
theorem quadraticReturn_mem_residue
    (φ : Dynamics V) {k i j : ℕ}
    (hij : i + j ≤ k)
    (z w : OffDiag (V := V))
    (hz : z.1 ∈ hidden φ i)
    (hw : w.1 ∈ hidden φ j) :
    quadraticReturn (V := V) z w ∈ residue φ k := by
  apply Submodule.subset_span
  exact ⟨i, j, hij, z, w, hz, hw, rfl⟩

/-- A single admissible hidden Hadamard flow belongs to `F_k`.-/
theorem hadamardFlow_mem_hiddenFlow
    (φ : Dynamics V) {k i j : ℕ}
    (hij : i + j ≤ k)
    (z w : OffDiag (V := V))
    (hz : z.1 ∈ hidden φ i)
    (hw : w.1 ∈ hidden φ j) :
    hadamardFlow (V := V) z w ∈ hiddenFlow φ k := by
  apply Submodule.subset_span
  exact ⟨i, j, hij, z, w, hz, hw, rfl⟩

/-- D1: the quadratic residue filtration is monotone in depth.-/
theorem residue_mono (φ : Dynamics V) {k l : ℕ} (hkl : k ≤ l) :
    residue φ k ≤ residue φ l := by
  apply Submodule.span_mono
  intro r hr
  rcases hr with ⟨i, j, hij, z, w, hz, hw, rfl⟩
  exact ⟨i, j, hij.trans hkl, z, w, hz, hw, rfl⟩

/-- D1: the hidden flow filtration is monotone in depth.-/
theorem hiddenFlow_mono (φ : Dynamics V) {k l : ℕ} (hkl : k ≤ l) :
    hiddenFlow φ k ≤ hiddenFlow φ l := by
  apply Submodule.span_mono
  intro f hf
  rcases hf with ⟨i, j, hij, z, w, hz, hw, rfl⟩
  exact ⟨i, j, hij.trans hkl, z, w, hz, hw, rfl⟩

/-! ## D1: initial vanishing -/

/-- An off-diagonal vector belonging to `H₀` must be zero.-/
theorem offDiag_eq_zero_of_mem_hidden_zero
    (φ : Dynamics V) (z : OffDiag (V := V))
    (hz : z.1 ∈ hidden φ 0) :
    z = 0 := by
  rw [hidden_zero] at hz
  have hz0 : z.1 = 0 := by
    simpa using hz
  apply Subtype.ext
  exact hz0

@[simp]
theorem hadamardFlow_zero_left
    (w : OffDiag (V := V)) :
    hadamardFlow (V := V) (0 : OffDiag (V := V)) w = 0 := by
  simpa using
    hadamardFlow_smul_left (V := V) (0 : ℂ)
      (0 : OffDiag (V := V)) w

@[simp]
theorem hadamardFlow_zero_right
    (z : OffDiag (V := V)) :
    hadamardFlow (V := V) z (0 : OffDiag (V := V)) = 0 := by
  simpa using
    hadamardFlow_smul_right (V := V) (0 : ℂ)
      z (0 : OffDiag (V := V))

@[simp]
theorem quadraticReturn_zero_left
    (w : OffDiag (V := V)) :
    quadraticReturn (V := V) (0 : OffDiag (V := V)) w = 0 := by
  rw [quadraticReturn_eq_divergence]
  simp

@[simp]
theorem quadraticReturn_zero_right
    (z : OffDiag (V := V)) :
    quadraticReturn (V := V) z (0 : OffDiag (V := V)) = 0 := by
  rw [quadraticReturn_eq_divergence]
  simp

/-- D1: `R₀ = 0`.-/
@[simp]
theorem residue_zero (φ : Dynamics V) :
    residue φ 0 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hz0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ z hz
    subst z
    change quadraticReturn (V := V) (0 : OffDiag (V := V)) w = 0
    simp
  · exact bot_le

/-- D1: `F₀ = 0`.-/
@[simp]
theorem hiddenFlow_zero (φ : Dynamics V) :
    hiddenFlow φ 0 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    have hi : i = 0 := by omega
    have hj : j = 0 := by omega
    subst i
    subst j
    have hz0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ z hz
    subst z
    change hadamardFlow (V := V) (0 : OffDiag (V := V)) w = 0
    simp
  · exact bot_le

/-- D1: total depth one still forces one hidden factor to lie in `H₀`,
hence `R₁ = 0`.-/
@[simp]
theorem residue_one (φ : Dynamics V) :
    residue φ 1 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    have hzero : i = 0 ∨ j = 0 := by omega
    rcases hzero with hi | hj
    · subst i
      have hz0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ z hz
      subst z
      change quadraticReturn (V := V) (0 : OffDiag (V := V)) w = 0
      simp
    · subst j
      have hw0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ w hw
      subst w
      change quadraticReturn (V := V) z (0 : OffDiag (V := V)) = 0
      simp
  · exact bot_le

/-- D1: likewise `F₁ = 0`.-/
@[simp]
theorem hiddenFlow_one (φ : Dynamics V) :
    hiddenFlow φ 1 = ⊥ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro f hf
    rcases hf with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    have hzero : i = 0 ∨ j = 0 := by omega
    rcases hzero with hi | hj
    · subst i
      have hz0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ z hz
      subst z
      change hadamardFlow (V := V) (0 : OffDiag (V := V)) w = 0
      simp
    · subst j
      have hw0 := offDiag_eq_zero_of_mem_hidden_zero (V := V) φ w hw
      subst w
      change hadamardFlow (V := V) z (0 : OffDiag (V := V)) = 0
      simp
  · exact bot_le

/-! ## D3: primitive hidden defects -/

/-- The primitive hidden defect produced by the `m`-th iterate of a diagonal
observable.  It is packaged directly in the off-diagonal sector.-/
def primitiveDefect
    (φ : Dynamics V) (m : ℕ)
    (d : diagonalSubmodule (V := V)) :
    OffDiag (V := V) :=
  ⟨offProjection (V := V) ((φ ^ m) d.1),
    delta_offProjection_eq_zero (V := V) ((φ ^ m) d.1)⟩

@[simp]
theorem primitiveDefect_val
    (φ : Dynamics V) (m : ℕ)
    (d : diagonalSubmodule (V := V)) :
    (primitiveDefect (V := V) φ m d).1 =
      offProjection (V := V) ((φ ^ m) d.1) := by
  rfl

/-- The span of primitive defects up to depth `k`.-/
def primitiveHiddenSpan
    (φ : Dynamics V) (k : ℕ) :
    Submodule ℂ (A V) :=
  Submodule.span ℂ
    {z | ∃ d : diagonalSubmodule (V := V), ∃ m : ℕ,
      m ≤ k ∧ (primitiveDefect (V := V) φ m d).1 = z}

/-- Each primitive defect at depth `m ≤ k` belongs to `H_k`.-/
theorem primitiveDefect_mem_hidden
    (φ : Dynamics V) {m k : ℕ} (hmk : m ≤ k)
    (d : diagonalSubmodule (V := V)) :
    (primitiveDefect (V := V) φ m d).1 ∈ hidden φ k := by
  refine ⟨(φ ^ m) d.1, ?_, rfl⟩
  apply Submodule.subset_span
  exact ⟨d, m, hmk, rfl⟩

/-- D3: `H_k` is exactly the span of the primitive defects
`Q φ^m(d)` with `m ≤ k`.-/
theorem hidden_eq_span_primitive
    (φ : Dynamics V) (k : ℕ) :
    hidden φ k = primitiveHiddenSpan (V := V) φ k := by
  rw [hidden, closure, Submodule.map_span]
  unfold primitiveHiddenSpan
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨d, m, hmk, rfl⟩
    exact ⟨d, m, hmk, rfl⟩
  · rintro ⟨d, m, hmk, rfl⟩
    refine ⟨(φ ^ m) d.1, ?_, rfl⟩
    exact ⟨d, m, hmk, rfl⟩

/-! ## D4: primitive-pair description of the residue filtration -/

/-- Quadratic return is additive in its first hidden argument.-/
theorem quadraticReturn_add_left
    (z₁ z₂ w : OffDiag (V := V)) :
    quadraticReturn (V := V) (z₁ + z₂) w =
      quadraticReturn (V := V) z₁ w +
      quadraticReturn (V := V) z₂ w := by
  simp only [quadraticReturn_eq_divergence,
    hadamardFlow_add_left, LinearMap.map_add]

/-- Quadratic return is complex-linear in its first hidden argument.-/
theorem quadraticReturn_smul_left
    (c : ℂ) (z w : OffDiag (V := V)) :
    quadraticReturn (V := V) (c • z) w =
      c • quadraticReturn (V := V) z w := by
  simp only [quadraticReturn_eq_divergence,
    hadamardFlow_smul_left, LinearMap.map_smul]

/-- Quadratic return is additive in its second hidden argument.-/
theorem quadraticReturn_add_right
    (z w₁ w₂ : OffDiag (V := V)) :
    quadraticReturn (V := V) z (w₁ + w₂) =
      quadraticReturn (V := V) z w₁ +
      quadraticReturn (V := V) z w₂ := by
  simp only [quadraticReturn_eq_divergence,
    hadamardFlow_add_right, LinearMap.map_add]

/-- Quadratic return is conjugate-linear in its second hidden argument.-/
theorem quadraticReturn_smul_right
    (c : ℂ) (z w : OffDiag (V := V)) :
    quadraticReturn (V := V) z (c • w) =
      star c • quadraticReturn (V := V) z w := by
  simp only [quadraticReturn_eq_divergence,
    hadamardFlow_smul_right, LinearMap.map_smul]

/-- Residue span generated only by primitive defects `z_m(d)=Q φ^m(d)`.-/
def primitiveResidueSpan
    (φ : Dynamics V) (k : ℕ) :
    Submodule ℂ (DiagZero (V := V)) :=
  Submodule.span ℂ
    {r | ∃ m n : ℕ, m + n ≤ k ∧
      ∃ d e : diagonalSubmodule (V := V),
        quadraticReturn (V := V)
          (primitiveDefect (V := V) φ m d)
          (primitiveDefect (V := V) φ n e) = r}

/-- A primitive-pair return of total depth at most `k` belongs to the primitive residue span.-/
theorem primitiveReturn_mem_primitiveResidueSpan
    (φ : Dynamics V) {k m n : ℕ}
    (hmn : m + n ≤ k)
    (d e : diagonalSubmodule (V := V)) :
    quadraticReturn (V := V)
        (primitiveDefect (V := V) φ m d)
        (primitiveDefect (V := V) φ n e)
      ∈ primitiveResidueSpan (V := V) φ k := by
  apply Submodule.subset_span
  exact ⟨m, n, hmn, d, e, rfl⟩

/-- Package an element of the primitive hidden span as an `OffDiag` element.-/
def offDiagOfPrimitiveSpan
    (φ : Dynamics V) (k : ℕ)
    (x : A V) (hx : x ∈ primitiveHiddenSpan (V := V) φ k) :
    OffDiag (V := V) := by
  refine ⟨x, ?_⟩
  apply hidden_le_OffDiag (V := V) φ k
  rw [hidden_eq_span_primitive (V := V) φ k]
  exact hx

@[simp]
theorem offDiagOfPrimitiveSpan_val
    (φ : Dynamics V) (k : ℕ)
    (x : A V) (hx : x ∈ primitiveHiddenSpan (V := V) φ k) :
    (offDiagOfPrimitiveSpan (V := V) φ k x hx).1 = x := by
  rfl

/-- If both arguments lie in primitive hidden spans of depths `i,j`,
their quadratic return lies in the primitive residue span at every
`k ≥ i+j`.-/
theorem quadraticReturn_mem_primitiveResidueSpan_of_mem
    (φ : Dynamics V) {i j k : ℕ} (hij : i + j ≤ k)
    (z w : OffDiag (V := V))
    (hz : z.1 ∈ primitiveHiddenSpan (V := V) φ i)
    (hw : w.1 ∈ primitiveHiddenSpan (V := V) φ j) :
    quadraticReturn (V := V) z w
      ∈ primitiveResidueSpan (V := V) φ k := by
  let S : Set (A V) :=
    {x | ∃ d : diagonalSubmodule (V := V), ∃ m : ℕ,
      m ≤ i ∧ (primitiveDefect (V := V) φ m d).1 = x}
  let T : Set (A V) :=
    {y | ∃ e : diagonalSubmodule (V := V), ∃ n : ℕ,
      n ≤ j ∧ (primitiveDefect (V := V) φ n e).1 = y}

  have hzspan : z.1 ∈ Submodule.span ℂ S := by
    simpa [S, primitiveHiddenSpan] using hz
  have hwspan : w.1 ∈ Submodule.span ℂ T := by
    simpa [T, primitiveHiddenSpan] using hw

  let packS :
      (x : A V) → x ∈ Submodule.span ℂ S → OffDiag (V := V) :=
    fun x hx =>
      offDiagOfPrimitiveSpan (V := V) φ i x
        (by simpa [S, primitiveHiddenSpan] using hx)
  let packT :
      (y : A V) → y ∈ Submodule.span ℂ T → OffDiag (V := V) :=
    fun y hy =>
      offDiagOfPrimitiveSpan (V := V) φ j y
        (by simpa [T, primitiveHiddenSpan] using hy)

  let P :
      (x y : A V) →
      x ∈ Submodule.span ℂ S →
      y ∈ Submodule.span ℂ T → Prop :=
    fun x y hx hy =>
      quadraticReturn (V := V) (packS x hx) (packT y hy)
        ∈ primitiveResidueSpan (V := V) φ k

  have hP : P z.1 w.1 hzspan hwspan := by
    refine Submodule.span_induction₂
      (s := S) (t := T) (p := P) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hzspan hwspan
    · intro x y hx hy
      rcases hx with ⟨d, m, hmi, rfl⟩
      rcases hy with ⟨e, n, hnj, rfl⟩
      have hmn : m + n ≤ k := by omega
      have hS :
          (primitiveDefect (V := V) φ m d).1 ∈ Submodule.span ℂ S :=
        Submodule.subset_span
          (show (primitiveDefect (V := V) φ m d).1 ∈ S from
            ⟨d, m, hmi, rfl⟩)
      have hT :
          (primitiveDefect (V := V) φ n e).1 ∈ Submodule.span ℂ T :=
        Submodule.subset_span
          (show (primitiveDefect (V := V) φ n e).1 ∈ T from
            ⟨e, n, hnj, rfl⟩)
      have hpackS :
          packS (primitiveDefect (V := V) φ m d).1 hS =
            primitiveDefect (V := V) φ m d := by
        apply Subtype.ext
        rfl
      have hpackT :
          packT (primitiveDefect (V := V) φ n e).1 hT =
            primitiveDefect (V := V) φ n e := by
        apply Subtype.ext
        rfl
      change quadraticReturn (V := V)
          (packS (primitiveDefect (V := V) φ m d).1 hS)
          (packT (primitiveDefect (V := V) φ n e).1 hT)
        ∈ primitiveResidueSpan (V := V) φ k
      rw [hpackS, hpackT]
      exact primitiveReturn_mem_primitiveResidueSpan
        (V := V) φ hmn d e
    · intro y hy
      have h0S : (0 : A V) ∈ Submodule.span ℂ S :=
        Submodule.zero_mem _
      change quadraticReturn (V := V)
          (packS 0 h0S) (packT y hy)
        ∈ primitiveResidueSpan (V := V) φ k
      have hzero : packS 0 h0S = (0 : OffDiag (V := V)) := by
        apply Subtype.ext
        rfl
      rw [hzero, quadraticReturn_zero_left]
      exact Submodule.zero_mem _
    · intro x hx
      have h0T : (0 : A V) ∈ Submodule.span ℂ T :=
        Submodule.zero_mem _
      change quadraticReturn (V := V)
          (packS x hx) (packT 0 h0T)
        ∈ primitiveResidueSpan (V := V) φ k
      have hzero : packT 0 h0T = (0 : OffDiag (V := V)) := by
        apply Subtype.ext
        rfl
      rw [hzero, quadraticReturn_zero_right]
      exact Submodule.zero_mem _
    · intro x y q hx hy hq hxy hqy
      have hsumS : x + y ∈ Submodule.span ℂ S :=
        (Submodule.span ℂ S).add_mem hx hy
      have hpack :
          packS (x + y) hsumS = packS x hx + packS y hy := by
        apply Subtype.ext
        rfl
      change quadraticReturn (V := V)
          (packS (x + y) hsumS) (packT q hq)
        ∈ primitiveResidueSpan (V := V) φ k
      rw [hpack, quadraticReturn_add_left]
      exact (primitiveResidueSpan (V := V) φ k).add_mem hxy hqy
    · intro x y q hx hy hq hxy hxq
      have hsumT : y + q ∈ Submodule.span ℂ T :=
        (Submodule.span ℂ T).add_mem hy hq
      have hpack :
          packT (y + q) hsumT = packT y hy + packT q hq := by
        apply Subtype.ext
        rfl
      change quadraticReturn (V := V)
          (packS x hx) (packT (y + q) hsumT)
        ∈ primitiveResidueSpan (V := V) φ k
      rw [hpack, quadraticReturn_add_right]
      exact (primitiveResidueSpan (V := V) φ k).add_mem hxy hxq
    · intro c x y hx hy hxy
      have hsmulS : c • x ∈ Submodule.span ℂ S :=
        (Submodule.span ℂ S).smul_mem c hx
      have hpack :
          packS (c • x) hsmulS = c • packS x hx := by
        apply Subtype.ext
        rfl
      change quadraticReturn (V := V)
          (packS (c • x) hsmulS) (packT y hy)
        ∈ primitiveResidueSpan (V := V) φ k
      rw [hpack, quadraticReturn_smul_left]
      exact (primitiveResidueSpan (V := V) φ k).smul_mem c hxy
    · intro c x y hx hy hxy
      have hsmulT : c • y ∈ Submodule.span ℂ T :=
        (Submodule.span ℂ T).smul_mem c hy
      have hpack :
          packT (c • y) hsmulT = c • packT y hy := by
        apply Subtype.ext
        rfl
      change quadraticReturn (V := V)
          (packS x hx) (packT (c • y) hsmulT)
        ∈ primitiveResidueSpan (V := V) φ k
      rw [hpack, quadraticReturn_smul_right]
      exact (primitiveResidueSpan (V := V) φ k).smul_mem (star c) hxy

  have hzpack : packS z.1 hzspan = z := by
    apply Subtype.ext
    rfl
  have hwpack : packT w.1 hwspan = w := by
    apply Subtype.ext
    rfl
  change quadraticReturn (V := V)
      (packS z.1 hzspan) (packT w.1 hwspan)
    ∈ primitiveResidueSpan (V := V) φ k at hP
  simpa [hzpack, hwpack] using hP

/-- D4: the residue filtration is exactly the span of primitive defect pairs.-/
theorem residue_eq_span_primitive
    (φ : Dynamics V) (k : ℕ) :
    residue φ k = primitiveResidueSpan (V := V) φ k := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    apply quadraticReturn_mem_primitiveResidueSpan_of_mem
      (V := V) φ hij z w
    · rw [← hidden_eq_span_primitive (V := V) φ i]
      exact hz
    · rw [← hidden_eq_span_primitive (V := V) φ j]
      exact hw
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨m, n, hmn, d, e, rfl⟩
    exact quadraticReturn_mem_residue
      (V := V) φ hmn
      (primitiveDefect (V := V) φ m d)
      (primitiveDefect (V := V) φ n e)
      (primitiveDefect_mem_hidden (V := V) φ le_rfl d)
      (primitiveDefect_mem_hidden (V := V) φ le_rfl e)

/-! ## D5: finite stabilization of the finite core -/

/-- Hidden-defect filtration as a monotone map.-/
def hiddenOrderHom (φ : Dynamics V) : ℕ →o Submodule ℂ (A V) where
  toFun := hidden φ
  monotone' := by
    intro i j hij
    exact hidden_mono φ hij

/-- Hidden-flow filtration as a monotone map.-/
def hiddenFlowOrderHom (φ : Dynamics V) :
    ℕ →o Submodule ℂ (EdgeSpace V) where
  toFun := hiddenFlow φ
  monotone' := by
    intro i j hij
    exact hiddenFlow_mono φ hij

/-- Residue filtration as a monotone map.-/
def residueOrderHom (φ : Dynamics V) :
    ℕ →o Submodule ℂ (DiagZero (V := V)) where
  toFun := residue φ
  monotone' := by
    intro i j hij
    exact residue_mono φ hij

/-- D5: the hidden-defect filtration stabilizes after finitely many steps.-/
theorem hidden_eventually_constant (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k → hidden φ k = hidden φ s := by
  let a : ℕ →o Submodule ℂ (A V) := hiddenOrderHom (V := V) φ
  obtain ⟨s, hs⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨s, ?_⟩
  intro k hsk
  exact (hs k hsk).symm

/-- D5: the hidden-flow filtration stabilizes after finitely many steps.-/
theorem hiddenFlow_eventually_constant (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k → hiddenFlow φ k = hiddenFlow φ s := by
  let a : ℕ →o Submodule ℂ (EdgeSpace V) := hiddenFlowOrderHom (V := V) φ
  obtain ⟨s, hs⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨s, ?_⟩
  intro k hsk
  exact (hs k hsk).symm

/-- D5: the quadratic residue filtration stabilizes after finitely many steps.-/
theorem residue_eventually_constant (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k → residue φ k = residue φ s := by
  let a : ℕ →o Submodule ℂ (DiagZero (V := V)) := residueOrderHom (V := V) φ
  obtain ⟨s, hs⟩ := WellFoundedGT.monotone_chain_condition a
  refine ⟨s, ?_⟩
  intro k hsk
  exact (hs k hsk).symm

/-- There is one common finite depth after which hidden defects, hidden flows,
and residues are all stationary.-/
theorem finite_core_eventually_constant (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k →
      hidden φ k = hidden φ s ∧
      hiddenFlow φ k = hiddenFlow φ s ∧
      residue φ k = residue φ s := by
  obtain ⟨sH, hH⟩ := hidden_eventually_constant (V := V) φ
  obtain ⟨sF, hF⟩ := hiddenFlow_eventually_constant (V := V) φ
  obtain ⟨sR, hR⟩ := residue_eventually_constant (V := V) φ
  let s := max sH (max sF sR)
  refine ⟨s, ?_⟩
  intro k hsk
  have hsH : sH ≤ s := by
    exact le_max_left _ _
  have hsF : sF ≤ s := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsR : sR ≤ s := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hkH : sH ≤ k := hsH.trans hsk
  have hkF : sF ≤ k := hsF.trans hsk
  have hkR : sR ≤ k := hsR.trans hsk
  constructor
  · calc
      hidden φ k = hidden φ sH := hH k hkH
      _ = hidden φ s := (hH s hsH).symm
  constructor
  · calc
      hiddenFlow φ k = hiddenFlow φ sF := hF k hkF
      _ = hiddenFlow φ s := (hF s hsF).symm
  · calc
      residue φ k = residue φ sR := hR k hkR
      _ = residue φ s := (hR s hsR).symm

/-! ## Closure--Residue Profile (CRP) -/

/-- Complex dimension of the finite closure at depth `k`.-/
def closureDim (φ : Dynamics V) (k : ℕ) : ℕ :=
  Module.finrank ℂ (closure φ k)

/-- Complex dimension of the quadratic residue space at depth `k`.-/
def residueDim (φ : Dynamics V) (k : ℕ) : ℕ :=
  Module.finrank ℂ (residue φ k)

/-- Linear closure growth `g_k`, with the paper's convention `g₀ = N`.-/
def closureGrowth (φ : Dynamics V) : ℕ → ℕ
  | 0 => Fintype.card V
  | k + 1 => closureDim φ (k + 1) - closureDim φ k

/-- Quadratic residue growth `q_k`, with `q₀ = 0`.-/
def residueGrowth (φ : Dynamics V) : ℕ → ℕ
  | 0 => 0
  | k + 1 => residueDim φ (k + 1) - residueDim φ k

/-- The finite Closure--Residue Profile.-/
def CRP (φ : Dynamics V) (k : ℕ) : ℕ × ℕ :=
  (closureGrowth φ k, residueGrowth φ k)

@[simp]
theorem closureGrowth_zero (φ : Dynamics V) :
    closureGrowth φ 0 = Fintype.card V := rfl

@[simp]
theorem residueGrowth_zero (φ : Dynamics V) :
    residueGrowth φ 0 = 0 := rfl

@[simp]
theorem CRP_zero (φ : Dynamics V) :
    CRP φ 0 = (Fintype.card V, 0) := by
  rfl

/-- Closure dimensions are monotone with depth.-/
theorem closureDim_mono (φ : Dynamics V) {i j : ℕ} (hij : i ≤ j) :
    closureDim φ i ≤ closureDim φ j := by
  exact Submodule.finrank_mono (closure_mono φ hij)

/-- Residue dimensions are monotone with depth.-/
theorem residueDim_mono (φ : Dynamics V) {i j : ℕ} (hij : i ≤ j) :
    residueDim φ i ≤ residueDim φ j := by
  exact Submodule.finrank_mono (residue_mono φ hij)

/-- Additive form of the closure-growth definition, avoiding truncated-subtraction
ambiguity in later proofs.-/
theorem closureDim_add_growth (φ : Dynamics V) (k : ℕ) :
    closureDim φ k + closureGrowth φ (k + 1) =
      closureDim φ (k + 1) := by
  change closureDim φ k +
      (closureDim φ (k + 1) - closureDim φ k) =
    closureDim φ (k + 1)
  exact Nat.add_sub_of_le (closureDim_mono φ (Nat.le_succ k))

/-- Additive form of the residue-growth definition.-/
theorem residueDim_add_growth (φ : Dynamics V) (k : ℕ) :
    residueDim φ k + residueGrowth φ (k + 1) =
      residueDim φ (k + 1) := by
  change residueDim φ k +
      (residueDim φ (k + 1) - residueDim φ k) =
    residueDim φ (k + 1)
  exact Nat.add_sub_of_le (residueDim_mono φ (Nat.le_succ k))

/-- The first two residue-growth entries vanish because `R₀ = R₁ = 0`.-/
@[simp]
theorem residueGrowth_one (φ : Dynamics V) :
    residueGrowth φ 1 = 0 := by
  change Module.finrank ℂ (residue φ 1) -
      Module.finrank ℂ (residue φ 0) = 0
  rw [residue_one (V := V) φ, residue_zero (V := V) φ]
  simp

/-- Once the residue filtration has stabilized, all later residue growth vanishes.-/
theorem residueGrowth_eq_zero_of_stable
    (φ : Dynamics V) {s k : ℕ}
    (hsk : s ≤ k)
    (hstable : ∀ n : ℕ, s ≤ n → residue φ n = residue φ s) :
    residueGrowth φ (k + 1) = 0 := by
  change Module.finrank ℂ (residue φ (k + 1)) -
      Module.finrank ℂ (residue φ k) = 0
  have hk : residue φ k = residue φ s := hstable k hsk
  have hks : s ≤ k + 1 := hsk.trans (Nat.le_succ k)
  have hsucc : residue φ (k + 1) = residue φ s :=
    hstable (k + 1) hks
  rw [hsucc, hk]
  simp

/-- D-stage summary: a finite depth exists after which both the finite core and
the residue-growth component of CRP are stationary.-/
theorem CRP_residue_eventually_zero (φ : Dynamics V) :
    ∃ s : ℕ, ∀ k : ℕ, s ≤ k → residueGrowth φ (k + 1) = 0 := by
  obtain ⟨s, hs⟩ := residue_eventually_constant (V := V) φ
  exact ⟨s, fun k hsk =>
    residueGrowth_eq_zero_of_stable (V := V) φ hsk hs⟩

/--
D2 / Corollary 6.2 (Flow--Residue Factorization at filtration level):
`R_k` is exactly the image of `F_k` under divergence.

Crucially, this is a theorem connecting two independently defined spans.-/
theorem residue_eq_map_divergence (φ : Dynamics V) (k : ℕ) :
    residue φ k = (hiddenFlow φ k).map (divergence (V := V)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro r hr
    rcases hr with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    rw [quadraticReturn_eq_divergence (V := V) z w]
    exact ⟨hadamardFlow (V := V) z w,
      hadamardFlow_mem_hiddenFlow (V := V) φ hij z w hz hw, rfl⟩
  · rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    intro f hf
    rcases hf with ⟨i, j, hij, z, w, hz, hw, rfl⟩
    change divergence (V := V) (hadamardFlow (V := V) z w) ∈ residue φ k
    rw [← quadraticReturn_eq_divergence (V := V) z w]
    exact quadraticReturn_mem_residue (V := V) φ hij z w hz hw

end Filtration

end P3
