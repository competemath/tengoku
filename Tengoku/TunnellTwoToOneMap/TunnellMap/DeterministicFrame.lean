import Tengoku.TunnellTwoToOneMap.TunnellMap.OrthogonalFrameExistence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A deterministic executable orthogonal frame

`TunnellMap.orthogonalFrame_exists_of_squarefree_norm` only asserts that an
oriented orthogonal frame of a primitive source vector exists, and the
computational pipeline used to select one through `Classical.choice`.  This
file removes that boundary: the two kernel basis vectors are *computed* from
the source vector by extended-Euclidean arithmetic with completely fixed
sign, ordering and quotient conventions.

The conventions are:

* the coordinate gcd is taken as `Int.gcd p.x p.y`, and the Bezout
  coefficients are Lean's canonical `Int.gcdA` / `Int.gcdB`;
* if `Int.gcd p.x p.y = 0` (so `p = (0,0,±1)`) the frame is the ordered pair
  of standard basis vectors `(e_x, e_y)` when `p.z > 0` and `(e_y, e_x)`
  otherwise;
* otherwise `e₁ = (-y/G, x/G, 0)` and `e₂ = (-A z, -B z, G)`, in this order;
* the Bezout vector is `tripleBezout p`.

Everything is a plain `def`, so repeated execution returns a definitionally
identical answer.
-/

namespace TunnellMap

/-! ## Integral combinations of two vectors -/

/-- The integral combination `a u + b v` of two lattice vectors.-/
def span2 (a b : ℤ) (u v : Triple) : Triple := vadd (vsmul a u) (vsmul b v)

/--
@isnad1 id=eq.0h4v.s6.bad2ec5b5dd9 from=translated src=- shape=715a7b46 vocab=526a858b
-/
@[simp] theorem span2_apply (a b : ℤ) (u v : Triple) :
    span2 a b u v = ⟨a * u.x + b * v.x, a * u.y + b * v.y, a * u.z + b * v.z⟩ :=
  rfl

/--
@isnad1 id=eq.0h5v.s4.b2843e4b156a from=translated src=- shape=0b2fcec7 vocab=1075affd
-/
theorem linComb3_zero (a b : ℤ) (u v z : Triple) :
    linComb3 a b 0 u v z = span2 a b u v := by
  apply Triple.ext <;> simp [linComb3, span2, vadd, vsmul]

/--
@isnad1 id=eq.0h6v.s5.5906cace5b02 from=translated src=- shape=e1f13d23 vocab=b3c94644
-/
theorem cross_span2 (a b c d : ℤ) (u v : Triple) :
    cross (span2 a b u v) (span2 c d u v) = vsmul (a * d - b * c) (cross u v) := by
  apply Triple.ext <;> simp [cross, span2, vadd, vsmul] <;> ring

/--
@isnad1 id=eq.2h5v.s5.bc8c4203af67 from=translated src=- shape=236f6a3e vocab=99a28d52
-/
theorem dot_span2_left (p : Triple) {u v : Triple} (hu : dot p u = 0)
    (hv : dot p v = 0) (a b : ℤ) : dot p (span2 a b u v) = 0 := by
  simp only [dot, span2_apply] at hu hv ⊢
  linear_combination a * hu + b * hv

/-! ## The deterministic kernel basis -/

/-- The first kernel basis vector of the deterministic frame.-/
def frameE₁ (p : Triple) : Triple :=
  if (Int.gcd p.x p.y : ℤ) = 0 then
    (if 0 < p.z then ⟨1, 0, 0⟩ else ⟨0, 1, 0⟩)
  else
    ⟨-(p.y / (Int.gcd p.x p.y : ℤ)), p.x / (Int.gcd p.x p.y : ℤ), 0⟩

/-- The second kernel basis vector of the deterministic frame.-/
def frameE₂ (p : Triple) : Triple :=
  if (Int.gcd p.x p.y : ℤ) = 0 then
    (if 0 < p.z then ⟨0, 1, 0⟩ else ⟨1, 0, 0⟩)
  else
    ⟨-(p.x.gcdA p.y) * p.z, -(p.x.gcdB p.y) * p.z, (Int.gcd p.x p.y : ℤ)⟩

/--
@isnad1 id=and.2h1v.s6.0dce0b318483 from=translated src=- shape=b9df22ba vocab=0293c8e5
-/
theorem gcd_xy_eq_zero_cases {p : Triple} (hp : tripleGCD p = 1)
    (h0 : (Int.gcd p.x p.y : ℤ) = 0) : p.x = 0 ∧ p.y = 0 ∧ (p.z = 1 ∨ p.z = -1) := by
  have h0' : Int.gcd p.x p.y = 0 := by exact_mod_cast h0
  obtain ⟨hx, hy⟩ := Int.gcd_eq_zero_iff.mp h0'
  refine ⟨hx, hy, ?_⟩
  have : Int.gcd (0 : ℤ) p.z = 1 := by
    have := hp
    unfold tripleGCD at this
    rwa [h0'] at this
  simp only [Int.gcd_zero_left] at this
  omega

/-- **The computed pair is a basis of the orthogonal lattice**: its cross
product is the source vector.
@isnad1 id=eq.1h1v.s4.899440a33ae0 from=translated src=- shape=e2196cba vocab=f2e9d08b
-/
theorem cross_frameE₁_frameE₂ {p : Triple} (hp : tripleGCD p = 1) :
    cross (frameE₁ p) (frameE₂ p) = p := by
  by_cases h0 : (Int.gcd p.x p.y : ℤ) = 0
  · obtain ⟨hx, hy, hz⟩ := gcd_xy_eq_zero_cases hp h0
    rcases hz with hz | hz
    · have hzpos : 0 < p.z := by omega
      simp only [frameE₁, frameE₂, ite_eq_left h0, ite_eq_left hzpos]
      apply Triple.ext <;> simp [cross, hx, hy, hz]
    · have hzpos : ¬ (0 < p.z) := by omega
      simp only [frameE₁, frameE₂, ite_eq_left h0, ite_eq_right hzpos]
      apply Triple.ext <;> simp [cross, hx, hy, hz]
  · simp only [frameE₁, frameE₂, ite_eq_right h0]
    set G : ℤ := (Int.gcd p.x p.y : ℤ) with hG
    set A : ℤ := p.x.gcdA p.y with hA
    set B : ℤ := p.x.gcdB p.y with hB
    set a : ℤ := p.x / G with ha
    set b : ℤ := p.y / G with hb
    have hxDiv : G * a = p.x := by
      rw [ha, mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_left p.x p.y)
    have hyDiv : G * b = p.y := by
      rw [hb, mul_comm]
      exact Int.ediv_mul_cancel (Int.gcd_dvd_right p.x p.y)
    have hBezout : G = p.x * A + p.y * B := Int.gcd_eq_gcd_ab p.x p.y
    have hAB : A * a + B * b = 1 := by
      apply mul_left_cancel₀ h0
      calc
        G * (A * a + B * b) = (G * a) * A + (G * b) * B := by ring
        _ = p.x * A + p.y * B := by rw [hxDiv, hyDiv]
        _ = G := hBezout.symm
        _ = G * 1 := by ring
    apply Triple.ext
    · dsimp only [cross]
      linear_combination hxDiv
    · dsimp only [cross]
      linear_combination hyDiv
    · dsimp only [cross]
      linear_combination p.z * hAB

/-- **The deterministic oriented orthogonal frame** of a primitive triple.
Both kernel vectors and the Bezout vector are computed by extended-Euclidean
arithmetic; the construction is a plain `def`.-/
def orthogonalFrameExec (p : Triple) (hp : tripleGCD p = 1) : OrthogonalFrame p where
  e₁ := frameE₁ p
  e₂ := frameE₂ p
  z := tripleBezout p
  cross_eq := cross_frameE₁_frameE₂ hp
  bezout := dot_tripleBezout_of_gcd_eq_one hp

/--
@isnad1 id=eq.1h1v.s4.e86cf4308ba5 from=translated src=- shape=08e9f661 vocab=89914161
-/
@[simp] theorem orthogonalFrameExec_e₁ (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₁ = frameE₁ p := rfl

/--
@isnad1 id=eq.1h1v.s4.238a41abbd3a from=translated src=- shape=08e9f661 vocab=1ca069ea
-/
@[simp] theorem orthogonalFrameExec_e₂ (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).e₂ = frameE₂ p := rfl

/--
@isnad1 id=eq.1h1v.s4.9035c656e679 from=translated src=- shape=08e9f661 vocab=a3e38419
-/
@[simp] theorem orthogonalFrameExec_z (p : Triple) (hp : tripleGCD p = 1) :
    (orthogonalFrameExec p hp).z = tripleBezout p := rfl

/-- **Determinism.**  The computed frame does not depend on the proof of
primitivity, so repeated execution returns a definitionally identical
answer.
@isnad1 id=eq.2h1v.s4.b75f06ac2f15 from=translated src=- shape=7af23ece vocab=fd54f566
-/
theorem orthogonalFrameExec_deterministic (p : Triple) (hp hp' : tripleGCD p = 1) :
    orthogonalFrameExec p hp = orthogonalFrameExec p hp' := rfl

/-! ## Correctness of the computed frame -/

section Frame

variable {p : Triple} (F : OrthogonalFrame p)

/-- Both computed basis vectors are orthogonal to the source vector.
@isnad1 id=and.0h2v.s4.a24b998faed9 from=translated src=- shape=3c06122f vocab=ad42142d
-/
theorem frame_orthogonal : dot p F.e₁ = 0 ∧ dot p F.e₂ = 0 :=
  ⟨F.e₁_orthogonal, F.e₂_orthogonal⟩

/-- The two computed basis vectors are linearly independent over `ℤ`.
@isnad1 id=and.1h4v.s5.c366684948c0 from=translated src=- shape=b91231cc vocab=0cb19cf7
-/
theorem frame_linearIndependent {a b : ℤ}
    (h : span2 a b F.e₁ F.e₂ = ⟨0, 0, 0⟩) : a = 0 ∧ b = 0 := by
  have h0 : span2 (0 : ℤ) 0 F.e₁ F.e₂ = ⟨0, 0, 0⟩ := by
    apply Triple.ext <;> simp
  have hlin : linComb3 a b 0 F.e₁ F.e₂ F.z = linComb3 0 0 0 F.e₁ F.e₂ F.z := by
    rw [linComb3_zero, linComb3_zero, h, h0]
  have key : ((a, b, 0) : ℤ × ℤ × ℤ) = (0, 0, 0) := F.linComb3_injective (by exact hlin)
  exact ⟨congrArg (fun t : ℤ × ℤ × ℤ => t.1) key,
    congrArg (fun t : ℤ × ℤ × ℤ => t.2.1) key⟩

/-- **The computed pair spans the whole orthogonal lattice**: an integral
vector is an integral combination of the two basis vectors exactly when it is
orthogonal to the source vector, and the coefficients are unique.
@isnad1 id=iff.0h3v.s5.641a37b0c593 from=translated src=- shape=6f98319d vocab=c5303e51
-/
theorem frame_span_iff (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔ dot p r = 0 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    exact dot_span2_left p F.e₁_orthogonal F.e₂_orthogonal a b
  · intro hr
    obtain ⟨⟨a, b⟩, hab, -⟩ := F.affine_coset 0 r hr
    exact ⟨a, b, by rw [hab, linComb3_zero]⟩

/--
@isnad1 id=existsun.1h3v.s5.18e4e23a719d from=translated src=- shape=e5655b2d vocab=2d408963
-/
theorem frame_span_unique {r : Triple} (hr : dot p r = 0) :
    ∃! ab : ℤ × ℤ, r = span2 ab.1 ab.2 F.e₁ F.e₂ := by
  obtain ⟨ab, hab, huniq⟩ := F.affine_coset 0 r hr
  refine ⟨ab, by rw [hab, linComb3_zero], ?_⟩
  intro cd hcd
  refine huniq cd ?_
  show r = linComb3 cd.1 cd.2 0 F.e₁ F.e₂ F.z
  rw [linComb3_zero]; exact hcd

/-- The Gram determinant of the computed basis is the norm of the source
vector, as required by the manuscript.
@isnad1 id=eq.0h2v.s5.da080f05d47f from=translated src=- shape=695b556c vocab=304d0ede
-/
theorem frame_gram_det :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := F.gram_det

end Frame

/-! ## The computed frame, specialized -/

section Exec

variable {p : Triple}

/-- Both computed basis vectors are integral and orthogonal to the source.
@isnad1 id=and.1h1v.s5.03f3669fe562 from=translated src=- shape=bdfd92d3 vocab=c1403346
-/
theorem orthogonalFrameExec_orthogonal (hp : tripleGCD p = 1) :
    dot p (frameE₁ p) = 0 ∧ dot p (frameE₂ p) = 0 :=
  frame_orthogonal (orthogonalFrameExec p hp)

/-- The two computed basis vectors are linearly independent over `ℤ`.
@isnad1 id=and.2h3v.s5.fd0ec07b8d38 from=translated src=- shape=07c24ef3 vocab=0341404e
-/
theorem orthogonalFrameExec_linearIndependent (hp : tripleGCD p = 1) {a b : ℤ}
    (h : span2 a b (frameE₁ p) (frameE₂ p) = ⟨0, 0, 0⟩) : a = 0 ∧ b = 0 :=
  frame_linearIndependent (orthogonalFrameExec p hp) h

/-- **The computed pair spans every integral vector orthogonal to the
source.**
@isnad1 id=iff.1h2v.s5.5ba620f5e097 from=translated src=- shape=f81fdee3 vocab=d1c9cc6f
-/
theorem orthogonalFrameExec_span_iff (hp : tripleGCD p = 1) (r : Triple) :
    (∃ a b : ℤ, r = span2 a b (frameE₁ p) (frameE₂ p)) ↔ dot p r = 0 :=
  frame_span_iff (orthogonalFrameExec p hp) r

/-- The coefficients over the computed basis are unique.
@isnad1 id=existsun.2h2v.s5.6da7ee37dc34 from=translated src=- shape=f520cd79 vocab=22a92fe8
-/
theorem orthogonalFrameExec_span_unique (hp : tripleGCD p = 1) {r : Triple}
    (hr : dot p r = 0) :
    ∃! ab : ℤ × ℤ, r = span2 ab.1 ab.2 (frameE₁ p) (frameE₂ p) :=
  frame_span_unique (orthogonalFrameExec p hp) hr

/-- **The Gram determinant of the computed basis** is the norm of the source
vector required by the manuscript.
@isnad1 id=eq.1h1v.s5.bbaca3801ef4 from=translated src=- shape=a055306b vocab=6042c22d
-/
theorem orthogonalFrameExec_gram_det (hp : tripleGCD p = 1) :
    dot (frameE₁ p) (frameE₁ p) * dot (frameE₂ p) (frameE₂ p) -
      dot (frameE₁ p) (frameE₂ p) ^ 2 = dot p p :=
  frame_gram_det (orthogonalFrameExec p hp)

end Exec

/-! ## The change of basis between two frames of the same source -/

section Change

variable {p : Triple} (F G : OrthogonalFrame p)

/-- **The change of basis between any two frames of the same primitive source
is unimodular of determinant one.**
@isnad1 id=ex.1h3v.s6.b41d2dcc24a9 from=translated src=- shape=7b73162d vocab=8e9ccdd5
-/
theorem frame_change_unimodular (hp : p ≠ ⟨0, 0, 0⟩) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      G.e₁ = span2 a b F.e₁ F.e₂ ∧ G.e₂ = span2 c d F.e₁ F.e₂ := by
  obtain ⟨a, b, h₁⟩ := (frame_span_iff F G.e₁).mpr G.e₁_orthogonal
  obtain ⟨c, d, h₂⟩ := (frame_span_iff F G.e₂).mpr G.e₂_orthogonal
  refine ⟨a, b, c, d, ?_, h₁, h₂⟩
  have hcross : cross G.e₁ G.e₂ = vsmul (a * d - b * c) (cross F.e₁ F.e₂) := by
    rw [h₁, h₂, cross_span2]
  rw [G.cross_eq, F.cross_eq] at hcross
  by_contra hne
  apply hp
  have hx : (a * d - b * c - 1) * p.x = 0 := by
    have := congrArg Triple.x hcross
    simp only [vsmul] at this
    linarith [this]
  have hy : (a * d - b * c - 1) * p.y = 0 := by
    have := congrArg Triple.y hcross
    simp only [vsmul] at this
    linarith [this]
  have hz : (a * d - b * c - 1) * p.z = 0 := by
    have := congrArg Triple.z hcross
    simp only [vsmul] at this
    linarith [this]
  have hk : a * d - b * c - 1 ≠ 0 := by omega
  exact Triple.ext ((mul_eq_zero.mp hx).resolve_left hk)
    ((mul_eq_zero.mp hy).resolve_left hk) ((mul_eq_zero.mp hz).resolve_left hk)

/-- **Two frames of the same source span the same lattice.**
@isnad1 id=iff.0h4v.s5.ea5807497a97 from=translated src=- shape=c8ba8443 vocab=71e7ee61
-/
theorem frame_same_lattice (r : Triple) :
    (∃ a b : ℤ, r = span2 a b F.e₁ F.e₂) ↔ (∃ a b : ℤ, r = span2 a b G.e₁ G.e₂) := by
  rw [frame_span_iff F r, frame_span_iff G r]

end Change

end TunnellMap
