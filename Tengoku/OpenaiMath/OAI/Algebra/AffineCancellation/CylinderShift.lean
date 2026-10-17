import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

/-! Polynomial stabilization without division by the distinguished coordinate. -/
namespace ComplexCancellation.Cylinder

variable {R : Type*} [CommRing R]

@[ext] structure Point (R : Type*) where
  p : R
  s : R
  u : R
  f : R
  j : R

namespace Point

def x (q : Point R) : R := q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f
def equation (q : Point R) : R :=
  q.x ^ 2 * q.f - (1 + 2 * q.s * q.x) * q.j - q.p ^ 2 * q.j ^ 2 - q.p * q.u

def cubicDiff (p u w : R) : R := -3 * u ^ 2 * w + 3 * u * p ^ 2 * w ^ 2 - p ^ 4 * w ^ 3

/--
@isnad1 id=eq.0h4v.s7.bd6ec91fb993 from=translated src=- shape=a4720962 vocab=99a3f7be
-/
lemma cubicDiff_spec (p u w : R) :
    (u - p ^ 2 * w) ^ 3 = u ^ 3 + p ^ 2 * cubicDiff p u w := by
  unfold cubicDiff
  ring

/--
@isnad1 id=eq.0h5v.s6.d36349bca358 from=translated src=- shape=5f52274e vocab=99a3f7be
-/
lemma cubicDiff_add (p u w z : R) :
    cubicDiff p u w + cubicDiff p (u - p ^ 2 * w) z = cubicDiff p u (w + z) := by
  unfold cubicDiff
  ring

/-- A finite exponential shift fixing `p`, `x`, `y`, `z` and translating `u` by `-p²w`. -/
def shift (q : Point R) (w : R) : Point R :=
  let k := cubicDiff q.p q.u w
  ⟨q.p, q.s + q.p ^ 2 * q.x * k, q.u - q.p ^ 2 * w,
    q.f - (2 * q.s * q.x + 1) * k - q.p ^ 2 * q.x ^ 2 * k ^ 2,
    q.j - q.x ^ 2 * k⟩

/--
@isnad1 id=eq.0h3v.s4.66e03c5e7259 from=translated src=- shape=d1f51a78 vocab=64774e76
-/
@[simp] lemma shift_p (q : Point R) (w : R) : (q.shift w).p = q.p := rfl
/--
@isnad1 id=eq.0h3v.s6.fa63ce9d323e from=translated src=- shape=a4f815bd vocab=414163ab
-/
@[simp] lemma shift_u (q : Point R) (w : R) : (q.shift w).u = q.u - q.p ^ 2 * w := rfl

/--
@isnad1 id=eq.0h3v.s4.725da8fefac6 from=translated src=- shape=d1f51a78 vocab=f34bf8d1
-/
@[simp] lemma shift_x (q : Point R) (w : R) : (q.shift w).x = q.x := by
  change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) ^ 2 +
    (q.u - q.p ^ 2 * w) ^ 3 + q.p ^ 2 *
    (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) = q.x
  rw [cubicDiff_spec]
  calc
    _ = q.s ^ 2 + q.u ^ 3 + q.p ^ 2 * q.f := by ring
    _ = q.x := rfl

/--
@isnad1 id=eq.0h2v.s4.cd3248d3dde2 from=translated src=- shape=7841e525 vocab=7f606e88
-/
@[simp] lemma shift_zero (q : Point R) : q.shift 0 = q := by
  cases q
  simp [shift, cubicDiff]

/--
@isnad1 id=eq.0h4v.s5.a03ccff3f5a3 from=translated src=- shape=22d3aa17 vocab=2eaf8312
-/
lemma shift_add (q : Point R) (w z : R) : (q.shift w).shift z = q.shift (w + z) := by
  have hk := cubicDiff_add q.p q.u w z
  have hx := shift_x q w
  apply Point.ext
  · rfl
  · change (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) +
      q.p ^ 2 * (q.shift w).x * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring
  · change q.u - q.p ^ 2 * w - q.p ^ 2 * z = q.u - q.p ^ 2 * (w + z)
    ring
  · change q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2 -
      (2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * (q.shift w).x + 1) *
        cubicDiff q.p (q.u - q.p ^ 2 * w) z -
      q.p ^ 2 * (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z ^ 2 = _
    rw [hx]
    change _ = q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u (w + z) -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u (w + z) ^ 2
    rw [← hk]
    ring
  · change q.j - q.x ^ 2 * cubicDiff q.p q.u w -
      (q.shift w).x ^ 2 * cubicDiff q.p (q.u - q.p ^ 2 * w) z = _
    rw [hx]
    change _ = q.j - q.x ^ 2 * cubicDiff q.p q.u (w + z)
    rw [← hk]
    ring

/--
@isnad1 id=eq.0h3v.s6.f928a1dc4c83 from=translated src=- shape=a4f815bd vocab=04b1a976
-/
lemma shift_equation (q : Point R) (w : R) :
    (q.shift w).equation = q.equation + q.p ^ 3 * w := by
  unfold equation
  rw [shift_x]
  change q.x ^ 2 * (q.f - (2 * q.s * q.x + 1) * cubicDiff q.p q.u w -
      q.p ^ 2 * q.x ^ 2 * cubicDiff q.p q.u w ^ 2) -
    (1 + 2 * (q.s + q.p ^ 2 * q.x * cubicDiff q.p q.u w) * q.x) *
      (q.j - q.x ^ 2 * cubicDiff q.p q.u w) -
    q.p ^ 2 * (q.j - q.x ^ 2 * cubicDiff q.p q.u w) ^ 2 -
    q.p * (q.u - q.p ^ 2 * w) = _
  ring

/--
@isnad1 id=eq.0h3v.s5.ac5f105a4fa2 from=translated src=- shape=46524aac vocab=8f6bf55a
-/
@[simp] lemma shift_neg_shift (q : Point R) (w : R) : (q.shift w).shift (-w) = q := by
  rw [shift_add, add_neg_cancel, shift_zero]

end Point
end ComplexCancellation.Cylinder

namespace ComplexCancellation.Cylinder
variable {R : Type*} [CommRing R]

@[ext] structure Frame (R : Type*) where
  p : R
  s : R
  u : R
  m : R

namespace Frame

def x₀ (t : Frame R) : R := t.s ^ 2 + t.u ^ 3
def f₁ (t : Frame R) : R := 4 * t.s ^ 2
def f₀ (t : Frame R) : R := (1 + 2 * t.s * t.x₀) * t.m
def j₁ (t : Frame R) : R := 2 * t.s * t.x₀ - 1
def j₀ (t : Frame R) : R := t.x₀ ^ 2 * t.m
def f (t : Frame R) (l : R) : R := t.f₁ * l + t.f₀
def j (t : Frame R) (l : R) : R := t.j₁ * l + t.j₀
def point (t : Frame R) (l : R) : Point R := ⟨t.p, t.s, t.u, t.f l, t.j l⟩
def Q (t : Frame R) (l : R) : R :=
  2 * t.x₀ * t.f l ^ 2 - 2 * t.s * t.f l * t.j l - t.j l ^ 2
def c (t : Frame R) : R := t.Q 0
def q₁ (t : Frame R) : R :=
  4 * t.x₀ * t.f₁ * t.f₀ - 2 * t.s * (t.f₁ * t.j₀ + t.f₀ * t.j₁) - 2 * t.j₁ * t.j₀
def q₂ (t : Frame R) : R :=
  2 * t.x₀ * t.f₁ ^ 2 - 2 * t.s * t.f₁ * t.j₁ - t.j₁ ^ 2
def Q₁ (t : Frame R) (l : R) : R := t.q₁ + t.q₂ * l

/--
@isnad1 id=eq.0h3v.s5.2552acfd57a4 from=translated src=- shape=a01f5c66 vocab=7843064c
-/
lemma Q_expand (t : Frame R) (l : R) : t.Q l = t.c + l * t.Q₁ l := by
  simp only [Q, c, Q₁, q₁, q₂, f, j]
  ring

/--
@isnad1 id=eq.0h3v.s7.a99f7b61e3cc from=translated src=- shape=07f851ba vocab=6b7f3a82
-/
lemma equation_point (t : Frame R) (l : R) :
    (t.point l).equation = l - t.p * t.u + t.p ^ 2 * t.Q l + t.p ^ 4 * t.f l ^ 3 := by
  have hl : t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l := by
    unfold f j f₁ f₀ j₁ j₀
    ring
  change (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.s ^ 2 + t.u ^ 3 + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  change (t.x₀ + t.p ^ 2 * t.f l) ^ 2 * t.f l -
    (1 + 2 * t.s * (t.x₀ + t.p ^ 2 * t.f l)) * t.j l -
    t.p ^ 2 * t.j l ^ 2 - t.p * t.u = _
  unfold Q
  linear_combination hl

def root (t : Frame R) : R := t.p * t.u - t.p ^ 2 * t.c
def h (t : Frame R) (l w : R) : R :=
  t.u - t.p * t.Q l - t.p ^ 3 * t.f l ^ 3 - t.p ^ 2 * w
def e (t : Frame R) (l w : R) : R := -w - t.p * t.f l ^ 3 - t.Q₁ l * t.h l w

def L (t : Frame R) (z : R) : R := t.root + t.p ^ 3 * z
def W (t : Frame R) (z : R) : R :=
  -z - (t.u - t.p * t.c + t.p ^ 2 * z) * t.Q₁ (t.L z) - t.p * t.f (t.L z) ^ 3

/--
@isnad1 id=eq.0h4v.s8.2182f1906de2 from=translated src=- shape=05e480f5 vocab=30c45f1a
-/
lemma e_certificate (t : Frame R) (l w : R) :
    t.p ^ 3 * t.e l w - (l - t.root) =
    (t.p ^ 2 * t.Q₁ l - 1) * ((t.point l).equation + t.p ^ 3 * w) := by
  rw [equation_point]
  unfold e h root
  rw [Q_expand]
  ring

/--
@isnad1 id=eq.0h3v.s6.6edad7f23471 from=translated src=- shape=96512443 vocab=6c630c2a
-/
lemma coordinate_equation (t : Frame R) (z : R) :
    (t.point (t.L z)).equation + t.p ^ 3 * t.W z = 0 := by
  rw [equation_point, Q_expand]
  unfold W L root
  ring

/--
@isnad1 id=eq.0h3v.s6.7028013ec840 from=translated src=- shape=96e674cb vocab=3eafb506
-/
lemma h_coordinates (t : Frame R) (z : R) :
    t.h (t.L z) (t.W z) = t.u - t.p * t.c + t.p ^ 2 * z := by
  unfold h W
  rw [Q_expand]
  unfold L root
  ring

/--
@isnad1 id=eq.0h3v.s4.a63f560f6249 from=translated src=- shape=0331b1ac vocab=af787be7
-/
lemma e_coordinates (t : Frame R) (z : R) : t.e (t.L z) (t.W z) = z := by
  unfold e
  rw [h_coordinates]
  unfold W
  ring

end Frame

namespace Point

def frame (q : Point R) : Frame R :=
  ⟨q.p, q.s, q.u, (1 - 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.f + 4 * q.s ^ 2 * q.j⟩
def linear (q : Point R) : R :=
  (q.s ^ 2 + q.u ^ 3) ^ 2 * q.f - (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.j

/--
@isnad1 id=eq.0h2v.s4.be5a1fdcf19f from=translated src=- shape=9cd113be vocab=8af13129
-/
lemma point_frame (q : Point R) : q.frame.point q.linear = q := by
  apply Point.ext
  · rfl
  · rfl
  · rfl
  · change 4 * q.s ^ 2 * q.linear +
      (1 + 2 * q.s * (q.s ^ 2 + q.u ^ 3)) * q.frame.m = q.f
    unfold linear frame
    ring
  · change (2 * q.s * (q.s ^ 2 + q.u ^ 3) - 1) * q.linear +
      (q.s ^ 2 + q.u ^ 3) ^ 2 * q.frame.m = q.j
    unfold linear frame
    ring

end Point
namespace Frame

/--
@isnad1 id=eq.0h3v.s4.ee11beecc83b from=translated src=- shape=45c8189d vocab=53073d21
-/
@[simp] lemma frame_point (t : Frame R) (l : R) : (t.point l).frame = t := by
  apply Frame.ext
  · rfl
  · rfl
  · rfl
  · change (1 - 2 * t.s * t.x₀) * t.f l + 4 * t.s ^ 2 * t.j l = t.m
    unfold f j f₁ f₀ j₁ j₀
    ring

/--
@isnad1 id=eq.0h3v.s4.ab3c802ae3c3 from=translated src=- shape=5f327239 vocab=e2bd1e9a
-/
@[simp] lemma linear_point (t : Frame R) (l : R) : (t.point l).linear = l := by
  change t.x₀ ^ 2 * t.f l - (1 + 2 * t.s * t.x₀) * t.j l = l
  unfold f j f₁ f₀ j₁ j₀
  ring

end Frame
end ComplexCancellation.Cylinder

end

end OAI
