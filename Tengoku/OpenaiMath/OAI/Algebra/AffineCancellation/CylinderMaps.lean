import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.CylinderShift

namespace OAI

noncomputable section

namespace ComplexCancellation.Cylinder
variable {R S : Type*} [CommRing R] [CommRing S]

def encode (q : Point R) (w : R) : Frame R × R :=
  let t := q.shift (-w)
  (t.frame, t.frame.e t.linear w)

def decode (t : Frame R) (z : R) : Point R × R :=
  ((t.point (t.L z)).shift (t.W z), t.W z)

/--
@isnad1 id=eq.0h3v.s5.969ed6bb3d57 from=translated src=- shape=74791175 vocab=49af10db
-/
lemma decode_equation (t : Frame R) (z : R) : (decode t z).1.equation = 0 := by
  change ((t.point (t.L z)).shift (t.W z)).equation = 0
  rw [Point.shift_equation]
  exact t.coordinate_equation z

/--
@isnad1 id=eq.0h3v.s5.04435da9d728 from=translated src=- shape=1c7f1580 vocab=e7689787
-/
lemma encode_decode (t : Frame R) (z : R) :
    encode (decode t z).1 (decode t z).2 = (t, z) := by
  simp only [decode, encode, Point.shift_neg_shift, Frame.frame_point,
    Frame.linear_point, Frame.e_coordinates]

/--
@isnad1 id=eq.2h3v.s7.8595d15cb085 from=translated src=- shape=f33e5b0c vocab=31a1a73f
-/
lemma decode_encode (q : Point R) (w : R) (hq : q.equation = 0)
    (hp : ∀ r : R, q.p ^ 3 * r = 0 → r = 0) :
    decode (encode q w).1 (encode q w).2 = (q, w) := by
  let r := q.shift (-w)
  let t := r.frame
  let l := r.linear
  let z := t.e l w
  have hpt : t.p = q.p := rfl
  have htl : t.point l = r := r.point_frame
  have heq : (t.point l).equation + t.p ^ 3 * w = 0 := by
    rw [htl]
    change (q.shift (-w)).equation + q.p ^ 3 * w = 0
    rw [Point.shift_equation, hq]
    ring
  have hL : t.L z = l := by
    have hc := t.e_certificate l w
    rw [heq, mul_zero] at hc
    change t.root + t.p ^ 3 * t.e l w = l
    linear_combination hc
  have hW : t.W z = w := by
    have h := t.coordinate_equation z
    rw [hL] at h
    apply sub_eq_zero.mp
    apply hp
    rw [← hpt, mul_sub]
    linear_combination h - heq
  change (((t.point (t.L z)).shift (t.W z)), t.W z) = (q, w)
  rw [hL, hW, htl]
  congr 1
  change (q.shift (-w)).shift w = q
  rw [Point.shift_add, neg_add_cancel, Point.shift_zero]

namespace Point

def map (q : Point R) (g : R →+* S) : Point S :=
  ⟨g q.p, g q.s, g q.u, g q.f, g q.j⟩

/--
@isnad1 id=eq.0h4v.s6.9fef8d2df5f0 from=translated src=- shape=b9c7b6e0 vocab=5b6c995e
-/
@[simp] lemma map_x (q : Point R) (g : R →+* S) : (q.map g).x = g q.x := by
  simp [map, x]

/--
@isnad1 id=eq.0h4v.s6.447e4134c057 from=translated src=- shape=b9c7b6e0 vocab=2a69d68d
-/
@[simp] lemma map_equation (q : Point R) (g : R →+* S) :
    (q.map g).equation = g q.equation := by
  simp [equation, map, x, map_ofNat]

/--
@isnad1 id=eq.0h5v.s6.fe13fbd6e842 from=translated src=- shape=440688dc vocab=f8d28ea8
-/
@[simp] lemma map_shift (q : Point R) (w : R) (g : R →+* S) :
    (q.shift w).map g = (q.map g).shift (g w) := by
  ext <;> simp [map, shift, cubicDiff, x, map_ofNat]

end Point
namespace Frame

def map (t : Frame R) (g : R →+* S) : Frame S := ⟨g t.p, g t.s, g t.u, g t.m⟩

/--
@isnad1 id=eq.0h5v.s6.bf440cbbaf74 from=translated src=- shape=72eb4439 vocab=e84df7ed
-/
@[simp] lemma map_point (t : Frame R) (l : R) (g : R →+* S) :
    (t.point l).map g = (t.map g).point (g l) := by
  ext <;> simp [Point.map, map, point, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

/--
@isnad1 id=eq.0h5v.s7.fb9b4c080b7b from=translated src=- shape=245c576c vocab=6d7c0d42
-/
@[simp] lemma map_L (t : Frame R) (z : R) (g : R →+* S) :
    g (t.L z) = (t.map g).L (g z) := by
  simp [map, L, root, c, Q, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

/--
@isnad1 id=eq.0h5v.s7.247d4e9741d8 from=translated src=- shape=245c576c vocab=6040896b
-/
@[simp] lemma map_W (t : Frame R) (z : R) (g : R →+* S) :
    g (t.W z) = (t.map g).W (g z) := by
  simp [W, map_L, map, c, Q, Q₁, q₁, q₂, f, j, f₁, f₀, j₁, j₀, x₀, map_ofNat]

end Frame

/--
@isnad1 id=eq.0h5v.s7.634423d8097f from=translated src=- shape=dffacd17 vocab=6faba1d7
-/
lemma decode_map (t : Frame R) (z : R) (g : R →+* S) :
    ((decode t z).1.map g, g (decode t z).2) = decode (t.map g) (g z) := by
  simp [decode]

/--
@isnad1 id=eq.0h5v.s7.9ef5aa8dbadb from=translated src=- shape=dffacd17 vocab=187d4ff8
-/
lemma encode_map (q : Point R) (w : R) (g : R →+* S) :
    ((encode q w).1.map g, g (encode q w).2) = encode (q.map g) (g w) := by
  simp only [encode, ← Point.map_shift, ← map_neg]
  apply Prod.ext
  · ext <;> simp [Point.frame, Frame.map, Point.map, map_ofNat]
  · simp [Frame.e, Frame.h, Frame.Q₁, Frame.q₁, Frame.q₂, Frame.Q, Frame.f, Frame.j,
      Frame.f₀, Frame.f₁, Frame.j₀, Frame.j₁, Frame.x₀, Point.linear, Point.frame, Point.map, map_ofNat]

end ComplexCancellation.Cylinder

end

end OAI
