import Tengoku.TunnellTwoToOneMap.TunnellMap.Midpoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebra for the affine-lattice generator

This file formalizes the exact vector and lattice identities used in Section
5 of the paper.  It does not yet implement Smith reduction or the ordered
enumerator; it supplies their verified algebraic interface.
-/

namespace TunnellMap

def dot (p q : Triple) : ℤ := p.x * q.x + p.y * q.y + p.z * q.z

def cross (p q : Triple) : Triple :=
  ⟨p.y * q.z - p.z * q.y,
    p.z * q.x - p.x * q.z,
    p.x * q.y - p.y * q.x⟩

def vadd (p q : Triple) : Triple := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩

def vsmul (a : ℤ) (p : Triple) : Triple := ⟨a * p.x, a * p.y, a * p.z⟩

def linComb3 (a b c : ℤ) (e₁ e₂ z : Triple) : Triple :=
  vadd (vsmul a e₁) (vadd (vsmul b e₂) (vsmul c z))

def det3 (e₁ e₂ z : Triple) : ℤ := dot (cross e₁ e₂) z

def tau (p : Triple) : Triple := ⟨p.x + p.z, p.y, p.x - p.z⟩

/--
@isnad1 id=eq.0h2v.s3.7a582c676ab9 from=translated src=- shape=ab795eaa vocab=4dc6e7b9
-/
theorem dot_comm (p q : Triple) : dot p q = dot q p := by
  simp [dot]
  ring

/--
@isnad1 id=eq.0h2v.s6.a55d0698f806 from=translated src=- shape=734b26d1 vocab=fb3a5cf9
-/
@[simp] theorem dot_tau (p q : Triple) : dot (tau p) (tau q) =
    2 * p.x * q.x + p.y * q.y + 2 * p.z * q.z := by
  simp [dot, tau]
  ring

/--
@isnad1 id=eq.0h1v.s3.5d69006fa5c2 from=translated src=- shape=1d5062f3 vocab=eec3fe70
-/
@[simp] theorem qForm_tau (p : Triple) : dot (tau p) (tau p) = qForm p := by
  simp [qForm]
  ring

/--
@isnad1 id=eq.0h2v.s4.339221748871 from=translated src=- shape=f66dca04 vocab=7f9ba52b
-/
theorem dot_cross_self_left (p q : Triple) : dot p (cross p q) = 0 := by
  simp [dot, cross]
  ring

/--
@isnad1 id=eq.0h2v.s4.b2ffa1562610 from=translated src=- shape=5c2623a4 vocab=7f9ba52b
-/
theorem dot_cross_self_right (p q : Triple) : dot q (cross p q) = 0 := by
  simp [dot, cross]
  ring

/--
@isnad1 id=eq.0h2v.s5.dc28acabcf08 from=translated src=- shape=efac3a1b vocab=5fcb2737
-/
theorem lagrange_identity (p q : Triple) :
    dot (cross p q) (cross p q) = dot p p * dot q q - dot p q ^ 2 := by
  simp [dot, cross]
  ring

/--
@isnad1 id=eq.0h4v.s5.dd206df9defc from=translated src=- shape=7a010364 vocab=bf981a29
-/
theorem cramer_identity (r e₁ e₂ z : Triple) :
    linComb3 (dot r (cross e₂ z)) (dot r (cross z e₁))
      (dot r (cross e₁ e₂)) e₁ e₂ z =
      vsmul (det3 e₁ e₂ z) r := by
  apply Triple.ext <;> simp [linComb3, vadd, vsmul, det3, dot, cross] <;> ring

/--
@isnad1 id=eq.0h6v.s5.5de9ae645bab from=translated src=- shape=a098734a vocab=042f35ee
-/
theorem dot_linComb3_cross_e₂_z (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross e₂ z) = a * det3 e₁ e₂ z := by
  simp [linComb3, vadd, vsmul, det3, dot, cross]
  ring

/--
@isnad1 id=eq.0h6v.s5.3ffbe9c99fd9 from=translated src=- shape=b984a338 vocab=042f35ee
-/
theorem dot_linComb3_cross_z_e₁ (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross z e₁) = b * det3 e₁ e₂ z := by
  simp [linComb3, vadd, vsmul, det3, dot, cross]
  ring

/--
@isnad1 id=eq.0h6v.s5.1379b2e26544 from=translated src=- shape=562a49c3 vocab=042f35ee
-/
theorem dot_linComb3_cross_e₁_e₂ (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross e₁ e₂) = c * det3 e₁ e₂ z := by
  simp [linComb3, vadd, vsmul, det3, dot, cross]
  ring

/--
@isnad1 id=eq.0h3v.s7.d5fa36e1459d from=translated src=- shape=e72752a3 vocab=dc5ef75c
-/
theorem gram_cubic_identity_general (e₁ e₂ z : Triple) :
    dot e₁ e₁ * dot e₂ e₂ * dot z z +
      2 * dot e₁ e₂ * dot z e₁ * dot z e₂ -
      dot e₁ e₁ * dot z e₂ ^ 2 -
      dot e₂ e₂ * dot z e₁ ^ 2 -
      dot e₁ e₂ ^ 2 * dot z z = det3 e₁ e₂ z ^ 2 := by
  simp [dot, det3, cross]
  ring

structure OrthogonalFrame (p : Triple) where
  e₁ : Triple
  e₂ : Triple
  z : Triple
  cross_eq : cross e₁ e₂ = p
  bezout : dot p z = 1

namespace OrthogonalFrame

variable {p : Triple} (F : OrthogonalFrame p)

/--
@isnad1 id=eq.0h2v.s4.d7a4efa34ab5 from=translated src=- shape=13b926ad vocab=d608427d
-/
theorem det_eq_one : det3 F.e₁ F.e₂ F.z = 1 := by
  rw [det3, F.cross_eq]
  exact F.bezout

/--
@isnad1 id=eq.0h2v.s4.2ce8126e5eda from=translated src=- shape=b9731c66 vocab=4590af5a
-/
theorem e₁_orthogonal : dot p F.e₁ = 0 := by
  have h := dot_cross_self_left F.e₁ F.e₂
  rw [F.cross_eq] at h
  calc
    dot p F.e₁ = dot F.e₁ p := dot_comm _ _
    _ = 0 := h

/--
@isnad1 id=eq.0h2v.s4.bf3bd35e89d7 from=translated src=- shape=b9731c66 vocab=78dfd10d
-/
theorem e₂_orthogonal : dot p F.e₂ = 0 := by
  have h := dot_cross_self_right F.e₁ F.e₂
  rw [F.cross_eq] at h
  calc
    dot p F.e₂ = dot F.e₂ p := dot_comm _ _
    _ = 0 := h

/--
@isnad1 id=eq.0h2v.s5.da080f05d47f from=translated src=- shape=695b556c vocab=304d0ede
-/
theorem gram_det :
    dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2 = dot p p := by
  have h := lagrange_identity F.e₁ F.e₂
  rw [F.cross_eq] at h
  exact h.symm

def coeff₁ (r : Triple) : ℤ := dot r (cross F.e₂ F.z)

def coeff₂ (r : Triple) : ℤ := dot r (cross F.z F.e₁)

def coeffZ (r : Triple) : ℤ := dot r p

/--
@isnad1 id=eq.0h3v.s4.0e161d74f670 from=translated src=- shape=1858ab94 vocab=4d0cbd9d
-/
theorem decompose (r : Triple) :
    linComb3 (F.coeff₁ r) (F.coeff₂ r) (coeffZ (p := p) r) F.e₁ F.e₂ F.z = r := by
  have h := cramer_identity r F.e₁ F.e₂ F.z
  rw [F.cross_eq, F.det_eq_one] at h
  simpa [coeff₁, coeff₂, coeffZ, vsmul] using h

/--
@isnad1 id=injectiv.0h2v.s5.8319ef3255c4 from=translated src=- shape=003b6c39 vocab=ccd6d7e7
-/
theorem linComb3_injective :
    Function.Injective (fun abc : ℤ × ℤ × ℤ =>
      linComb3 abc.1 abc.2.1 abc.2.2 F.e₁ F.e₂ F.z) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only at h
  have ha := congrArg (fun r => dot r (cross F.e₂ F.z)) h
  have hb := congrArg (fun r => dot r (cross F.z F.e₁)) h
  have hc := congrArg (fun r => dot r (cross F.e₁ F.e₂)) h
  simp only [dot_linComb3_cross_e₂_z, dot_linComb3_cross_z_e₁,
    dot_linComb3_cross_e₁_e₂, F.det_eq_one, mul_one] at ha hb hc
  subst ha; subst hb; subst hc; rfl

/-- Lemma 5.2: integral solutions of `p·r=t` are uniquely parametrized by
`r=t z+a e₁+b e₂`.
@isnad1 id=existsun.1h4v.s5.8511655757a5 from=translated src=- shape=3cbd4767 vocab=49aee67d
-/
theorem affine_coset (t : ℤ) (r : Triple) (hr : dot p r = t) :
    ∃! ab : ℤ × ℤ,
      r = linComb3 ab.1 ab.2 t F.e₁ F.e₂ F.z := by
  refine ⟨⟨F.coeff₁ r, F.coeff₂ r⟩, ?_, ?_⟩
  · have hd := F.decompose r
    have hcoeff : coeffZ (p := p) r = t := by
      rw [coeffZ, dot_comm, hr]
    rw [hcoeff] at hd
    exact hd.symm
  · rintro ⟨a, b⟩ hab
    have hcoeff : coeffZ (p := p) r = t := by
      rw [coeffZ, dot_comm, hr]
    have hrepr :
        r = linComb3 (F.coeff₁ r) (F.coeff₂ r) t F.e₁ F.e₂ F.z := by
      simpa [hcoeff] using (F.decompose r).symm
    have hlin :
        linComb3 a b t F.e₁ F.e₂ F.z =
          linComb3 (F.coeff₁ r) (F.coeff₂ r) t F.e₁ F.e₂ F.z := by
      exact hab.symm.trans hrepr
    have habc : (a, (b, t)) = (F.coeff₁ r, (F.coeff₂ r, t)) :=
      F.linComb3_injective hlin
    exact congrArg (fun abc : ℤ × ℤ × ℤ => (abc.1, abc.2.1)) habc

/--
@isnad1 id=eq.0h5v.s8.a32d8ea98db2 from=translated src=- shape=6eb8e18a vocab=de13f17e
-/
theorem affine_norm_expansion (t a b : ℤ) :
    dot (linComb3 a b t F.e₁ F.e₂ F.z)
      (linComb3 a b t F.e₁ F.e₂ F.z) =
      dot F.e₁ F.e₁ * a ^ 2 +
      2 * (dot F.e₁ F.e₂ * b + t * dot F.z F.e₁) * a +
      dot F.e₂ F.e₂ * b ^ 2 +
      2 * t * dot F.z F.e₂ * b + t ^ 2 * dot F.z F.z := by
  simp [linComb3, vadd, vsmul, dot]
  ring

/--
@isnad1 id=other.0h2v.s7.e16c06a56b8e from=translated src=- shape=6d0003fc vocab=8a32bdb9
-/
theorem gram_cubic_identity :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let γ := dot F.e₂ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    α * γ * ζ + 2 * β * δ * ε - α * ε ^ 2 - γ * δ ^ 2 - β ^ 2 * ζ = 1 := by
  dsimp
  rw [gram_cubic_identity_general, F.det_eq_one]
  norm_num

/--
@isnad1 id=other.0h2v.s7.26746e7976ef from=translated src=- shape=a6f848ad vocab=a015b754
-/
theorem short_identity_aux :
    let α := dot F.e₁ F.e₁
    let β := dot F.e₁ F.e₂
    let δ := dot F.z F.e₁
    let ε := dot F.z F.e₂
    let ζ := dot F.z F.z
    let n := dot p p
    let K := β * δ - α * ε
    K ^ 2 + n * (δ ^ 2 - α * ζ) = -α := by
  dsimp
  have hg := F.gram_det
  have hc := F.gram_cubic_identity
  dsimp at hc
  calc
    (dot F.e₁ F.e₂ * dot F.z F.e₁ - dot F.e₁ F.e₁ * dot F.z F.e₂) ^ 2 +
        dot p p * (dot F.z F.e₁ ^ 2 - dot F.e₁ F.e₁ * dot F.z F.z) =
      (dot F.e₁ F.e₂ * dot F.z F.e₁ - dot F.e₁ F.e₁ * dot F.z F.e₂) ^ 2 +
        (dot F.e₁ F.e₁ * dot F.e₂ F.e₂ - dot F.e₁ F.e₂ ^ 2) *
          (dot F.z F.e₁ ^ 2 - dot F.e₁ F.e₁ * dot F.z F.z) := by rw [hg]
    _ = -dot F.e₁ F.e₁ *
        (dot F.e₁ F.e₁ * dot F.e₂ F.e₂ * dot F.z F.z +
          2 * dot F.e₁ F.e₂ * dot F.z F.e₁ * dot F.z F.e₂ -
          dot F.e₁ F.e₁ * dot F.z F.e₂ ^ 2 -
          dot F.e₂ F.e₂ * dot F.z F.e₁ ^ 2 -
          dot F.e₁ F.e₂ ^ 2 * dot F.z F.z) := by ring
    _ = -dot F.e₁ F.e₁ := by rw [hc]; ring

end OrthogonalFrame

end TunnellMap
