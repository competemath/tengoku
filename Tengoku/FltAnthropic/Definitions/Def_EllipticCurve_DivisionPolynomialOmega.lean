import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Tengoku.Seed.Algebra.MvPolynomial.CommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Polynomial
open scoped Polynomial.Bivariate

noncomputable section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def ψDbl (n : ℤ) : R[X][Y] :=
  complEDS₂ W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

def twoω (n : ℤ) : R[X][Y] :=
  W.ψDbl n - W.ψ n * (C (C W.a₁) * W.φ n + C (C W.a₃) * W.ψ n ^ 2)

namespace Universal

abbrev Poly : Type := MvPolynomial (Fin 5) ℤ

def curve : WeierstrassCurve Poly :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

def specialize (W : WeierstrassCurve R) : Poly →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/--
@isnad1 id=eq.0h2v.s6.0ea585b0f0b0 from=translated src=- shape=508947fd vocab=a03c4dd0
-/
@[simp] lemma specialize_X_zero : specialize W (MvPolynomial.X 0) = W.a₁ := by simp [specialize]
/--
@isnad1 id=eq.0h2v.s6.29e2e3291d87 from=translated src=- shape=508947fd vocab=8c8cb63d
-/
@[simp] lemma specialize_X_one : specialize W (MvPolynomial.X 1) = W.a₂ := by simp [specialize]
/--
@isnad1 id=eq.0h2v.s6.badbdd29f03d from=translated src=- shape=508947fd vocab=c8c3cb8d
-/
@[simp] lemma specialize_X_two : specialize W (MvPolynomial.X 2) = W.a₃ := by simp [specialize]
/--
@isnad1 id=eq.0h2v.s6.f5de5a00431a from=translated src=- shape=508947fd vocab=0879b174
-/
@[simp] lemma specialize_X_three : specialize W (MvPolynomial.X 3) = W.a₄ := by simp [specialize]
/--
@isnad1 id=eq.0h2v.s6.d515e9b579d1 from=translated src=- shape=508947fd vocab=f29d451e
-/
@[simp] lemma specialize_X_four : specialize W (MvPolynomial.X 4) = W.a₆ := by simp [specialize]

/--
@isnad1 id=eq.0h2v.s5.a6247d34a56c from=translated src=- shape=b9656c4e vocab=b99d5cee
-/
lemma map_specialize : curve.map (specialize W) = W := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp [curve, specialize, WeierstrassCurve.map]

def halveCoeff (r : Poly) : Poly :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun z : ℤ => z / 2) (by simp) (AddMonoidAlgebra.coeff r))

/--
@isnad1 id=eq.0h0v.s6.e7d775a22b85 from=translated src=- shape=3c26ae4f vocab=eddcb20e
-/
@[simp] lemma halveCoeff_zero : halveCoeff 0 = 0 := by
  simp [halveCoeff]

/--
@isnad1 id=eq.0h2v.s5.6c1c5fbbc68e from=translated src=- shape=796c5b7e vocab=5ae79e36
-/
lemma coeff_halveCoeff (r : Poly) (m : Fin 5 →₀ ℕ) :
    MvPolynomial.coeff m (halveCoeff r) = MvPolynomial.coeff m r / 2 :=
  Finsupp.mapRange_apply (hf := by simp) ..

def halveX (p : Poly[X]) : Poly[X] :=
  ⟨AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange halveCoeff halveCoeff_zero)⟩

/--
@isnad1 id=eq.0h2v.s6.c6c027dd82a5 from=translated src=- shape=f53e208b vocab=df7f8a08
-/
@[simp] lemma coeff_halveX (p : Poly[X]) (i : ℕ) : (halveX p).coeff i = halveCoeff (p.coeff i) := by
  rcases p with ⟨f⟩
  simp [halveX, Polynomial.coeff]

/--
@isnad1 id=eq.0h0v.s7.ba4696430523 from=translated src=- shape=e467432f vocab=c3024b27
-/
@[simp] lemma halveX_zero : halveX 0 = 0 := by
  ext i
  simp

def halve (p : Poly[X][Y]) : Poly[X][Y] :=
  ⟨AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange halveX halveX_zero)⟩

/--
@isnad1 id=eq.0h2v.s7.8738fed7abdb from=translated src=- shape=5135710e vocab=31e2dd75
-/
@[simp] lemma coeff_halve (p : Poly[X][Y]) (i : ℕ) : (halve p).coeff i = halveX (p.coeff i) := by
  rcases p with ⟨f⟩
  simp [halve, Polynomial.coeff]

/--
@isnad1 id=eq.0h1v.s6.cb207a4271a3 from=translated src=- shape=20e71180 vocab=b14f8d2c
-/
lemma halveCoeff_two_mul (r : Poly) : halveCoeff (2 * r) = r := by
  ext m
  rw [coeff_halveCoeff, show (2 : Poly) = MvPolynomial.C 2 from (map_ofNat MvPolynomial.C 2).symm,
    MvPolynomial.coeff_C_mul]
  exact Int.mul_ediv_cancel_left _ two_ne_zero

/--
@isnad1 id=eq.0h1v.s8.76cd4172842d from=translated src=- shape=06a21e52 vocab=78031594
-/
lemma halveX_two_mul (p : Poly[X]) : halveX (2 * p) = p := by
  ext i
  rw [coeff_halveX, show (2 : Poly[X]) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    halveCoeff_two_mul]

/--
@isnad1 id=eq.0h1v.s9.007f309c8665 from=translated src=- shape=e9e787a2 vocab=97ce6e33
-/
lemma halve_two_mul (p : Poly[X][Y]) : halve (2 * p) = p := by
  ext i : 1
  rw [coeff_halve, show (2 : Poly[X][Y]) = C 2 from (map_ofNat C 2).symm, coeff_C_mul,
    halveX_two_mul]

end Universal

def ω (n : ℤ) : R[X][Y] :=
  (Universal.halve (Universal.curve.twoω n)).map (mapRingHom (Universal.specialize W))

/--
@isnad1 id=eq.0h3v.s7.baa261a8c901 from=translated src=- shape=c7fc93ae vocab=89068d57
-/
lemma ψ_mul_ψDbl (n : ℤ) : W.ψ n * W.ψDbl n = W.ψ (2 * n) :=
  normEDS_mul_complEDS₂ ..

section Map

variable {S : Type*} [CommRing S] (f : R →+* S)

/--
@isnad1 id=eq.0h5v.s6.d8bbdbd874d2 from=translated src=- shape=055d400a vocab=fe3835d4
-/
lemma map_ψDbl (n : ℤ) : (W.map f).ψDbl n = (W.ψDbl n).map (mapRingHom f) := by
  rw [ψDbl, ψDbl, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄, coe_mapRingHom,
    map_C, map_C, coe_mapRingHom]

/--
@isnad1 id=eq.0h5v.s6.824a0392af26 from=translated src=- shape=055d400a vocab=5c3bf5d5
-/
lemma map_twoω (n : ℤ) : (W.map f).twoω n = (W.twoω n).map (mapRingHom f) := by
  simp only [twoω, map_ψDbl, map_ψ, map_φ, map_a₁, map_a₃, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_add, Polynomial.map_pow, map_C, coe_mapRingHom]

end Map

/--
@isnad1 id=eq.1h4v.s9.78299b02c292 from=translated src=- shape=1ceddf43 vocab=5996cb47
-/
lemma ω_eq_map_of_twoω_eq {n : ℤ} {q : Universal.Poly[X][Y]}
    (hq : Universal.curve.twoω n = 2 * q) :
    W.ω n = q.map (mapRingHom (Universal.specialize W)) := by
  rw [ω, hq, Universal.halve_two_mul]

/--
@isnad1 id=eq.1h4v.s9.53dd78d4bdaa from=translated src=- shape=e17d823e vocab=3d73aa24
-/
theorem two_mul_ω_of_twoω_universal_eq {n : ℤ} {q : Universal.Poly[X][Y]}
    (hq : Universal.curve.twoω n = 2 * q) : 2 * W.ω n = W.twoω n := by
  calc 2 * W.ω n = 2 * q.map (mapRingHom (Universal.specialize W)) := by
        rw [W.ω_eq_map_of_twoω_eq hq]
    _ = (2 * q).map (mapRingHom (Universal.specialize W)) := by
        rw [Polynomial.map_mul, Polynomial.map_ofNat]
    _ = (Universal.curve.map (Universal.specialize W)).twoω n := by rw [← hq, map_twoω]
    _ = W.twoω n := by rw [Universal.map_specialize]

end WeierstrassCurve

end
