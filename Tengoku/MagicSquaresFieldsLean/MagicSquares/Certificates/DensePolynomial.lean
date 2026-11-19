import Tengoku.MagicSquaresFieldsLean.MagicSquares.FieldTransport
import Tengoku.Seed.RingTheory.AdjoinRoot

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.Certificates.DensePolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Dense coefficients in increasing order, evaluated by Horner's rule.-/
def eval (h : R →+* S) (x : S) : List R → S
  | [] => 0
  | a :: p => h a + x * eval h x p

def add : List R → List R → List R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def neg (p : List R) : List R := p.map (- ·)
def sub (p q : List R) : List R := add p (neg q)
def scale (a : R) (p : List R) : List R := p.map (a * ·)
def mul : List R → List R → List R
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

@[simp] theorem eval_add (h : R →+* S) (x : S) (p q : List R) :
    eval h x (add p q) = eval h x p + eval h x q := by
  induction p generalizing q with
  | nil => simp [add, eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, eval]
    | cons b q => simp [add, eval, ih]; ring

@[simp] theorem eval_neg (h : R →+* S) (x : S) (p : List R) :
    eval h x (neg p) = -eval h x p := by
  induction p with
  | nil => simp [neg, eval]
  | cons a p ih => simp [neg, eval, neg] at ih ⊢; rw [ih]; ring

@[simp] theorem eval_sub (h : R →+* S) (x : S) (p q : List R) :
    eval h x (sub p q) = eval h x p - eval h x q := by simp [sub, sub_eq_add_neg]

@[simp] theorem eval_scale (h : R →+* S) (x : S) (a : R) (p : List R) :
    eval h x (scale a p) = h a * eval h x p := by
  induction p with
  | nil => simp [scale, eval]
  | cons b p ih => simp only [scale, List.map_cons, eval, map_mul] at ih ⊢; rw [ih]; ring

@[simp] theorem eval_mul (h : R →+* S) (x : S) (p q : List R) :
    eval h x (mul p q) = eval h x p * eval h x q := by
  induction p with
  | nil => simp [mul, eval]
  | cons a p ih => simp [mul, eval, ih]; ring

/-- Exact coefficient comparison; trailing zero coefficients are harmless.-/
def eqCheck [DecidableEq R] (p q : List R) : Bool :=
  (sub p q).all (fun a => decide (a = 0))

theorem eval_zero_of_all [DecidableEq R] (h : R →+* S) (x : S) (p : List R)
    (hp : p.all (fun a => decide (a = 0)) = true) : eval h x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hp
    simp [eval, hp.1, ih hp.2]

theorem eqCheck_sound [DecidableEq R] (h : R →+* S) (x : S) {p q : List R}
    (hc : eqCheck p q = true) : eval h x p = eval h x q := by
  have hz := eval_zero_of_all h x (sub p q) hc
  simpa only [eval_sub, sub_eq_zero] using hz

/-- Polynomial represented by the coefficient list.-/
noncomputable def poly (p : List R) : Polynomial R := eval Polynomial.C Polynomial.X p

@[simp] theorem eval_poly (h : R →+* S) (x : S) (p : List R) :
    Polynomial.eval₂ h x (poly p) = eval h x p := by
  induction p with
  | nil => simp [poly, eval]
  | cons a p ih => simpa [poly, eval] using congrArg (fun z => x * z) ih

end MagicSquares.Certificates.DensePolynomial
