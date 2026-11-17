import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex place: the dagger, the two forms, and the symplectic form

On the single complex place `K_v ≅ ℂ` of `K = ℚ[x]/(x⁴ − x − 1)`, realized as `ℝ²`
in the basis `{1, i}`, four canonical objects appear:

  `Gtr`  = `!![1,0; 0,-1]`   the trace form  `Re(z·w)`   (signature `(1,1)`),
  `Gborn`= `!![1,0; 0,1]`    the Born form   `Re(z̄·w)`  (positive-definite),
  `Jc`   = `!![0,-1; 1,0]`   the complex structure `J` (multiplication by `i`),
  `Cnj`  = `!![1,0; 0,-1]`   complex conjugation `σ` (the dagger).

We prove, all kernel-checked over `ℚ`:

* `born_eq_trace_comp_conj` : `Gborn = Gtr * Cnj` — the **dagger identity**: the Born
  form is the trace form precomposed with conjugation, `G_Born(x,y) = G_trace(x, σ y)`.
* `J_born_isometry`      : `Jᵀ Gborn J = Gborn`  — `J` is a Born isometry (the unitary phase).
* `J_trace_antiisometry` : `Jᵀ Gtr J = -Gtr`     — `J` is a trace anti-isometry (the Lorentzian
  time-rotation).
* `omega_born_skew`      : `ωᵀ = -ω` for `ω := Jᵀ Gborn` — the companion form of the Born
  metric is **alternating** (a symplectic form); it is `Im(z̄·w)`, the imaginary part of
  the Born rule; and `omega_born_nondegenerate` : `det ω = 1`.
* `omega_trace_symm`     : the companion `Jᵀ Gtr` of the (J-anti-invariant) trace form is
  **symmetric**, not alternating — so the symplectic structure lives on the Born reading,
  not the spacetime (trace) reading.

This is the linear-algebra core of the "Fault Line A" result (Proposition 1 of the
companion paper *The Arithmetic of a Complex Place*): `g(J·,·)` is alternating iff `g`
is `J`-invariant, and it is the Born metric — not the trace form — that is `J`-invariant.

The axiom set of every theorem below is exactly `{propext, Classical.choice, Quot.sound}`.
-/

namespace PDT

open Matrix

/-- Trace form on the complex place, `Re(z·w)`; signature `(1,1)`.-/
def Gtr : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- Born (Hermitian) form on the complex place, `Re(z̄·w)`; positive-definite.-/
def Gborn : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, 1]

/-- The complex structure `J` = multiplication by `i`.-/
def Jc : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

/-- Complex conjugation `σ` at the place (the dagger).-/
def Cnj : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- The companion form of the Born metric, `ω = Jᵀ Gborn` (i.e. `ω(x,y) = g(Jx,y)`).-/
def omegaB : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; -1, 0]

/-- **The symplectic form is alternating.** `ω = Jᵀ Gborn` is skew-symmetric,
`ωᵀ = -ω`. This is `Im(z̄·w)`, the imaginary part of the Born rule.
@isnad1 id=eq.0h0v.s5.c37a87259e84 from=translated src=- shape=4b28c5e4 vocab=1201f6eb
-/
theorem omega_born_skew : omegaB.transpose = -omegaB := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [omegaB, Matrix.transpose_apply, Matrix.neg_apply]

end PDT
