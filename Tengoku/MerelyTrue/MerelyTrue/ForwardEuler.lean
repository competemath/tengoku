import Tengoku

/-!
# Forward Euler Method

We implement the explicit Euler method for ODEs and prove its
convergence.

## Generic infrastructure

- `piecewiseLinear`, `piecewiseConst`: Piecewise linear/constant
  interpolation on a regular grid.
- `locallyFinite_Icc_grid`: The regular grid is locally finite.
- `ContinuousOn.of_Icc_grid`: Cell-wise continuity implies
  continuity on `[a, ∞)`.

## Euler method

- `ODE.EulerMethod.step`, `ODE.EulerMethod.point`,
  `ODE.EulerMethod.slope`: The Euler iteration.
- `ODE.EulerMethod.path`, `ODE.EulerMethod.deriv`: Piecewise
  linear/constant interpolation of the Euler points.
- `ODE.EulerMethod.dist_deriv_le`: Global bound on the local
  truncation error.
- `ODE.EulerMethod.dist_path_le`: Error bound via Gronwall's
  inequality.
- `ODE.EulerMethod.tendsto_path`: Convergence as `h → 0⁺`.
-/

open Set Filter

/-! ## Grid helpers -/

variable {α : Type*} [Field α] [LinearOrder α] [FloorSemiring α] [IsStrictOrderedRing α]

/-- If `t ∈ [a + n * h, a + (n + 1) * h)` and `0 < h`, then `⌊(t - a) / h⌋₊ = n`. -/
theorem Nat.floor_div_eq_of_mem_Ico {h : α} (hh : 0 < h) {a : α}
    {n : ℕ} {t : α} (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    ⌊(t - a) / h⌋₊ = n := by
  refine Nat.floor_eq_on_Ico n _ ⟨?_, ?_⟩ <;>
    (first | rw [le_div_iff₀ hh] | rw [div_lt_iff₀ hh]) <;> linarith [ht.1, ht.2]

/-- If `0 < h` and `a ≤ t`, then `t` lies in the floor interval
`[a + ⌊(t - a) / h⌋₊ * h, a + (⌊(t - a) / h⌋₊ + 1) * h)`. -/
theorem mem_Ico_Nat_floor_div {h : α} (hh : 0 < h) {a t : α} (hat : a ≤ t) :
    t ∈ Ico (a + ⌊(t - a) / h⌋₊ * h) (a + (↑⌊(t - a) / h⌋₊ + 1) * h) := by
  constructor <;> nlinarith [Nat.floor_le (div_nonneg (sub_nonneg.mpr hat) hh.le),
    Nat.lt_floor_add_one ((t - a) / h), mul_div_cancel₀ (t - a) hh.ne']

/-! ## Piecewise linear interpolation -/

/-- The piecewise linear interpolation of a sequence `y` with slopes `c` on a regular grid
with step size `h` starting at `a`. On `[a + n * h, a + (n + 1) * h)`, the value is
`y n + (t - (a + n * h)) • c n`. -/
noncomputable def piecewiseLinear {E : Type*} [AddCommGroup E] [Module α E]
    (y : ℕ → E) (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  let n := ⌊(t - a) / h⌋₊
  y n + (t - (a + n * h)) • c n

/-- The piecewise constant function taking value `c n` on `[a + n * h, a + (n + 1) * h)`. -/
noncomputable def piecewiseConst {E : Type*} (c : ℕ → E) (h : α) (a : α) (t : α) : E :=
  c ⌊(t - a) / h⌋₊

/-- The piecewise constant function equals `c n` on `[a + n * h, a + (n + 1) * h)`. -/
theorem piecewiseConst_eq_on_Ico {E : Type*} {c : ℕ → E} {h : α} {a : α}
    (hh : 0 < h) {n : ℕ} {t : α}
    (ht : t ∈ Ico (a + n * h) (a + (n + 1) * h)) :
    piecewiseConst c h a t = c n := by
  simp [piecewiseConst, Nat.floor_div_eq_of_mem_Ico hh ht]

variable [TopologicalSpace α] [OrderTopology α]

/-- The regular grid of closed intervals `[a + n * h, a + (n + 1) * h]` is locally finite. -/
theorem locallyFinite_Icc_grid {h : α} (hh : 0 < h) (a : α) :
    LocallyFinite fun n : ℕ => Icc (a + n * h) (a + (↑n + 1) * h) := by
  intro x
  refine ⟨Ioo (x - h) (x + h), Ioo_mem_nhds (by linarith) (by linarith),
    (finite_Icc (⌊(x - h - a) / h⌋₊) (⌈(x + h - a) / h⌉₊)).subset ?_⟩
  rintro n ⟨z, ⟨hz1, hz2⟩, hz3, hz4⟩
  refine ⟨Nat.lt_add_one_iff.mp ((Nat.floor_lt' (by linarith)).mpr ?_),
    Nat.cast_le.mp ((?_ : (n : α) ≤ _).trans (Nat.le_ceil _))⟩ <;>
    (first | rw [div_lt_iff₀ hh] | rw [le_div_iff₀ hh]) <;> push_cast <;> nlinarith

/-- A function continuous on each cell `[a + n * h, a + (n + 1) * h]` is continuous
on `[a, ∞)`. -/
theorem ContinuousOn.of_Icc_grid {F : Type*} [TopologicalSpace F]
    {f : α → F} {h : α} (hh : 0 < h) {a : α}
    (hf : ∀ n : ℕ, ContinuousOn f (Icc (a + n * h) (a + (n + 1) * h))) :
    ContinuousOn f (Ici a) :=
  ((locallyFinite_Icc_grid hh a).continuousOn_iUnion (fun _ => isClosed_Icc) (hf ·)).mono
    fun t (hat : a ≤ t) =>
      mem_iUnion.mpr ⟨_, Ico_subset_Icc_self (mem_Ico_Nat_floor_div hh hat)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {y : ℕ → E} {c : ℕ → E} {h : ℝ} {a : ℝ}

/-! ## Euler method -/

namespace ODE.EulerMethod

/-- A single step of the explicit Euler method: `y + h • v(t, y)`. -/
def step {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t : 𝕜) (y : E) : E :=
  y + h • v t y

/-- The sequence of Euler points, defined recursively:
`point v h t₀ y₀ 0 = y₀` and `point v h t₀ y₀ (n+1) = step v h (t₀ + n*h) (point v h t₀ y₀ n)`.
-/
def point {𝕜 : Type*} {E : Type*} [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
    (v : 𝕜 → E → E) (h : 𝕜) (t₀ : 𝕜) (y₀ : E) : ℕ → E
  | 0 => y₀
  | n + 1 => step v h (t₀ + n * h) (point v h t₀ y₀ n)

/-- The slope of the Euler method on the `n`-th cell: `v(t₀ + n * h, yₙ)`. -/
noncomputable def slope (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) (n : ℕ) : E :=
  v (t₀ + n * h) (point v h t₀ y₀ n)

/-- The piecewise linear Euler path, interpolating the Euler points with Euler slopes. -/
noncomputable def path (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseLinear (point v h t₀ y₀) (slope v h t₀ y₀) h t₀

/-- The piecewise constant right derivative of the Euler path. -/
noncomputable def deriv (v : ℝ → E → E) (h : ℝ) (t₀ : ℝ) (y₀ : E) : ℝ → E :=
  piecewiseConst (slope v h t₀ y₀) h t₀

variable {v : ℝ → E → E} {K L : NNReal} {M : ℝ}
  (hv : ∀ t, LipschitzWith K (v t))
  (hvt : ∀ y, LipschitzWith L (fun t => v t y))
  (hM : ∀ t y, ‖v t y‖ ≤ M)
include hv hvt hM

end ODE.EulerMethod
