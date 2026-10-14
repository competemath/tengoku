/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.LeanPool.LeanPool.CenteredMaximal.Statement

/-!
# The constants of the weighted lattice

The chosen configuration is the periodic measure with columns at `x = i * hgap`, carrying mass
`1` for even `i` and mass `heavy` for odd `i`, and rows at `y = j * vgap` of unit weight. Its
parameters are determined by three edge collisions of witness rectangles; they reduce to the single
quadratic `3 u² - 4 u - 6 = 0` for `u = root = (2 + √22)/3`:

* `heavy = u² - 1 = (17 + 4√22)/9`, so a light and a heavy atom together weigh `u²`;
* `hgap = (1 + u)/2 = (5 + √22)/6` and `vgap = hgap + 1 = (11 + √22)/6`.

The witness squares use the sides `1`, `u`, `sideH1 = √heavy`, `sideLH2 = √2 · u`,
`sideLHL2 = √(2 (2 + heavy))` and `2 hgap + 1`. The witnesses cover the period cell outside
four open slots, each of width `slotW` and height `slotH`, and
`phi = (2 hgap vgap - 4 slotW slotH) / (1 + heavy)`.

All numerical facts are proved from rational enclosures of `√2` and `√22`.
-/

@[expose] public section

noncomputable section

namespace LeanPool.CenteredMaximal.Lattice

/-- `u = (2 + √22)/3`, the positive root of `3u² - 4u - 6 = 0`. -/
def root : ℝ := (2 + √22) / 3

/-- The heavy mass `w = u² - 1 = (17 + 4√22)/9`. -/
def heavy : ℝ := root ^ 2 - 1

/-- The column spacing `h = (1 + u)/2 = (5 + √22)/6`. -/
def hgap : ℝ := (1 + root) / 2

/-- The row spacing `V = h + 1 = (11 + √22)/6`. -/
def vgap : ℝ := hgap + 1

/-- Side of the witness made of one heavy atom: `√w`. -/
def sideH1 : ℝ := √heavy

/-- Side of the witness made of a light and a heavy atom in two rows: `√(2(1 + w)) = √2 · u`. -/
def sideLH2 : ℝ := √2 * root

/-- Side of the witness made of light, heavy, light atoms in two rows: `√(2(2 + w))`. -/
def sideLHL2 : ℝ := √(2 * (2 + heavy))

/-- Width of a slot excluded from the witnessed region: `2h - √(2(2 + w))/2 - u/2`. -/
def slotW : ℝ := 2 * hgap - sideLHL2 / 2 - root / 2

/-- Height of a slot excluded from the witnessed region: `V - √(2(1 + w))/2 - √w/2`. -/
def slotH : ℝ := vgap - sideLH2 / 2 - sideH1 / 2

/-! ### Square roots -/

/--
@isnad1 id=eq.0h0v.s5.84741e25f163 from=translated src=- shape=424e5f08 vocab=2d61703d
-/
theorem sqrt22_sq : √22 ^ 2 = 22 := Real.sq_sqrt (by norm_num)

/-- Lower rational enclosure of `√22`.
@isnad1 id=lt.0h0v.s4.1efadcfd4585 from=translated src=- shape=8905eb1d vocab=18350630
-/
theorem sqrt22_gt : (4.69 : ℝ) < √22 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

/-- Upper rational enclosure of `√22`.
@isnad1 id=lt.0h0v.s4.6b4b9278da69 from=translated src=- shape=339e478a vocab=18350630
-/
theorem sqrt22_lt : √22 < (4.691 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-- Lower rational enclosure of `√2`.
@isnad1 id=lt.0h0v.s4.cbeab8bf9c35 from=translated src=- shape=8905eb1d vocab=18350630
-/
theorem sqrt2_gt : (1.414 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)

/-- Upper rational enclosure of `√2`.
@isnad1 id=lt.0h0v.s4.58a2047ce2ad from=translated src=- shape=339e478a vocab=18350630
-/
theorem sqrt2_lt : √2 < (1.4143 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

/-! ### Exact identities -/

/-- `3u² - 4u - 6 = 0`.
@isnad1 id=eq.0h0v.s6.833ba61b52ea from=translated src=- shape=d831db8d vocab=56662f80
-/
theorem root_quadratic : 3 * root ^ 2 - 4 * root - 6 = 0 := by
  unfold root
  linear_combination (1 / 3 : ℝ) * sqrt22_sq

/-- `u = 2h - 1`: the light–heavy one-row witness starts where the light atom's square ends.
@isnad1 id=eq.0h0v.s5.9cbb38b707b7 from=translated src=- shape=79d27617 vocab=5a9d175e
-/
theorem two_mul_hgap_sub_one : 2 * hgap - 1 = root := by
  unfold hgap
  ring

/-- A light and a heavy atom together weigh `u²`.
@isnad1 id=eq.0h0v.s5.1888ae94f5bd from=translated src=- shape=954f16a4 vocab=44b8159b
-/
theorem one_add_heavy : 1 + heavy = root ^ 2 := by
  unfold heavy
  ring

/-- `V = h + 1`.
@isnad1 id=eq.0h0v.s4.b9c34b6bdda2 from=translated src=- shape=2960861a vocab=7bcf980a
-/
theorem vgap_eq : vgap = hgap + 1 := rfl

/-- `w = (17 + 4√22)/9`.
@isnad1 id=eq.0h0v.s5.f37e2128681f from=translated src=- shape=89b5e36a vocab=e4ae5343
-/
theorem heavy_eq : heavy = (17 + 4 * √22) / 9 := by
  unfold heavy root
  linear_combination (1 / 9 : ℝ) * sqrt22_sq

/-- The side `2h + 1` of the heavy–light–heavy two-row witness squares to its mass.
@isnad1 id=eq.0h0v.s6.27e2dba341fb from=translated src=- shape=60a3cf29 vocab=d675a43a
-/
theorem two_mul_hgap_add_one_sq : (2 * hgap + 1) ^ 2 = 2 * (heavy + 1 + heavy) := by
  unfold hgap heavy
  linear_combination (-1 : ℝ) * root_quadratic

/-! ### Numerical facts -/

/--
@isnad1 id=lt.0h0v.s3.c51b2806c213 from=translated src=- shape=a948b8aa vocab=8834485a
-/
theorem root_gt : (2.23 : ℝ) < root := by
  unfold root
  linarith [sqrt22_gt]

/-- Upper enclosure of `u`.
@isnad1 id=lt.0h0v.s3.1019c21d7a97 from=translated src=- shape=425298da vocab=8834485a
-/
theorem root_lt : root < (2.2304 : ℝ) := by
  unfold root
  linarith [sqrt22_lt]

/-- `1 ≤ u`, so the light–heavy one-row witness has side at least `1`.
@isnad1 id=le.0h0v.s3.32627adc0b58 from=translated src=- shape=ff3a10fc vocab=4985a1fb
-/
theorem one_le_root : 1 ≤ root := by
  linarith [root_gt]

/-- Lower enclosure of `w`.
@isnad1 id=lt.0h0v.s3.1a5f39749568 from=translated src=- shape=a948b8aa vocab=625dbcb5
-/
theorem heavy_gt : (3.9729 : ℝ) < heavy := by
  unfold heavy
  nlinarith [root_gt]

/-- Upper enclosure of `w`.
@isnad1 id=lt.0h0v.s3.ff618664097d from=translated src=- shape=425298da vocab=625dbcb5
-/
theorem heavy_lt : heavy < (3.9747 : ℝ) := by
  unfold heavy
  nlinarith [root_gt, root_lt]

/-- The heavy mass is positive.
@isnad1 id=lt.0h0v.s3.f7cadec80686 from=translated src=- shape=ff3a10fc vocab=600d3950
-/
theorem heavy_pos : 0 < heavy := by
  linarith [heavy_gt]

/-- Lower enclosure of `h`.
@isnad1 id=lt.0h0v.s3.9455fee0709c from=translated src=- shape=a948b8aa vocab=b1a0e2cb
-/
theorem hgap_gt : (1.615 : ℝ) < hgap := by
  unfold hgap
  linarith [root_gt]

/-- Upper enclosure of `h`.
@isnad1 id=lt.0h0v.s3.bf73a4d5a3e5 from=translated src=- shape=425298da vocab=b1a0e2cb
-/
theorem hgap_lt : hgap < (1.6152 : ℝ) := by
  unfold hgap
  linarith [root_lt]

/-- The column spacing is positive.
@isnad1 id=lt.0h0v.s3.80ec5928efbf from=translated src=- shape=ff3a10fc vocab=e3027ad9
-/
theorem hgap_pos : 0 < hgap := by
  linarith [hgap_gt]

/-- Lower enclosure of `V`.
@isnad1 id=lt.0h0v.s3.cac9a292af2d from=translated src=- shape=a948b8aa vocab=0734d06c
-/
theorem vgap_gt : (2.615 : ℝ) < vgap := by
  unfold vgap
  linarith [hgap_gt]

/-- Upper enclosure of `V`.
@isnad1 id=lt.0h0v.s3.da5a2505f4e6 from=translated src=- shape=425298da vocab=0734d06c
-/
theorem vgap_lt : vgap < (2.6152 : ℝ) := by
  unfold vgap
  linarith [hgap_lt]

/-- The light–heavy two-row witness squares to its mass `2(1 + w)`.
@isnad1 id=eq.0h0v.s5.63dc6546f922 from=translated src=- shape=19d7495d vocab=f571123e
-/
theorem sideLH2_sq : sideLH2 ^ 2 = 2 * (1 + heavy) := by
  rw [sideLH2, mul_pow, Real.sq_sqrt (by norm_num), one_add_heavy]

/-- The one-heavy-atom witness squares to its mass `w`.
@isnad1 id=eq.0h0v.s4.08842a5c9bf7 from=translated src=- shape=f23f23a3 vocab=29cd8f55
-/
theorem sideH1_sq : sideH1 ^ 2 = heavy :=
  Real.sq_sqrt heavy_pos.le

/-- The light–heavy–light two-row witness squares to its mass `2(2 + w)`.
@isnad1 id=eq.0h0v.s5.4f1efc437fae from=translated src=- shape=536fdbe5 vocab=b5f1cf27
-/
theorem sideLHL2_sq : sideLHL2 ^ 2 = 2 * (1 + heavy + 1) := by
  rw [sideLHL2, Real.sq_sqrt (by linarith [heavy_pos])]
  ring

/-- Lower enclosure of `√2 u`.
@isnad1 id=lt.0h0v.s3.d86620f96acc from=translated src=- shape=a948b8aa vocab=8d2f4e08
-/
theorem sideLH2_gt : (3.153 : ℝ) < sideLH2 := by
  unfold sideLH2
  nlinarith [sqrt2_gt, root_gt]

/-- Upper enclosure of `√2 u`.
@isnad1 id=lt.0h0v.s3.17c8bf57ce9d from=translated src=- shape=425298da vocab=8d2f4e08
-/
theorem sideLH2_lt : sideLH2 < (3.1545 : ℝ) := by
  unfold sideLH2
  nlinarith [sqrt2_lt, sqrt2_gt, root_lt, root_gt]

/-- Lower enclosure of `√w`.
@isnad1 id=lt.0h0v.s3.aeb05936e9d5 from=translated src=- shape=a948b8aa vocab=b9b63549
-/
theorem sideH1_gt : (1.99 : ℝ) < sideH1 :=
  (Real.lt_sqrt (by norm_num)).2 (by linarith [heavy_gt])

/-- Upper enclosure of `√w`.
@isnad1 id=lt.0h0v.s3.667f7ec43ee3 from=translated src=- shape=425298da vocab=b9b63549
-/
theorem sideH1_lt : sideH1 < (1.994 : ℝ) :=
  (Real.sqrt_lt' (by norm_num)).2 (by linarith [heavy_lt])

/-- Lower enclosure of `√(2(2 + w))`.
@isnad1 id=lt.0h0v.s3.9962dfcca8ea from=translated src=- shape=a948b8aa vocab=9974968d
-/
theorem sideLHL2_gt : (3.45 : ℝ) < sideLHL2 :=
  (Real.lt_sqrt (by norm_num)).2 (by linarith [heavy_gt])

/-- Upper enclosure of `√(2(2 + w))`.
@isnad1 id=lt.0h0v.s3.5d0817eac229 from=translated src=- shape=425298da vocab=9974968d
-/
theorem sideLHL2_lt : sideLHL2 < (3.457 : ℝ) :=
  (Real.sqrt_lt' (by norm_num)).2 (by linarith [heavy_lt])

/-- `1 ≤ √w`: the heavy atom's square reaches back to the light–heavy one-row region.
@isnad1 id=le.0h0v.s3.173179dca9b3 from=translated src=- shape=ff3a10fc vocab=05747390
-/
theorem one_le_sideH1 : 1 ≤ sideH1 := by
  linarith [sideH1_gt]

/-- `u ≤ √2 u`: the light–heavy two-row witness is wider than the one-row one.
@isnad1 id=le.0h0v.s2.2ec448c2b402 from=translated src=- shape=54c8eceb vocab=7c80e0bc
-/
theorem root_le_sideLH2 : root ≤ sideLH2 := by
  unfold sideLH2
  nlinarith [sqrt2_gt, root_gt]

/-- `V ≤ √2 u`: the light–heavy two-row witness reaches the middle line `y = V/2`.
@isnad1 id=le.0h0v.s2.8acec91bacf3 from=translated src=- shape=54c8eceb vocab=b256658d
-/
theorem vgap_le_sideLH2 : vgap ≤ sideLH2 := by
  linarith [vgap_lt, sideLH2_gt]

/-- `2V ≤ u + √2 u`: above the one-row witness the two-row witness takes over.
@isnad1 id=le.0h0v.s4.fb53ea4e9368 from=translated src=- shape=1b42f84e vocab=def441d0
-/
theorem two_mul_vgap_le_root_add_sideLH2 : 2 * vgap ≤ root + sideLH2 := by
  linarith [vgap_lt, sideLH2_gt, root_gt]

/-- `2h ≤ √(2(2 + w))`: the light–heavy–light witness reaches the heavy column.
@isnad1 id=le.0h0v.s4.44f666145f5b from=translated src=- shape=e4de06d0 vocab=a8abed67
-/
theorem two_mul_hgap_le_sideLHL2 : 2 * hgap ≤ sideLHL2 := by
  linarith [hgap_lt, sideLHL2_gt]

/-- `V ≤ √(2(2 + w))`: the light–heavy–light witness reaches the middle line `y = V/2`.
@isnad1 id=le.0h0v.s2.e1f70da00858 from=translated src=- shape=54c8eceb vocab=06194388
-/
theorem vgap_le_sideLHL2 : vgap ≤ sideLHL2 := by
  linarith [vgap_lt, sideLHL2_gt]

/-- `2V - √(2(2 + w)) ≤ √w`: next to the heavy column the two witnesses overlap.
@isnad1 id=le.0h0v.s4.198b90d176cb from=translated src=- shape=f84d9e1d vocab=3cb10cce
-/
theorem vgap_sub_le_sideH1 : 2 * vgap - sideLHL2 ≤ sideH1 := by
  linarith [vgap_lt, sideLHL2_gt, sideH1_gt]

/-- `4h - √(2(2 + w)) ≤ √2 u`: left of the heavy column the two-row witnesses overlap.
@isnad1 id=le.0h0v.s4.fd42e6431f74 from=translated src=- shape=f84d9e1d vocab=92de4c73
-/
theorem four_mul_hgap_sub_le_sideLH2 : 4 * hgap - sideLHL2 ≤ sideLH2 := by
  linarith [hgap_lt, sideLHL2_gt, sideLH2_gt]

/-- The slot has positive width.
@isnad1 id=lt.0h0v.s3.b5fbc66daaad from=translated src=- shape=ff3a10fc vocab=c8a2d1e5
-/
theorem slotW_pos : 0 < slotW := by
  unfold slotW
  linarith [hgap_gt, sideLHL2_lt, root_lt]

/-- The slot has positive height.
@isnad1 id=lt.0h0v.s3.64c07323c8de from=translated src=- shape=ff3a10fc vocab=14df40f9
-/
theorem slotH_pos : 0 < slotH := by
  unfold slotH
  linarith [vgap_gt, sideLH2_lt, sideH1_lt]

/-! ### The closed form of `Φ` -/

/--
@isnad1 id=eq.0h0v.s5.0cf5ab3a2094 from=translated src=- shape=d22c8324 vocab=733e2c61
-/
theorem sqrt2_mul_sqrt22 : √2 * √22 = 2 * √11 := by
  rw [← Real.sqrt_mul (by norm_num), show (2 : ℝ) * 22 = 2 ^ 2 * 11 by norm_num,
    Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- `√(x/9) = √x / 3`.
@isnad1 id=eq.1h1v.s5.b843c41015d2 from=translated src=- shape=780b6097 vocab=461ca6a7
-/
theorem sqrt_div_nine {x : ℝ} (hx : 0 ≤ x) : √(x / 9) = √x / 3 := by
  rw [Real.sqrt_div hx, show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `√2 u = (2√2 + 2√11)/3`.
@isnad1 id=eq.0h0v.s6.3e5034b3a809 from=translated src=- shape=03f27757 vocab=79b35b44
-/
theorem sideLH2_eq : sideLH2 = (2 * √2 + 2 * √11) / 3 := by
  rw [sideLH2, root, ← sqrt2_mul_sqrt22]
  ring

/-- `√w = √(17 + 4√22)/3`.
@isnad1 id=eq.0h0v.s5.18875111fc82 from=translated src=- shape=3e8937af vocab=74519cdc
-/
theorem sideH1_eq : sideH1 = √(17 + 4 * √22) / 3 := by
  rw [sideH1, heavy_eq, sqrt_div_nine (by positivity)]

/-- `√(2(2 + w)) = √(70 + 8√22)/3`.
@isnad1 id=eq.0h0v.s5.827f7c0366ea from=translated src=- shape=3e8937af vocab=05850b4e
-/
theorem sideLHL2_eq : sideLHL2 = √(70 + 8 * √22) / 3 := by
  rw [sideLHL2, heavy_eq, ← sqrt_div_nine (by positivity)]
  ring_nf

/-- The slot width in radicals.
@isnad1 id=eq.0h0v.s6.46bbb6ca25e0 from=translated src=- shape=2397f095 vocab=a9db005a
-/
theorem slotW_eq : slotW = (8 + √22 - √(70 + 8 * √22)) / 6 := by
  rw [slotW, sideLHL2_eq, hgap, root]
  ring

/-- The slot height in radicals.
@isnad1 id=eq.0h0v.s7.dc255335f49c from=translated src=- shape=ca681eff vocab=b415973c
-/
theorem slotH_eq : slotH = (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22)) / 6 := by
  rw [slotH, sideLH2_eq, sideH1_eq, vgap, hgap, root]
  ring

/-- The mass per period cell in radicals.
@isnad1 id=eq.0h0v.s6.8aadc40b44c0 from=translated src=- shape=a73f0af7 vocab=e4ae5343
-/
theorem one_add_heavy_eq : 1 + heavy = (26 + 4 * √22) / 9 := by
  rw [heavy_eq]
  ring

/-- The area of the period cell in radicals.
@isnad1 id=eq.0h0v.s6.5c7b97f56377 from=translated src=- shape=89ff43f1 vocab=4c9282a5
-/
theorem two_mul_hgap_mul_vgap : 2 * hgap * vgap = (77 + 16 * √22) / 18 := by
  unfold vgap hgap root
  linear_combination (1 / 18 : ℝ) * sqrt22_sq

/-- The expression for `Φ` used in the area lower bound: subtract the four slot areas
`slotW · slotH` from the cell area `2 h V`, then divide by the cell mass `1 + w`.
@isnad1 id=eq.0h0v.s6.9603cbe05d49 from=translated src=- shape=73e2f267 vocab=b2181b40
-/
theorem phi_eq : phi = (2 * hgap * vgap - 4 * slotW * slotH) / (1 + heavy) := by
  rw [phi, mul_assoc 4, slotW_eq, slotH_eq, one_add_heavy_eq, two_mul_hgap_mul_vgap]
  have h₁ : (0 : ℝ) < 26 + 4 * √22 := by positivity
  field_simp
  ring

end LeanPool.CenteredMaximal.Lattice
