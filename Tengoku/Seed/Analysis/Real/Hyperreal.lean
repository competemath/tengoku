/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Violeta Hernández Palacios
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Order.Ring.StandardPart
public import Tengoku.Seed.Order.Filter.FilterProduct
public import Tengoku.Seed.Algebra.Order.Module.Field
public import Tengoku.Seed.Data.EReal.Inv
public import Tengoku.Seed.Topology.Algebra.InfiniteSum.Order
public import Tengoku.Seed.Topology.MetricSpace.Bounded

/-!
# Construction of the hyperreal numbers as an ultraproduct of real sequences

We define the `Hyperreal` numbers as quotients of sequences `ℕ → ℝ` by an ultrafilter. These form
a field, and we prove some of their basic properties.

Note that most of the machinery that is usually defined for the specific purpose of non-standard
analysis (infinitesimal and infinite elements, standard parts) has been generalized to other
non-archimedean fields. In particular:

- `ArchimedeanClass` can be used to measure whether an element is infinitesimal (`0 < mk x`) or
  infinite (`mk x < 0`).
- `ArchimedeanClass.stdPart` generalizes the standard part function to a general ordered field.

## TODO

Use Łoś's Theorem `FirstOrder.Language.Ultraproduct.sentence_realize` to formalize the transfer
principle on `Hyperreal`.
-/

@[expose] public section

open ArchimedeanClass Filter Germ Topology

noncomputable section

/-- Hyperreal numbers on the ultrafilter extending the cofinite filter. -/
def Hyperreal : Type :=
  Germ (hyperfilter ℕ : Filter ℕ) ℝ
deriving Inhabited

namespace Hyperreal

@[inherit_doc] notation "ℝ*" => Hyperreal

instance : Field ℝ* :=
  inferInstanceAs (Field (Germ _ _))

instance : LinearOrder ℝ* :=
  inferInstanceAs (LinearOrder (Germ _ _))

instance : IsStrictOrderedRing ℝ* :=
  inferInstanceAs (IsStrictOrderedRing (Germ _ _))

/-- Natural embedding `ℝ → ℝ*`. -/
@[coe] def ofReal : ℝ → ℝ* := const

instance : CoeTC ℝ ℝ* := ⟨ofReal⟩

/--
@isnad1 id=iff.0h2v.s3.07ea6469b290 from=seed src=0 shape=e5555f7a vocab=8e2264c2
-/
@[simp, norm_cast]
theorem coe_eq_coe {x y : ℝ} : (x : ℝ*) = y ↔ x = y :=
  Germ.const_inj

/--
@isnad1 id=iff.0h2v.s3.27691c686ac1 from=seed src=0 shape=e5555f7a vocab=8e2264c2
-/
theorem coe_ne_coe {x y : ℝ} : (x : ℝ*) ≠ y ↔ x ≠ y :=
  coe_eq_coe.not

/--
@isnad1 id=iff.0h1v.s5.5708fb3788a7 from=seed src=0 shape=3a75f94e vocab=8e2264c2
-/
@[simp, norm_cast]
theorem coe_eq_zero {x : ℝ} : (x : ℝ*) = 0 ↔ x = 0 :=
  coe_eq_coe

/--
@isnad1 id=iff.0h1v.s5.d671132b83f6 from=seed src=0 shape=3a75f94e vocab=8e2264c2
-/
@[simp, norm_cast]
theorem coe_eq_one {x : ℝ} : (x : ℝ*) = 1 ↔ x = 1 :=
  coe_eq_coe

/--
@isnad1 id=iff.0h1v.s5.634ad3d30945 from=seed src=0 shape=3a75f94e vocab=8e2264c2
-/
@[norm_cast]
theorem coe_ne_zero {x : ℝ} : (x : ℝ*) ≠ 0 ↔ x ≠ 0 :=
  coe_ne_coe

/--
@isnad1 id=iff.0h1v.s5.82056c9ca78f from=seed src=0 shape=3a75f94e vocab=8e2264c2
-/
@[norm_cast]
theorem coe_ne_one {x : ℝ} : (x : ℝ*) ≠ 1 ↔ x ≠ 1 :=
  coe_ne_coe

/--
@isnad1 id=eq.0h0v.s4.a6b0cd884f13 from=seed src=0 shape=1ac31801 vocab=8e2264c2
-/
@[simp, norm_cast]
theorem coe_one : ↑(1 : ℝ) = (1 : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.8f7a77c61213 from=seed src=0 shape=1ac31801 vocab=8e2264c2
-/
@[simp, norm_cast]
theorem coe_zero : ↑(0 : ℝ) = (0 : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.6129b756032f from=seed src=0 shape=5a02da31 vocab=26f30fe8
-/
@[simp, norm_cast]
theorem coe_inv (x : ℝ) : ↑x⁻¹ = (x⁻¹ : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h1v.s4.9ad56a32b817 from=seed src=0 shape=5a02da31 vocab=9ee23a0c
-/
@[simp, norm_cast]
theorem coe_neg (x : ℝ) : ↑(-x) = (-x : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.8154b2959786 from=seed src=0 shape=0438c7a3 vocab=eb847cce
-/
@[simp, norm_cast]
theorem coe_add (x y : ℝ) : ↑(x + y) = (x + y : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h1v.s5.9785cea4bbb8 from=seed src=0 shape=6184e9bf vocab=49d61e0e
-/
@[simp, norm_cast]
theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : ℝ) : ℝ*) = OfNat.ofNat n :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.a4a9d167e585 from=seed src=0 shape=0438c7a3 vocab=714724f6
-/
@[simp, norm_cast]
theorem coe_mul (x y : ℝ) : ↑(x * y) = (x * y : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.b4b81e60af16 from=seed src=0 shape=0438c7a3 vocab=ba85eeb8
-/
@[simp, norm_cast]
theorem coe_div (x y : ℝ) : ↑(x / y) = (x / y : ℝ*) :=
  rfl

/--
@isnad1 id=eq.0h2v.s5.488dbb12b502 from=seed src=0 shape=0438c7a3 vocab=9e73e533
-/
@[simp, norm_cast]
theorem coe_sub (x y : ℝ) : ↑(x - y) = (x - y : ℝ*) :=
  rfl

/--
@isnad1 id=iff.0h2v.s4.5f65c5a41f15 from=seed src=0 shape=e5555f7a vocab=a4ee5d56
-/
@[simp, norm_cast]
theorem coe_le_coe {x y : ℝ} : (x : ℝ*) ≤ y ↔ x ≤ y :=
  Germ.const_le_iff

/--
@isnad1 id=iff.0h2v.s4.8ac4db39bacf from=seed src=0 shape=e5555f7a vocab=30c5c760
-/
@[simp, norm_cast]
theorem coe_lt_coe {x y : ℝ} : (x : ℝ*) < y ↔ x < y :=
  Germ.const_lt_iff

/--
@isnad1 id=iff.0h1v.s5.07815ef76238 from=seed src=0 shape=6e44893f vocab=a4ee5d56
-/
@[simp, norm_cast]
theorem coe_nonneg {x : ℝ} : 0 ≤ (x : ℝ*) ↔ 0 ≤ x :=
  coe_le_coe

/--
@isnad1 id=iff.0h1v.s5.af1dd680abb3 from=seed src=0 shape=6e44893f vocab=30c5c760
-/
@[simp, norm_cast]
theorem coe_pos {x : ℝ} : 0 < (x : ℝ*) ↔ 0 < x :=
  coe_lt_coe

/--
@isnad1 id=eq.0h1v.s4.37421d754bf1 from=seed src=0 shape=5a02da31 vocab=9a873bd6
-/
@[simp, norm_cast]
theorem coe_abs (x : ℝ) : ((|x| : ℝ) : ℝ*) = |↑x| :=
  const_abs x

/--
@isnad1 id=eq.0h2v.s4.e5e544e87acf from=seed src=0 shape=ca05dc17 vocab=ce24b58b
-/
@[simp, norm_cast]
theorem coe_max (x y : ℝ) : ((max x y : ℝ) : ℝ*) = max ↑x ↑y :=
  Germ.const_max _ _

/--
@isnad1 id=eq.0h2v.s4.e1edae51e403 from=seed src=0 shape=ca05dc17 vocab=0911490f
-/
@[simp, norm_cast]
theorem coe_min (x y : ℝ) : ((min x y : ℝ) : ℝ*) = min ↑x ↑y :=
  Germ.const_min _ _

/-- The canonical map `ℝ → ℝ*` as an `OrderRingHom`. -/
@[simps]
def coeRingHom : ℝ →+*o ℝ* where
  toFun x := x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  monotone' _ _ := coe_le_coe.2

/--
@isnad1 id=le.0h1v.s7.01d7b15ed02d from=seed src=0 shape=7fac7bed vocab=1e619e10
-/
@[simp]
theorem archimedeanClassMk_coe_nonneg (x : ℝ) : 0 ≤ mk (x : ℝ*) :=
  mk_map_nonneg_of_archimedean coeRingHom x

/--
@isnad1 id=eq.1h1v.s6.97fcb731c60e from=seed src=0 shape=5904ae71 vocab=4db860d4
-/
@[simp]
theorem archimdeanClassMk_coe {x : ℝ} (hx : x ≠ 0) : mk (x : ℝ*) = 0 :=
  mk_map_of_archimedean' coeRingHom hx

/--
@isnad1 id=eq.0h1v.s3.bbed6185a1f8 from=seed src=0 shape=c3f7ecf6 vocab=2cb45a79
-/
@[simp]
theorem stdPart_coe (x : ℝ) : stdPart (x : ℝ*) = x :=
  stdPart_map_real coeRingHom x

/-! ### Basic constants -/

/-- Construct a hyperreal number from a sequence of real numbers. -/
def ofSeq (f : ℕ → ℝ) : ℝ* := (↑f : Germ (hyperfilter ℕ : Filter ℕ) ℝ)

/--
@isnad1 id=surjecti.0h0v.s2.8bf89d683880 from=seed src=0 shape=db2d4fff vocab=e1f65cfe
-/
theorem ofSeq_surjective : Function.Surjective ofSeq := Quot.exists_rep

/--
@isnad1 id=iff.0h2v.s5.112a422e94bc from=seed src=0 shape=d5c86e8a vocab=c4fab53d
-/
theorem ofSeq_lt_ofSeq {f g : ℕ → ℝ} : ofSeq f < ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n < g n :=
  Germ.coe_lt

/--
@isnad1 id=iff.0h2v.s5.bd703b4b323d from=seed src=0 shape=d5c86e8a vocab=504ff594
-/
theorem ofSeq_le_ofSeq {f g : ℕ → ℝ} : ofSeq f ≤ ofSeq g ↔ ∀ᶠ n in hyperfilter ℕ, f n ≤ g n :=
  Germ.coe_le

/-! #### ω -/

/-- A sample infinite hyperreal ω = ⟦(0, 1, 2, 3, ⋯)⟧. -/
def omega : ℝ* := ofSeq Nat.cast

@[inherit_doc] scoped notation "ω" => Hyperreal.omega
recommended_spelling "omega" for "ω" in [omega, «termω»]

/--
@isnad1 id=lt.0h1v.s4.7e9f91bd09b3 from=seed src=0 shape=f0bb1bdd vocab=fc409b0c
-/
theorem coe_lt_omega (r : ℝ) : r < ω := by
  apply ofSeq_lt_ofSeq.2 <| Filter.Eventually.filter_mono Nat.hyperfilter_le_atTop _
  obtain ⟨n, hn⟩ := exists_nat_gt r
  rw [eventually_atTop]
  exact ⟨n, fun m hm ↦ hn.trans_le (mod_cast hm)⟩

/--
@isnad1 id=lt.0h0v.s5.dc74b41ad58b from=seed src=0 shape=ff3a10fc vocab=aed0d6fa
-/
theorem omega_pos : 0 < ω :=
  coe_lt_omega 0

/--
@isnad1 id=ne.0h0v.s4.984526143a13 from=seed src=0 shape=ffdda526 vocab=9d452104
-/
@[simp]
theorem omega_ne_zero : ω ≠ 0 :=
  omega_pos.ne'

/--
@isnad1 id=eq.0h0v.s4.ce65ab4f7b74 from=seed src=0 shape=28fc0566 vocab=bb4ce571
-/
@[simp]
theorem abs_omega : |ω| = ω :=
  abs_of_pos omega_pos

/--
@isnad1 id=lt.0h0v.s7.c30a82749005 from=seed src=0 shape=40e3074d vocab=d9815ba9
-/
@[simp]
theorem archimedeanClassMk_omega_neg : mk ω < 0 :=
  fun n ↦ by simpa using! coe_lt_omega n

/--
@isnad1 id=eq.0h0v.s3.6a11f2c8f455 from=seed src=0 shape=b3c4969c vocab=6ccda35e
-/
@[simp]
theorem stdPart_omega : stdPart ω = 0 := by
  rw [stdPart_eq_zero]
  exact archimedeanClassMk_omega_neg.ne

/-! #### ε -/

/-- A sample infinitesimal hyperreal ε = ⟦(0, 1, 1/2, 1/3, ⋯)⟧. -/
def epsilon : ℝ* :=
  ofSeq fun n => n⁻¹

@[inherit_doc] scoped notation "ε" => Hyperreal.epsilon
recommended_spelling "epsilon" for "ε" in [epsilon, «termε»]

/--
@isnad1 id=eq.0h0v.s4.fd601da7c72c from=seed src=0 shape=28fc0566 vocab=ebd570b7
-/
@[simp]
theorem inv_omega : ω⁻¹ = ε :=
  rfl

/--
@isnad1 id=eq.0h0v.s4.2656725e6451 from=seed src=0 shape=28fc0566 vocab=ebd570b7
-/
@[simp]
theorem inv_epsilon : ε⁻¹ = ω :=
  @inv_inv _ _ ω

/--
@isnad1 id=lt.0h0v.s5.04afb540a534 from=seed src=0 shape=ff3a10fc vocab=20c85a4b
-/
@[simp]
theorem epsilon_pos : 0 < ε :=
  inv_pos_of_pos omega_pos

/--
@isnad1 id=ne.0h0v.s4.1008129b1aa1 from=seed src=0 shape=ffdda526 vocab=5c5d74ad
-/
@[simp]
theorem epsilon_ne_zero : ε ≠ 0 :=
  epsilon_pos.ne'

/--
@isnad1 id=eq.0h0v.s5.9f3803671e2a from=seed src=0 shape=33aceabd vocab=8b64795b
-/
@[simp]
theorem epsilon_mul_omega : ε * ω = 1 :=
  @inv_mul_cancel₀ _ _ ω omega_ne_zero

/--
@isnad1 id=lt.0h0v.s7.3741cda50cda from=seed src=0 shape=6ed7cd4d vocab=13844f37
-/
@[simp]
theorem archimedeanClassMk_epsilon_pos : 0 < mk ε := by
  simp [← inv_omega]

/-!
### Some facts about `Tendsto`
-/

/--
@isnad1 id=iff.0h2v.s4.844281e84f15 from=seed src=0 shape=92c73727 vocab=01bc7cc7
-/
@[simp]
theorem tendsto_ofSeq {f : ℕ → ℝ} {lb : Filter ℝ} :
    (ofSeq f).Tendsto lb ↔ Tendsto f (hyperfilter ℕ) lb :=
  .rfl

/--
@isnad1 id=tendsto.2h3v.s6.a34812a881e4 from=seed src=0 shape=a17c7ba6 vocab=8f855b2b
-/
theorem stdPart_map {x : ℝ*} {r : ℝ} {f : ℝ → ℝ} (hf : ContinuousAt f r)
    (hxr : x.Tendsto (𝓝 r)) : (x.map f).Tendsto (𝓝 (f r)) := by
  rcases ofSeq_surjective x with ⟨g, rfl⟩
  exact hf.tendsto.comp hxr

/--
@isnad1 id=tendsto.3h5v.s6.380e9fbb83c4 from=seed src=0 shape=9666d18a vocab=a7bc67f5
-/
theorem stdPart_map₂ {x y : ℝ*} {r s : ℝ} {f : ℝ → ℝ → ℝ}
    (hxr : x.Tendsto (𝓝 r)) (hys : y.Tendsto (𝓝 s))
    (hf : ContinuousAt (Function.uncurry f) (r, s)) : (x.map₂ f y).Tendsto (𝓝 (f r s)) := by
  rcases ofSeq_surjective x with ⟨x, rfl⟩
  rcases ofSeq_surjective y with ⟨y, rfl⟩
  exact hf.tendsto.comp (hxr.prodMk_nhds hys)

/--
@isnad1 id=iff.0h2v.s6.3cc9f74e2f98 from=seed src=0 shape=df86ce3f vocab=7b95cf13
-/
theorem tendsto_iff_forall {x : ℝ*} {r : ℝ} :
    x.Tendsto (𝓝 r) ↔ (∀ s < r, s ≤ x) ∧ (∀ s > r, x ≤ s) := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq, (nhds_basis_Ioo _).tendsto_right_iff]
  simp_rw [Set.mem_Ioo, eventually_and, ← ofSeq_lt_ofSeq]
  refine ⟨fun H ↦ ⟨fun s hs ↦ ?_, fun s hs ↦ ?_⟩, fun H ⟨s, t⟩ ⟨hs, ht⟩ ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨t, ht⟩ := exists_gt r
    exact (H ⟨s, t⟩ ⟨hs, ht⟩).1.le
  · obtain ⟨t, ht⟩ := exists_lt r
    exact (H ⟨t, s⟩ ⟨ht, hs⟩).2.le
  · obtain ⟨u, hu, hu'⟩ := exists_between hs
    exact (coe_lt_coe.2 hu).trans_le (H.1 _ hu')
  · obtain ⟨u, hu, hu'⟩ := exists_between ht
    exact (H.2 _ hu).trans_lt (coe_lt_coe.2 hu')

/--
@isnad1 id=le.1h2v.s7.c1e917f96ac9 from=seed src=0 shape=93e941c0 vocab=77f1c1e6
-/
theorem archimedeanClassMk_nonneg_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) :
    0 ≤ mk x := by
  rw [tendsto_iff_forall] at hx
  obtain ⟨s, hs⟩ := exists_lt r
  obtain ⟨t, ht⟩ := exists_gt r
  exact mk_nonneg_of_le_of_le_of_archimedean coeRingHom (hx.1 s hs) (hx.2 t ht)

/--
@isnad1 id=eq.1h2v.s4.d83319e2981a from=seed src=0 shape=9c3fbc1e vocab=8c3c97e7
-/
theorem stdPart_of_tendsto {x : ℝ*} {r : ℝ} (hx : x.Tendsto (𝓝 r)) : stdPart x = r := by
  rw [tendsto_iff_forall] at hx
  exact stdPart_eq coeRingHom hx.1 hx.2

/--
@isnad1 id=lt.1h1v.s7.0a8f63e67d1d from=seed src=0 shape=6f6dc81b vocab=ea2cc56c
-/
theorem archimedeanClassMk_pos_of_tendsto {x : ℝ*} (hx : x.Tendsto (𝓝 0)) : 0 < mk x := by
  apply (archimedeanClassMk_nonneg_of_tendsto hx).lt_of_ne'
  rw [← stdPart_eq_zero, stdPart_of_tendsto hx]

/--
@isnad1 id=eq.0h0v.s3.1c54bc519337 from=seed src=0 shape=b3c4969c vocab=7369d51a
-/
@[simp]
theorem stdPart_epsilon : stdPart ε = 0 :=
  stdPart_eq_zero.2 <| archimedeanClassMk_epsilon_pos.ne'

/--
@isnad1 id=lt.1h1v.s4.b8c4a64887a8 from=seed src=0 shape=2e7587c9 vocab=4d5b0322
-/
theorem epsilon_lt_of_pos {r : ℝ} : 0 < r → ε < r :=
  lt_of_pos_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

/--
@isnad1 id=lt.1h1v.s4.93214e86815b from=seed src=0 shape=23bbbe6f vocab=4d5b0322
-/
theorem epsilon_lt_of_neg {r : ℝ} : r < 0 → r < ε :=
  lt_of_neg_of_archimedean coeRingHom archimedeanClassMk_epsilon_pos

/--
@isnad1 id=lt.1h2v.s5.4b00ca4a6e4c from=seed src=0 shape=a0e73407 vocab=f5f0b8c2
-/
theorem lt_of_tendsto_atTop {x : ℝ*} (r : ℝ) (hx : x.Tendsto atTop) : r < x := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Ioi_mem_atTop r)

/--
@isnad1 id=lt.1h2v.s5.b9b6d64c1aa1 from=seed src=0 shape=166c77f7 vocab=a5b09b4f
-/
theorem lt_of_tendsto_atBot {x : ℝ*} (r : ℝ) (hx : x.Tendsto atBot) : x < r := by
  rcases ofSeq_surjective x with ⟨f, rfl⟩
  rw [tendsto_ofSeq] at hx
  exact ofSeq_lt_ofSeq.2 <| hx.eventually_mem (Iio_mem_atBot r)

/--
@isnad1 id=lt.1h1v.s7.57b884a0672f from=seed src=0 shape=0260e2eb vocab=6cb86faa
-/
theorem archimedeanClassMk_neg_of_tendsto_atTop {x : ℝ*} (hx : x.Tendsto atTop) : mk x < 0 := by
  have : 0 < x := lt_of_tendsto_atTop 0 hx
  intro n
  simpa [abs_of_pos this] using! lt_of_tendsto_atTop n hx

/--
@isnad1 id=lt.1h1v.s7.7e58cdc3ad2c from=seed src=0 shape=0260e2eb vocab=19c5123e
-/
theorem archimedeanClassMk_neg_of_tendsto_atBot {x : ℝ*} (hx : x.Tendsto atBot) : mk x < 0 := by
  have : x < 0 := lt_of_tendsto_atBot 0 hx
  intro n
  simpa [abs_of_neg this, lt_neg] using! lt_of_tendsto_atBot (-n) hx

/--
@isnad1 id=iff.0h1v.s7.257e8c636dda from=seed src=0 shape=1e8584bc vocab=6cb86faa
-/
theorem tendsto_atTop_iff {x : ℝ*} : x.Tendsto atTop ↔ 0 < x ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atTop 0 h, archimedeanClassMk_neg_of_tendsto_atTop h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atTop]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonneg (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

/--
@isnad1 id=iff.0h1v.s7.99848e7eb2f2 from=seed src=0 shape=7263329e vocab=19c5123e
-/
theorem tendsto_atBot_iff {x : ℝ*} : x.Tendsto atBot ↔ x < 0 ∧ mk x < 0 where
  mp h := ⟨lt_of_tendsto_atBot 0 h, archimedeanClassMk_neg_of_tendsto_atBot h⟩
  mpr h := by
    rcases ofSeq_surjective x with ⟨f, rfl⟩
    rw [tendsto_ofSeq, tendsto_atBot]
    exact fun r ↦ ofSeq_le_ofSeq.1 <|
      (lt_of_mk_lt_mk_of_nonpos (h.2.trans_le <| archimedeanClassMk_coe_nonneg r) h.1.le).le

end Hyperreal
end

/-
Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `positivity` plugin

namespace Tactic

open Positivity

private theorem hyperreal_coe_ne_zero {r : ℝ} : r ≠ 0 → (r : ℝ*) ≠ 0 :=
  Hyperreal.coe_ne_zero.2

private theorem hyperreal_coe_nonneg {r : ℝ} : 0 ≤ r → 0 ≤ (r : ℝ*) :=
  Hyperreal.coe_nonneg.2

private theorem hyperreal_coe_pos {r : ℝ} : 0 < r → 0 < (r : ℝ*) :=
  Hyperreal.coe_pos.2

/-- Extension for the `positivity` tactic: cast from `ℝ` to `ℝ*`. -/
@[positivity]
unsafe def positivity_coe_real_hyperreal : expr → tactic strictness
  | q(@coe _ _ $(inst) $(a)) => do
    unify inst q(@coeToLift _ _ Hyperreal.hasCoeT)
    let strictness_a ← core a
    match strictness_a with
      | positive p => positive <$> mk_app `` hyperreal_coe_pos [p]
      | nonnegative p => nonnegative <$> mk_app `` hyperreal_coe_nonneg [p]
      | nonzero p => nonzero <$> mk_app `` hyperreal_coe_ne_zero [p]
  | e =>
    pp e >>= fail ∘ format.bracket "The expression " " is not of the form `(r : ℝ*)` for `r : ℝ`"

end Tactic
-/
