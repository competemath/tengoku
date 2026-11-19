import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.LeadingEigenvalueTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

noncomputable section

namespace OddCycleBound.IntermediateRegion

noncomputable def directedKernel
    (p : Real) (m : Nat) (lambda : Real) : Real :=
  oneSidedGeom p m (-lambda)

/--
@isnad1 id=eq.3h3v.s6.e029037dcc41 from=translated src=- shape=5d8534cf vocab=298f40ff
-/
theorem directedKernel_mul_add
    {p lambda : Real} {m : Nat} (hm : Odd m) (hm2 : 2 <= m)
    (hlower : -p <= lambda) :
    directedKernel p m lambda * (p + lambda) =
      p ^ (m - 1) - lambda ^ (m - 1) := by
  have heven : Even (m - 1) :=
    hm.tsub_odd (by decide : Odd 1)
  have hgeom := oneSidedGeom_mul_sub
    (p := p) (lambda := -lambda) hm2 (by linarith)
  simpa [directedKernel, heven.neg_pow] using hgeom

/--
@isnad1 id=le.3h3v.s6.d63ad2f1e69b from=translated src=- shape=988423c1 vocab=5bcffee6
-/
theorem directedKernel_zero_le_of_nonpos
    {p lambda : Real} {m : Nat} (hp : 0 <= p) (hlambda : lambda <= 0)
    (hm2 : 2 <= m) :
    p ^ (m - 2) <= directedKernel p m lambda := by
  unfold directedKernel oneSidedGeom
  have hzeroMem : 0 ∈ Finset.range (m - 1) :=
    Finset.mem_range.mpr (by omega)
  have hterm : p ^ (m - 2) =
      p ^ (m - 2 - 0) * (-lambda) ^ 0 := by simp
  rw [hterm]
  exact Finset.single_le_sum
    (f := fun j => p ^ (m - 2 - j) * (-lambda) ^ j)
    (fun j _ => mul_nonneg (pow_nonneg hp _)
      (pow_nonneg (by linarith) _)) hzeroMem

/--
@isnad1 id=le.4h3v.s6.fc6dd89377f3 from=translated src=- shape=8ac3a456 vocab=bb831d52
-/
theorem directedKernel_le_zero_value
    {p L : Real} {m : Nat} (hp : 0 < p) (hL : 0 <= L)
    (hm : Odd m) (hm2 : 2 <= m) :
    directedKernel p m L <= p ^ (m - 2) := by
  have hmul := directedKernel_mul_add
    (p := p) (lambda := L) hm hm2 (by linarith)
  have hden : 0 < p + L := by linarith
  have hpow : p ^ (m - 1) = p ^ (m - 2) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have hLpow : 0 <= L ^ (m - 1) := pow_nonneg hL _
  have hproduct :
      directedKernel p m L * (p + L) <=
        p ^ (m - 2) * (p + L) := by
    rw [hmul, hpow]
    nlinarith [pow_nonneg (le_of_lt hp) (m - 2)]
  exact le_of_mul_le_mul_right hproduct hden

/--
@isnad1 id=le.5h4v.s5.8fd1b6bd7f73 from=translated src=- shape=7cebbc22 vocab=f3250f73
-/
theorem directedKernel_anti_on_nonneg
    {p lambda L : Real} {m : Nat}
    (hp : 0 < p) (hlambda : 0 <= lambda) (hle : lambda <= L)
    (hm : Odd m) (hm2 : 2 <= m) :
    directedKernel p m L <= directedKernel p m lambda := by
  have hL : 0 <= L := hlambda.trans hle
  have hlamId := directedKernel_mul_add
    (p := p) (lambda := lambda) hm hm2 (by linarith)
  have hLId := directedKernel_mul_add
    (p := p) (lambda := L) hm hm2 (by linarith)
  have hpowMain : lambda ^ (m - 1) <= L ^ (m - 1) :=
    pow_le_pow_left₀ hlambda hle _
  have hpowTail : lambda ^ (m - 2) <= L ^ (m - 2) :=
    pow_le_pow_left₀ hlambda hle _
  have hfirst : 0 <= p ^ (m - 1) * (L - lambda) :=
    mul_nonneg (pow_nonneg (le_of_lt hp) _) (sub_nonneg.mpr hle)
  have hsecond : 0 <= p * (L ^ (m - 1) - lambda ^ (m - 1)) :=
    mul_nonneg (le_of_lt hp) (sub_nonneg.mpr hpowMain)
  have hthird : 0 <= lambda * L *
      (L ^ (m - 2) - lambda ^ (m - 2)) :=
    mul_nonneg (mul_nonneg hlambda hL) (sub_nonneg.mpr hpowTail)
  have hcross :
      (p ^ (m - 1) - L ^ (m - 1)) * (p + lambda) <=
        (p ^ (m - 1) - lambda ^ (m - 1)) * (p + L) := by
    have hLm1 : L ^ (m - 1) = L ^ (m - 2) * L := by
      rw [← pow_succ]
      congr 1
      omega
    have hlamM1 : lambda ^ (m - 1) =
        lambda ^ (m - 2) * lambda := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hLm1, hlamM1]
    nlinarith
  have hproduct :
      directedKernel p m L * ((p + L) * (p + lambda)) <=
        directedKernel p m lambda * ((p + L) * (p + lambda)) := by
    calc
      directedKernel p m L * ((p + L) * (p + lambda)) =
          (p ^ (m - 1) - L ^ (m - 1)) * (p + lambda) := by
            rw [← hLId]
            ring
      _ <= (p ^ (m - 1) - lambda ^ (m - 1)) * (p + L) := hcross
      _ = directedKernel p m lambda * ((p + L) * (p + lambda)) := by
            rw [← hlamId]
            ring
  have hden : 0 < (p + L) * (p + lambda) :=
    mul_pos (by linarith) (by linarith)
  exact le_of_mul_le_mul_right hproduct hden

/--
@isnad1 id=le.5h4v.s6.a6471fe578f0 from=translated src=- shape=e156fed5 vocab=7d447731
-/
theorem directedKernel_safe_lower_bound
    {p lambda L : Real} {m : Nat}
    (hp : 0 < p) (hL : 0 <= L)
    (hlambda : lambda ∈ Set.Icc (-L) L)
    (hm : Odd m) (hm2 : 2 <= m) :
    directedKernel p m L <= directedKernel p m lambda := by
  by_cases hlam0 : 0 <= lambda
  · exact directedKernel_anti_on_nonneg hp hlam0 hlambda.2 hm hm2
  · have hzero := directedKernel_zero_le_of_nonpos
      (le_of_lt hp) (le_of_not_ge hlam0) hm2
    exact (directedKernel_le_zero_value hp hL hm hm2).trans hzero

end OddCycleBound.IntermediateRegion
