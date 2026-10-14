/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 27).
@isnad1 id=eq.0h0v.s5.0ec3ffbfe678 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_27 :
    branchClaimRootValidB 0 27 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 33).
@isnad1 id=eq.0h0v.s5.8255154f10af from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_33 :
    branchClaimRootValidB 5 33 (.patternThree 3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 33).
@isnad1 id=eq.0h0v.s5.32a86808384d from=translated src=- shape=e9e0773c vocab=21f8cd6c
-/
theorem coverageBranchRoot_2_33 :
    branchClaimRootValidB 2 33 (.search branchClaims2Row33) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 32), starting at 64.
@isnad1 id=eq.0h0v.s3.3d97c6174df9 from=translated src=- shape=6f582f20 vocab=88c127b1
-/
theorem coverageBranchNodes_2_32_00064 :
    nodeClaimChunkValidB branchClaims2Row32 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 32), starting at 128.
@isnad1 id=eq.0h0v.s3.f1d4152afdf6 from=translated src=- shape=6f582f20 vocab=88c127b1
-/
theorem coverageBranchNodes_2_32_00128 :
    nodeClaimChunkValidB branchClaims2Row32 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 32), starting at 192.
@isnad1 id=eq.0h0v.s3.df9a096d3213 from=translated src=- shape=6f582f20 vocab=88c127b1
-/
theorem coverageBranchNodes_2_32_00192 :
    nodeClaimChunkValidB branchClaims2Row32 192 27 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 33), starting at 0.
@isnad1 id=eq.0h0v.s3.4774c1bdbdce from=translated src=- shape=6f582f20 vocab=f45cb2fb
-/
theorem coverageBranchNodes_2_33_00000 :
    nodeClaimChunkValidB branchClaims2Row33 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
