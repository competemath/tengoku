/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 25).
@isnad1 id=eq.0h0v.s5.da6da07a70b0 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_25 :
    branchClaimRootValidB 0 25 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 23).
@isnad1 id=eq.0h0v.s5.97cd9c8505ce from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_23 :
    branchClaimRootValidB 5 23 (.patternThree 3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 31).
@isnad1 id=eq.0h0v.s5.07041ea80063 from=translated src=- shape=e9e0773c vocab=9bb57363
-/
theorem coverageBranchRoot_2_31 :
    branchClaimRootValidB 2 31 (.search branchClaims2Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 64.
@isnad1 id=eq.0h0v.s3.0fa2cc15f6cd from=translated src=- shape=6f582f20 vocab=aa47b7e8
-/
theorem coverageBranchNodes_2_30_00064 :
    nodeClaimChunkValidB branchClaims2Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 128.
@isnad1 id=eq.0h0v.s3.291930ca276c from=translated src=- shape=6f582f20 vocab=aa47b7e8
-/
theorem coverageBranchNodes_2_30_00128 :
    nodeClaimChunkValidB branchClaims2Row30 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 30), starting at 192.
@isnad1 id=eq.0h0v.s3.97683c552ad8 from=translated src=- shape=6f582f20 vocab=aa47b7e8
-/
theorem coverageBranchNodes_2_30_00192 :
    nodeClaimChunkValidB branchClaims2Row30 192 14 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 31), starting at 0.
@isnad1 id=eq.0h0v.s3.c7c830ce7289 from=translated src=- shape=6f582f20 vocab=a14e66ab
-/
theorem coverageBranchNodes_2_31_00000 :
    nodeClaimChunkValidB branchClaims2Row31 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
