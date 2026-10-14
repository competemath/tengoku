/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData02
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 17).
@isnad1 id=eq.0h0v.s5.ad1436cbc9fd from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_17 :
    branchClaimRootValidB 0 17 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 0).
@isnad1 id=eq.0h0v.s5.1aba70b67ce7 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_00 :
    branchClaimRootValidB 5 0 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 9).
@isnad1 id=eq.0h0v.s5.8f2cab8d13cd from=translated src=- shape=e9e0773c vocab=909b24a5
-/
theorem coverageBranchRoot_2_09 :
    branchClaimRootValidB 2 9 (.search branchClaims2Row9) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 10).
@isnad1 id=eq.0h0v.s5.a329a0c3e015 from=translated src=- shape=e9e0773c vocab=7fc09498
-/
theorem coverageBranchRoot_2_10 :
    branchClaimRootValidB 2 10 (.search branchClaims2Row10) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 9), starting at 0.
@isnad1 id=eq.0h0v.s3.1ddac1c38fea from=translated src=- shape=6f582f20 vocab=291863b7
-/
theorem coverageBranchNodes_2_09_00000 :
    nodeClaimChunkValidB branchClaims2Row9 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 9), starting at 64.
@isnad1 id=eq.0h0v.s3.5ae34af32c65 from=translated src=- shape=6f582f20 vocab=291863b7
-/
theorem coverageBranchNodes_2_09_00064 :
    nodeClaimChunkValidB branchClaims2Row9 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 9), starting at 128.
@isnad1 id=eq.0h0v.s3.870e231d604b from=translated src=- shape=6f582f20 vocab=291863b7
-/
theorem coverageBranchNodes_2_09_00128 :
    nodeClaimChunkValidB branchClaims2Row9 128 54 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 10), starting at 0.
@isnad1 id=eq.0h0v.s3.58998d7c468f from=translated src=- shape=6f582f20 vocab=a3ed85ac
-/
theorem coverageBranchNodes_2_10_00000 :
    nodeClaimChunkValidB branchClaims2Row10 0 15 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
