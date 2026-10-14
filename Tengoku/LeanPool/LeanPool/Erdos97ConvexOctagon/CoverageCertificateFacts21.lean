/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 21).
@isnad1 id=eq.0h0v.s5.b1f6f41321cb from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_21 :
    branchClaimRootValidB 0 21 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 13).
@isnad1 id=eq.0h0v.s5.174cd5574b47 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_13 :
    branchClaimRootValidB 5 13 (.patternThree 3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 23).
@isnad1 id=eq.0h0v.s5.9ac855869f76 from=translated src=- shape=e9e0773c vocab=744fa331
-/
theorem coverageBranchRoot_2_23 :
    branchClaimRootValidB 2 23 (.search branchClaims2Row23) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 24).
@isnad1 id=eq.0h0v.s5.cf24a7b9d62b from=translated src=- shape=e9e0773c vocab=34333197
-/
theorem coverageBranchRoot_2_24 :
    branchClaimRootValidB 2 24 (.search branchClaims2Row24) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 18), starting at 128.
@isnad1 id=eq.0h0v.s3.695e03aaa2e4 from=translated src=- shape=6f582f20 vocab=6056e36d
-/
theorem coverageBranchNodes_2_18_00128 :
    nodeClaimChunkValidB branchClaims2Row18 128 12 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 23), starting at 0.
@isnad1 id=eq.0h0v.s3.8cc8201086b3 from=translated src=- shape=6f582f20 vocab=f832ede4
-/
theorem coverageBranchNodes_2_23_00000 :
    nodeClaimChunkValidB branchClaims2Row23 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 23), starting at 64.
@isnad1 id=eq.0h0v.s3.878794545f44 from=translated src=- shape=6f582f20 vocab=f832ede4
-/
theorem coverageBranchNodes_2_23_00064 :
    nodeClaimChunkValidB branchClaims2Row23 64 56 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 24), starting at 0.
@isnad1 id=eq.0h0v.s3.0e99a06bba29 from=translated src=- shape=6f582f20 vocab=302567cb
-/
theorem coverageBranchNodes_2_24_00000 :
    nodeClaimChunkValidB branchClaims2Row24 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
