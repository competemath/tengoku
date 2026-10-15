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

/-- Root audit for fixed branch (0, 26).
@isnad1 id=eq.0h0v.s5.d87243088019 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_26 :
    branchClaimRootValidB 0 26 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 30).
@isnad1 id=eq.0h0v.s5.573b7012d9b7 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_30 :
    branchClaimRootValidB 5 30 (.patternThree 3) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 32).
@isnad1 id=eq.0h0v.s5.963b92273fd3 from=translated src=- shape=e9e0773c vocab=236b5e27
-/
theorem coverageBranchRoot_2_32 :
    branchClaimRootValidB 2 32 (.search branchClaims2Row32) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 31), starting at 64.
@isnad1 id=eq.0h0v.s3.e02c3494d85b from=translated src=- shape=6f582f20 vocab=a14e66ab
-/
theorem coverageBranchNodes_2_31_00064 :
    nodeClaimChunkValidB branchClaims2Row31 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 31), starting at 128.
@isnad1 id=eq.0h0v.s3.cec9bc6a9cee from=translated src=- shape=6f582f20 vocab=a14e66ab
-/
theorem coverageBranchNodes_2_31_00128 :
    nodeClaimChunkValidB branchClaims2Row31 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 31), starting at 192.
@isnad1 id=eq.0h0v.s3.d1a554c15f47 from=translated src=- shape=6f582f20 vocab=a14e66ab
-/
theorem coverageBranchNodes_2_31_00192 :
    nodeClaimChunkValidB branchClaims2Row31 192 31 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 32), starting at 0.
@isnad1 id=eq.0h0v.s3.fa9648ced4fb from=translated src=- shape=6f582f20 vocab=88c127b1
-/
theorem coverageBranchNodes_2_32_00000 :
    nodeClaimChunkValidB branchClaims2Row32 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
