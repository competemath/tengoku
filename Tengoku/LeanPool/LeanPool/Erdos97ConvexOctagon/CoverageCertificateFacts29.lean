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

/-- Root audit for fixed branch (0, 29).
@isnad1 id=eq.0h0v.s5.9dbd304bed54 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_29 :
    branchClaimRootValidB 0 29 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 19).
@isnad1 id=eq.0h0v.s5.792ba3f8175f from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_19 :
    branchClaimRootValidB 6 19 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 1).
@isnad1 id=eq.0h0v.s5.1fee0e787044 from=translated src=- shape=e9e0773c vocab=d2b20c27
-/
theorem coverageBranchRoot_3_01 :
    branchClaimRootValidB 3 1 (.search branchClaims3Row1) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 2).
@isnad1 id=eq.0h0v.s5.ea208f89e83b from=translated src=- shape=e9e0773c vocab=bf5b6a44
-/
theorem coverageBranchRoot_3_02 :
    branchClaimRootValidB 3 2 (.search branchClaims3Row2) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 34), starting at 128.
@isnad1 id=eq.0h0v.s3.5620b0b00399 from=translated src=- shape=6f582f20 vocab=f7cc570d
-/
theorem coverageBranchNodes_2_34_00128 :
    nodeClaimChunkValidB branchClaims2Row34 128 34 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 1), starting at 0.
@isnad1 id=eq.0h0v.s3.a4188451c504 from=translated src=- shape=6f582f20 vocab=d1577beb
-/
theorem coverageBranchNodes_3_01_00000 :
    nodeClaimChunkValidB branchClaims3Row1 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 1), starting at 64.
@isnad1 id=eq.0h0v.s3.c312c5481832 from=translated src=- shape=6f582f20 vocab=d1577beb
-/
theorem coverageBranchNodes_3_01_00064 :
    nodeClaimChunkValidB branchClaims3Row1 64 47 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 2), starting at 0.
@isnad1 id=eq.0h0v.s3.77f1558b0e9a from=translated src=- shape=6f582f20 vocab=dd379bbc
-/
theorem coverageBranchNodes_3_02_00000 :
    nodeClaimChunkValidB branchClaims3Row2 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
