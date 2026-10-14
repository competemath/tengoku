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

/-- Root audit for fixed branch (0, 16).
@isnad1 id=eq.0h0v.s5.fd779770ce2c from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_16 :
    branchClaimRootValidB 0 16 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 34).
@isnad1 id=eq.0h0v.s5.caa1a278aefa from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_34 :
    branchClaimRootValidB 4 34 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 8).
@isnad1 id=eq.0h0v.s5.02f190a06857 from=translated src=- shape=e9e0773c vocab=1e25805a
-/
theorem coverageBranchRoot_2_08 :
    branchClaimRootValidB 2 8 (.search branchClaims2Row8) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 6), starting at 64.
@isnad1 id=eq.0h0v.s3.db608d7b8a93 from=translated src=- shape=6f582f20 vocab=02e96baa
-/
theorem coverageBranchNodes_2_06_00064 :
    nodeClaimChunkValidB branchClaims2Row6 64 45 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 8), starting at 0.
@isnad1 id=eq.0h0v.s3.15b6cc8228c6 from=translated src=- shape=6f582f20 vocab=94c204cb
-/
theorem coverageBranchNodes_2_08_00000 :
    nodeClaimChunkValidB branchClaims2Row8 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 8), starting at 64.
@isnad1 id=eq.0h0v.s3.6085c3b67af3 from=translated src=- shape=6f582f20 vocab=94c204cb
-/
theorem coverageBranchNodes_2_08_00064 :
    nodeClaimChunkValidB branchClaims2Row8 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 8), starting at 128.
@isnad1 id=eq.0h0v.s3.fe2cfcce11ba from=translated src=- shape=6f582f20 vocab=94c204cb
-/
theorem coverageBranchNodes_2_08_00128 :
    nodeClaimChunkValidB branchClaims2Row8 128 36 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
