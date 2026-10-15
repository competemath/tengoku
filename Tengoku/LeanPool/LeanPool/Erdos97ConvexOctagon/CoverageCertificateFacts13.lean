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

/-- Root audit for fixed branch (0, 13).
@isnad1 id=eq.0h0v.s5.9cb005bca48a from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_13 :
    branchClaimRootValidB 0 13 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 31).
@isnad1 id=eq.0h0v.s5.dce2c360d150 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_31 :
    branchClaimRootValidB 4 31 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 1).
@isnad1 id=eq.0h0v.s5.aa2efc9fbef8 from=translated src=- shape=e9e0773c vocab=c9189a44
-/
theorem coverageBranchRoot_2_01 :
    branchClaimRootValidB 2 1 (.search branchClaims2Row1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 2).
@isnad1 id=eq.0h0v.s5.0d299cf61e6b from=translated src=- shape=e9e0773c vocab=929660f0
-/
theorem coverageBranchRoot_2_02 :
    branchClaimRootValidB 2 2 (.search branchClaims2Row2) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 34), starting at 64.
@isnad1 id=eq.0h0v.s3.ed58121f371d from=translated src=- shape=6f582f20 vocab=33c4912d
-/
theorem coverageBranchNodes_1_34_00064 :
    nodeClaimChunkValidB branchClaims1Row34 64 41 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 1), starting at 0.
@isnad1 id=eq.0h0v.s3.fa22f95b737c from=translated src=- shape=6f582f20 vocab=69e7aeda
-/
theorem coverageBranchNodes_2_01_00000 :
    nodeClaimChunkValidB branchClaims2Row1 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 1), starting at 64.
@isnad1 id=eq.0h0v.s3.7a0dd17bcc6e from=translated src=- shape=6f582f20 vocab=69e7aeda
-/
theorem coverageBranchNodes_2_01_00064 :
    nodeClaimChunkValidB branchClaims2Row1 64 46 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 2), starting at 0.
@isnad1 id=eq.0h0v.s3.71b4ce564cae from=translated src=- shape=6f582f20 vocab=5298d63b
-/
theorem coverageBranchNodes_2_02_00000 :
    nodeClaimChunkValidB branchClaims2Row2 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
