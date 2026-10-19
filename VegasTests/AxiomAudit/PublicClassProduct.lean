/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicClassFactorization

/-! # Axiom guards for literal whole-history source reach products -/

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_historyReach_foreign_products'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_historyReach_foreign_products

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_historyReachWeight_foreign_products'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_historyReachWeight_foreign_products
