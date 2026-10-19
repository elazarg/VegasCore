/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalFreshTerminalCoupling

/-! # Full ordinary terminal-history coupling dependency regression -/

/-- info: 'Vegas.RecoverySourceWitness.ordinary_fresh_terminal_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.ordinary_fresh_terminal_coupling
