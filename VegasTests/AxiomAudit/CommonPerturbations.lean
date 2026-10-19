/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalConsistentSequence

/-! # Axiom guards for the actual common-rate and shared sequence consumers -/

/-- info:
'Vegas.exists_phaseProposal_common_perturbations'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposal_common_perturbations

/-- info:
'Vegas.exists_phaseProposal_consistent_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposal_consistent_sequence
