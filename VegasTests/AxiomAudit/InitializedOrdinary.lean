/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalInitializedLawError
import Vegas.Game.RecoveryRetryWitness

/-! # Axiom guards for initialized ordinary source and native laws -/

/-- info:
'Vegas.RecoverySourceCheckpoint.retry_archive_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.retry_archive_extension

/-- info:
'Vegas.RecoverySourceCheckpoint.retry_phase_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.retry_phase_archive

/-- info:
'Vegas.RecoverySourceWitness.retry_checkpoint_archived_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.retry_checkpoint_archived_source

/-- info:
'Interaction.ReactiveApplication.schedulerMixture_finish_marginal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_finish_marginal

/-- info:
'Interaction.ReactiveApplication.schedulerMixture_finish_map_eq_of_supported'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.schedulerMixture_finish_map_eq_of_supported

/-- info:
'Vegas.phaseProposalUnflagged_initialized_terminal_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_initialized_terminal_coupling

/-- info:
'Vegas.phaseProposalUnflagged_initialized_joint_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_initialized_joint_readout

/-- info:
'Vegas.phaseProposal_initialized_joint_withinTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_initialized_joint_withinTV
