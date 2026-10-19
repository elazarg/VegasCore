/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOriginalResetPayoff
import Vegas.Game.PhaseProposalStandingBindingDebt

/-! # Actual original binding debt and reset continuation dependencies -/

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_bindingsHoldValues_or_failedBinding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_bindingsHoldValues_or_failedBinding

/-- info:
'Vegas.RecoverySourceWitness.prefix_at_same_attempt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.prefix_at_same_attempt

/-- info:
'Vegas.RecoverySourceWitness.raw_closing_checkpoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.raw_closing_checkpoint

/-- info:
'Vegas.phaseProposal_current_binding_failure_checkpointed_at_original_close'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_current_binding_failure_checkpointed_at_original_close

/-- info:
'Vegas.phaseProposal_standing_binding_terminal_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_standing_binding_terminal_payoff

/-- info:
'Vegas.RecoverySourceWitness.bindingsHoldValues_of_no_saved_failure_and_foreign_good'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.bindingsHoldValues_of_no_saved_failure_and_foreign_good

/-- info:
'Vegas.RecoverySourceWitness.original_retry_archived_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.original_retry_archived_source

/-- info:
'Vegas.phaseProposal_original_reset_payoff_law_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_original_reset_payoff_law_eq

/-- info:
'Vegas.phaseProposal_fresh_mixture_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_fresh_mixture_payoff_law
