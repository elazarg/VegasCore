/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Interaction
import Vegas

/-! # Source proof dependency regressions -/

/-- info: 'Vegas.SourceProgram.Setup.decision_allNonterminal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.decision_allNonterminal

/-- info: 'Vegas.SourceProgram.Setup.openingExtension_disclosing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.openingExtension_disclosing

/-- info: 'Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff

/-- info: 'Vegas.SourceProgram.Setup.exclusion_failure_context_value' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exclusion_failure_context_value

/-- info:
'Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_without_voluntary_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_without_voluntary_failure

/-- info: 'Vegas.SourceProgram.CommitPrefix.Close.retry_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Close.retry_checkpoint

/-- info: 'Vegas.SourceProgram.CommitCloseChain.reset_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitCloseChain.reset_bound

/-- info: 'Vegas.SourceProgram.Setup.deviation_history_values_representation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.deviation_history_values_representation

/-- info: 'Vegas.SourceProgram.Setup.run_copied_opponents_from_values_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.run_copied_opponents_from_values_history

/-- info: 'Vegas.SourceProgram.Setup.exists_values_site_continuation_ge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_values_site_continuation_ge

/-- info: 'Vegas.SourceProgram.Setup.values_sequentialEquilibrium_preserved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.values_sequentialEquilibrium_preserved

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.retry_restore'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.retry_restore

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.step_potential_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_potential_lt

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryProtocol_bounded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryProtocol_bounded

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_generation_le_players'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_generation_le_players

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryModel_perfectRecall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryModel_perfectRecall

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryModel_decisionAntichain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryModel_decisionAntichain

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.step_empty_point'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_empty_point

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_finite_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_finite_history

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryReference_fullyMixed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryReference_fullyMixed

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.step_intended_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_intended_support

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryClearTrace_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryClearTrace_length

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryClearTrace_observe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryClearTrace_observe

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.step_lifted_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_lifted_intended

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryClearHistory_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryClearHistory_lift

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryInformation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryInformation_observed

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryRestriction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryRestriction

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_clear_step_reconstruct'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_clear_step_reconstruct

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_retained_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_retained_clear

/-- info: 'Vegas.SourceProgram.Setup.exists_consistent_commitRecovery_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_consistent_commitRecovery_completion

/-- info: 'Vegas.SourceProgram.Registry.FailureExtension.completedBy_all_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Registry.FailureExtension.completedBy_all_eq

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.step_preserves_excluded_or_owesFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_preserves_excluded_or_owesFailure

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_blockFrontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_blockFrontier

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_failuresCovered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_failuresCovered

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_terminal_excluded_of_owesFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_terminal_excluded_of_owesFailure

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_terminal_payoff_of_checkpointed_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_terminal_payoff_of_checkpointed_debt

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_initialized_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_initialized_joint

/-- info: 'Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_deviation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_deviation_payoff

/-- info: 'Vegas.SourceProgram.Setup.hidden_commit_terminal_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.hidden_commit_terminal_debt

/-- info: 'Vegas.SourceProgram.Setup.hidden_commit_recovery_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.hidden_commit_recovery_step

/-- info: 'Vegas.SourceProgram.lifted_commit_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.lifted_commit_successor

/-- info: 'Vegas.SourceProgram.CommitPrefix.Close.reaches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Close.reaches

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.reaches_of_lifted_nonCommit_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.reaches_of_lifted_nonCommit_path

/-- info: 'Vegas.SourceProgram.CommitPrefix.Attempt.compiledTail'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.compiledTail

/-- info: 'Vegas.SourceProgram.CommitPrefix.liftPoint_recovery'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.liftPoint_recovery

/-- info: 'Vegas.SourceProgram.CommitPrefix.Close.reaches_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Close.reaches_lift

/-- info: 'Vegas.SourceProgram.Setup.recoveryTrace_of_reaches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.recoveryTrace_of_reaches

/-- info: 'Vegas.SourceProgram.Setup.commitRecovery_clear_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_clear_info_eq

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryInformation_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryInformation_of_clear

/-- info: 'Vegas.SourceProgram.CommitPrefix.prefixLaw_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_continuation

/-- info: 'Vegas.SourceProgram.CommitPrefix.prefixLaw_view_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_view_eq

/-- info: 'Vegas.SourceProgram.CommitPrefix.prefixPosterior_binding_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixPosterior_binding_joint

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryClearInformation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryClearInformation_observed

/-- info: 'Vegas.SourceProgram.Setup.commitRecoveryClearInformation_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryClearInformation_intended

/-- info: 'Vegas.SourceProgram.Setup.sourceTrace_intended_or_owes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.sourceTrace_intended_or_owes

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_voluntaryFailure_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_voluntaryFailure_step

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_voluntaryFailure_context_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_voluntaryFailure_context_value

/-- info:
'Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery_continuing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery_continuing

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_approximation_continuing_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_approximation_continuing_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_approximation_failure_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_approximation_failure_probability

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_approximation_missing_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_approximation_missing_probability

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryReference_raw_eq_of_menu'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryReference_raw_eq_of_menu

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_prefix_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_prefix_continuation

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_prefix_next_raw_at_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_prefix_next_raw_at_trace

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_approximation_missing_eq_at_traces'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_approximation_missing_eq_at_traces

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_no_omission_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_no_omission_factorization

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_clear_prefix_conditioning'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_clear_prefix_conditioning

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_nonmissing_prefix_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_nonmissing_prefix_continuation

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_nonmissing_belief'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_nonmissing_belief

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_compiled_policy_raw_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_compiled_policy_raw_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_run_nonmissing_commit_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_run_nonmissing_commit_clear

/-- info:
'Vegas.SourceProgram.CommitPrefix.length_le_commit_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.length_le_commit_window

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_compiled_policy_raw_law_of_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_compiled_policy_raw_law_of_intended

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_commit_window_factorization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_commit_window_factorization

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_belief_commit_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_belief_commit_window

/-- info:
'Vegas.SourceProgram.Setup.exists_commitRecovery_choice_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_commitRecovery_choice_floor

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_intended_of_clear_nonCommit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_intended_of_clear_nonCommit

/-- info:
'Vegas.SourceProgram.ProtocolState.intended_of_clear_nonCommit_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.intended_of_clear_nonCommit_path

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.intended_of_clear_nonCommit_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.intended_of_clear_nonCommit_path

/-- info:
'Vegas.SourceProgram.CommitPrefix.exists_snoc'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.exists_snoc

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_views_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_views_product

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_histories_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_histories_product

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_history_prefix_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_history_prefix_product

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_readout

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_conditional'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_conditional

/-- info:
'Vegas.SourceProgram.CommitPrefix.binding_kernel_protocolAction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.binding_kernel_protocolAction

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_owned_word_conditional'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_owned_word_conditional

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_entry_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_entry_readout

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_entry_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_binding_entry_posterior

/-- info:
'Vegas.SourceProgram.CommitPrefix.ownedEntryWordKernel_at_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.ownedEntryWordKernel_at_entry

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_entry_word_kernels'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_entry_word_kernels

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_view_eq_of_history_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_view_eq_of_history_eq

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixPosterior_eq_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixPosterior_eq_history

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_wordAction_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_wordAction_history

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_local_source_patch'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_local_source_patch

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_local_source_patch_continuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_local_source_patch_continuation

/-- info:
'Vegas.SourceProgram.CommitPrefix.length_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.length_append

/-- info:
'Vegas.SourceProgram.CommitPrefix.entryView_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.entryView_append

/-- info:
'Vegas.SourceProgram.CommitPrefix.wordAction_append_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.wordAction_append_prefix

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_append

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.entryView'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.entryView

/-- info:
'Vegas.SourceProgram.CommitPrefix.exists_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.exists_split

/-- info:
'Vegas.SourceProgram.CommitPrefix.exists_binding_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.exists_binding_split

/-- info:
'Vegas.SourceProgram.CommitPrefix.binding_split_of_layout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.binding_split_of_layout

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_focal_view_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_focal_view_product

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_focal_view_entry_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_focal_view_entry_product

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.split

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.atRank_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.atRank_lift

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.atRank_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.atRank_lift

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_own_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_own_history

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_own_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_own_history

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_surviving_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_surviving_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_surviving_ownPlay_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_surviving_ownPlay_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_surviving_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_surviving_info_eq

/-- info:
'Vegas.SourceProgram.CommitPrefix.liftPoint_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.liftPoint_append

/-- info:
'Vegas.SourceProgram.Config.view_automaticCommit_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.view_automaticCommit_congr

/-- info:
'Vegas.SourceProgram.ProtocolState.observe_withHistory_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.observe_withHistory_congr

/-- info:
'Vegas.SourceProgram.ProtocolState.automaticCommitBlock_observe_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.automaticCommitBlock_observe_congr

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_observed_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_observed_congr

/-- info:
'Vegas.SourceProgram.ProtocolView.entryView_recoveryStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.entryView_recoveryStep

/-- info:
'Vegas.SourceProgram.ProtocolView.atRank_recoveryStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.atRank_recoveryStep

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNonmissingSourcePolicy_clear_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNonmissingSourcePolicy_clear_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear_missing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear_missing

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear_mixture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePolicy_clear_mixture

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_clear_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_clear_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_clear_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_clear_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_source_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_source_run

/-- info:
'Vegas.SourceProgram.ProtocolView.recover_recoveryStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.recover_recoveryStep

/-- info:
'Vegas.SourceProgram.ProtocolView.recoveryStep_predecessor_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.recoveryStep_predecessor_eq

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_plan_config_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_plan_config_joint

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueAssessment_nonmissing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueAssessment_nonmissing

/-- info:
'Vegas.SourceProgram.ProtocolState.observe_entry_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.observe_entry_congr

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_split

/-- info:
'Vegas.SourceProgram.CommitPrefix.prefixLaw_foreign_focal_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.prefixLaw_foreign_focal_view

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_saved_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_saved_rank

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_saved_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_saved_rank

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_saved_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_saved_rank

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_saved_view_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_saved_view_eq

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.close_retry_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.close_retry_lift

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.observe_reflect'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.observe_reflect

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.residual_eq_of_instructionCount'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.residual_eq_of_instructionCount

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.instructions_closed_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.instructions_closed_lift

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.close_clean_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.close_clean_lift

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.close_exhausted_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.close_exhausted_lift

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_commit_pure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_commit_pure

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_unique_of_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_unique_of_commit

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_inside_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_inside_commit

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_prefix_inside_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_prefix_inside_commit

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_history_eq_of_commit_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_history_eq_of_commit_window

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_noncommit_atPoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_noncommit_atPoint

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noncommit_public_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noncommit_public_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noncommit_predecessor_private'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noncommit_predecessor_private

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.noncommit_of_reveal_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.noncommit_of_reveal_window

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.noncommit_of_sample_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.noncommit_of_sample_rank

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noncommit_signals_eq_of_rank_windows'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noncommit_signals_eq_of_rank_windows

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_saved_remaining_le_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_saved_remaining_le_of_prefix

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noncommit_choice_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noncommit_choice_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_clear_noncommit_atom_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_clear_noncommit_atom_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_source_content_density'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_source_content_density

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_opening_factor_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_opening_factor_bounds

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_binding_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_binding_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValuePlan_binding_likelihood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValuePlan_binding_likelihood

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_source_binding_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_source_binding_bounds

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_opening_factor_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_opening_factor_tendsto

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_run

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_record_likelihood'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_record_likelihood

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPosterior_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPosterior_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_condition_records'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_condition_records

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_foreign_of_focal_record'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPlan_foreign_of_focal_record

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPolicyPosterior_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPolicyPosterior_split

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_attempt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_attempt

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_surviving_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_surviving_view

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_eq_of_unchanged_exclusions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.withoutMisses_eq_of_unchanged_exclusions

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedInformation_menu'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedInformation_menu

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noMiss_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noMiss_information

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_eraseHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_eraseHistory

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.eraseHistory_retry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.eraseHistory_retry

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.eraseHistory_exhausted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.eraseHistory_exhausted

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.eraseHistory_close'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.eraseHistory_close

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryBindingAtom_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryBindingAtom_surjective

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryBindingValueLaw_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryBindingValueLaw_fullSupport

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.instructions_closed_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.instructions_closed_lift

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedModel_actsOnce'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedModel_actsOnce

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPlan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPlan_run

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPlan_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPlan_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPosterior_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedPolicyPosterior_split

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_eraseHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_eraseHistory

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedHistory_extend'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedHistory_extend

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_oneStep_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_oneStep_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_runUntil_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_runUntil_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_terminal_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_terminal_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_terminal_readout_excluded_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_terminal_readout_excluded_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_terminal_readout_excluded_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_terminal_readout_excluded_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_commit_public_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_commit_public_congr

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_eraseHistory_eq_of_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_eraseHistory_eq_of_failure

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_failed_attempt_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_failed_attempt_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_failed_attempt_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedProfile_failed_attempt_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryBindingValueAtom_surjective'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryBindingValueAtom_surjective

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedBindingValueEquiv_map'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedBindingValueEquiv_map

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueFlags_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueFlags_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueTremble_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueTremble_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueTremble_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueTremble_binding

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueTremble_binding_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueTremble_binding_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_run

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_source_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_source_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryDomainPolicy_consistent_update'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryDomainPolicy_consistent_update

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_posterior_split'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryDomainPlan_posterior_split

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryTrembledProfile_fullyMixed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryTrembledProfile_fullyMixed

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryTrembledProfile_plan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryTrembledProfile_plan_run

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noMiss_observe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noMiss_observe

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.noMiss_instruction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.noMiss_instruction

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_attempt_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_attempt_entry

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_noMiss_prefix_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_noMiss_prefix_information

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_genuine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_genuine

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_idempotent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_idempotent

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_menu'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_menu

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased_idempotent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased_idempotent

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedChoice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedChoice

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_genuine_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_genuine_history

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased_word_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_erased_word_length

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_raw

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_failed_attempt_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagLaw_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagLaw_choice

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryErasedModel_record_clock_nodup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryErasedModel_record_clock_nodup

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_current_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_current_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_record_present'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_record_present

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_posterior_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_posterior_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_toBehavioralWith'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_toBehavioralWith

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryFlagPlan_run

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_current_record_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_current_record_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_record_present'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_record_present

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_posterior_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_posterior_readout

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_toBehavioralWith'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_toBehavioralWith

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPlan_run

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueFlags_binding_spec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueFlags_binding_spec

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_spec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_spec

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_congr

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_joint_missed_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_joint_missed_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_raw_public_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_raw_public_congr

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_omissionRecall_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_omissionRecall_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_failed_attempt_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_failed_attempt_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_failed_attempt_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_failed_attempt_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueReference_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueReference_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPooledDomainLaw_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPooledDomainLaw_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_bind

/-- info:
'Vegas.SourceProgram.Setup.exists_consistent_commitRecovery_normalized_pool'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_consistent_commitRecovery_normalized_pool

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.MetadataEq.close'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.MetadataEq.close

/-- info:
'Vegas.SourceProgram.Config.splice_automaticCommit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_automaticCommit

/-- info:
'Vegas.SourceProgram.Config.splice_automaticReveal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_automaticReveal

/-- info:
'Vegas.SourceProgram.Config.splice_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_commit

/-- info:
'Vegas.SourceProgram.Config.splice_disclosureResult'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_disclosureResult

/-- info:
'Vegas.SourceProgram.Config.splice_reveal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_reveal

/-- info:
'Vegas.SourceProgram.Config.splice_sample'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_sample

/-- info:
'Vegas.SourceProgram.Config.splice_view_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_view_other

/-- info:
'Vegas.SourceProgram.Config.splice_view_self'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.splice_view_self

/-- info:
'Vegas.SourceProgram.ProtocolState.history_splice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.history_splice

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_commit_observe_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_commit_observe_congr

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_metadata'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_metadata

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_mass_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_mass_eq

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_observe_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_observe_congr

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_public_excluded_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_public_excluded_eq

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_result_eq_of_public'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_result_eq_of_public

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_splice_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_splice_support

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_automaticCommitBlock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_automaticCommitBlock

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_entry

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_metadata_eq_others'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_metadata_eq_others

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_observe_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_observe_other

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_observe_self'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_observe_self

/-- info:
'Vegas.SourceProgram.ProtocolState.splice_withHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.splice_withHistory

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_missed_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_binding_missed_congr

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_counterfactual_reach_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_counterfactual_reach_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_nonfocal_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_nonfocal_info_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_nonfocal_reach_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_nonfocal_reach_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_reach_cross_mul_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedFlagPolicy_reach_cross_mul_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_counterfactual_reach_eq_of_public_and_coordinates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecovery_counterfactual_reach_eq_of_public_and_coordinates

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_history_eq_of_public_and_joints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_history_eq_of_public_and_joints

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_info_eq_of_public_and_coordinate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_info_eq_of_public_and_coordinate

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_metadata_of_publicRecall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_metadata_of_publicRecall

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_reach_cross_mul_eq_of_public_and_coordinates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_reach_cross_mul_eq_of_public_and_coordinates

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_step_eq_of_public'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_step_eq_of_public

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_step_mass_eq_of_public'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_step_mass_eq_of_public

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_step_observed_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_step_observed_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_supported_step_of_erased_history_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_supported_step_of_erased_history_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_supported_suffix_of_erased_history_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_supported_suffix_of_erased_history_eq

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_base'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_base

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.splice_close'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.splice_close

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_base'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_base

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_splice_support_of_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_splice_support_of_raw

/-- info:
'Vegas.SourceProgram.Config.public_view_eq_for_observer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.public_view_eq_for_observer

/-- info:
'Vegas.SourceProgram.ProtocolState.public_observe_eq_for_observer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.public_observe_eq_for_observer

/-- info:
'Vegas.SourceProgram.ProtocolState.sourceObserve_base_eq_of_erased_observe_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.sourceObserve_base_eq_of_erased_observe_eq

/-- info:
'Vegas.SourceProgram.Setup.attemptPublicRecall_eq_for_observer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.attemptPublicRecall_eq_for_observer

/-- info:
'Vegas.SourceProgram.Setup.attemptPublicSignal_eq_for_observer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.attemptPublicSignal_eq_for_observer

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_base_observe_eq_of_query_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_base_observe_eq_of_query_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_base_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_base_of_prefix

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_hybrid_of_initial_inputs'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_hybrid_of_initial_inputs

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_initial_hiddenAgree_of_query_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_initial_hiddenAgree_of_query_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_step_splice_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_step_splice_support

/-- info:
'Vegas.SourceProgram.hiddenAgree_of_sourceObserve_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.hiddenAgree_of_sourceObserve_eq

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.InstructionPath.addresses_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.InstructionPath.addresses_length

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_preserves_intendedFor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_preserves_intendedFor

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_preserves_intendedFor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_preserves_intendedFor

/-- info:
'Vegas.SourceProgram.Config.IntendedFor.automaticCommit_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.IntendedFor.automaticCommit_other

/-- info:
'Vegas.SourceProgram.Config.intendedFor_withHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.intendedFor_withHistory

/-- info:
'Vegas.SourceProgram.ProtocolState.commitOwners_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.commitOwners_entry

/-- info:
'Vegas.SourceProgram.ProtocolState.commitOwners_withHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.commitOwners_withHistory

/-- info:
'Vegas.SourceProgram.ProtocolState.intendedFor_automaticCommitBlock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.intendedFor_automaticCommitBlock

/-- info:
'Vegas.SourceProgram.ProtocolState.intendedFor_recoveryStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.intendedFor_recoveryStep

/-- info:
'Vegas.SourceProgram.ProtocolState.intendedFor_withHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.intendedFor_withHistory

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_public_excluded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryStep_noncommit_public_excluded

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.publicSuccessorExclusions_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.publicSuccessorExclusions_lift

/-- info:
'Vegas.SourceProgram.ProtocolView.publicPadding_observe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.publicPadding_observe

/-- info:
'Vegas.SourceProgram.ProtocolView.publicSuccessorExclusions_reveal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.publicSuccessorExclusions_reveal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_bayes_eq_of_erasedInformation_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_bayes_eq_of_erasedInformation_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_commit_public_readback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_commit_public_readback

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_coordinate_eq_of_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_coordinate_eq_of_info_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_erasedInformation_read'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_erasedInformation_read

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_hybrid_of_erasedInformation_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_hybrid_of_erasedInformation_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_information_fiber_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_information_fiber_equiv

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_publicRecall_addresses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_publicRecall_addresses

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_publicRecall_eq_of_erasedInformation_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_public_expansion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_public_expansion

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_public_rank_of_reaches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_public_rank_of_reaches

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_same_generation_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_same_generation_length

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_virtual_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_virtual_history

/-- info:
'Vegas.SourceProgram.Setup.recoveryInstructionPath_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.recoveryInstructionPath_information

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.no_failure_iff_closed_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.no_failure_iff_closed_readout

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.no_failure_iff_completed_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.no_failure_iff_completed_readout

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.own_bindings_success_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.own_bindings_success_iff

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.own_joints_not_failed_of_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.own_joints_not_failed_of_bound

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.preserves_failedBinding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.preserves_failedBinding

/-- info:
'Vegas.SourceProgram.CommitPrefix.bindingsHoldValues_liftPoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.bindingsHoldValues_liftPoint

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_success_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_success_readout

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.eraseHistory_success_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.eraseHistory_success_readout

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_commit_inside_or_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_commit_inside_or_exit

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.step_noncommit_public_controls'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.step_noncommit_public_controls

/-- info:
'Vegas.SourceProgram.ProtocolState.bindingsHoldValues_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.bindingsHoldValues_entry

/-- info:
'Vegas.SourceProgram.ProtocolState.bindingsHoldValues_withHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.bindingsHoldValues_withHistory

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.bindingsHoldValues_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.bindingsHoldValues_lift

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_local_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_local_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_stopped_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_stopped_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_stopped_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_stopped_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_bayes_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_terminal_local_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissErasedProfile_terminal_local_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_baseline_value_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_baseline_value_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_conditional_gain_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_conditional_gain_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_conditional_value_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_conditional_value_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_run_commit_window_instructions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_run_commit_window_instructions

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_run_until_attempt_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_run_until_attempt_exit

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_splice_erased_state_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_splice_erased_state_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_instructions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_instructions

/-- info:
'Vegas.SourceProgram.CommitPrefix.attempt_of_instructions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.attempt_of_instructions

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.instructions_of_nonCommit_path'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.instructions_of_nonCommit_path

/-- info:
'Vegas.SourceProgram.ProtocolView.intendedWord_eraseHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.intendedWord_eraseHistory

/-- info:
'Vegas.SourceProgram.ProtocolView.intended_step_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.intended_step_word

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_raw

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPooledDomainLaw_honest_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPooledDomainLaw_honest_raw

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_honest_information_eq_of_query_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_honest_information_eq_of_query_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_beliefs_converge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_beliefs_converge

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_beliefs_of_rates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_beliefs_of_rates

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_raw_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_raw_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_run_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_run_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_success'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_success

/-- info:
'Vegas.SourceProgram.Setup.intended_history_of_typed_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_history_of_typed_view

/-- info:
'Vegas.SourceProgram.Setup.intended_observe_eq_of_erased'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_observe_eq_of_erased

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNoMissInformation_eq_of_unchanged_exclusions

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_failed_window_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_failed_window_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_joint_missed_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_joint_missed_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_missed_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_missed_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_window_omission_law_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_window_omission_law_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryValueTremble_missed_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryValueTremble_missed_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryWithAttemptExclusions_fixed_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryWithAttemptExclusions_fixed_of_prefix

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_erased_eq_of_query_eq_of_unchanged_exclusions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_erased_eq_of_query_eq_of_unchanged_exclusions

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_failed_window_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_failed_window_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_joint_missed_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_joint_missed_law

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_limit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_limit

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_limit_extends'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_honest_limit_extends

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_component_gain_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_component_gain_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_gain_nonpos_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_gain_nonpos_iff

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_gain_sum'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_gain_sum

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_query_fiber_cases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_query_fiber_cases

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_query_fiber_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_query_fiber_of_history

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_window_omission_law_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_window_omission_law_eq

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.failedBinding_of_failed_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.failedBinding_of_failed_joint

/-- info:
'Vegas.SourceProgram.CommitPrefix.Attempt.failedOwners_eq_empty_iff_no_missed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.Attempt.failedOwners_eq_empty_iff_no_missed

/-- info:
'Vegas.SourceProgram.CommitPrefix.failedBinding_liftPoint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitPrefix.failedBinding_liftPoint

/-- info:
'Vegas.SourceProgram.CommitRecoveryState.close_checkpointed_owesFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.close_checkpointed_owesFailure

/-- info:
'Vegas.SourceProgram.ProtocolState.exists_committing_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.exists_committing_entry

/-- info:
'Vegas.SourceProgram.ProtocolSuffix.failedBinding_lift'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolSuffix.failedBinding_lift

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_decision_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_decision_witness

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_ordinary_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryHonestPoolPins_ordinary_witness

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_accepted_failure_value_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_accepted_failure_value_le

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_failed_local_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_failed_local_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_terminal_of_prescribed

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_terminal_window

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_window_omissions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_local_window_omissions

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_unpinned_converges'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryPoolComponent_unpinned_converges

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_commit_window_success_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_commit_window_success_iff

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_component_missed_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_component_missed_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_conditional_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_conditional_value_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_failed_commit_attempt_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_failed_commit_attempt_payoff

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_failed_commit_window_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_failed_commit_window_payoff

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_local_failed_window_recorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_local_failed_window_recorded

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_accepted_failure_conditional_value_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.commitRecovery_normalized_accepted_failure_conditional_value_le

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_belief_terminal_joint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_belief_terminal_joint_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_conditional_value_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_conditional_value_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_failed_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_gain_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_gain_eq

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_localOptimal_of_erased_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_localOptimal_of_erased_copy

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_ordinary_agent_gain_nonpos_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_ordinary_agent_gain_nonpos_iff

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_ordinary_agent_gain_sum'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_ordinary_agent_gain_sum

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pool_complement_known_failed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pool_complement_known_failed

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_component_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_component_optimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_limit_domain_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_limit_domain_optimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_failed_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_stopped_attempt_failed_payoff

/-- info:
'Vegas.SourceProgram.Setup.prefix_excluded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.prefix_excluded

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_domain_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_domain_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_mass_loss'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_mass_loss

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_mass_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_mass_lower

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_value_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedTrembledProfile_success_value_error

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_accepted_failure_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_accepted_failure_le

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_localOptimal_of_domain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_localOptimal_of_domain

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_pinned_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_pinned_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_noncommit_limit_choice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_noncommit_limit_choice

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_noncommit_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_noncommit_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_pooled_limit_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_pooled_limit_sequentialEquilibrium

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_success_belief_value_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_success_belief_value_error

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_commitment_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_commitment_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.continuing_noncommit_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.continuing_noncommit_unique

/-- info:
'Vegas.SourceProgram.nonfailure_noncommit_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.nonfailure_noncommit_unique

/-- info:
'Vegas.SourceProgram.ProtocolView.available_virtualBindings'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.available_virtualBindings

/-- info:
'Vegas.SourceProgram.ProtocolView.eraseHistory_virtualBindings'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.eraseHistory_virtualBindings

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedDomainLaw_converges'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedDomainLaw_converges

/-- info:
'Vegas.SourceProgram.Setup.commitRecoveryNormalizedDomainLaw_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoveryNormalizedDomainLaw_raw

/-- info:
'Vegas.SourceProgram.Setup.commitRecoverySuccessValue_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecoverySuccessValue_tendsto

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_domain_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_normalized_limit_domain_support

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_success_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_success_regret

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_success_regret_uniform'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_pooled_ordinary_success_regret_uniform

/-- info:
'Vegas.SourceProgram.Setup.exists_commitRecovery_sequentialEquilibrium_construction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_commitRecovery_sequentialEquilibrium_construction

/-- info:
'Vegas.SourceProgram.Setup.exists_commitRecovery_sequentialEquilibrium_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_commitRecovery_sequentialEquilibrium_extension

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryProtocol_terminates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryProtocol_terminates

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryEraseTrace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryEraseTrace

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryProposal_reveal_success'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryProposal_reveal_success

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryEraseInfo_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryEraseInfo_observed

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryQuery_semantic_genuine'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryQuery_semantic_genuine

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryTrembledLaw_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryTrembledLaw_fullSupport

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryDomainLaw_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryDomainLaw_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryTrembledDomainLaw_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryTrembledDomainLaw_value_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_step_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_step_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_supported_suffix_of_erased_history_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_supported_suffix_of_erased_history_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryQuery_eq_of_erased_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryQuery_eq_of_erased_history

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryProposal_splice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryProposal_splice

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_splice_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_splice_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_splice_joint_legal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_splice_joint_legal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_step_splice_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_step_splice_support

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryPublicRecall_semantic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPublicRecall_semantic

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_information_extend_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_information_extend_congr

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_lift_joint_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_lift_joint_word

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_eq_of_actor_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_eq_of_actor_information

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_info_eq_of_semantic_public_coordinate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_info_eq_of_semantic_public_coordinate

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryProposal_rank'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryProposal_rank

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_prefix_eq_of_same_proposal_address'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_prefix_eq_of_same_proposal_address

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_proposal_word_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_proposal_word_origin

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_fresh_address'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryProposalOf_fresh_address

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryProposalWord_addresses_nodup'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryProposalWord_addresses_nodup

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryArchive_eq_of_same_address'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryArchive_eq_of_same_address

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryQuery_trace_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryQuery_trace_length

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_prefix_eq_of_same_query'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_prefix_eq_of_same_query

/-- info:
'Vegas.SourceProgram.ProtocolView.actor_publicOnly'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolView.actor_publicOnly

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryAvailable_reveal_of_not_commit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryAvailable_reveal_of_not_commit

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_reveal_joint_of_legal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_reveal_joint_of_legal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryHistory_eq_of_semantic_word'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryHistory_eq_of_semantic_word

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_coordinate_eq_of_info_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_coordinate_eq_of_info_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryPublicRecall_eq_of_erased_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPublicRecall_eq_of_erased_archive

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryDeltaRecall_eq_of_split_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryDeltaRecall_eq_of_split_information

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_hybrid_of_erased_information_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_hybrid_of_erased_information_archive

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_counterfactual_cross_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_counterfactual_cross_factor

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_counterfactual_reach_eq_of_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_counterfactual_reach_eq_of_reference

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_information_fiber_equiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_information_fiber_equiv

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_bayes_eq_of_erased_information_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_bayes_eq_of_erased_information_archive

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_oneStep_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_oneStep_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_runUntil_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_runUntil_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_terminal_erased_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_terminal_erased_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_bayes_stopped_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_bayes_stopped_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_bayes_terminal_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_bayes_terminal_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryComponentChoice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryComponentChoice

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryPrescribedProfile_terminal_local_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPrescribedProfile_terminal_local_law

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_bayes_local_terminal_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_bayes_local_terminal_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryPayoff_eq_image'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPayoff_eq_image

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_conditional_value_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_conditional_value_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_baseline_value_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_baseline_value_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_conditional_gain_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_conditional_gain_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_query_ordinary_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_query_ordinary_of_history

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_query_fiber_cases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_query_fiber_cases

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_failed_attempt_terminal_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_failed_attempt_terminal_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_stopped_window_omission_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_stopped_window_omission_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_stopped_window_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_stopped_window_boundary

open Vegas.SourceProgram.Setup in
/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_failed_local_terminal_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms proposalRecoveryNormalizedTrembledProfile_failed_local_terminal_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_failed_conditional_gain_eq_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_normalized_failed_conditional_gain_eq_zero

/-- info:
'Vegas.SourceProgram.Setup.exists_consistent_proposalRecovery_pool'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_consistent_proposalRecovery_pool

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryPooledDomainLaw_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPooledDomainLaw_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pool_complement_known_failed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_pool_complement_known_failed

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pooled_component_gain_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_pooled_component_gain_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_gain_sum'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_gain_sum

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_component_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_component_optimal

/-- info:
'Vegas.SourceProgram.ProtocolState.recoveryProposal_virtual_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.recoveryProposal_virtual_eq

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_virtual_event_delta'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_virtual_event_delta

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_virtual_labeled_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_virtual_labeled_trace

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_virtual_labeled_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_virtual_labeled_archive

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_isDecisionInfo_of_surviving_actor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_isDecisionInfo_of_surviving_actor

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_clear_ordinary_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_clear_ordinary_archive

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryInformation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryInformation_observed

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryInformation_menu'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryInformation_menu

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_initialized_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_initialized_history

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_initialized_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_initialized_joint

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryHonestPoolPins_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryHonestPoolPins_raw

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_terminal_payoff_of_checkpointed_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_terminal_payoff_of_checkpointed_debt

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_voluntaryFailure_context_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_voluntaryFailure_context_value

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_failed_commit_prefix_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_failed_commit_prefix_payoff

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_accepted_failure_conditional_value_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_normalized_accepted_failure_conditional_value_le

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_limit_domain_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_pooled_ordinary_limit_domain_optimal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_raw_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_raw_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_beliefs_of_rates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_beliefs_of_rates

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_hidden_commit_terminal_debt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_hidden_commit_terminal_debt

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_deviation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_deviation_payoff

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_limit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_honest_limit

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_limit_localOptimal_of_domain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_limit_localOptimal_of_domain

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_noncommit_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_noncommit_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_failed_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_normalized_failed_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_limit_localOptimal_of_erased_copy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_normalized_limit_localOptimal_of_erased_copy

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryHonestPoolPins_ordinary_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryHonestPoolPins_ordinary_witness

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_pooled_commitment_limit_localOptimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_pooled_commitment_limit_localOptimal

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_normalized_pooled_limit_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecovery_normalized_pooled_limit_sequentialEquilibrium

/-- info:
'Vegas.SourceProgram.Setup.exists_proposalRecovery_sequentialEquilibrium_construction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_proposalRecovery_sequentialEquilibrium_construction

/-- info:
'Vegas.SourceProgram.Setup.exists_proposalRecovery_sequentialEquilibrium_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_proposalRecovery_sequentialEquilibrium_extension

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryComponentTrembledLaw_ordinary_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryComponentTrembledLaw_ordinary_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_ordinary_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_ordinary_lower

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_future_flags_withinTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_future_flags_withinTV

/-- info:
'Vegas.SourceProgram.Setup.proposalRecovery_future_foreign_flags_withinTV'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_future_foreign_flags_withinTV

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_ordinary_virtual_erased_info'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_ordinary_virtual_erased_info

/-- info:
'Vegas.SourceProgram.Setup.commitRecovery_ordinary_virtual_normalized_info'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.commitRecovery_ordinary_virtual_normalized_info

/-- info: 'Vegas.SourceProgram.Config.FocalRepair.commit_kept' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.FocalRepair.commit_kept

/-- info: 'Vegas.SourceProgram.Config.FocalRepair.reveal_preparation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Config.FocalRepair.reveal_preparation

/-- info: 'Vegas.SourceProgram.ProtocolState.FocalRepair.preparation_recoveryStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.FocalRepair.preparation_recoveryStep

/-- info: 'Vegas.SourceProgram.CommitRecoveryState.FocalRepair.preparation_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.CommitRecoveryState.FocalRepair.preparation_step

/-- info: 'Vegas.SourceProgram.ProtocolState.FocalRepair.recoveryProposal_preparation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.FocalRepair.recoveryProposal_preparation

/-- info: 'Vegas.SourceProgram.ProtocolState.repairPreparationJoint_prepared' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.ProtocolState.repairPreparationJoint_prepared

/-- info: 'Vegas.SourceProgram.Setup.proposalRecovery_preparation_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecovery_preparation_history

/-- info: 'Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_preparation_domination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_preparation_domination

/-- info: 'Vegas.SourceProgram.Setup.exists_proposalRecoveryPreparation_response_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_proposalRecoveryPreparation_response_floor

/-- info: 'Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_generated_atom_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryNormalizedTrembledProfile_generated_atom_le

/-- info: 'Vegas.SourceProgram.Setup.proposalRecoveryPrepared_word_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryPrepared_word_lower

/-- info: 'Vegas.SourceProgram.Setup.proposalRecoveryGenerated_word_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.proposalRecoveryGenerated_word_upper

/-- info: 'Vegas.SourceProgram.Setup.exists_proposalRecovery_generatedPreparation_posterior_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_proposalRecovery_generatedPreparation_posterior_bound

/-- info: 'Vegas.SourceProgram.Setup.exists_proposalRecovery_foreignPreparation_posterior_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.exists_proposalRecovery_foreignPreparation_posterior_bound
