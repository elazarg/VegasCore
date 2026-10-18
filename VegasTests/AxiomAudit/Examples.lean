/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Interaction
import Vegas

/-! # Examples proof dependency regressions -/

/-- info: 'Vegas.Examples.CommittedResolutionRecovery.initialized_clean_recovery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionRecovery.initialized_clean_recovery

/-- info: 'Vegas.Examples.CommittedResolutionReadout.bob_success_true' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionReadout.bob_success_true

/-- info: 'Vegas.Examples.CommittedResolutionBobService.canonical_bob_round' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobService.canonical_bob_round

/-- info: 'Vegas.Examples.CommittedResolutionBobAudit.canonical_bob_audit_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobAudit.canonical_bob_audit_clear

/-- info: 'Vegas.Examples.CommittedResolutionBobDecision.bob_continuation_current_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobDecision.bob_continuation_current_law

/-- info: 'Vegas.Examples.CommittedResolutionBobFailure.bob_failed_response_at_horizon' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobFailure.bob_failed_response_at_horizon

/-- info: 'Vegas.Examples.CommittedResolutionBobReadout.bob_continuation_readout_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobReadout.bob_continuation_readout_eq

/-- info: 'Vegas.Examples.CommittedResolutionReliability.exists_contract_below_failure_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionReliability.exists_contract_below_failure_floor

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.consistent_bobBinding_uniform' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.consistent_bobBinding_uniform

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_value_eq_safe_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_value_eq_safe_iff

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_safe_probability_of_near_optimal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.bob_answer_law_safe_probability_of_near_optimal

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_withholding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_withholding

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_sequential_equilibrium

/-- info: 'Vegas.Examples.CommittedResolutionBobIncentive.canonical_bob_response_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionBobIncentive.canonical_bob_response_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_terminal_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_equilibrium_with_safe_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.exists_withholding_equilibrium_with_safe_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.bayes_rational_terminal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.bayes_rational_terminal_law

/-- info: 'Vegas.Examples.CommittedResolutionErasure.certain_late_inclusion_with_joint_contract'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommittedResolutionErasure.certain_late_inclusion_with_joint_contract

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.clock_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.clock_history

/-- info: 'Vegas.Examples.LateOpeningRuntimeServiceErasure.scheduler_blind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeServiceErasure.scheduler_blind

/-- info: 'Vegas.Examples.LateOpeningRuntimeReadout.bob_continuation_success_immutable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeReadout.bob_continuation_success_immutable

/-- info: 'Vegas.Examples.LateOpeningRuntimeUtility.alice_accepted_openings_audit_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeUtility.alice_accepted_openings_audit_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.completes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.completes

/-- info: 'Vegas.Examples.LateOpeningRuntimeObservation.leaks_singleton' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeObservation.leaks_singleton

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.binding_values_covered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.binding_values_covered

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.initial_values_covered' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.initial_values_covered

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.opportunity' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.opportunity

/-- info: 'Vegas.Examples.LateOpeningRuntimeLatePrefix.firstBob_recall_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLatePrefix.firstBob_recall_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.contract_and_blind' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.contract_and_blind

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.protected_submission_receipt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.protected_submission_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_nash_iff

/-- info: 'Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeNash.first_opportunity_settlement_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeFiberEvidence.bob_information_no_packets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFiberEvidence.bob_information_no_packets

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateAcceptance.answerDecision_unseen_timing_info'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLateAcceptance.answerDecision_unseen_timing_info

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateHistories.answerDecision_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLateHistories.answerDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeReliability.exists_joint_service_below_failure_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeReliability.exists_joint_service_below_failure_floor

/-- info: 'Vegas.Examples.LateOpeningRuntimeTerminalReceipt.terminal_receipt_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeTerminalReceipt.terminal_receipt_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeTerminalReceipt.exists_joint_service_with_exact_failure

/-- info: 'Vegas.Examples.LateOpeningRuntimeRetryAudit.alice_two_envelopes_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRetryAudit.alice_two_envelopes_utility_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_dominates' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_dominates

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_regret' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobIncentive.canonical_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_sequential_equilibrium

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_expected_payoff_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_expected_payoff_lower

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_strictly_beats_second_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceContinuation.quiet_strictly_beats_second_packet

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceContinuation.exists_service_with_quiet_normalization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceContinuation.exists_service_with_quiet_normalization

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRationality.equilibrium_final_failure_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRationality.equilibrium_final_failure_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRationality.final_failure_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRationality.final_failure_le_of_deviation_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuffix.finalDecision_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuffix.finalDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuffix.final_disclosure_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuffix.final_disclosure_class_nonempty

/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedOpening.protected_miss_terminal_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedOpening.protected_miss_terminal_failure

/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedReceipt.native_almost_sure_success_protected_receipt_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeProtectedReceipt.native_almost_sure_success_protected_receipt_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyBobAudit.early_submission_continuation_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEarlyBobAudit.early_submission_continuation_utility_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceDecision.decision_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceDecision.decision_of_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceIncentive.quiet_second_packet_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceIncentive.quiet_second_packet_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.quiet_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.quiet_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.equilibrium_second_packet_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.equilibrium_second_packet_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceRationality.second_packet_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceRationality.second_packet_le_of_deviation_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceWitness.last_alice_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceWitness.last_alice_class_nonempty

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTremble.weighted_retry_ratio_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTremble.weighted_retry_ratio_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTremble.equilibrium_consistency_retry_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTremble.equilibrium_consistency_retry_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingService.binding_round'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingService.binding_round

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobQuietPrefix.binding_activation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobQuietPrefix.binding_activation

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceEmptyDecision.quiet_pending_empty

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_nonnegative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.safe_continuation_nonnegative

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.permitted_alice_payload'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.permitted_alice_payload

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.equilibrium_early_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.equilibrium_early_response_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.early_packet_le_of_deviation_regrets'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.early_packet_le_of_deviation_regrets

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.opening_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.opening_regret

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.equilibrium_nongenuine_response_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.equilibrium_nongenuine_response_zero

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.nongenuine_le_of_deviation_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceOpeningRationality.nongenuine_le_of_deviation_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.answer_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafeContinuation.answer_continuation_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingInformation.decision_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingInformation.decision_of_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_representative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_representative

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff.failed_answer_continuation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobAnswerPayoff.failed_answer_continuation_payoff

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.answer_context_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.answer_context_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.exists_bit_guess_value_ge_half'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.exists_bit_guess_value_ge_half

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingDecision.equilibrium_binding_value_ge_half'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingDecision.equilibrium_binding_value_ge_half

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingWitness.failed_binding_information_representative

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceNormalization.equilibrium_last_responses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceNormalization.equilibrium_last_responses

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_last_responses_normalized

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceEmptyWitness.secondLateDecision_trace

/-- info: 'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.equilibrium_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.equilibrium_constraints

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.sequentially_rational_constraints

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.exists_service_with_constraints'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEquilibriumConstraints.exists_service_with_constraints

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases.opening_payoff_law_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceOpeningAliases.opening_payoff_law_eq

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFinalSupport.final_response_value_lower'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFinalSupport.final_response_value_lower

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix.final_decision_of_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceQuietPrefix.final_decision_of_silence

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.equilibrium_nongenuine_packet_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.equilibrium_nongenuine_packet_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstWitness.first_alice_class_nonempty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFirstWitness.first_alice_class_nonempty

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingLaw.successful_readout_protected_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingLaw.successful_readout_protected_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingLaw.intended_law_protected_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingLaw.intended_law_protected_receipt

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobRawPayoff.continuation_payoff_le_score'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobRawPayoff.continuation_payoff_le_score

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_supported_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_supported_binding

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_value_eq_bestGuessValue'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingOptimization.rational_value_eq_bestGuessValue

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobKnownBit.equilibrium_correct_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobKnownBit.equilibrium_correct_publication

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness.failed_publication_known_bit_class'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobKnownBitWitness.failed_publication_known_bit_class

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.equilibrium_consistency_nongenuine_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.equilibrium_consistency_nongenuine_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.weighted_nongenuine_ratio_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFirstTremble.weighted_nongenuine_ratio_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingSettlement.rational_supported_clean_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobBindingSettlement.rational_supported_clean_settlement

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstObservation.first_observation_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstObservation.first_observation_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_common_depth'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_common_depth

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_prefix_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingPrefix.binding_prefix_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingPrefix.initialized_type_reach_eq_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingPrefix.initialized_type_reach_eq_prefix

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingPosterior.consistent_conditional_probabilities'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingPosterior.consistent_conditional_probabilities

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.rational_value_eq_posterior_max'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.rational_value_eq_posterior_max

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.consistent_value_limit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobPosteriorOptimization.consistent_value_limit

/-- info: 'Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.transmitted_binding_silent_event_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.transmitted_binding_silent_event_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.settlement_activation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLatePrefixKernel.settlement_activation

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateResponseKernel.after_early_quiet_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLateResponseKernel.after_early_quiet_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeLateResponseKernel.genuine_retry_publication_law' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLateResponseKernel.genuine_retry_publication_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeConsistency.consistency_witness'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeConsistency.consistency_witness

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_charge_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_charge_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_settlement_pure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimePreservingSettlement.history_settlement_pure

/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedRecall.information_histories_protected_silent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeProtectedRecall.information_histories_protected_silent

/-- info: 'Vegas.Examples.LateOpeningRuntimeProtectedPrefix.protected_submission_event_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedPrefix.protected_submission_event_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.bestAnswerValue_formula'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.bestAnswerValue_formula

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.rational_supported_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSuccessOptimization.rational_supported_binding

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement.rational_supported_clean_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement.rational_supported_clean_settlement

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor.rational_supported_payoff_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor.rational_supported_payoff_floor

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedPrefix.initialized_binding_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeInitializedPrefix.initialized_binding_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedPrefix.clean_information_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeInitializedPrefix.clean_information_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeSuccessPosterior.conditional_value_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSuccessPosterior.conditional_value_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingObservation.genuine_retry_information_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingObservation.genuine_retry_information_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingObservation.failed_unseen_timing_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingObservation.failed_unseen_timing_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingObservation.failed_empty_information_inputs'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingObservation.failed_empty_information_inputs

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingObservationWitness.failed_information_representative'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBindingObservationWitness.failed_information_representative

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingFactors.canonical_seen_information_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingFactors.canonical_seen_information_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeBindingFactors.unseen_empty_failure_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBindingFactors.unseen_empty_failure_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeRetryKernel.relative_event_error_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRetryKernel.relative_event_error_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeRetryWitness.genuine_alias_response_close_quiet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRetryWitness.genuine_alias_response_close_quiet

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSuccessBindingClean.rational_supported_clean_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSuccessBindingClean.rational_supported_clean_binding

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingChronology.accepted_chronology'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingChronology.accepted_chronology

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobBindingChronology.canonical_openability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobBindingChronology.canonical_openability

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobFinalObservation.continuation_owner_same_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobFinalObservation.continuation_owner_same_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality.equilibrium_supported_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobFinalFiberRationality.equilibrium_supported_publication

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalOpening.canonical_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOptionalOpening.canonical_continuation_clean

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalInformation.decisionOfInformation_spec'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOptionalInformation.decisionOfInformation_spec

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalIncentive.canonical_audit_regret'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOptionalIncentive.canonical_audit_regret

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalDecision.canonical_context_outcome_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOptionalDecision.canonical_context_outcome_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalRationality.rational_supported_clean_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeOptionalRationality.rational_supported_clean_settlement

/-- info: 'Vegas.Examples.LateOpeningRuntimeOptionalPacket.equilibrium_supported_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOptionalPacket.equilibrium_supported_response

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation.continuation_charge_same_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobFinalAuditObservation.continuation_charge_same_information

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality.equilibrium_supported_clean_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobFinalAuditRationality.equilibrium_supported_clean_publication

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobFailedBindingClean.rational_supported_clean_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobFailedBindingClean.rational_supported_clean_binding

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDisclosureChronology.final_of_optional_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDisclosureChronology.final_of_optional_silence

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication.binding_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDisclosurePublication.binding_publication

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor.sequentially_rational_supported_payoff_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFullFiberFloor.sequentially_rational_supported_payoff_floor

/-- info: 'Vegas.Examples.LateOpeningRuntimeSettlementContinuation.genuine_first_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSettlementContinuation.genuine_first_payoff_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSettlementContinuation.genuine_final_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSettlementContinuation.genuine_final_payoff_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstRetryComparison.original_close_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstRetryComparison.original_close_comparison

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstRetryRationality.rational_comparison_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstRetryRationality.rational_comparison_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeOpeningIdentity.nongenuine_first_observed_event_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeOpeningIdentity.nongenuine_first_observed_event_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyRecall.first_silent_observed_event_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEarlyRecall.first_silent_observed_event_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeSeenLikelihood.original_seen_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSeenLikelihood.original_seen_error

/-- info: 'Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEarlyResponseLaw.sequentially_rational_response_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation.receiver_expected_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceSuccessfulContinuation.receiver_expected_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFailurePayoff.failed_completion_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFailurePayoff.failed_completion_payoff

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation.receiver_expected_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFailureContinuation.receiver_expected_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood.initialized_history_seen_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood.initialized_history_seen_error

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood.early_silence_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeInitializedSeenLikelihood.early_silence_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstFiber.context_value_eq_physical'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFirstFiber.context_value_eq_physical

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceProtectedFiber.protected_none_suffix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceProtectedFiber.protected_none_suffix

open Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality in
/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality.sequentially_rational_supported_response_maximal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sequentially_rational_supported_response_maximal

open Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality in
/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFirstOptimality.sequentially_rational_genuineProbability_one_of_preference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sequentially_rational_genuineProbability_one_of_preference

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstResponseLimits.genuineProbability_tendsto'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstResponseLimits.genuineProbability_tendsto

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation.original_completion_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstSettlementContinuation.original_completion_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization.rational_response_completion_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeFirstResponseRetryNormalization.rational_response_completion_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeFirstOpeningPayoff.first_genuine_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeFirstOpeningPayoff.first_genuine_payoff_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeSecondOpeningPayoff.first_silence_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSecondOpeningPayoff.first_silence_payoff_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeUnseenLikelihood.original_unseen_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeUnseenLikelihood.original_unseen_error

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood.initialized_history_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeInitializedTypeLikelihood.initialized_history_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedUnseenLikelihood.initialized_history_unseen_error'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeInitializedUnseenLikelihood.initialized_history_unseen_error

/-- info: 'Vegas.Examples.LateOpeningRuntimeInitializedSuccessReadout.label_mass_eq_initialized_type'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeInitializedSuccessReadout.label_mass_eq_initialized_type

/-- info: 'Vegas.Examples.LateOpeningRuntimeTypeWeight.witness_typeWeight_positive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeTypeWeight.witness_typeWeight_positive

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFailureReduction.receiver_known_expected_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceFailureReduction.receiver_known_expected_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceFailureReduction.receiver_empty_expected_value_closed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFailureReduction.receiver_empty_expected_value_closed

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction.receiver_expected_value_closed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceSuccessfulReduction.receiver_expected_value_closed

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafePosterior.supported_safe_label_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSafePosterior.supported_safe_label_bounds

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTimingValues.timing_value_difference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTimingValues.timing_value_difference

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTimingValues.first_genuine_response_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTimingValues.first_genuine_response_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTimingValues.first_silence_response_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTimingValues.first_silence_response_value

/-- info: 'Vegas.Examples.LateOpeningRuntimeLabelCross.label_belief_cross_identity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelCross.label_belief_cross_identity

/-- info: 'Vegas.Examples.LateOpeningRuntimeLabelCross.label_belief_product_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelCross.label_belief_product_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeProbability.positive_safe_label_product_lower_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSafeProbability.positive_safe_label_product_lower_bound

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSafeProbability.safeProbability_zero_of_label_product_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSafeProbability.safeProbability_zero_of_label_product_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality.preserving_first_value_le_half_all_types'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality.preserving_first_value_le_half_all_types

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality.first_value_ge_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceProtectedOptimality.first_value_ge_response

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTimingSorting.opposite_emission_probabilities'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTimingSorting.opposite_emission_probabilities

/-- info: 'Vegas.Examples.LateOpeningRuntimeAliceTimingFloor.first_value_lower_of_safe_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceTimingFloor.first_value_lower_of_safe_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeSeObstruction.consistent_rational_excludes_one_safe_probability'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSeObstruction.consistent_rational_excludes_one_safe_probability

/-- info: 'Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_safe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_safe

/-- info: 'Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_intended'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSeObstruction.equilibrium_terminal_law_ne_intended

open Vegas.Examples in
/-- info: 'Vegas.Examples.LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LateOpeningRuntimeUniformSeObstruction.exists_service_with_no_preserving_equilibrium

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.withholding_equilibrium_preserved_under_forfeiture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.withholding_equilibrium_preserved_under_forfeiture

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_forfeiture'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_preserved_under_forfeiture

/-- info: 'Vegas.Examples.LateOpeningRuntimeSource.exists_forfeiting_equilibrium_with_safe_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeSource.exists_forfeiting_equilibrium_with_safe_law

open Vegas.Examples.LateOpeningRuntimeSourceSeObstruction in
/-- info: 'Vegas.Examples.LateOpeningRuntimeSourceSeObstruction.exists_source_equilibrium_with_uniform_service_obstruction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_source_equilibrium_with_uniform_service_obstruction

/-- info: 'Vegas.Examples.LateOpeningRuntimePartialAudit.exists_service_with_no_preserving_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimePartialAudit.exists_service_with_no_preserving_equilibrium

open Vegas.Examples.LateOpeningRuntimePartialAuditSourceObstruction in
/-- info: 'Vegas.Examples.LateOpeningRuntimePartialAuditSourceObstruction.exists_source_equilibrium_with_partial_audit_obstruction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_source_equilibrium_with_partial_audit_obstruction

/-- info: 'Vegas.Examples.LateOpeningRuntimeService.runRounds_observable_scheduler'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeService.runRounds_observable_scheduler

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSunkAudit.early_submission_continuation_full_charge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSunkAudit.early_submission_continuation_full_charge

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix.dirty_information_history_full_charge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDirtyPrefix.dirty_information_history_full_charge

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDirtyScore.dirty_continuation_payoff_le_score'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDirtyScore.dirty_continuation_payoff_le_score

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSunkAudit.rejected_identifier_same_view_full_charge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobSunkAudit.rejected_identifier_same_view_full_charge

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDirtyFinalRationality.rational_final_failure_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDirtyFinalRationality.rational_final_failure_zero

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobSunkDisclosure.canonical_dominates'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobSunkDisclosure.canonical_dominates

/-- info: 'Vegas.Examples.LateOpeningRuntimeBobDirtyFinalFiber.rational_supported_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDirtyFinalFiber.rational_supported_publication

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalRationality.rational_optional_failure_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalRationality.rational_optional_failure_zero

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalFiber.rational_supported_response_not_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobDirtyOptionalFiber.rational_supported_response_not_failure

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication.binding_response_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication.binding_response_publication

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication.binding_payoff_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobDirtyDisclosurePublication.binding_payoff_floor

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication.accepted_genuine_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication.accepted_genuine_floor

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication.opening_payoff_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceProtectedPublication.opening_payoff_floor

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor.sourceUtility_highLabel_upper'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceSuccessFloor.sourceUtility_highLabel_upper

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.repair_regret_of_continuation_margin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.repair_regret_of_continuation_margin

open Vegas.Examples.LateOpeningRuntimeAliceFirstRationality in
/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceFirstRationality.sequentially_rational_nongenuine_packet_zero_of_continuation_margin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sequentially_rational_nongenuine_packet_zero_of_continuation_margin

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceNormalization.sequentially_rational_responses'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAliceNormalization.sequentially_rational_responses

/-- info:
'Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_responses_normalized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAliceNormalization.exists_service_with_responses_normalized

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.charge'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.charge

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.payoff

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.charge_not_scaled_of_omission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.charge_not_scaled_of_omission

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.successful_binding_continuation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAllOrNoneTrafficAudit.successful_binding_continuation_payoff

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNonePreservingSettlement.preserving_implies_full'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNonePreservingSettlement.preserving_implies_full

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneAlice.rational_alice'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneAlice.rational_alice

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding.failed_binding_rationality_scaled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding.failed_binding_rationality_scaled

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding.dirty_binding_rationality_scaled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneBinding.dirty_binding_rationality_scaled

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNoneCleanBinding.clean_binding_rationality_scaled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAllOrNoneCleanBinding.clean_binding_rationality_scaled

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding.optional_binding_rationality_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding.optional_binding_rationality_iff

/-- info:
'Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding.final_binding_rationality_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNonePostBinding.final_binding_rationality_iff

/-- info: 'Vegas.Examples.LateOpeningRuntimeContinuationRationality.continuations_rational_of_rational'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeContinuationRationality.continuations_rational_of_rational

open Vegas.Examples in
/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneDirtyFailedBinding.dirty_failed_binding_rationality_scaled'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LateOpeningRuntimeAllOrNoneDirtyFailedBinding.dirty_failed_binding_rationality_scaled

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneRationality.receiver_continuations_rational'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeAllOrNoneRationality.receiver_continuations_rational

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob.sequentially_rational_early_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob.sequentially_rational_early_response_law

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob.sequentially_rational_responses_silent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAllOrNoneEarlyBob.sequentially_rational_responses_silent

/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction.equilibrium_terminal_law_ne_safe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction.equilibrium_terminal_law_ne_safe

open Vegas.Examples in
/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction.exists_service_with_no_preserving_equilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LateOpeningRuntimeAllOrNoneSeObstruction.exists_service_with_no_preserving_equilibrium

open Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction in
/-- info: 'Vegas.Examples.LateOpeningRuntimeAllOrNoneSeObstruction.exists_source_equilibrium_with_uniform_service_obstruction'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_source_equilibrium_with_uniform_service_obstruction

/-- info: 'Vegas.Examples.LateOpeningRuntimeSeObstruction.consistent_rational_terminal_law_ne_safe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeSeObstruction.consistent_rational_terminal_law_ne_safe

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_consistent_alice_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_consistent_alice_completion

/-- info:
'Vegas.Examples.ConcurrentRevealOrderLaw.terminal_store_laws_differ'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ConcurrentRevealOrderLaw.terminal_store_laws_differ

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelSymmetry.replaceStateInputs_bob_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelSymmetry.replaceStateInputs_bob_view

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelSymmetry.replaceStateInputs_handle'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelSymmetry.replaceStateInputs_handle

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTransitions.environment_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTransitions.environment_replace

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTransitions.emit_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTransitions.emit_replace

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelHistories.respond_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelHistories.respond_replace

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelHistories.environmentStep_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelHistories.environmentStep_replace

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelHistories.rawMenu_replace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelHistories.rawMenu_replace

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelHistories.prior_label_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelHistories.prior_label_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTrace.initial_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTrace.initial_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTrace.permuteProtocolState_transition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTrace.permuteProtocolState_transition

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTrace.recordedLabels_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTrace.recordedLabels_history

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTrace.permuteExecution_inverse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTrace.permuteExecution_inverse

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelTrace.info_bob_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelTrace.info_bob_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelOrbits.permuteHistory_inverse'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelOrbits.permuteHistory_inverse

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelOrbits.historyEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelOrbits.historyEquiv

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelOrbits.informationHistoryEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelOrbits.informationHistoryEquiv

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelKernels.menu_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelKernels.menu_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelKernels.uniformPolicy_raw_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelKernels.uniformPolicy_raw_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelKernels.behavioralJoint_raw_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelKernels.behavioralJoint_raw_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelReach.stepHistory_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelReach.stepHistory_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelReach.runBehavioralFrom_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelReach.runBehavioralFrom_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelReach.historyReachWeight_permutation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelReach.historyReachWeight_permutation

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelBeliefs.belief_permutation_of_uniform_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelBeliefs.belief_permutation_of_uniform_sequence

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelBeliefs.label_belief_uniform_of_uniform_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelBeliefs.label_belief_uniform_of_uniform_sequence

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_uniform_alice_bob_completion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_uniform_alice_bob_completion

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobTail.terminal_law_eq_of_bob_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobTail.terminal_law_eq_of_bob_agreement

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobTail.tail_of_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobTail.tail_of_information

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobTail.continuation_context_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobTail.continuation_context_eq

/-- info:
'Vegas.Examples.LateOpeningRuntimeBobTail.rationality_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeBobTail.rationality_iff

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.pending_handle_none'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.pending_handle_none

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.runRounds_config_and_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.runRounds_config_and_clean

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.early_binding_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPrefix.early_binding_opening

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryValue.reactiveDecision_late_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryValue.reactiveDecision_late_opening

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_callback_safe_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_callback_safe_payoff_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_callback_safe_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_callback_safe_value

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_compiler_action_value_lt_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryValue.late_compiler_action_value_lt_source

/-- info:
'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.rational_early_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.rational_early_response_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.sequentially_rational_early_response_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeEarlyBobRationality.sequentially_rational_early_response_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_uniform_bob_reference'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeEquilibrium.exists_uniform_bob_reference

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_binding

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_opening

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_silent_after_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobPolicy.canonical_silent_after_completed

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.after_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.after_opening

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.opening_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.opening_continuation_clean

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.binding_continuation_clean'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.binding_continuation_clean

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.safe_continuation_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobContinuation.safe_continuation_payoff

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobTiming.early_binding_timer'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobTiming.early_binding_timer

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_binding_opportunity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_binding_opportunity

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_audit_charge_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_audit_charge_zero

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_safe_payoff_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryDomination.silent_safe_payoff_law

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.late_compiler_action_value_lt_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeRecoveryDomination.late_compiler_action_value_lt_silence

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.source_opening_value_gt_silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeRecoveryDomination.source_opening_value_gt_silence

/-- info:
'Vegas.Examples.LateOpeningRuntimeRecoveryDomination.exists_positive_weight_action_reversal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeRecoveryDomination.exists_positive_weight_action_reversal

/-- info:
'Vegas.Examples.LateOpeningRuntimeProtectedBobMenu.canonical_admissible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeProtectedBobMenu.canonical_admissible

open Vegas.Examples in
/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelContinuation.continuation_law_permutation_of_uniform_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms LateOpeningRuntimeLabelContinuation.continuation_law_permutation_of_uniform_sequence

open Vegas.Examples.LateOpeningRuntimeLabelContinuation in
/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelContinuation.continuation_successful_gross_le_of_uniform_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms continuation_successful_gross_le_of_uniform_sequence

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelContinuation.terminal_alice_publication_persistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeLabelContinuation.terminal_alice_publication_persistent

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelContinuation.information_alice_publication'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.LateOpeningRuntimeLabelContinuation.information_alice_publication

/-- info:
'Vegas.Examples.LateOpeningRuntimeLabelContinuation.continuation_payoff_le_of_uniform_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.LateOpeningRuntimeLabelContinuation.continuation_payoff_le_of_uniform_sequence

/-- info:
'Vegas.Examples.CommitSeedSignalling.exists_honest_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.exists_honest_sequentialEquilibrium

/-- info:
'Vegas.Examples.CommitSeedSignalling.scheduler_completesPlay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.scheduler_completesPlay

/-- info:
'Vegas.Examples.CommitSeedSignalling.scheduler_asyncContract'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.scheduler_asyncContract

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_equilibrium_extends_counted'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_equilibrium_extends_counted

/-- info:
'Vegas.Examples.CommitSeedSignalling.original_nohelper_acceptance_half'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.original_nohelper_acceptance_half

/-- info:
'Vegas.Examples.CommitSeedSignalling.bobPrefixFinalJoint_physical'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bobPrefixFinalJoint_physical

/-- info:
'Vegas.Examples.CommitSeedSignalling.alice_binding_unaccepted_after_late'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.alice_binding_unaccepted_after_late

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_counted_netPayoff_expectation'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_counted_netPayoff_expectation

/-- info:
'Vegas.Examples.CommitSeedSignalling.silent_unsubmitted_publication_excluded'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.silent_unsubmitted_publication_excluded

/-- info:
'Vegas.Examples.CommitSeedSignalling.menu_trace_fixed_seed'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.menu_trace_fixed_seed

/-- info:
'Vegas.Examples.CommitSeedSignalling.bob_initialized_weighted_half'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bob_initialized_weighted_half

/-- info:
'Vegas.Examples.CommitSeedSignalling.alice_initialized_half'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.alice_initialized_half

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_equilibrium_own_clean_terminal_charge_zero'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_equilibrium_own_clean_terminal_charge_zero

/-- info:
'Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_initialized_value'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_initialized_value

/-- info:
'Vegas.Examples.CommitSeedSignalling.family_privateActivationCalendar'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.family_privateActivationCalendar

/-- info:
'Vegas.Examples.CommitSeedSignalling.fixed_late_acceptance_probability'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.fixed_late_acceptance_probability

/-- info:
'Vegas.Examples.CommitSeedSignalling.bob_fixed_late_weighted_acceptance_probability'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bob_fixed_late_weighted_acceptance_probability

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_joint_acceptance_half'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_joint_acceptance_half

/-- info:
'Vegas.Examples.CommitSeedSignalling.surviving_original_binding_accepted'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.surviving_original_binding_accepted

/-- info:
'Vegas.Examples.CommitSeedSignalling.counted_successful_publication_wait_not_supported'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.counted_successful_publication_wait_not_supported

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_tail_opening_value_on_same_input'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_tail_opening_value_on_same_input

/-- info:
'Vegas.Examples.CommitSeedSignalling.family_privateBindingSuccess'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.family_privateBindingSuccess

/-- info:
'Vegas.Examples.CommitSeedSignalling.alice_fixed_late_exclusive_acceptance_quarter'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.alice_fixed_late_exclusive_acceptance_quarter

/-- info:
'Vegas.Examples.CommitSeedSignalling.bob_fixed_late_exclusive_acceptance_quarter'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bob_fixed_late_exclusive_acceptance_quarter

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_helper_clock_two_information_fiber'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_helper_clock_two_information_fiber

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_recalled_helper_information_fiber'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_recalled_helper_information_fiber

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_successful_publication_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_successful_publication_survives

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_missing_original_binding_publication_failed'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.CommitSeedSignalling.initialized_missing_original_binding_publication_failed

/-- info:
'Vegas.Examples.CommitSeedSignalling.fixed_late_completed_binding_success_of_consistent'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.fixed_late_completed_binding_success_of_consistent

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_counted_netPayoff_receipt_lower_bound'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_counted_netPayoff_receipt_lower_bound

/-- info:
'Vegas.Examples.CommitSeedSignalling.bob_early_binding_accepted_six'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bob_early_binding_accepted_six

/-- info:
'Vegas.Examples.CommitSeedSignalling.counted_successful_publication_response_nonsilent'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.counted_successful_publication_response_nonsilent

/-- info:
'Vegas.Examples.CommitSeedSignalling.fixed_late_original_binding_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.fixed_late_original_binding_survives

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_original_binding_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_original_binding_survives

/-- info:
'Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_netPayoff_quarter'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_netPayoff_quarter

/-- info:
'Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_quarter'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_quarter

/-- info:
'Vegas.Examples.CommitSeedSignalling.preserving_equilibrium_bobQuiet_not_wait'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.preserving_equilibrium_bobQuiet_not_wait

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_helper_input_counted_trace'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_helper_input_counted_trace

/-- info:
'Vegas.Examples.CommitSeedSignalling.helper_pending_binding_accepted_next'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.helper_pending_binding_accepted_next

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_helper_binding_wait_context_value'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_helper_binding_wait_context_value

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_failed_helper_binding_context_value'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_failed_helper_binding_context_value

/-- info:
'Vegas.Examples.CommitSeedSignalling.raw_helper_context_value_nonnegative'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.raw_helper_context_value_nonnegative

/-- info:
'Vegas.Examples.CommitSeedSignalling.helper_eligible_counted_response_usable_at_source'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.helper_eligible_counted_response_usable_at_source

/-- info:
'Vegas.Examples.CommitSeedSignalling.helper_wrong_slot_counted_decoded_wait_at_source'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.helper_wrong_slot_counted_decoded_wait_at_source

/-- info:
'Vegas.Examples.CommitSeedSignalling.assessed_publication_run_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.assessed_publication_run_survives

/-- info:
'Vegas.Examples.CommitSeedSignalling.bobQuiet_counted_transmission_alice_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bobQuiet_counted_transmission_alice_survives

/-- info:
'Vegas.Examples.CommitSeedSignalling.bobQuiet_counted_decoded_wait'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.bobQuiet_counted_decoded_wait

/-- info:
'Vegas.Examples.CommitSeedSignalling.native_equilibrium_alice_payoff_quarter'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.native_equilibrium_alice_payoff_quarter

/-- info:
'Vegas.Examples.CommitSeedSignalling.no_preserving_sequentialEquilibrium'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedSignalling.no_preserving_sequentialEquilibrium

open Vegas.Examples in
/-- info:
'Vegas.Examples.CommitSeedSignalling.exists_honest_sequentialEquilibrium_without_native_preservation'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CommitSeedSignalling.exists_honest_sequentialEquilibrium_without_native_preservation

/-- info:
'Vegas.Examples.CommitSeedBroadcast.exists_honest_sequentialEquilibrium'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.exists_honest_sequentialEquilibrium

/-- info:
'Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_independent'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_independent

/-- info:
'Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_partition_expect'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_partition_expect

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_assessment_finish_eq'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_assessment_finish_eq

/-- info:
'Vegas.Examples.CommitSeedBroadcast.family_completesPlay'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.family_completesPlay

/-- info:
'Vegas.Examples.CommitSeedBroadcast.family_opportunity'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.family_opportunity

/-- info:
'Vegas.Examples.CommitSeedBroadcast.nohelper_first_late_physical_kernel'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.nohelper_first_late_physical_kernel

/-- info:
'Vegas.Examples.CommitSeedBroadcast.initialized_quiet_first_late_input_kernel'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.initialized_quiet_first_late_input_kernel

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_bad_mass_le'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_bad_mass_le

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_all_good_mass'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_firstLate_all_good_mass

/-- info:
'Vegas.Examples.CommitSeedBroadcast.initialized_firstLate_raw_information'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.initialized_firstLate_raw_information

/-- info:
'Vegas.Examples.CommitSeedBroadcast.original_first_late_bad_iff'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.original_first_late_bad_iff

/-- info:
'Vegas.Examples.CommitSeedBroadcast.properPolicy_binding_response'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.properPolicy_binding_response

/-- info:
'Vegas.Examples.CommitSeedBroadcast.properPolicy_opening_response'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.properPolicy_opening_response

/-- info:
'Vegas.Examples.CommitSeedBroadcast.family_asyncContract'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.family_asyncContract

/-- info:
'Vegas.Examples.CommitSeedBroadcast.scheduler_asyncContract'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.scheduler_asyncContract

/-- info:
'Vegas.Examples.CommitSeedBroadcast.family_privateActivationCalendar'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.family_privateActivationCalendar

/-- info:
'Vegas.Examples.CommitSeedBroadcast.family_privateBindingSuccess'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.family_privateBindingSuccess

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_input_raw_fiber_trace'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_input_raw_fiber_trace

/-- info:
'Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_bad_le'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_bad_le

/-- info:
'Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_regular_lower'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.assessed_firstLate_regular_lower

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_ne_wait'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_ne_wait

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_proper_clock_two_context_value_lower'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_proper_clock_two_context_value_lower

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_first_late_wait_context_value_upper'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_first_late_wait_context_value_upper

/-- info:
'Vegas.Examples.CommitSeedBroadcast.scheduled_proper_original_binding_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.scheduled_proper_original_binding_survives

/-- info:
'Vegas.Examples.CommitSeedBroadcast.scheduled_proper_eligible_finish_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.scheduled_proper_eligible_finish_survives

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_scheduled_proper_finish_foreign_miss'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_scheduled_proper_finish_foreign_miss

/-- info:
'Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_survival_reward_expectation'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.nativeSeedLaw_survival_reward_expectation

/-- info:
'Vegas.Examples.CommitSeedBroadcast.recorded_unusable_binding_result'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.recorded_unusable_binding_result

/-- info:
'Vegas.Examples.CommitSeedBroadcast.completed_binding_failure_persists'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.completed_binding_failure_persists

/-- info:
'Vegas.Examples.CommitSeedBroadcast.standing_failed_binding_terminal_payoff'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.standing_failed_binding_terminal_payoff

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_clock_three_response_ne_wait'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_clock_three_response_ne_wait

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_helper_clock_two_response_wait'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_helper_clock_two_response_wait

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_assessed_publication_finish_survives'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_assessed_publication_finish_survives

/-- info:
'Vegas.Examples.CommitSeedBroadcast.regular_assessed_original_admission'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.regular_assessed_original_admission

/-- info:
'Vegas.Examples.CommitSeedBroadcast.all_original_admissions_unusable_record_payoff'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.all_original_admissions_unusable_record_payoff

/-- info:
'Vegas.Examples.CommitSeedBroadcast.foreign_good_original_receipt_forecast'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.foreign_good_original_receipt_forecast

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_proper_early_context_value_nonnegative'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_proper_early_context_value_nonnegative

/-- info:
'Vegas.Examples.CommitSeedBroadcast.single_helper_conditional_original_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.single_helper_conditional_original_joint

/-- info:
'Vegas.Examples.CommitSeedBroadcast.single_helper_conditional_next_input_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.single_helper_conditional_next_input_joint

/-- info:
'Vegas.Examples.CommitSeedBroadcast.initial_public_continuation_error_tendsto'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.initial_public_continuation_error_tendsto

/-- info:
'Vegas.Examples.CommitSeedBroadcast.prepared_protocol_public_frame_posterior'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.prepared_protocol_public_frame_posterior

/-- info:
'Vegas.Examples.CommitSeedBroadcast.assessed_sent_helper_original_observation_law'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.assessed_sent_helper_original_observation_law

/-- info:
'Vegas.Examples.CommitSeedBroadcast.initial_single_helper_frame'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.initial_single_helper_frame

/-- info:
'Vegas.Examples.CommitSeedBroadcast.original_prefix_clear_of_all_final_receipts'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.original_prefix_clear_of_all_final_receipts

/-- info:
'Vegas.Examples.CommitSeedBroadcast.good_original_admission'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.good_original_admission

/-- info:
'Vegas.Examples.CommitSeedBroadcast.original_first_late_foreign_records'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.original_first_late_foreign_records

/-- info:
'Vegas.Examples.CommitSeedBroadcast.proper_bad_clock_two_finish_value_nonnegative'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.proper_bad_clock_two_finish_value_nonnegative

/-- info:
'Vegas.Examples.CommitSeedBroadcast.original_helper_gap_run'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.original_helper_gap_run

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_usable'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_first_late_response_usable

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_first_late_response_usable'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_first_late_response_usable

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_unusable_clock_two_context_gap'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_unusable_clock_two_context_gap

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_early_response_usable'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_early_response_usable

/-- info:
'Vegas.Examples.CommitSeedBroadcast.counted_early_response_usable'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.counted_early_response_usable

/-- info:
'Vegas.Examples.CommitSeedBroadcast.raw_unusable_early_context_value'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.raw_unusable_early_context_value

/-- info:
'Vegas.Examples.CommitSeedBroadcast.foreign_singleton_bad_original_admission_iff_packets'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.Examples.CommitSeedBroadcast.foreign_singleton_bad_original_admission_iff_packets

/-- info:
'Vegas.Examples.CommitSeedBroadcast.early_response_original_admissions'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.early_response_original_admissions

/-- info:
'Vegas.Examples.CommitSeedBroadcast.proper_clock_two_consistent_good_original_admission'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.proper_clock_two_consistent_good_original_admission

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_initialized_proper_clock_two_value_lower'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_initialized_proper_clock_two_value_lower

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_initial_raw_fiber_execution'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_initial_raw_fiber_execution

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_initial_original_seed_posterior'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_initial_original_seed_posterior

/-- info:
'Vegas.Examples.CommitSeedBroadcast.quiet_initial_native_finish'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.quiet_initial_native_finish

/-- info:
'Vegas.Examples.CommitSeedBroadcast.single_helper_assessed_conditional_original_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitSeedBroadcast.single_helper_assessed_conditional_original_joint

/-- info:
'Vegas.Examples.CommitTimingInformation.exists_honest_sequentialEquilibrium_alice_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.exists_honest_sequentialEquilibrium_alice_value

/-- info:
'Vegas.Examples.CommitTimingInformation.addressed_scheduler_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.addressed_scheduler_eq

/-- info:
'Vegas.Examples.CommitTimingInformation.alice_clock_two_empty_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.alice_clock_two_empty_input

/-- info:
'Vegas.Examples.CommitTimingInformation.bob_clock_two_quiet_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.bob_clock_two_quiet_input

/-- info:
'Vegas.Examples.CommitTimingInformation.bob_quiet_bad_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.bob_quiet_bad_posterior

/-- info:
'Vegas.Examples.CommitTimingInformation.no_forbidden_supported_of_ownPastPermitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.no_forbidden_supported_of_ownPastPermitted

/-- info:
'Vegas.Examples.CommitTimingInformation.raw_equilibrium_extends_counted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.raw_equilibrium_extends_counted

/-- info:
'Vegas.Examples.CommitTimingInformation.raw_equilibrium_counted_deviation_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.raw_equilibrium_counted_deviation_support

/-- info:
'Vegas.Examples.CommitTimingInformation.raw_equilibrium_supported_commit_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitTimingInformation.raw_equilibrium_supported_commit_support

/-- info:
'Vegas.Examples.ReservedEpochConcurrency.concurrent_prefix_supported'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReservedEpochConcurrency.concurrent_prefix_supported

/-- info:
'Vegas.Examples.ReservedEpochConcurrency.pending_binding_admissible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReservedEpochConcurrency.pending_binding_admissible

/-- info:
'Vegas.Examples.ReservedEpochConcurrency.pending_binding_usable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReservedEpochConcurrency.pending_binding_usable
