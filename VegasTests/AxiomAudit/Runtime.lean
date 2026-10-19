/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions
import Interaction
import Vegas

/-! # Runtime proof dependency regressions -/

/-- info: 'Vegas.EventGraphRuntime.deadPacket_collection_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.deadPacket_collection_continuation

/-- info: 'Vegas.EventGraphRuntime.lateSend_collection_continuation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.lateSend_collection_continuation

/-- info:
'Vegas.EventGraphRuntime.MessageBounds.onePacket_sequentialEquilibrium_extends' depends on
axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.MessageBounds.onePacket_sequentialEquilibrium_extends

/-- info: 'Vegas.EventGraphRuntime.MessageBounds.onePacket_binding_fresh' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.MessageBounds.onePacket_binding_fresh

/-- info: 'Vegas.EventGraphRuntime.RecoveryState.drain_quiescent' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryState.drain_quiescent

/-- info: 'Vegas.EventGraphRuntime.recoveryApplication_history_invariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoveryApplication_history_invariant

/-- info: 'Vegas.EventGraphRuntime.recoveryApplication_exclusion_monotone' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoveryApplication_exclusion_monotone

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.respond_of_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.respond_of_empty

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.liftExecution_execution_of_history_clear' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.liftExecution_execution_of_history_clear

/-- info: 'Vegas.EventGraphRuntime.Recovery.onePacketMenu_countCharge_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.onePacketMenu_countCharge_zero

/-- info: 'Vegas.EventGraphRuntime.Recovery.onePacketMenu_projected_of_empty' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.onePacketMenu_projected_of_empty

/-- info: 'Vegas.EventGraphRuntime.Recovery.onePacket_raw_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.onePacket_raw_sequentialEquilibrium

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.exists_paired_environmentStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.exists_paired_environmentStep

/-- info: 'Vegas.EventGraphRuntime.publicExclusionRecord_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.publicExclusionRecord_history

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.runJoint_replay' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.runJoint_replay

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.clearHistoryEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.clearHistoryEquiv

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.informationHistoryEquiv' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.informationHistoryEquiv

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.environmentStep_lift_apply' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.environmentStep_lift_apply

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_liftedSite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_liftedSite

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_map_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_map_eq

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.schedulerMixture_liftScheduler_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.schedulerMixture_liftScheduler_posterior

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_projectedState'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_projectedState

/-- info: 'Vegas.EventGraphRuntime.Recovery.due_owner_recalled_turn_clear_native'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.due_owner_recalled_turn_clear_native

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_or_classified_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_or_classified_eq

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.seededSampledRoundDecisionLaw_control'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.seededSampledRoundDecisionLaw_control

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_classified_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.runBehavioralUntil_exclusion_classified_eq

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_seed_product

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.ownerObservation_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.ownerObservation_seed_product

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.runJoint_counted_log_emittedAtActivation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.runJoint_counted_log_emittedAtActivation

/-- info: 'Vegas.EventGraphRuntime.Recovery.Opportunity.clear_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.Opportunity.clear_native

/-- info: 'Vegas.EventGraphRuntime.Recovery.ProtectedInclusion.clear_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.ProtectedInclusion.clear_native

/-- info: 'Vegas.EventGraphRuntime.countedSeedDomain_dispatch_of_activated_survives'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.countedSeedDomain_dispatch_of_activated_survives

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.runRounds_log_eq_of_owner_info'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.runRounds_log_eq_of_owner_info

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.posterior_ready_activation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.posterior_ready_activation

/-- info: 'Vegas.EventGraphRuntime.Recovery.CompletesPlay.clear_native' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.Recovery.CompletesPlay.clear_native

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.informationHistoryEquiv_reachWeight'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.informationHistoryEquiv_reachWeight

/-- info: 'Vegas.EventGraphRuntime.countedLocalSeedController' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.countedLocalSeedController

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.CountedQueryLog.eq_of_unsent_signature'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.CountedQueryLog.eq_of_unsent_signature

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.runJoint_ready_initial_exhaustionRange'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.runJoint_ready_initial_exhaustionRange

/-- info: 'Vegas.EventGraphRuntime.counted_binding_resolves_of_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.counted_binding_resolves_of_history

/-- info: 'Vegas.EventGraphRuntime.counted_opening_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.counted_opening_accepted

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.posterior_transcript_log' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.posterior_transcript_log

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.runJoint_initial_ownerLog' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.runJoint_initial_ownerLog

/-- info:
'Vegas.EventGraphRuntime.BindingMemory.RecordsSubmittedBindings.accepted_output_succeeded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.BindingMemory.RecordsSubmittedBindings.accepted_output_succeeded

/-- info: 'Vegas.EventGraphRuntime.environmentStep_resolution_no_success' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.environmentStep_resolution_no_success

/-- info: 'Vegas.EventGraphRuntime.blindToLatePackets_pendingLottery' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.blindToLatePackets_pendingLottery

/-- info: 'Vegas.EventGraphRuntime.accepting_identifiers_unique' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.accepting_identifiers_unique

/-- info: 'Vegas.EventGraphRuntime.reactiveOriginal_silent_of_initialized_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveOriginal_silent_of_initialized_support

/-- info: 'Vegas.EventGraphRuntime.reactiveOriginal_accepted_of_initialized_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveOriginal_accepted_of_initialized_support

/-- info: 'Vegas.EventGraphRuntime.prescribedReactiveResponse_originalConfig'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactiveResponse_originalConfig

/-- info: 'Vegas.EventGraphRuntime.prescribedReactiveResponse_sampledFrontierContinuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactiveResponse_sampledFrontierContinuation

/-- info: 'Vegas.EventGraphRuntime.sampled_owned_output_eq_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.sampled_owned_output_eq_settlement

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.respond_some'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.respond_some

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.sample_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.sample_coupling

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.sampled_response_canonicalContinuation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.sampled_response_canonicalContinuation

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.include_pending'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.include_pending

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.response_harmonic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.response_harmonic

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.sample_command_harmonic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.sample_command_harmonic

/-- info: 'Vegas.EventGraphRuntime.ReactiveFrontier.expire_silent_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveFrontier.expire_silent_resolution

/-- info: 'Vegas.EventGraphRuntime.prescribedReactivePolicy_inclusion_fits'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePolicy_inclusion_fits

/-- info:
'Vegas.EventGraphRuntime.recoverReactivePolicy_final_callback_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoverReactivePolicy_final_callback_comparison

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePosterior_fresh_before_turn_of_initialized_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.prescribedReactivePosterior_fresh_before_turn_of_initialized_support

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePolicy_silent_after_recorded_turn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePolicy_silent_after_recorded_turn

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePolicy_silent_after_turn_of_initialized_support'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.prescribedReactivePolicy_silent_after_turn_of_initialized_support

/-- info:
'Vegas.EventGraphRuntime.recoverReactivePolicy_ready_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoverReactivePolicy_ready_callback

/-- info:
'Vegas.EventGraphRuntime.recoverReactivePolicy_ready_callback_comparison'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoverReactivePolicy_ready_callback_comparison

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePosterior_snoc_of_no_turn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePosterior_snoc_of_no_turn

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePosterior_intentions_snoc_of_no_turn'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePosterior_intentions_snoc_of_no_turn

/-- info:
'Vegas.EventGraphRuntime.originalConfig_respond_of_empty_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_respond_of_empty_memory

/-- info:
'Vegas.EventGraphRuntime.unilateralFrontier_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.unilateralFrontier_ready

/-- info:
'Vegas.EventGraphRuntime.unilateralFrontier_foreign_sequence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.unilateralFrontier_foreign_sequence

/-- info:
'Vegas.EventGraphRuntime.unilateralFrontier_coupled_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.unilateralFrontier_coupled_step

/-- info:
'Vegas.EventGraphRuntime.reactiveBinding_activation_joint_result_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveBinding_activation_joint_result_law

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePolicy_binding_activation_input_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePolicy_binding_activation_input_law

/-- info:
'Vegas.EventGraphRuntime.recoverReactivePolicy_zero_rounds_store'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recoverReactivePolicy_zero_rounds_store

/-- info:
'Vegas.EventGraphRuntime.recovery_zero_rounds_action_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recovery_zero_rounds_action_value

/-- info:
'Vegas.EventGraphRuntime.recovery_zero_rounds_active_site'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recovery_zero_rounds_active_site

/-- info:
'Vegas.EventGraphRuntime.originalConfig_playerObserve_of_empty_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_playerObserve_of_empty_memory

/-- info:
'Vegas.EventGraphRuntime.originalConfig_include_focal_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_include_focal_history

/-- info:
'Vegas.EventGraphRuntime.originalConfig_include_focal_eq_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_include_focal_eq_complete

/-- info:
'Vegas.EventGraphRuntime.originalConfig_complete_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_complete_focal

/-- info:
'Vegas.EventGraphRuntime.originalConfig_expire_focal_eq_or_mem_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_expire_focal_eq_or_mem_step

/-- info:
'Vegas.EventGraphRuntime.reactiveBinding_activation_response_joint_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveBinding_activation_response_joint_law

/-- info:
'Vegas.EventGraphRuntime.reactiveBinding_activation_response_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveBinding_activation_response_posterior

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.congr_execution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.congr_execution

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.wait'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.wait

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.activate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.activate

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.advanceClock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.advanceClock

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.chance_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.chance_complete

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.sample_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.sample_coupling

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.expire_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.expire_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.retained_foreign'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.retained_foreign

/-- info:
'Vegas.EventGraphRuntime.reactiveUnilateralFrontier_initial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactiveUnilateralFrontier_initial

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.complete_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.complete_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.step_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.step_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.normalizeObservation_focal'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.normalizeObservation_focal

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.ready_foreign'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.ready_foreign

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_foreign_some'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_foreign_some

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_foreign_none'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.respond_foreign_none

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_foreign_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_foreign_binding

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_foreign_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_foreign_resolution

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_accepted

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_rejected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_rejected

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_pending'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.include_pending

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.expire_foreign_silent_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.expire_foreign_silent_resolution

/-- info:
'Vegas.EventGraphRuntime.ReactiveRetainedFrontier.pending_owner_suffix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveRetainedFrontier.pending_owner_suffix

/-- info:
'Vegas.EventGraphRuntime.handle_event_actor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.handle_event_actor

/-- info:
'Vegas.EventGraphRuntime.round_posterior_frontier_exists_of_expiry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.round_posterior_frontier_exists_of_expiry

/-- info:
'Vegas.EventGraphRuntime.round_posterior_potential_of_expiry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.round_posterior_potential_of_expiry

/-- info:
'Vegas.EventGraphRuntime.runRounds_posterior_potential_of_expiry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.runRounds_posterior_potential_of_expiry

/-- info:
'Vegas.EventGraphRuntime.runRounds_terminal_store_of_expiry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.runRounds_terminal_store_of_expiry

/-- info:
'Vegas.EventGraphRuntime.initial_posterior_potential'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.initial_posterior_potential

/-- info:
'Vegas.EventGraphRuntime.initial_terminal_store_of_expiry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.initial_terminal_store_of_expiry

/-- info:
'Vegas.EventGraphRuntime.prescribedReactivePolicy_emitted_acceptable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.prescribedReactivePolicy_emitted_acceptable

/-- info:
'Vegas.EventGraphRuntime.recordedTimelyCalls_policyInvariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recordedTimelyCalls_policyInvariant

/-- info:
'Vegas.EventGraphRuntime.recordedTimelyCalls_unilateral_policyInvariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.recordedTimelyCalls_unilateral_policyInvariant

/-- info:
'Vegas.EventGraphRuntime.respond_policy_unilateral_frontier_exists'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.respond_policy_unilateral_frontier_exists

/-- info:
'Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.sample_command_frontier_exists'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReactiveUnilateralFrontier.sample_command_frontier_exists

/-- info: 'Vegas.EventGraphRuntime.responseMenu_stopped_exclusion_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.responseMenu_stopped_exclusion_boundary

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_seededState'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_seededState

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.clear_bayesBelief_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.clear_bayesBelief_seed_product

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_informationHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.bounded_bayesBelief_informationHistory

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.boundedNativeProfile_update'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.boundedNativeProfile_update

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.clear_bayesBelief_finish_seeded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.clear_bayesBelief_finish_seeded

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_response_first_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_response_first_resolution

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_first_binding_log_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_first_binding_log_eq

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.native_exit_mass_eq_terminal_failure_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.native_exit_mass_eq_terminal_failure_mass

/-- info: 'Vegas.EventGraphRuntime.RecoveryProjection.terminal_readout_withinTV_of_native_failure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryProjection.terminal_readout_withinTV_of_native_failure

/-- info: 'Vegas.EventGraphRuntime.guardedBindingServiceResponse_eq_at_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.guardedBindingServiceResponse_eq_at_history

/-- info: 'Vegas.EventGraphRuntime.resolvingSeedCommand_binding_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.resolvingSeedCommand_binding_readout

/-- info: 'Vegas.EventGraphRuntime.bindingServiceResponse_resolution_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.bindingServiceResponse_resolution_result

/-- info: 'Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_first_binding_output_common'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.LocalSeedController.bayesBelief_first_binding_output_common

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_invariant

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_frontier'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_frontier

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_quiescent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_quiescent

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_initial_quiescent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_initial_quiescent

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_clock_monotone'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_clock_monotone

/-- info: 'Vegas.EventGraphRuntime.phaseBindingRecord_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseBindingRecord_history

/-- info: 'Vegas.EventGraphRuntime.phaseStoredCheckpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseStoredCheckpoint_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacketMenu_countCharge_zero'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacketMenu_countCharge_zero

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.binding_accepted_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.binding_accepted_of_history

/-- info: 'Vegas.EventGraphRuntime.phaseLiveBindingStamp_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseLiveBindingStamp_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.realize_private_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.realize_private_joint

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.reply_opening_raw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.reply_opening_raw

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedScheduler.runRounds_wordRecall'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedScheduler.runRounds_wordRecall

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.posterior_after_namespace_change'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.posterior_after_namespace_change

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.expire_resolves_of_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.expire_resolves_of_request

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.physicalBindings_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.physicalBindings_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.opening_accepted_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.opening_accepted_of_history

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.request_or_sample'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.request_or_sample

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_live'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_live

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.sample_ready_of_live'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.sample_ready_of_live

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.sample_advances_phase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.sample_advances_phase

/-- info: 'Vegas.EventGraphRuntime.phase_environment_checkpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_environment_checkpoint_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.audit_collection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.audit_collection

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.clockAccounting_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.clockAccounting_invariant

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.history_clock_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.history_clock_le

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_publicFailureOrder'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_publicFailureOrder

/-- info: 'Vegas.EventGraphRuntime.phasePublicFailureOrder_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phasePublicFailureOrder_history

/-- info: 'Vegas.EventGraphRuntime.phase_inclusion_failureOrder_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_inclusion_failureOrder_history

/-- info: 'Vegas.EventGraphRuntime.phase_environment_failureOrder_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_environment_failureOrder_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.runRounds_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.runRounds_complete

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.terminal_history_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.terminal_history_complete

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.mixture_terminal_history_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.mixture_terminal_history_complete

/-- info: 'Vegas.EventGraphRuntime.phaseNativeInvariant_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseNativeInvariant_history

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_activationOrigin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_activationOrigin

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.advanceClock_activationOrigin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.advanceClock_activationOrigin

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.advanceClock_retry_timers'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.advanceClock_retry_timers

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedScheduler.activation_informationInput'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedScheduler.activation_informationInput

/-- info: 'Vegas.EventGraphRuntime.phasePlanGeometry_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phasePlanGeometry_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCandidates.reactiveFreshSlot_lt_horizon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCandidates.reactiveFreshSlot_lt_horizon

/-- info: 'Vegas.EventGraphRuntime.phaseBindingResponse_result_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseBindingResponse_result_law

/-- info: 'Vegas.EventGraphRuntime.exists_phaseBindingResponse_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.exists_phaseBindingResponse_of_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.history_tickExhaustion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.history_tickExhaustion

/-- info: 'Vegas.EventGraphRuntime.currentTokenPrerequisites_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.currentTokenPrerequisites_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.survivor_pending'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.survivor_pending

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedScheduler.active_informationInput_of_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedScheduler.active_informationInput_of_trace

/-- info: 'Vegas.EventGraphRuntime.phaseTerminalExclusion_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseTerminalExclusion_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.exists_phaseBindingResponse_onePacket_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.exists_phaseBindingResponse_onePacket_of_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.nonactivation_wait_of_future_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.nonactivation_wait_of_future_request

/-- info: 'Vegas.EventGraphRuntime.CommitAttemptEvent.Resolved.no_request_runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.CommitAttemptEvent.Resolved.no_request_runRounds

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.coordinateConsistent_iff_of_unsent_information'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseSeedCalendar.coordinateConsistent_iff_of_unsent_information

/-- info: 'Vegas.EventGraphRuntime.MessageBounds.phaseAcceptedHandles_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.MessageBounds.phaseAcceptedHandles_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseOpeningResponse_permitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseOpeningResponse_permitted

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.exists_phaseOpeningResponse_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.exists_phaseOpeningResponse_of_history

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseOncePolicy_later'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseOncePolicy_later

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseOpeningPolicy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseOpeningPolicy_of_history

/-- info: 'Vegas.EventGraphRuntime.phaseLiveCompletionStamp_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseLiveCompletionStamp_history

/-- info: 'Vegas.EventGraphRuntime.phase_completed_owned_message'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_completed_owned_message

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.runRounds_activationTranscript'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.runRounds_activationTranscript

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.unsent_information_delay_filter'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.unsent_information_delay_filter

/-- info:
'Vegas.EventGraphRuntime.PhaseSeedCalendar.coordinateConsistent_iff_of_unsent_information_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseSeedCalendar.coordinateConsistent_iff_of_unsent_information_eq

/-- info: 'Vegas.EventGraphRuntime.State.BindingInvariant.recorded_binding_action'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.State.BindingInvariant.recorded_binding_action

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.unsent_posterior_splitAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.unsent_posterior_splitAt

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.bayesBelief_unsent_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.bayesBelief_unsent_seed_product

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_sent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_sent

/-- info: 'Vegas.EventGraphRuntime.phaseHistoryCheckpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseHistoryCheckpoint_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.first_delay_eq_elapsed_of_unrecorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.first_delay_eq_elapsed_of_unrecorded

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.first_callback_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.first_callback_protected

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.first_bayes_input_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.first_bayes_input_protected

/-- info: 'Vegas.EventGraphRuntime.environment_request_or_own_resolution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.environment_request_or_own_resolution

/-- info: 'Vegas.EventGraphRuntime.runRounds_request_or_resolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.runRounds_request_or_resolved

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedScheduler.runRounds_emissions_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedScheduler.runRounds_emissions_prefix

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.inclusionWindow_of_decision'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.inclusionWindow_of_decision

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.decision_single_emission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.decision_single_emission

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_covered

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_mass

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_result_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_result_law

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlots_nonempty_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlots_nonempty_of_history

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.callback_tick_unclosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.callback_tick_unclosed

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_request_time'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_request_time

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_first_resolution_includes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_first_resolution_includes

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.onePacket_binding_fresh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacket_binding_fresh

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.binding_slot_mem_of_onePacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.binding_slot_mem_of_onePacket

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_bounded_mass'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_bounded_mass

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.Permits.eq_of_same_event'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.Permits.eq_of_same_event

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_eventually_included'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.protected_eventually_included

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_swap

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_swap

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.respond_phaseExecution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.respond_phaseExecution

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.environmentStep_phaseExecution'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.environmentStep_phaseExecution

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.history_calendar_state'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.history_calendar_state

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.service_tick_bounds_request_time'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.service_tick_bounds_request_time

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.future_tick_unclosed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.future_tick_unclosed

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.window_eventually_included'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.window_eventually_included

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.swap_mem_onePacketActions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.swap_mem_onePacketActions

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.phaseNormalize_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.phaseNormalize_entry

/-- info: 'Vegas.EventGraphRuntime.phase_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_clear_history

/-- info: 'Vegas.EventGraphRuntime.phase_clear_nativeProgress_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_clear_nativeProgress_of_prefix

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.handle_swap_of_admitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.handle_swap_of_admitted

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.foreignPairs_phaseInput_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.foreignPairs_phaseInput_eq

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.normalize_binding_evidence_none'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.normalize_binding_evidence_none

/-- info: 'Vegas.EventGraphRuntime.PhaseCount.normalize_mem_onePacketActions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.normalize_mem_onePacketActions

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.receipt_iff_inclusionWindow'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.receipt_iff_inclusionWindow

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.receipt_runRounds_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.receipt_runRounds_law

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.bayesBelief_original_window_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.bayesBelief_original_window_law

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.future_unsent_inclusion_window'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.future_unsent_inclusion_window

/-- info: 'Vegas.EventGraphRuntime.phaseSwapGuard_of_transition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseSwapGuard_of_transition

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.phaseTransition_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.phaseTransition_swap

/-- info: 'Vegas.EventGraphRuntime.phaseOnePacketSwapSymmetry_involutive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseOnePacketSwapSymmetry_involutive

/-- info: 'Vegas.EventGraphRuntime.phaseSwapInformationFiberEquiv'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseSwapInformationFiberEquiv

/-- info: 'Vegas.EventGraphRuntime.HiddenSwap.ofPairs_initial_phase_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.ofPairs_initial_phase_law

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_authored_receipt_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_authored_receipt_law

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_receipt_control_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_receipt_control_product

/-- info: 'Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_receipt_original_residual_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.bayes_receipt_original_residual_product

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.respond_of_onePacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.respond_of_onePacket

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.nativeScheduler_at_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.nativeScheduler_at_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_environmentStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_environmentStep

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.nativeTrace_length'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.nativeTrace_length

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicy_at_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicy_at_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.binding_replacement_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.binding_replacement_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.binding_menu'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.binding_menu

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.include_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.include_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.activate_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.activate_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.wait_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.wait_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_transition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_transition

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_controlStep'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_controlStep

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.foreign_response_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.foreign_response_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.raw_binding_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.raw_binding_response

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.opening_response_binding_success'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.opening_response_binding_success

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_response

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.clock_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.clock_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.silence'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.silence

/-- info:
'Vegas.EventGraphRuntime.originalConfig_eq_of_publication_true'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.originalConfig_eq_of_publication_true

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.application_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.application_coupling

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.application_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.application_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.sample_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.sample_coupling

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.expiry_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.expiry_coupling

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.include_unauthorized'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.include_unauthorized

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_opening_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_opening_inclusion

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_foreign_binding_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_foreign_binding_inclusion

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_inclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_inclusion

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_include_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counted_include_trace

/-- info:
'Vegas.EventGraphRuntime.phase_opening_binding_success_before_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_opening_binding_success_before_binding

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_menu_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_menu_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.native_countClean_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.native_countClean_of_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.raw_binding_response_records'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.raw_binding_response_records

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_request

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.environment_transition_apply'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.environment_transition_apply

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.foreign_playerReach'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.foreign_playerReach

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counterfactual_environment_extend'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.counterfactual_environment_extend

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.repair_clear_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.repair_clear_history

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicy_consistent_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicy_consistent_of_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_behavioral_run'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_behavioral_run

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_first_exclusion_transition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_first_exclusion_transition

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_native_failure_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.exists_native_failure_exit

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicies_consistent_of_local_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseNativeProjection.nativePolicies_consistent_of_local_agreement

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.native_controlLaw_eq_of_local_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.native_controlLaw_eq_of_local_agreement

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_behavioral_run_of_local_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseNativeProjection.exists_paired_behavioral_run_of_local_agreement

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.opportunity_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.opportunity_projection

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.protectedInclusion_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.protectedInclusion_projection

/-- info:
'Vegas.EventGraphRuntime.PhaseService.recorded_activation_within_delay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.recorded_activation_within_delay

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.due_owner_response_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.due_owner_response_prefix

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.recall_sole_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.recall_sole_of_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseService.due_recalled_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.due_recalled_response

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.exists_clear_physical_of_native_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseNativeProjection.exists_clear_physical_of_native_consistent

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.not_publicFailure_of_native_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.not_publicFailure_of_native_consistent

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.terminal_of_native_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.terminal_of_native_consistent

/-- info:
'Vegas.EventGraphRuntime.environmentStep_expire_config_eq_of_no_publicFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.environmentStep_expire_config_eq_of_no_publicFailure

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.frontier_expire_of_native_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.frontier_expire_of_native_consistent

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.initial_terminal_store_of_physical_safety'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseNativeProjection.initial_terminal_store_of_physical_safety

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.rounds_projection_of_local_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.rounds_projection_of_local_agreement

open Vegas.EventGraphRuntime in
/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.rounds_projection_of_local_agreement_of_supported_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms PhaseNativeProjection.rounds_projection_of_local_agreement_of_supported_input

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.packet_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.packet_callback

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacket_binding_shape'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacket_binding_shape

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.expire_excludes_of_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.expire_excludes_of_request

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_posterior_wait'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_posterior_wait

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_posterior_send'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_posterior_send

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingWordPolicy_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlots_eq_fresh_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlots_eq_fresh_of_history

/-- info:
'Vegas.EventGraphRuntime.phaseBindingResponse_observation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseBindingResponse_observation_law

/-- info:
'Vegas.EventGraphRuntime.phaseBindingSlotPolicy_observation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseBindingSlotPolicy_observation_law

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.binding_handle_all_values'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.binding_handle_all_values

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.normalize_external_views'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.normalize_external_views

/-- info:
'Vegas.EventGraphRuntime.PhaseService.activation_response_or_current'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.activation_response_or_current

/-- info:
'Vegas.EventGraphRuntime.phase_ready_owner_rank_lt_of_clear_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_ready_owner_rank_lt_of_clear_prefix

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.recorded_binding_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.recorded_binding_request

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.recorded_binding_rank_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.recorded_binding_rank_lt

/-- info:
'Vegas.EventGraphRuntime.handle_commitment_publicView_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.handle_commitment_publicView_congr

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_publicView_congr_of_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_publicView_congr_of_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.handle_opaque_external_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.handle_opaque_external_congr

/-- info:
'Vegas.EventGraphRuntime.phase_include_opaque_external_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_include_opaque_external_congr

/-- info:
'Vegas.EventGraphRuntime.phase_opaque_include_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_opaque_include_trace

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.handle_binding_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.handle_binding_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.phase_handle_binding_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.phase_handle_binding_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.rememberCandidate_native_fresh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.rememberCandidate_native_fresh

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.binding_preparation_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.binding_preparation_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_binding_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_binding_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_binding_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_binding_memory

/-- info:
'Vegas.EventGraphRuntime.RecoveryState.expiry_native_stutter'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RecoveryState.expiry_native_stutter

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_opaque_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_opaque_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_opaque_replay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_opaque_replay

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.operationalView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.operationalView_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_timingKey_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.Frame.opening_timingKey_eq

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_foreign_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_foreign_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.activation_memory_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.activation_memory_coupling

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.phase_handle_binding_memory_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.phase_handle_binding_memory_of_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.accepted_call_in_commitment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.accepted_call_in_commitment

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_counted_binding_memory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_counted_binding_memory

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.phase_binding_memory_include_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.phase_binding_memory_include_trace

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_opaque_memory_of_clear_right'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_opaque_memory_of_clear_right

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_clear_observation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_clear_observation_law

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.handled_commitmentPhase_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.handled_commitmentPhase_clear

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_commitmentPhase_clear'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_commitmentPhase_clear

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_unsent

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.callback_binding_or_silent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.callback_binding_or_silent

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_command_stopped_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_command_stopped_coupling

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retry_archivedHistory'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retry_archivedHistory

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivesBefore_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.archivesBefore_history

/-- info:
'Vegas.EventGraphRuntime.phase_ownRecall_namespace_le_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_ownRecall_namespace_le_history

/-- info:
'Vegas.EventGraphRuntime.phase_ownRecall_fresh_after_environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_ownRecall_fresh_after_environment

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_entry_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_entry_prefix

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retiredPhaseResults'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retiredPhaseResults

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retry_survivor_record'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_retry_survivor_record

/-- info:
'Vegas.EventGraphRuntime.phaseRetiredCompletion_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseRetiredCompletion_history

/-- info:
'Vegas.EventGraphRuntime.phase_retired_survivor_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_retired_survivor_completed

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_retry_survivor_record'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_retry_survivor_record

/-- info:
'Vegas.EventGraphRuntime.phaseApplication_sameAttempt_phases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_sameAttempt_phases

/-- info:
'Vegas.EventGraphRuntime.phaseApplication_retryCompletion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_retryCompletion

/-- info:
'Vegas.EventGraphRuntime.phaseRetiredBindings_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseRetiredBindings_history

/-- info:
'Vegas.EventGraphRuntime.State.BindingInvariant.bindingHistory_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.State.BindingInvariant.bindingHistory_eq

/-- info:
'Vegas.EventGraphRuntime.phaseRetiredBindingInterval_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseRetiredBindingInterval_history

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedHistory_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedHistory_observed

/-- info:
'Vegas.EventGraphRuntime.phaseRetiredInputs_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseRetiredInputs_history

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedPlayerStore_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedPlayerStore_observed

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedPlayerStores_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedPlayerStores_eq_of_observed

/-- info:
'Vegas.EventGraphRuntime.SuffixExclusionRecord.failureOwners_union'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.SuffixExclusionRecord.failureOwners_union

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedExclusions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedExclusions

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.ArchivedExclusions.saved_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.ArchivedExclusions.saved_eq

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedExclusions_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedExclusions_history

/-- info:
'Vegas.EventGraphRuntime.phasePublicFailureCheckpoint_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phasePublicFailureCheckpoint_history

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.saved_excluded_eq_public_failures'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.saved_excluded_eq_public_failures

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.saved_excluded_eq_of_publicView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.saved_excluded_eq_of_publicView_eq

/-- info:
'Vegas.EventGraphRuntime.phase_saved_excluded_eq_of_publicView_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_saved_excluded_eq_of_publicView_eq

/-- info:
'Vegas.EventGraphRuntime.phase_anchoredPolicy_of_fresh_attempt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_anchoredPolicy_of_fresh_attempt

/-- info:
'Vegas.EventGraphRuntime.phaseRetiredOwnPrefix_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseRetiredOwnPrefix_history

/-- info:
'Vegas.EventGraphRuntime.State.BindingInvariant.recoverOwnActions_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.State.BindingInvariant.recoverOwnActions_eq

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedPlayerObservation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedPlayerObservation_observed

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedPlayerObservations_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedPlayerObservations_eq_of_observed

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivedHistory_readout'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.archivedHistory_readout

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedSourceObservation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedSourceObservation_observed

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedSourceObservations_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedSourceObservations_eq_of_observed

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntriesFrom_getElem'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntriesFrom_getElem

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntriesFrom_eq_of_publicViews_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntriesFrom_eq_of_publicViews_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntries_append_drain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.archivedExclusionEntries_append_drain

/-- info:
'Vegas.EventGraphRuntime.phase_archivedExclusionEntries_append_drain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_archivedExclusionEntries_append_drain

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.RetiredReceiptOrderFrom.getElem'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.RetiredReceiptOrderFrom.getElem

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedReceiptRecord'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedReceiptRecord

/-- info:
'Vegas.EventGraphRuntime.phaseApplication_archivedReceiptRecord'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_archivedReceiptRecord

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedReceiptRecord_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedReceiptRecord_history

/-- info:
'Vegas.EventGraphRuntime.PhaseSeedScheduler.serviceClocks_of_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedScheduler.serviceClocks_of_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_covered'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_covered

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_eq_of_clocks'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_eq_of_clocks

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_send_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingServicePolicy_send_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingServiceStrategy_finite_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingServiceStrategy_finite_agreement

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingServiceValue_finite'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingServiceValue_finite

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.exists_optimal_phase_binding_service'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.exists_optimal_phase_binding_service

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.controller_calendar'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.controller_calendar

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.callback_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.callback_request

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_activationTranscript'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_activationTranscript

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.clockAdvance_query_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.clockAdvance_query_origin

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.counted_call_resolves_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.counted_call_resolves_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.deadlineExpiry_calendar'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.deadlineExpiry_calendar

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.reply_inclusion_packet_of_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.reply_inclusion_packet_of_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.inclusion_resolves_of_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.inclusion_resolves_of_trace

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.nonactivation_wait_of_future_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.nonactivation_wait_of_future_request

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.history_tickExhaustion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.history_tickExhaustion

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_wait_of_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_wait_of_request

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.past_wait_query_of_tickExhaustion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.past_wait_query_of_tickExhaustion

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_queryOperationalPrefixes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_queryOperationalPrefixes

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.initialized_queryOperationalPrefixes'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.initialized_queryOperationalPrefixes

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_queried_input'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_queried_input

/-- info:
'Vegas.EventGraphRuntime.phase_runRounds_serviceProgress'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_runRounds_serviceProgress

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_activationClocks'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_activationClocks

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_timing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_timing

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_wait_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_query_wait_count

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.history_countedQueryLog'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.history_countedQueryLog

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.active_wait_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.active_wait_count

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.active_unsent_transcript_signature'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.active_unsent_transcript_signature

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_clock_transcript'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_clock_transcript

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_posterior_splitAt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.unsent_posterior_splitAt

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.belief_unsent_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.belief_unsent_seed_product

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_entry'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_entry

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_activate_or_wait'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_activate_or_wait

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_clock_ne_after_nonactivation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.queried_clock_ne_after_nonactivation

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_queries_elapsed_mono'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_queries_elapsed_mono

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_queries_elapsed_strict_after_nonactivation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseServiceScheduler.recorded_queries_elapsed_strict_after_nonactivation

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedSavedObservation_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedSavedObservation_observed

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedSavedObservations_eq_of_observed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedSavedObservations_eq_of_observed

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_first_visit_fresh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_first_visit_fresh

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_private_seed_joint'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.runRounds_private_seed_joint

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.belief_unsent_private_seed_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.belief_unsent_private_seed_product

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_progress_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_progress_of_prefix

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_ancestor_of_exit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_ancestor_of_exit

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_stopped_ancestor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_stopped_ancestor

/-- info:
'Vegas.EventGraphRuntime.phase_phases_eq_of_clear_unfinished_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_phases_eq_of_clear_unfinished_prefix

/-- info:
'Vegas.EventGraphRuntime.phase_interval_of_between_clear_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_interval_of_between_clear_ready

/-- info:
'Vegas.EventGraphRuntime.phase_current_attempt_until_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_current_attempt_until_atom

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacket_commitment_shape'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacket_commitment_shape

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.active_query_transcript_signature'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.active_query_transcript_signature

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.operational_word_transcript'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.operational_word_transcript

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.active_owner_word_clocks'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.active_owner_word_clocks

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.clocks_eq_of_seed_packet_pattern'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.clocks_eq_of_seed_packet_pattern

/-- info:
'Vegas.EventGraphRuntime.PhaseServiceScheduler.operational_emission_of_onePacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseServiceScheduler.operational_emission_of_onePacket

/-- info:
'Vegas.EventGraphRuntime.phase_information_control_of_view'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_information_control_of_view

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_first_passage_eq_some'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_first_passage_eq_some

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_first_passage_atom'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_first_passage_atom

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_entry_of_supported_hit'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_entry_of_supported_hit

/-- info:
'Vegas.EventGraphRuntime.PhaseBindingRepair.inert_response_menu_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseBindingRepair.inert_response_menu_iff

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.opening_menu_law_eq_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.opening_menu_law_eq_of_history

/-- info:
'Vegas.EventGraphRuntime.phaseNativeInvariant_of_initialized_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseNativeInvariant_of_initialized_history

/-- info:
'Vegas.EventGraphRuntime.phase_infoOf_mapTrace_of_fixed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_infoOf_mapTrace_of_fixed

/-- info:
'Vegas.EventGraphRuntime.phase_initial_support_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_initial_support_invariant

/-- info:
'Vegas.EventGraphRuntime.phase_initialClosed_swapAllowed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_initialClosed_swapAllowed

/-- info:
'Vegas.EventGraphRuntime.phaseSwapAllowed_closed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseSwapAllowed_closed

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.initial_phase_of_native_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.initial_phase_of_native_swap

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.initial_inputs_mem_phaseSwapAllowed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.initial_inputs_mem_phaseSwapAllowed

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.phaseSwapGuard_of_tracePrefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.phaseSwapGuard_of_tracePrefix

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.phaseAction_eq_of_nonbinding_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.phaseAction_eq_of_nonbinding_callback

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.environmentStep_phaseExecution_of_guards'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.environmentStep_phaseExecution_of_guards

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.phaseTransition_apply_swap'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.phaseTransition_apply_swap

/-- info:
'Vegas.EventGraphRuntime.HiddenSwap.exists_phase_continuation_common_factor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.HiddenSwap.exists_phase_continuation_common_factor

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_stopped_results'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_stopped_results

/-- info:
'Vegas.EventGraphRuntime.phase_recorded_binding_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_recorded_binding_result

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.accepted_binding_of_recorded_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.accepted_binding_of_recorded_completed

/-- info:
'Vegas.EventGraphRuntime.PhaseNativeProjection.completed_binding_action_of_recorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseNativeProjection.completed_binding_action_of_recorded

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedBindingStamp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archivedBindingStamp

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_archivedBindingStamp'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_archivedBindingStamp

/-- info:
'Vegas.EventGraphRuntime.phaseArchivedBindingStamp_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchivedBindingStamp_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.archived_recorded_binding_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.archived_recorded_binding_accepted

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.archived_recorded_binding_action'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.archived_recorded_binding_action

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.completed_recorded_binding_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.completed_recorded_binding_accepted

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.completed_recorded_binding_action'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.completed_recorded_binding_action

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceReference_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceReference_fullSupport

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.countedSendLaw_binding_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.countedSendLaw_binding_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceReference_transmission_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceReference_transmission_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceEmissionLaw_send'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceEmissionLaw_send

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingEncoders_transmission_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingEncoders_transmission_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceCoinResponse_average'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceCoinResponse_average

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceOrdinal_lt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceOrdinal_lt

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_posterior'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_posterior

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_realization'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_realization

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceCoinResponse_transmission_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceCoinResponse_transmission_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceOrdinal_lt_horizon'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceOrdinal_lt_horizon

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_transmission_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_transmission_of_history

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_recorded_wait'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_recorded_wait

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_wait_before_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_wait_before_unsent

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_send_decision'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_send_decision

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_send_index_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_send_index_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_silent_of_resolved_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_silent_of_resolved_unsent

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_emission_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_emission_origin

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_accepted_iff_of_resolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingServiceTapeMember_accepted_iff_of_resolved

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacket_request_of_nonsilent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacket_request_of_nonsilent

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingEmissionClocks_eq_nil_of_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingEmissionClocks_eq_nil_of_unsent

/-- info:
'Vegas.EventGraphRuntime.PhaseService.PrivateActivationCalendar.unsentPrivacy'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.PrivateActivationCalendar.unsentPrivacy

/-- info:
'Vegas.EventGraphRuntime.PhaseService.PrivateBindingSuccess.accepted_iff_of_emission_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseService.PrivateBindingSuccess.accepted_iff_of_emission_clock

/-- info:
'Vegas.EventGraphRuntime.PhaseService.PrivateActivationCalendar.accepted_iff_of_callbacks'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseService.PrivateActivationCalendar.accepted_iff_of_callbacks

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingServiceReference_transmission_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingServiceReference_transmission_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.handle_event_resolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.handle_event_resolved

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.handle_event_unresolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.handle_event_unresolved

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingAccepted_resolved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingAccepted_resolved

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingReceiptResolution_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingReceiptResolution_history

/-- info:
'Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_after_commitment_exclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_after_commitment_exclusion

/-- info:
'Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_of_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_of_request

/-- info:
'Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_runRounds_after_expire'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.not_bindingAccepted_runRounds_after_expire

/-- info:
'Vegas.EventGraphRuntime.PhaseService.phase_attempt_stopped_exclusion_unaccepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.phase_attempt_stopped_exclusion_unaccepted

/-- info:
'Vegas.EventGraphRuntime.phaseBindingAcceptedReceipts_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseBindingAcceptedReceipts_history

/-- info:
'Vegas.EventGraphRuntime.phase_archived_bindingAccepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_archived_bindingAccepted

/-- info:
'Vegas.EventGraphRuntime.phase_archived_survivor_bindingAccepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_archived_survivor_bindingAccepted

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_stopped_exclusion_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_stopped_exclusion_origin

/-- info:
'Vegas.EventGraphRuntime.phase_inclusion_snapshot_bindingAccepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_inclusion_snapshot_bindingAccepted

/-- info:
'Vegas.EventGraphRuntime.phase_live_bindingAccepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_live_bindingAccepted

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.ArchiveGeneration.retry_count'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.ArchiveGeneration.retry_count

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.archivedRetryAttemptsFrom_eq_of_publicViews_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseRuntimeState.archivedRetryAttemptsFrom_eq_of_publicViews_eq

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.finished_of_normalize_attempt_ne'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.finished_of_normalize_attempt_ne

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archiveGeneration'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_archiveGeneration

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.sourcePublicAddressWord_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.sourcePublicAddressWord_congr

/-- info:
'Vegas.EventGraphRuntime.RuntimePhasePlan.containing_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RuntimePhasePlan.containing_unique

/-- info:
'Vegas.EventGraphRuntime.phaseArchiveGeneration_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseArchiveGeneration_history

/-- info:
'Vegas.EventGraphRuntime.phase_archived_retry_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_archived_retry_boundary

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_stopped_receipt_snapshot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_stopped_receipt_snapshot

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_stopped_survivor_iff_receipts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_stopped_survivor_iff_receipts

/-- info:
'Vegas.EventGraphRuntime.phase_closed_transition_receipt_snapshot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_closed_transition_receipt_snapshot

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.sourcePublicAddressWord_eq_of_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.sourcePublicAddressWord_eq_of_prefix

/-- info:
'Vegas.EventGraphRuntime.RuntimePhasePlan.sourceArchiveAddresses_append'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.RuntimePhasePlan.sourceArchiveAddresses_append

/-- info:
'Vegas.EventGraphRuntime.State.publicFailure_iff_accepted_none'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.State.publicFailure_iff_accepted_none

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingSuccess_eq_of_resolved'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingSuccess_eq_of_resolved

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingSuccess_eq_false_of_unsent'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingSuccess_eq_false_of_unsent

/-- info:
'Vegas.EventGraphRuntime.PhaseService.bindingSuccess_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.bindingSuccess_joint

/-- info:
'Vegas.EventGraphRuntime.PhaseService.runRounds_bindingSuccess_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.runRounds_bindingSuccess_joint

/-- info:
'Vegas.EventGraphRuntime.phase_ready_earlier_binding_read'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_ready_earlier_binding_read

/-- info:
'Vegas.EventGraphRuntime.phase_ready_earlier_binding_declaration'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_ready_earlier_binding_declaration

/-- info:
'Vegas.EventGraphRuntime.phase_completed_recorded_binding_read'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_completed_recorded_binding_read

/-- info:
'Vegas.EventGraphRuntime.PhaseService.CompletesPlay.resolved_runRounds'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.CompletesPlay.resolved_runRounds

/-- info:
'Vegas.EventGraphRuntime.PhaseService.runRounds_complete_bindingSuccess_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.runRounds_complete_bindingSuccess_joint

/-- info:
'Vegas.EventGraphRuntime.PhaseService.response_runRounds_complete_bindingSuccess_joint'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseService.response_runRounds_complete_bindingSuccess_joint

/-- info:
'Vegas.EventGraphRuntime.phase_bindingAccepted_declaration'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_bindingAccepted_declaration

/-- info:
'Vegas.EventGraphRuntime.phase_attempt_metadata_of_prefix'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_metadata_of_prefix

/-- info:
'Vegas.EventGraphRuntime.phase_recorded_material_binding_result'

depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_recorded_material_binding_result

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.onePacketMenu_trace_of_completeInput'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.onePacketMenu_trace_of_completeInput

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.realize'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.realize

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.process_step'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.process_step

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_epoch_clears'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_epoch_clears

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.observedArchive_eq_submitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.observedArchive_eq_submitted

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.archive_coordinate_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.archive_coordinate_unique

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_project'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_project

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_fullSupport

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.inputs_le_cycles'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.inputs_le_cycles

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_finiteNature'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_finiteNature

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_callback'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_callback

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_binding_meaning'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_binding_meaning

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.clock_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.clock_history

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.runRounds_work_le'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.runRounds_work_le

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.expiry_round_decreases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.expiry_round_decreases

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.actual_epoch_clears'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.actual_epoch_clears

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.same_attempt_prefix_keeps_store'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.same_attempt_prefix_keeps_store

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_current_binding_meaning'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_current_binding_meaning

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_source_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_source_binding

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_source_delta'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_source_delta

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_replay_value'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_replay_value

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.openingOrigins_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.openingOrigins_history

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.recorded_disclosure_submitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.recorded_disclosure_submitted

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.recorded_disclosure_typed_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.recorded_disclosure_typed_archive

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.requested_interval_decreases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.requested_interval_decreases

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.nonterminal_interval_decreases'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.nonterminal_interval_decreases

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.runRounds_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.runRounds_complete

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.terminal_history_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.terminal_history_complete

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.family_completesPlay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.family_completesPlay

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_terminal_history_complete'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_terminal_history_complete

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.epoch_covers_submitted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.epoch_covers_submitted

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.activation_state_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.activation_state_history

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_activation_state_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_activation_state_history

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.family_opportunity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.family_opportunity

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_opportunity'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_opportunity

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.idle_emission_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.idle_emission_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_emission_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_emission_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_protectedInclusion'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_protectedInclusion

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_asyncContract'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_asyncContract

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_response_protected'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_response_protected

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_submission_admissible'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_submission_admissible

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.active_fresh_candidate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.active_fresh_candidate

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.timely_request_loss_accepts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.timely_request_loss_accepts

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.binding_accepted_of_own_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.binding_accepted_of_own_history

/-- info:
'Vegas.EventGraphRuntime.PhaseSeedCalendar.service_tick_eventually_included'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseSeedCalendar.service_tick_eventually_included

/-- info:
'Vegas.consumed_publication_phase_archive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.consumed_publication_phase_archive

/-- info:
'Vegas.proposalLift_archive_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.proposalLift_archive_extension

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_owner_not_in_scan'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.submitted_proposal_owner_not_in_scan

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.sourceArchive_future_bucket_empty'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.sourceArchive_future_bucket_empty

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_preserves_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_preserves_accepted

/-- info:
'Vegas.EventGraphRuntime.PhaseRuntimeState.accepted_progress'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.accepted_progress

/-- info:
'Vegas.EventGraphRuntime.phase_runRounds_accepted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_runRounds_accepted

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.opening_accepted_of_certificate'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.opening_accepted_of_certificate

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.readyCall_accepts'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.readyCall_accepts

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.ReadyCall.environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.ReadyCall.environment

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.ReadyCall.runRounds'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.ReadyCall.runRounds

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_segment_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_segment_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.receipt_at_processing_boundary'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.receipt_at_processing_boundary

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.protected_pending_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.protected_pending_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.first_response_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.first_response_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_response_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.implementation_first_response_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.receipt_of_later_processing_deadline'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.receipt_of_later_processing_deadline

/-- info:
'Vegas.Examples.ReservedEpochCertifiedConcurrency.valid_concurrent_service'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.ReservedEpochCertifiedConcurrency.valid_concurrent_service

/-- info:
'Vegas.recoverySourceCheckpoint_proposalArchive_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.recoverySourceCheckpoint_proposalArchive_history

/-- info:
'Vegas.RecoverySourceWitness.respond_archivedProposals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.respond_archivedProposals

/-- info:
'Vegas.RecoverySourceWitness.environment_archivedProposals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.environment_archivedProposals

/-- info:
'Vegas.RecoverySourceWitness.initialized_archivedProposals'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.initialized_archivedProposals

/-- info:
'Vegas.RecoverySourceCheckpoint.ArchivedProposals.binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceCheckpoint.ArchivedProposals.binding

/-- info:
'Vegas.phaseProposalBaseClasses_fullSupport_of_counted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBaseClasses_fullSupport_of_counted

/-- info:
'Vegas.phaseProposalReferenceClasses_eq_of_counted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceClasses_eq_of_counted

/-- info:
'Vegas.phaseProposalReferenceResponses_project_of_counted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceResponses_project_of_counted

/-- info:
'Vegas.phaseProposalReferencePolicy_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferencePolicy_fullSupport

/-- info:
'Vegas.phaseProposalReferenceStrategy_fullSupport'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceStrategy_fullSupport

/-- info:
'Vegas.phaseProposalReferencePolicy_decompose'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferencePolicy_decompose

/-- info:
'Vegas.phaseProposalQuery?_genuine_of_counted_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalQuery?_genuine_of_counted_binding

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_segment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.empty_processing_segment

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_prefix_application'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_prefix_application

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_epoch_application'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_epoch_application

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.trace_activation_words_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.trace_activation_words_congr

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.trace_response_ordinals_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.trace_response_ordinals_congr

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.BindingFrame.handle_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.BindingFrame.handle_binding

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.commitment_drain_frame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.commitment_drain_frame

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.phase_binding_handler_counterpart'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.phase_binding_handler_counterpart

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.foreign_processing_prefix_frame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.foreign_processing_prefix_frame

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_owned_packet_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_owned_packet_congr

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.BindingFrame.expire_owned'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.BindingFrame.expire_owned

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.binding_expiry_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.binding_expiry_pair

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.normalize_binding_pair_unfinished'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.normalize_binding_pair_unfinished

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.phase_owned_expiry_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.phase_owned_expiry_pair

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.phase_binding_successor_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.phase_binding_successor_pair

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.current_commitment_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.current_commitment_packet

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_unfinished'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_unfinished

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_event_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_event_eq

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_unique'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_unique

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.pending_frontier_surroundings'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_frontier_surroundings

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.completed_owner_pending_stale'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.completed_owner_pending_stale

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.binding_processing_snapshot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.binding_processing_snapshot

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_binding_projection'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_binding_projection

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_owned_processing_pair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_owned_processing_pair

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_foreign_processing'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_foreign_processing

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_foreign_batch'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.same_attempt_foreign_batch

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_original_prefix_frame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_original_prefix_frame

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_foreign_exit_snapshot'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_foreign_exit_snapshot

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.counted_processing_owned_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.counted_processing_owned_packet

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.processing_owned_receipt_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.processing_owned_receipt_congr

/-- info:
'Vegas.EventGraphRuntime.phase_prefix_semantic_extension'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_prefix_semantic_extension

/-- info:
'Vegas.EventGraphRuntime.phase_unfinished_predecessor_no_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_unfinished_predecessor_no_response

/-- info:
'Vegas.EventGraphRuntime.phase_successor_first_after_environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_successor_first_after_environment

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.successor_response_receipt'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.successor_response_receipt

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.counted_processing_owned_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.counted_processing_owned_successor

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.drain_excluded_owner_completed'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.drain_excluded_owner_completed

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.drain_excluded_owner_binding_records'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.drain_excluded_owner_binding_records

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_packet'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_packet

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingResponse_localPacket'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingResponse_localPacket

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingResponse_packet_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingResponse_packet_law

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingPolicy_packet_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingPolicy_packet_congr

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_packet_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.phaseBindingSlotPolicy_packet_congr

/-- info:
'Vegas.EventGraphRuntime.PhaseCount.bindingResultEncoder_packet_congr'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseCount.bindingResultEncoder_packet_congr

/-- info:
'Vegas.phaseProposalQuery?_eq_of_masked_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalQuery?_eq_of_masked_prefix

/-- info:
'Vegas.phaseProposalQuery?_eq_of_ready_saved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalQuery?_eq_of_ready_saved

/-- info:
'Vegas.phaseProposalBindingResults_eq_of_query'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBindingResults_eq_of_query

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_config'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_config

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.OwnBindings.restrictCompleted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.OwnBindings.restrictCompleted

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_native'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_native

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_restore'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_restore

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.rememberCompletion_saved'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.rememberCompletion_saved

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_completeFailure'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_completeFailure

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_completeAutomatic'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_completeAutomatic

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_drainFuel'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_drainFuel

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_drain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_drain

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_restore_drain'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.restrictCompleted_restore_drain

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.settle_phaseStateFrame'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.settle_phaseStateFrame

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.normalize'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.normalize

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.playerView_other'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.playerView_other

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_binding

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_owned_binding_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_owned_binding_of_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_owned_binding_external_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_owned_binding_external_of_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.native_advanceClock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.native_advanceClock

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.native_expire'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.native_expire

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.environment_expire'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.environment_expire

/-- info:
'Vegas.phaseProposalUnflaggedBinding_preparation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflaggedBinding_preparation_law

/-- info:
'Vegas.phaseProposalUnflaggedBinding_supported_usable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflaggedBinding_supported_usable

/-- info:
'Vegas.compileChecks_read_cone'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.compileChecks_read_cone

/-- info:
'Vegas.CompiledSuffix.revealTail_guard_cones'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.revealTail_guard_cones

/-- info:
'Vegas.CompiledSuffix.resolve_read_cone'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.CompiledSuffix.resolve_read_cone

/-- info:
'Vegas.EventGraphRuntime.phase_first_recorded_request_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_first_recorded_request_prefix

/-- info:
'Vegas.EventGraphRuntime.phase_recorded_unfinished_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_recorded_unfinished_request

/-- info:
'Vegas.EventGraphRuntime.phase_anchoredPolicy_eq_of_unrecorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_anchoredPolicy_eq_of_unrecorded

/-- info:
'Vegas.EventGraphRuntime.phase_recorded_prescribed_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_recorded_prescribed_response

/-- info:
'Vegas.EventGraphRuntime.phase_unrecorded_request_unsent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_unrecorded_request_unsent

/-- info:
'Vegas.EventGraphRuntime.phase_finish_supported_of_consistent_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_finish_supported_of_consistent_prefix

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.expired_request_first_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.expired_request_first_response

/-- info:
'Vegas.EventGraphRuntime.ReservedEpoch.first_binding_response_cannot_expire'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.first_binding_response_cannot_expire

/-- info:
'Vegas.phaseProposalUnflagged_expiry_recorded_at_anchor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_expiry_recorded_at_anchor

/-- info:
'Vegas.phaseProposalUnflagged_stopped_exclusion_request'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_exclusion_request

/-- info:
'Vegas.phaseProposalUnflagged_stopped_survival_of_fresh'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_survival_of_fresh

/-- info:
'Vegas.RecoverySourceWitness.checkpointDebt_of_failed_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.checkpointDebt_of_failed_binding

/-- info:
'Vegas.phaseCheckpointDebt_invariant'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCheckpointDebt_invariant

/-- info:
'Vegas.phaseCheckpointDebt_transition'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCheckpointDebt_transition

/-- info:
'Vegas.phaseCheckpointDebt_excluded_of_finished'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCheckpointDebt_excluded_of_finished

/-- info:
'Vegas.phaseCheckpointDebt_terminal_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseCheckpointDebt_terminal_payoff

/-- info:
'Vegas.reserved_checkpointDebt_terminal_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.reserved_checkpointDebt_terminal_payoff

/-- info:
'Vegas.reserved_checkpointDebt_expected_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.reserved_checkpointDebt_expected_payoff

/-- info:
'Vegas.reserved_checkpointDebt_behavioral_terminal_payoff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.reserved_checkpointDebt_behavioral_terminal_payoff

/-- info:
'Vegas.RecoverySourceWitness.ordinary_binding_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.ordinary_binding_draw

/-- info:
'Vegas.RecoverySourceWitness.ordinary_binding_preparation_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.ordinary_binding_preparation_law

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_binding_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_binding_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_binding_raw_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_binding_raw_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.binding_response_member'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.binding_response_member

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_owned_binding_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_owned_binding_of_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_owned_binding_repair_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_owned_binding_repair_trace

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_foreign_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_foreign_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_wait_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_wait_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.native_executeSample'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.native_executeSample

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.native_environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.native_environment

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.environment_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.environment_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_external_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_external_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.activation_external_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.activation_external_coupling

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.completeFailure_bindingRefines'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.completeFailure_bindingRefines

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.CompletedAt.automatic_refinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.CompletedAt.automatic_refinement

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.CompletedAt.phase_drain_refinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.CompletedAt.phase_drain_refinement

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.successful_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.successful_opening

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_opening'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_opening

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.transitionMass_le_one'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.transitionMass_le_one

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.exists_transitionMass_floor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.exists_transitionMass_floor

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.exists_ownPlay_length_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.exists_ownPlay_length_bound

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.historyReach_eq_transitionMass_mul_ownPlay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.historyReach_eq_transitionMass_mul_ownPlay

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.preparedBindingResult_of_recorded'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.preparedBindingResult_of_recorded

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PreparedBindingResult.rebase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindingResult.rebase

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.preparedBindings_initial'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.preparedBindings_initial

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.rebase'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.rebase

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.environment'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.environment

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.respond'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.respond

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.prepared_binding_result'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.prepared_binding_result

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_foreign_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handle_foreign_binding

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.CompletedAt.completionStep_refinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.CompletedAt.completionStep_refinement

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.CompletedAt.environment_refinement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.CompletedAt.environment_refinement

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.binding_response'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.binding_response

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.respond_inert_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.respond_inert_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.opening_response_external'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.opening_response_external

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.binding_response_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.binding_response_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.response_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.response_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_foreign_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_foreign_binding

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_opening_of_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.repair_opening_of_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.opening_acceptance_reflects'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.opening_acceptance_reflects

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.binding_handler_isSome_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.binding_handler_isSome_eq

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.rejection_of_counted'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.rejection_of_counted

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_rejected_repair_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_rejected_repair_trace

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_accepted_repair_trace'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_accepted_repair_trace

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handler_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PhaseStateFrame.handler_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.include_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.include_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.environment_repair'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.environment_repair

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.repair_counted_history'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.repair_counted_history

/-- info:
'Vegas.EventGraphRuntime.BindingShadow.repair_counted_history_ownPlay'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.repair_counted_history_ownPlay

/-- info:
'Vegas.EventGraphRuntime.PhaseProposal.phase_attempt_stopped_sourceArchive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.phase_attempt_stopped_sourceArchive

/-- info:
'Vegas.phaseProposalUnflagged_stopped_binding_image'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_binding_image

/-- info:
'Vegas.decodeCommitAttempt_joint_at_typed_admission'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_joint_at_typed_admission

/-- info:
'Vegas.decodeCommitAttempt_joint_of_recorded_preparation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.decodeCommitAttempt_joint_of_recorded_preparation

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.responseAliasMass_positive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.responseAliasMass_positive

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_probability_le_class' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_probability_le_class

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_probability_ge_alias' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.splitResponseLaw_probability_ge_alias

/-- info: 'Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.recorded_preparation_usable' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.BindingShadow.PreparedBindings.recorded_preparation_usable

/-- info: 'Vegas.phaseProposalPooledDomain_ordinary_domination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalPooledDomain_ordinary_domination

/-- info: 'Vegas.phaseProposalBasePolicy_ordinary_domination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBasePolicy_ordinary_domination

/-- info: 'Vegas.phaseProposalReferenceResponses_ordinary_domination' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceResponses_ordinary_domination

/-- info: 'Vegas.exists_phaseProposalOrdinaryStrategy_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposalOrdinaryStrategy_floor

/-- info: 'Vegas.phaseProposalOrdinaryResponses_supported_of_counted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalOrdinaryResponses_supported_of_counted

/-- info: 'Vegas.phaseProposalRepaired_recorded_prepared' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalRepaired_recorded_prepared

/-- info: 'Vegas.phaseProposalReferenceResponses_badPreparation_mass_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceResponses_badPreparation_mass_le

/-- info: 'Vegas.phaseProposalReferenceResponses_badPreparation_atom_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReferenceResponses_badPreparation_atom_le

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.repair_information_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.repair_information_history

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.GeneratedUnusableBindingHistory

/-- info: 'Vegas.exists_phaseProposalPooled_response_floor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposalPooled_response_floor

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.historyReach_le_of_designated_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.historyReach_le_of_designated_word

/-- info: 'Vegas.phaseProposalReference_word_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalReference_word_probability

/-- info: 'Vegas.phaseProposalRepaired_owner_word_lower' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalRepaired_owner_word_lower

/-- info: 'Vegas.phaseProposalGenerated_owner_word_upper' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalGenerated_owner_word_upper

/-- info: 'Vegas.exists_phaseProposal_generatedPreparation_posterior_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposal_generatedPreparation_posterior_bound

/-- info: 'Vegas.exists_phaseProposal_foreignPreparation_posterior_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.exists_phaseProposal_foreignPreparation_posterior_bound

/-- info: 'Interaction.ReactiveApplication.new_accepting_receipt_command' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.ReactiveApplication.new_accepting_receipt_command

/-- info: 'Vegas.EventGraphRuntime.phase_prefix_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_prefix_accepted

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.accepting_include_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.accepting_include_binding

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_receipt_requires_timely_epoch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_receipt_requires_timely_epoch

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_receipt_iff_timely_epoch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.pending_binding_receipt_iff_timely_epoch

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_receipt_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_receipt_iff

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_receipts_congr' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_receipts_congr

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_joint_receipt_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.old_pending_response_joint_receipt_law

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.first_owner_offer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.first_owner_offer

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.first_due_check' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.first_due_check

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsent_request_before_next_offer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsent_request_before_next_offer

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsent_request_at_owner_offer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsent_request_at_owner_offer

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsent_due_check_before_offer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsent_due_check_before_offer

/-- info: 'Vegas.phaseProposalUnflagged_unsent_binding_receipt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_unsent_binding_receipt

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.original_binding_receipt_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.original_binding_receipt_accepted

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.original_snapshot_preserves_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.original_snapshot_preserves_accepted

/-- info: 'Vegas.phaseProposalUnflagged_stopped_rejected_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_rejected_binding

/-- info: 'Vegas.phaseProposalUnflagged_stopped_owned_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_owned_word

/-- info: 'Vegas.phaseProposalObservedBindingFailure_observe' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalObservedBindingFailure_observe

/-- info: 'Vegas.phaseProposalObservedBindingFailure_withHistory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalObservedBindingFailure_withHistory

/-- info: 'Vegas.phaseProposalSavedBindingFailure_iff_of_seed_request' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_iff_of_seed_request

/-- info: 'Vegas.phaseProposalCurrentBindingFailure_iff_of_restored_readback' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalCurrentBindingFailure_iff_of_restored_readback

/-- info: 'Vegas.phaseProposalCancelableBindingFailure_iff_of_readbacks' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalCancelableBindingFailure_iff_of_readbacks

/-- info: 'Vegas.RecoverySourceWitness.checkpointDebt_of_observed_saved_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.checkpointDebt_of_observed_saved_binding

/-- info: 'Vegas.RecoverySourceWitness.observed_saved_binding_of_failed_cell' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.observed_saved_binding_of_failed_cell

/-- info: 'Vegas.phaseProposalSavedBindingFailure_checkpointDebt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_checkpointDebt

/-- info: 'Vegas.phaseProposalCurrentBindingFailure_genuine' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalCurrentBindingFailure_genuine

/-- info: 'Vegas.phaseProposalCurrentBindingFailure_checkpointed_after_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalCurrentBindingFailure_checkpointed_after_step

/-- info: 'Vegas.phaseProposalSavedBindingFailure_information_history' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_information_history

/-- info: 'Vegas.phaseProposalSavedBindingFailure_information_terminal_payoff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_information_terminal_payoff

/-- info: 'Vegas.phaseProposalSavedBindingFailure_historyGain_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_historyGain_eq_zero

/-- info: 'Vegas.phaseProposalSavedBindingFailure_gain_eq_zero' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalSavedBindingFailure_gain_eq_zero

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.prefix_accepting_receipt_boundary' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.prefix_accepting_receipt_boundary

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.input_mem_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.input_mem_prefix

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.retired_binding_receipt_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.retired_binding_receipt_iff

/-- info: 'Vegas.stopped_prefix_roundsSupported' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.stopped_prefix_roundsSupported

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.stopped_pending_binding_receipt_iff_epoch' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.stopped_pending_binding_receipt_iff_epoch

/-- info: 'Vegas.phaseProposalBindingGraphView_archive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBindingGraphView_archive

/-- info: 'Vegas.phaseProposalBindingPotentialProfile_harmonic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBindingPotentialProfile_harmonic

/-- info: 'Vegas.phaseProposalUnflagged_binding_action_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_binding_action_law

/-- info: 'Vegas.phaseProposalUnflagged_binding_emission_harmonic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_binding_emission_harmonic

/-- info: 'Vegas.phaseProposalUnflagged_binding_response_harmonic' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_binding_response_harmonic

/-- info: 'Vegas.phaseProposalEmissionFrontier_binding_step' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalEmissionFrontier_binding_step

/-- info: 'Vegas.phaseProposalBinding_completed_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBinding_completed_agreement

/-- info: 'Vegas.phaseProposalBinding_settled_domain' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalBinding_settled_domain

/-- info: 'Vegas.phaseProposalEmissionFrontier_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalEmissionFrontier_ready

/-- info: 'Vegas.phaseProposalEmissionFrontier_traceInvariant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalEmissionFrontier_traceInvariant

/-- info: 'Vegas.phaseProposalEmissionFrontier_automatic_values' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalEmissionFrontier_automatic_values

/-- info: 'Vegas.phaseProposalEmissionFrontier_callback_frame' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalEmissionFrontier_callback_frame

/-- info: 'Vegas.phaseProposalUnflagged_stopped_potential_of_fresh_entry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_potential_of_fresh_entry

/-- info: 'Vegas.phaseProposalUnflagged_stopped_binding_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_binding_word

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.phase_commitment_prefix_sourceArchive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseProposal.phase_commitment_prefix_sourceArchive

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.settle_entry_excluded_of_same' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.settle_entry_excluded_of_same

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_entry_excluded_of_changed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.normalize_entry_excluded_of_changed

/-- info: 'Vegas.EventGraphRuntime.PhaseRuntimeState.initial_entry_excluded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.PhaseRuntimeState.initial_entry_excluded

/-- info: 'Vegas.EventGraphRuntime.phaseApplication_namespaceInstallation' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phaseApplication_namespaceInstallation

/-- info: 'Vegas.EventGraphRuntime.phase_attempt_installed_prefix' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.phase_attempt_installed_prefix

/-- info: 'Vegas.phaseProposal_binding_entry_checkpoint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposal_binding_entry_checkpoint

/-- info: 'Vegas.phaseProposalUnflagged_installed_binding_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_installed_binding_word

/-- info: 'Vegas.RecoverySourceWitness.ordinary_frozen_binding_query' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.RecoverySourceWitness.ordinary_frozen_binding_query

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.complete_rounds_extension' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.complete_rounds_extension

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.request_binding_identifier_not_receipted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.request_binding_identifier_not_receipted

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.not_unsentQualification_of_due' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.not_unsentQualification_of_due

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsentQualification_iff_first_offer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsentQualification_iff_first_offer

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.first_owner_offer_or_due' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.first_owner_offer_or_due

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsent_first_offer_or_due_before_exit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsent_first_offer_or_due_before_exit

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.unsent_race_response_before_exit' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.unsent_race_response_before_exit

/-- info: 'Vegas.phaseProposalUnflagged_stopped_unsent_offer_receipt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_unsent_offer_receipt

/-- info: 'Vegas.phaseProposalUnflagged_stopped_unsent_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.phaseProposalUnflagged_stopped_unsent_binding

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.rejected_binding_not_accepted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.ReservedEpoch.rejected_binding_not_accepted

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.closing_receipt_record' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.closing_receipt_record

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.original_binding_publicFailure_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.original_binding_publicFailure_iff

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.original_binding_sourceFailureFootprint' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.original_binding_sourceFailureFootprint

/-- info: 'Vegas.phaseProposalUnflagged_stopped_acceptance_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_stopped_acceptance_word

/-- info: 'Vegas.phaseProposalUnflagged_response_acceptance_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_response_acceptance_word

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.frontierQualification_respond_foreign' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.frontierQualification_respond_foreign

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.ownedAcceptanceWord_respond_foreign' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.ownedAcceptanceWord_respond_foreign

/-- info: 'Vegas.EventGraphRuntime.PhaseProposal.commitment_response_archive' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.PhaseProposal.commitment_response_archive

/-- info: 'Vegas.phaseProposalUnflagged_paired_response_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_paired_response_word

/-- info: 'Vegas.EventGraphRuntime.ReservedEpoch.ownedAcceptanceWord_wait_imp_available_binding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.EventGraphRuntime.ReservedEpoch.ownedAcceptanceWord_wait_imp_available_binding

/-- info: 'Vegas.phaseProposalUnflagged_wait_send_stopped_word' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.phaseProposalUnflagged_wait_send_stopped_word
