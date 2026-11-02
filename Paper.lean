/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Safety
import Vegas.Compile.EventGraphScheduling
import Vegas.Compile.EventGraphDeviation
import Vegas.Game.EventCompilation
import Vegas.Game.CompilerCorrectness
import Vegas.Pending.GraphRefinement
import Vegas.Game.IntendedPreservation
import Vegas.Game.IntendedNash
import Vegas.Game.AsyncServiceRawNash
import Vegas.Game.AsyncClientObservables
import Vegas.Game.ProgramPaymentAsyncNash
import Vegas.Game.OnePacketExtension
import Vegas.Game.SequentialCompilation
import Vegas.Game.ClientObservables
import Vegas.Game.PaymentPreservation
import Vegas.Game.ServiceRosterAsync
import Vegas.Examples.LateLeak
import Vegas.Examples.CommitRevealAuction
import Vegas.Examples.BoundedPaymentAuction
import Vegas.Examples.OddsEvensRawEquilibrium
import Vegas.Examples.OddsEvensFullSource

/-! # Mathematical results stated in the maintained paper

Each guarded command pins the exact axiom dependencies of its owning result.
The manuscript's theorem and invariant inventory determines this set.
-/

/-! ## Source game -/

/-- info: 'Vegas.SourceProgram.Setup.protocol_bounded' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.protocol_bounded

/-- info: 'Vegas.SourceProgram.Setup.intended_forfeit_isεNash_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_forfeit_isεNash_preserved

/-- info: 'Vegas.SourceProgram.Setup.intended_forfeit_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intended_forfeit_sequentialEquilibrium_preserved

/-- info: 'Vegas.SourceProgram.Setup.intendedState_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.intendedState_trace

/-- info: 'Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.failedReveals_eq_zero_of_intendedState

/-- info: 'Vegas.SourceProgram.Setup.revealed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.revealed

/-- info: 'Vegas.SourceProgram.Setup.terminal_guards_hold' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.terminal_guards_hold

/-- info: 'Vegas.sourceObserve_privateInput' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceObserve_privateInput

/-! ## Graph compilation -/

/-- info: 'Vegas.scheduled_terminalConfig_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.scheduled_terminalConfig_law

/-- info: 'Vegas.scheduled_setup_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.scheduled_setup_deviation_law

/-- info: 'Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SourceProgram.Setup.eventGame_approximate_nash_iff

/-! ## Physical compilation -/

/-- info: 'Vegas.EventGraphRuntime.reactive_protocol_graph_refinement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.reactive_protocol_graph_refinement

/-- info: 'Vegas.sourceServiceClientPolicy_outcome_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceServiceClientPolicy_outcome_law

/-- info: 'Vegas.sourceServiceClientPolicy_graph_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.sourceServiceClientPolicy_graph_law

/-! ## Nash correspondence -/

/-- info: 'Vegas.AsyncServiceSpec.isεNash_rawClientProfile_approximate' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_rawClientProfile_approximate

/-- info: 'Vegas.AsyncServiceSpec.intended_rawClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_rawClientProfile_isεNash

/-- info: 'Vegas.AsyncServiceSpec.isεNash_firstTurnClientProfile_iff' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.isεNash_firstTurnClientProfile_iff

/-- info: 'Vegas.AsyncServiceSpec.intended_firstTurnClientProfile_isεNash' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.intended_firstTurnClientProfile_isεNash

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.clientSettlementLaw_withinTV

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_event_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.clientSettlementLaw_event_lower_bound

/-- info: 'Vegas.AsyncServiceSpec.clientSettlementLaw_expect_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.clientSettlementLaw_expect_lower_bound

/-- info: 'Vegas.asyncDeviation_readout_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.asyncDeviation_readout_law

/-! ## Monetary observations -/

/-- info: 'Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.AsyncServiceSpec.payment_firstTurnClientProfile_settlement_law

/-- info: 'Vegas.intended_raw_programPayments_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.intended_raw_programPayments_preserved

/-! ## Sequential compilation and clients -/

/-- info: 'Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraphRuntime.MessageBounds.onePacket_raw_sequentialEquilibrium

/-- info: 'Vegas.intended_raw_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.intended_raw_sequentialEquilibrium_preserved

/-- info: 'Vegas.ClientSpec.compile_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientSpec.compile_correct

/-- info: 'Vegas.ClientCompilation.clients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientCompilation.clients_sequentiallyRational

/-- info: 'Vegas.ClientSpec.compile_ledger_correct' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientSpec.compile_ledger_correct

/-- info: 'Vegas.ClientCompilation.ledgerClients_sequentiallyRational' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientCompilation.ledgerClients_sequentiallyRational

/-- info: 'Vegas.ClientSpec.intended_outcomeLaws_subset' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientSpec.intended_outcomeLaws_subset

/-- info: 'Vegas.ClientCompilation.clients_postprocessLaw' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ClientCompilation.clients_postprocessLaw

/-- info: 'Vegas.intended_onePacket_sequentialEquilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.intended_onePacket_sequentialEquilibrium_preserved

/-! ## Concrete instances -/

/-- info: 'Vegas.rosterScheduler_asyncContract' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_asyncContract

/-- info: 'Vegas.rosterScheduler_asyncTimely' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.rosterScheduler_asyncTimely

/-- info: 'Vegas.Examples.OddsEvensRaw.intended_equilibrium_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRaw.intended_equilibrium_preserved

/-- info: 'Vegas.Examples.OddsEvensRaw.fair_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRaw.fair_equilibrium_exists

/-- info: 'Vegas.Examples.OddsEvensRaw.collection_probability' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvensRaw.collection_probability

/-- info: 'Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvens.fair_full_source_equilibrium_exists

/-- info: 'Vegas.Examples.CommitRevealAuction.truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitRevealAuction.truthful_not_dominant

/-- info: 'Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant

/-- info: 'Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.BoundedPaymentAuction.truthful_not_dominant

/-- info: 'Vegas.Examples.OddsEvens.uniformAssessment_equilibrium' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvens.uniformAssessment_equilibrium

/-- info: 'Vegas.Examples.OddsEvens.uniformJointLaw_expected' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.Examples.OddsEvens.uniformJointLaw_expected

/-! ## Alternative late-acceptance game -/

/-- info: 'Vegas.lateLeak_intended_outcome_not_preserved' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_intended_outcome_not_preserved

/-- info: 'Vegas.lateLeak_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_not_preserved_for_every_margin

/-- info: 'Vegas.settleLate_not_preserved_for_every_margin' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.settleLate_not_preserved_for_every_margin

/-- info: 'Vegas.lateLeak_sample_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_sample_totalVariation_lower_bound

/-- info: 'Vegas.lateLeak_sample_result_totalVariation_lower_bound' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_sample_result_totalVariation_lower_bound

/-- info: 'Vegas.lateLeak_outcome_preserved_of_half_reward_costs' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.lateLeak_outcome_preserved_of_half_reward_costs
