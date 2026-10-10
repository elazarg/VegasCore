/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.BindingRepairTrace
import Vegas.Source.SetupProtocolBehavioral
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Continuation kernels against copied value-interface opponents -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable (setup : Setup (Player := Player) (L := L))

/-- On a represented actual prefix, copied foreign laws equal the global
value-menu embedding. Equality is derived from actual retained sites. -/
theorem copied_foreign_law (admission : CommitmentInterface setup.program)
    (who observer : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (original : (setup.executionProtocol admission).History)
    (repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (related : setup.FocalRepair who original.state repaired.state)
    (observed : (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
      observer repaired.trace = (setup.informationModel admission).infoOf observer original.trace)
    (running : ¬ (setup.executionProtocol admission).terminal original.state)
    (foreign : observer ≠ who) :
    target observer ((setup.informationModel admission).infoOf observer original.trace) =
      (source observer ((setup.informationModel admission).infoOf observer original.trace)).map
        ((setup.valuesRestriction admission).choice observer
          ((setup.informationModel admission).infoOf observer original.trace)) := by
  by_cases active : (setup.executionProtocol admission).active original.state observer
  · have running' : ¬ (setup.executionProtocol
        (CommitmentInterface.values setup.program)).terminal repaired.state :=
      fun stopped => running ((FocalRepair.terminal_iff setup related admission).mp stopped)
    have active' : (setup.executionProtocol (CommitmentInterface.values setup.program)).active
        repaired.state observer := by
      change (setup.protocolObserve observer repaired.state).elim False
        (fun view => ProtocolView.actor observer setup.program view = some observer)
      rw [FocalRepair.foreign_observe setup related foreign]
      exact active
    obtain ⟨site, siteView⟩ := (setup.informationModel
      (CommitmentInterface.values setup.program)).exists_informationSite_of_active
        observer repaired running' active'
    have sameInfo : (setup.informationModel admission).infoOf observer original.trace = site.1 :=
      observed.symm.trans siteView.symm
    rw [sameInfo]
    exact copies observer site
  · exact (setup.informationModel admission).behavioral_eq_of_not_active
      (target observer)
      (fun info => (source observer info).map
        ((setup.valuesRestriction admission).choice observer info)) original.trace active

/-- The actual larger-game continuation against copied opponents has the
kernel of the fixed globally embedded source opponents, even after focal failed
commitments. No continuation optimality or kernel equality is assumed. -/
theorem run_copied_opponents_from_values_history [Fintype Player]
    (admission : CommitmentInterface setup.program) (who : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (start : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (fuel : ℕ) :
    (setup.informationModel admission).runBehavioralFrom
      (Function.update target who deviation) fuel
        ((setup.valuesRestriction admission).history start) =
    (setup.informationModel admission).runBehavioralFrom
      (Function.update (fun player info => (source player info).map
        ((setup.valuesRestriction admission).choice player info)) who deviation)
      fuel ((setup.valuesRestriction admission).history start) := by
  apply (setup.informationModel admission).runBehavioralFrom_congr_on_support
  intro elapsed _ later supported running observer
  by_cases own : observer = who
  · subst observer
    simp only [Function.update_self]
  · simp only [Function.update_of_ne own]
    obtain ⟨repaired, _, related, observed⟩ :=
      setup.deviation_history_values_representation admission who source target copies deviation
        start elapsed later supported
    exact setup.copied_foreign_law admission who observer source target copies later repaired
      related
      (observed observer own) running own

/-- The structural value-menu embedding is exactly the same admitted source
policy interpreted in the larger actual commitment interface. -/
theorem toProtocolBehavioralPolicy_values_embedding
    (admission : CommitmentInterface setup.program) (who : Player)
    (policy : BehavioralPolicy who setup.program) (values : ValueBinding setup.program policy)
    (view : setup.ProtocolView who) :
    (setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who policy
      (values.admitted setup.program policy (CommitmentInterface.values setup.program)) view).map
        ((setup.valuesRestriction admission).choice who view) =
      setup.toProtocolBehavioralPolicy admission who policy
        (values.admitted setup.program policy admission) view := by
  apply pmf_map_injective Subtype.val_injective
  rw [PMF.map_comp]
  change (setup.toProtocolBehavioralPolicy (CommitmentInterface.values setup.program) who policy
    (values.admitted setup.program policy (CommitmentInterface.values setup.program)) view).map
      Subtype.val = _
  erw [setup.toProtocolBehavioralPolicy_map_val, setup.toProtocolBehavioralPolicy_map_val]
  rfl

/-- Actual copied-policy continuation readout is the original source continuation
against a single arbitrary admitted focal source deviation. -/
theorem copied_continuation_readout_eq [Fintype Player]
    (admission : CommitmentInterface setup.program) (who : Player)
    (profile : BehavioralProfile setup.program)
    (values : ∀ player, ValueBinding setup.program (profile player))
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile
      (fun player => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player (profile player)
          ((values player).admitted setup.program (profile player)
            (CommitmentInterface.values setup.program))) target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (start : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (fuel : ℕ) (enough : setup.protocolRemaining start.state ≤ fuel) :
    ((setup.informationModel admission).runBehavioralFrom
      (Function.update target who deviation) fuel
      ((setup.valuesRestriction admission).history start)).map
        (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw
        (Function.update profile who ((setup.behavioralPolicyEquiv admission who).symm
          deviation).1) start.state).map some := by
  rw [setup.run_copied_opponents_from_values_history admission who _ target copies]
  have embedded :
      (fun player info => (setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player (profile player)
          ((values player).admitted setup.program (profile player)
            (CommitmentInterface.values setup.program)) info).map
          ((setup.valuesRestriction admission).choice player info)) =
      (fun player => setup.toProtocolBehavioralPolicy admission player (profile player)
        ((values player).admitted setup.program (profile player) admission)) := by
    funext player info
    exact setup.toProtocolBehavioralPolicy_values_embedding admission player _ (values player) info
  erw [embedded]
  let replacement := (setup.behavioralPolicyEquiv admission who).symm deviation
  have permitted : ∀ player,
      ((Function.update profile who replacement.1) player).Admitted setup.program admission := by
    intro player
    by_cases own : player = who
    · subst player
      simpa only [Function.update_self] using replacement.2
    · simpa only [Function.update_of_ne own] using
        (values player).admitted setup.program (profile player) admission
  have profiles : Function.update
      (fun player => setup.toProtocolBehavioralPolicy admission player (profile player)
        ((values player).admitted setup.program (profile player) admission)) who deviation =
      (fun player => setup.toProtocolBehavioralPolicy admission player
        ((Function.update profile who replacement.1) player) (permitted player)) := by
    funext player
    by_cases own : player = who
    · subst player
      simp only [Function.update_self]
      convert ((setup.behavioralPolicyEquiv admission who).apply_symm_apply deviation).symm using 1
      change setup.toProtocolBehavioralPolicy admission who
        ((Function.update profile who replacement.1) who) _ =
        setup.toProtocolBehavioralPolicy admission who replacement.1 replacement.2
      congr 1
      exact Function.update_self ..
    · simp only [Function.update_of_ne own]
      congr 1
      exact (Function.update_of_ne own ..).symm
  erw [profiles]
  rw [← GameTheory.Protocol.InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (single := setup.protocol_singleMover admission)]
  exact setup.protocol_runBehavioralFrom_eq admission _ permitted fuel
    ((setup.valuesRestriction admission).history start) enough

/-- Terminal native source utility is exactly the utility of its existing
source continuation; an arbitrary terminal certificate does not change this law. -/
theorem terminal_expect_source_continuation [Fintype Player]
    (admission : CommitmentInterface setup.program)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ player, (profile player).Admitted setup.program admission)
    (certificate : (setup.executionProtocol admission).WellFoundedHistories)
    (history : (setup.executionProtocol admission).History)
    (payoff : State L setup.program.terminalCtx → ℝ) :
    expect ((setup.informationModel admission).runBehavioralTerminalFrom certificate
      (fun player => setup.toProtocolBehavioralPolicy admission player (profile player)
        (permitted player)) history)
      (fun final => (setup.protocolReadout final.state).elim 0 payoff) =
    expect (setup.continuationLaw profile history.state) payoff := by
  have enough : setup.protocolRemaining history.state ≤ instructionCount setup.program + 1 := by
    have clock := setup.protocol_history_length admission history.trace
    omega
  have law := setup.protocol_runBehavioralFrom_eq admission profile permitted
    (instructionCount setup.program + 1) history enough
  rw [GameTheory.Protocol.InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom]
    at law
  rw [(setup.informationModel admission).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    certificate (setup.protocol_bounded admission)]
  have equality := congrArg (fun distribution => expect distribution
    (fun result => result.elim 0 payoff)) law
  simpa only [expect_map, Function.comp_def, Option.elim_some] using equality

/-- Copied native opponents admit the source continuation utility after any
legal focal policy deviation, at every embedded actual values history. -/
theorem copied_terminal_expect_source_continuation [Fintype Player]
    (admission : CommitmentInterface setup.program) (who : Player)
    (profile : BehavioralProfile setup.program)
    (values : ∀ player, ValueBinding setup.program (profile player))
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile
      (fun player => setup.toProtocolBehavioralPolicy
        (CommitmentInterface.values setup.program) player (profile player)
          ((values player).admitted setup.program (profile player)
            (CommitmentInterface.values setup.program))) target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (certificate : (setup.executionProtocol admission).WellFoundedHistories)
    (history : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (payoff : State L setup.program.terminalCtx → ℝ) :
    expect ((setup.informationModel admission).runBehavioralTerminalFrom certificate
      (Function.update target who deviation) ((setup.valuesRestriction admission).history history))
      (fun final => (setup.protocolReadout final.state).elim 0 payoff) =
    expect (setup.continuationLaw
      (Function.update profile who ((setup.behavioralPolicyEquiv admission who).symm deviation).1)
      history.state) payoff := by
  have enough : setup.protocolRemaining history.state ≤ instructionCount setup.program + 1 := by
    have clock := setup.protocol_history_length (CommitmentInterface.values setup.program)
      history.trace
    omega
  have law := setup.copied_continuation_readout_eq admission who profile values target copies
    deviation history (instructionCount setup.program + 1) enough
  rw [(setup.informationModel admission).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    certificate (setup.protocol_bounded admission)]
  have equality := congrArg (fun distribution => expect distribution
    (fun result => result.elim 0 payoff)) law
  simpa only [expect_map, Function.comp_def, Option.elim_some] using equality

end Vegas.SourceProgram.Setup
