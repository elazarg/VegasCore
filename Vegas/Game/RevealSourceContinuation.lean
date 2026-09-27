/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceLocalContinuation
import Vegas.Source.RevealSequence

/-! # Binary local continuation values in the original revelation source

The original source assessment and its ordinary continuation contexts are
retained. At a reveal-only source site, the immediate behavioral law matters
only through the disclosure Boolean; its action representation is irrelevant.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (admission : CommitmentInterface setup.program)

omit [Fintype Player] in
theorem informationSite_nonterminal (who : Player)
    (site : (setup.informationModel admission).InformationSite who) : site.AllNonterminal := by
  intro history stopped
  have active := InformationModel.InformationSite.active _ site history
  cases state : history.1.state with
  | none =>
      rw [state] at active
      cases active
  | some current =>
      have terminal : ProtocolState.terminal setup.program current := by
        simpa only [Setup.executionProtocol, state, Option.elim_some] using stopped
      have actor : ProtocolView.actor who setup.program
          (ProtocolState.observe who setup.program current) = some who := by
        simpa only [Setup.executionProtocol, state, Setup.protocolObserve, Option.map_some,
          Option.elim_some] using active
      rw [ProtocolState.terminal_actor_none who setup.program current terminal] at actor
      cases actor

open Classical in
/-- Any Boolean section of joint actions computes the original source local
value, provided it has the chosen disclosure at the active owner. No section
legality premise is necessary: the actual local law remains source-legal. -/
theorem reveal_local_value
    (reveals : setup.program.RevealOnly)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (law : FinDist ((setup.informationModel admission).Choice who site.1))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    (assessment.continuationContext site
      (fun final => (setup.protocolReadout final.state).elim 0 utility)
      (instructionCount setup.program + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      (assessment.stateBelief who site).expect (fun state =>
        (law.map (fun choice => OwnAction.disclosure choice.1)).expect (fun disclose =>
          ((setup.protocolStep state (joint disclose)).bind
            (setup.continuationLaw (setup.decodeBehavioralProfile admission
              assessment.strategy))).expect utility)) := by
  have enough (history : (setup.informationModel admission).InformationHistory who site.1) :
      setup.protocolRemaining history.1.state ≤ instructionCount setup.program + 1 := by
    have counted := setup.protocol_history_length admission history.1.trace
    omega
  rw [setup.continuationContext_local_value_stateBelief admission assessment who site
    (setup.informationSite_nonterminal admission who site) law utility
    (instructionCount setup.program) enough]
  simp only [InformationModel.BehavioralAssessment.stateBelief, FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _supported
  apply FinDist.expect_congr
  intro choice _chosen
  have active := InformationModel.InformationSite.active _ site history
  have same : setup.protocolStep history.1.state
      (fun player => if player = who then choice.1 else none) =
      setup.protocolStep history.1.state (joint (OwnAction.disclosure choice.1)) := by
    cases state : history.1.state with
    | none => rfl
    | some current =>
        have actor : ProtocolView.actor who setup.program
            (ProtocolState.observe who setup.program current) = some who := by
          simpa only [Setup.executionProtocol, state, Setup.protocolObserve, Option.map_some,
            Option.elim_some] using active
        exact congrArg (fun distribution => distribution.map some)
          (ProtocolState.step_disclosure_congr who setup.program reveals current actor
            (fun player => if player = who then choice.1 else none)
            (joint (OwnAction.disclosure choice.1)) (by simp only [↓reduceIte, chosen]))
  rw [same]

open Classical in
/-- Binary source action probabilities multiply the two original conditional
continuation values, with the same source belief for each action. -/
theorem reveal_local_value_binary
    (reveals : setup.program.RevealOnly)
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (law : FinDist ((setup.informationModel admission).Choice who site.1))
    (joint : Bool → Player → Option (OwnAction Player L))
    (chosen : ∀ disclose, OwnAction.disclosure (joint disclose who) = disclose)
    (utility : State L setup.program.terminalCtx → ℝ) :
    let choice := law.map (fun action => OwnAction.disclosure action.1)
    let values := fun disclose => (assessment.stateBelief who site).expect (fun state =>
      ((setup.protocolStep state (joint disclose)).bind (setup.continuationLaw
        (setup.decodeBehavioralProfile admission assessment.strategy))).expect utility)
    (assessment.continuationContext site
      (fun final => (setup.protocolReadout final.state).elim 0 utility)
      (instructionCount setup.program + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      choice.prob true * values true + (1 - choice.prob true) * values false := by
  intro choice values
  rw [setup.reveal_local_value admission reveals assessment who site law joint chosen utility]
  have total := choice.sum_prob
  simp only [Fintype.sum_bool] at total
  have complement : choice.prob false = 1 - choice.prob true := by linarith
  change (assessment.stateBelief who site).expect
    (fun state => choice.expect (fun disclose =>
      ((setup.protocolStep state (joint disclose)).bind (setup.continuationLaw
        (setup.decodeBehavioralProfile admission assessment.strategy))).expect utility)) = _
  simp only [FinDist.expect_eq_sum choice, Fintype.sum_bool, complement,
    FinDist.expect_add, FinDist.expect_smul]
  rfl

end Vegas.SourceProgram.Setup
