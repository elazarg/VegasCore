/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceContinuation
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Analysis.Protocol.OneShotDeviation

/-! # Source continuations after one changed decision

Changing a law at one source information site first samples that law and then
uses the unchanged source policy. The original history evaluator supplies the
law; the existing source continuation evaluator only reads its resulting state.
This applies to all source instructions and commitment interfaces.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

open Classical in
/-- At an actual decision, only the acting player's local law contributes to
the next source state. All other coordinates are inactive. -/
theorem run_one_choice_state
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (history : (setup.executionProtocol admission).History)
    (who : Player) (running : ¬ (setup.executionProtocol admission).terminal history.state)
    (active : (setup.executionProtocol admission).active history.state who) :
    ((setup.informationModel admission).runBehavioralFrom profile 1 history).map History.state =
      (profile who ((setup.informationModel admission).infoOf who history.trace)).bind
        (fun choice => setup.protocolStep history.state
          (fun player => if player = who then choice.1 else none)) := by
  let model := setup.informationModel admission
  rw [model.runBehavioralFrom_succ_of_not_terminal profile 0 running,
    model.behavioralJoint_eq_map_of_at_most_one_active profile history.trace running who
      (fun player acts => setup.protocol_singleMover admission history.state acts active),
    FinDist.map_bind, FinDist.bind_map]
  apply FinDist.bind_congr
  intro choice _supported
  rw [FinDist.map_bindOnSupport]
  calc
    _ = ((setup.executionProtocol admission).step history.state
        (model.jointOfChoice (setup.protocol_singleMover admission) history running who active
          choice)).bind FinDist.pure := by
      apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
      intro next realized
      simp only [InformationModel.runBehavioralFrom, runRandomizedFor_zero, FinDist.map_pure]
      rfl
    _ = _ := by
      rw [FinDist.bind_pure]
      change setup.protocolStep history.state _ = setup.protocolStep history.state _
      congr 1
      funext player
      simp [InformationModel.jointOfChoice, singletonJoint]

open Classical in
/-- A one-site law replacement followed by the baseline source continuation,
with the exact terminal typed-state law. No future source decisions are changed. -/
theorem run_local_law_readout
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (history : (setup.executionProtocol admission).History)
    (who : Player) (running : ¬ (setup.executionProtocol admission).terminal history.state)
    (active : (setup.executionProtocol admission).active history.state who)
    {info : setup.ProtocolView who}
    (observed : (setup.informationModel admission).infoOf who history.trace = info)
    (law : FinDist ((setup.informationModel admission).Choice who info))
    (fuel : Nat) (enough : setup.protocolRemaining history.state ≤ fuel + 1) :
    ((setup.informationModel admission).runBehavioralFrom
      (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
        profile who ((profile who).withLaw info law))
      (fuel + 1) history).map (fun final => setup.protocolReadout final.state) =
      law.bind (fun choice =>
        ((setup.protocolStep history.state
          (fun player => if player = who then choice.1 else none)).bind
            (setup.continuationLaw (setup.decodeBehavioralProfile admission profile))).map
              some) := by
  cases observed
  let model := setup.informationModel admission
  let alternative := (profile who).withLaw (model.infoOf who history.trace) law
  let updated := Profile.update (sig := model.behavioralSignature) profile who alternative
  have split := model.one_step_then_baseline_eq_local_law (setup.decision_antichain admission)
    profile who alternative history active fuel
  simp only [alternative, InformationModel.BehavioralPolicy.withLaw_self] at split
  rw [← split, FinDist.map_bind]
  have further (next : (setup.executionProtocol admission).History)
      (supported : next ∈ (model.runBehavioralFrom updated 1 history).support) :
      setup.protocolRemaining next.state ≤ fuel := by
    rw [model.runBehavioralFrom_succ_of_not_terminal updated 0 running,
      FinDist.support_bind] at supported
    obtain ⟨joint, _, supported⟩ := Set.mem_iUnion₂.mp supported
    rw [FinDist.support_bindOnSupport] at supported
    obtain ⟨state, realized, supported⟩ := Set.mem_iUnion₂.mp supported
    cases FinDist.mem_support_pure.mp supported
    have consumed := setup.protocol_remaining_step history.state state joint.1 running realized
    change setup.protocolRemaining state ≤ fuel
    omega
  calc
    _ = (model.runBehavioralFrom updated 1 history).bind (fun next =>
        (setup.continuationLaw (setup.decodeBehavioralProfile admission profile) next.state).map
          some) := by
      apply FinDist.bind_congr
      intro next supported
      exact setup.runBehavioralFrom_readout admission profile fuel next (further next supported)
    _ = ((model.runBehavioralFrom updated 1 history).map History.state).bind (fun state =>
        (setup.continuationLaw (setup.decodeBehavioralProfile admission profile) state).map
          some) := by rw [FinDist.bind_map]
    _ = _ := by
      rw [setup.run_one_choice_state admission updated history who running active]
      simp only [updated, Profile.update_same, alternative, model,
        InformationModel.BehavioralPolicy.withLaw_self, FinDist.bind_bind, FinDist.map_bind]
      rfl

open Classical in
/-- The source continuation context after a local law replacement depends only
on the original assessment's posterior source state and its baseline policy. -/
theorem continuationContext_local_value_stateBelief
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (nonterminal : site.AllNonterminal)
    (law : FinDist ((setup.informationModel admission).Choice who site.1))
    (utility : State L setup.program.terminalCtx → ℝ) (fuel : Nat)
    (enough : ∀ history : (setup.informationModel admission).InformationHistory who site.1,
      setup.protocolRemaining history.1.state ≤ fuel + 1) :
    (assessment.continuationContext site
      (fun final => (setup.protocolReadout final.state).elim 0 utility) (fuel + 1)).value
        ((assessment.strategy who).withLaw site.1 law) =
      (assessment.stateBelief who site).expect (fun state => law.expect (fun choice =>
        ((setup.protocolStep state (fun player => if player = who then choice.1 else none)).bind
          (setup.continuationLaw
            (setup.decodeBehavioralProfile admission assessment.strategy))).expect utility)) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.expect_bind, InformationModel.BehavioralAssessment.stateBelief, FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _supported
  have lawEq := setup.run_local_law_readout admission assessment.strategy history.1 who
    (nonterminal history) (InformationModel.InformationSite.active _ site history)
    history.2 law fuel (enough history)
  have value := congrArg (fun distribution => distribution.expect
    (fun result => result.elim 0 utility)) lawEq
  simpa only [FinDist.expect_map, FinDist.expect_bind, Option.elim_some] using value

end Vegas.SourceProgram.Setup
