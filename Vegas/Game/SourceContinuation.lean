/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import GameTheoryExtensions.Protocol.SingleMover
import GameTheoryExtensions.Protocol.StateKernel
import GameTheory.Protocol.BehavioralAssessment

/-! # Source continuation values depend on the source state

The existing source state contains its private inputs and original action
memory. Every legal behavioral policy has an equivalent syntactic policy.
Consequently the standard sequential-equilibrium continuation evaluator factors
through that state, including for whole-policy deviations. Preserving its belief
marginal suffices for utilities of the terminal typed store; full histories need
not be identified across an implementation's different step counts.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- Decode arbitrary legal behavioral policies, uniformly over the setup draw. -/
def decodeBehavioralProfile
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    BehavioralProfile setup.program :=
  fun who => ((setup.behavioralPolicyEquiv admission who).symm (profile who)).1

open Classical in
/-- The state law of one actual protocol step, with its ordinary terminal
absorption. It uses the protocol's existing observations and transition. -/
def behavioralStateStep
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (state : setup.ProtocolState) : FinDist setup.ProtocolState :=
  if state.elim False (SourceProgram.ProtocolState.terminal setup.program) then
    FinDist.pure state
  else
    (FinDist.pi fun who => profile who (setup.protocolObserve who state)).bind fun choices =>
      setup.protocolStep state (fun who => (choices who).1)

/-- Forgetting history commutes with ordinary iteration of the actual source
step law. The history runner remains the defining execution semantics. -/
theorem runBehavioralFrom_state
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (fuel : Nat) (history : (setup.executionProtocol admission).History) :
    ((setup.informationModel admission).runBehavioralFrom profile fuel history).map History.state =
      (fun law => law.bind (setup.behavioralStateStep admission profile))^[fuel]
        (FinDist.pure history.state) := by
  apply ExecutionProtocol.runRandomizedFor_map_state
  · intro state stopped
    exact ite_eq_left stopped
  · intro current running
    change ((setup.informationModel admission).behavioralJoint profile current.trace running).bind
      ((setup.executionProtocol admission).step current.state) = _
    rw [InformationModel.behavioralJoint, FinDist.bind_map]
    unfold behavioralStateStep
    have active : ¬ current.state.elim False
        (SourceProgram.ProtocolState.terminal setup.program) := running
    rw [ite_eq_right active]
    change (FinDist.pi fun who => profile who
      ((setup.informationModel admission).infoOf who current.trace)).bind
        (fun choices => setup.protocolStep current.state (fun who => (choices who).1)) = _
    have observed (who : Player) : (setup.informationModel admission).infoOf who current.trace =
        setup.protocolObserve who current.state := setup.protocol_info admission who current.trace
    have infos : (fun who => (setup.informationModel admission).infoOf who current.trace) =
        (fun who => setup.protocolObserve who current.state) := funext observed
    exact congrArg (fun infos =>
      (FinDist.pi fun who => profile who (infos who)).bind fun choices =>
        setup.protocolStep current.state (fun who => (choices who).1)) infos

theorem runBehavioralFrom_readout
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (fuel : Nat) (history : (setup.executionProtocol admission).History)
    (enough : setup.protocolRemaining history.state ≤ fuel) :
    ((setup.informationModel admission).runBehavioralFrom profile fuel history).map
        (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw (setup.decodeBehavioralProfile admission profile) history.state).map
        some := by
  have permitted (who : Player) :
      (setup.decodeBehavioralProfile admission profile who).Admitted setup.program admission :=
    ((setup.behavioralPolicyEquiv admission who).symm (profile who)).2
  have same : (fun who => setup.toProtocolBehavioralPolicy admission who
      (setup.decodeBehavioralProfile admission profile who) (permitted who)) = profile :=
    funext fun who => (setup.behavioralPolicyEquiv admission who).apply_symm_apply (profile who)
  have law := setup.protocol_runBehavioralFrom_eq admission
    (setup.decodeBehavioralProfile admission profile) permitted fuel history enough
  rw [(setup.informationModel admission).runSingleMoverBehavioralFrom_eq_runBehavioralFrom,
    same] at law
  exact law

theorem runBehavioralFrom_value
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (utility : State L setup.program.terminalCtx → ℝ)
    (fuel : Nat) (history : (setup.executionProtocol admission).History)
    (enough : setup.protocolRemaining history.state ≤ fuel) :
    ((setup.informationModel admission).runBehavioralFrom profile fuel history).expect
        (fun final => (setup.protocolReadout final.state).elim 0 utility) =
      (setup.continuationLaw (setup.decodeBehavioralProfile admission profile)
        history.state).expect utility := by
  have law := congrArg (fun distribution => distribution.expect (fun state => state.elim 0 utility))
    (setup.runBehavioralFrom_readout admission profile fuel history enough)
  simpa only [FinDist.expect_map, Option.elim_some] using law

/-- The original assessment and its whole-policy deviations are retained.
Only the belief is pushed to the actual source state for evaluating utility. -/
theorem continuationContext_value_stateBelief
    (assessment : (setup.informationModel admission).BehavioralAssessment)
    (who : Player) (site : (setup.informationModel admission).InformationSite who)
    (alternative : (setup.informationModel admission).BehavioralPolicy who)
    (utility : State L setup.program.terminalCtx → ℝ) (fuel : Nat)
    (enough : ∀ history : (setup.informationModel admission).InformationHistory who site.1,
      setup.protocolRemaining history.1.state ≤ fuel) :
    (assessment.continuationContext site
      (fun final => (setup.protocolReadout final.state).elim 0 utility) fuel).value alternative =
      (assessment.stateBelief who site).expect (fun state =>
        (setup.continuationLaw (setup.decodeBehavioralProfile admission
          (Profile.update (sig := (setup.informationModel admission).behavioralSignature)
            assessment.strategy who alternative)) state).expect utility) := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value,
    FinDist.expect_bind, InformationModel.BehavioralAssessment.stateBelief, FinDist.expect_map]
  apply FinDist.expect_congr
  intro history _supported
  exact setup.runBehavioralFrom_value admission _ utility fuel history.1 (enough history)

end Vegas.SourceProgram.Setup
