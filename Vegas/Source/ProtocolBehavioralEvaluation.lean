/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolBehavioralPolicy
import Vegas.Source.ProtocolEvaluation
import GameTheoryExtensions.Protocol.SingleMover
import GameTheoryExtensions.Protocol.ContinuationLaw

/-! # Behavioral continuation laws

Only the current owner's action affects a source step. Consequently, matching
the player's action marginal suffices for the step law. The proof then uses
the canonical randomized history runner at every legal prefix.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- A joint law with the prescribed local marginals gives the existing source
continuation law. No finiteness assumption on the player universe is needed. -/
theorem continuationLaw_behavioral_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    (state : ProtocolState program) → ¬ terminal program state →
    (joint : FinDist (Player → Option (OwnAction Player L))) →
    (∀ who, joint.map (fun actions => actions who) =
      (profile who).protocolAction program (observe who program state)) →
    (joint.bind (step program state)).bind (continuationLaw program profile) =
      continuationLaw program profile state
  | _, _, .ret _, _, _, running, _, _ => (running trivial).elim
  | _, _, .sample _ _ _ next, profile, state, running, joint, marginal => by
      cases state with
      | inl config =>
          simp [step, continuationLaw, FinDist.bind_const, FinDist.bind_map, runFrom_sample]
          rfl
      | inr rest =>
          simpa only [step, continuationLaw, Sum.elim_inr, FinDist.bind_bind,
            FinDist.bind_map] using
            continuationLaw_behavioral_step next profile rest running joint marginal
  | _, _, .commit (payload := payload) name owner fresh guard next,
      profile, state, running, joint, marginal => by
      cases state with
      | inl config =>
          have law := congrArg (fun law => law.bind (fun action =>
            runFrom next (fun who => (profile who).2)
              (commitSuccessor name guard config (OwnAction.binding owner name payload action))))
            (marginal owner)
          simp only [FinDist.bind_map, BehavioralPolicy.protocolAction, observe,
            Sum.elim_inl, Sum.elim_inr, dite_true, OwnAction.binding_commit, step,
            FinDist.bind_bind, FinDist.pure_bind, continuationLaw, continuationLaw_entry,
            runFrom_commit, commitKernel, Config.view] at law ⊢
          convert law using 1
          rfl
      | inr rest =>
          simpa only [step, continuationLaw, Sum.elim_inr, FinDist.bind_bind,
            FinDist.bind_map] using
            continuationLaw_behavioral_step next (fun who => (profile who).2)
              rest running joint marginal
  | _, _, .reveal published owner name fresh source unresolved next,
      profile, state, running, joint, marginal => by
      cases state with
      | inl config =>
          have law := congrArg (fun law => law.bind (fun action =>
            runFrom next (fun who => (profile who).2)
              (revealSuccessor published source config (OwnAction.disclosure action))))
            (marginal owner)
          simp only [FinDist.bind_map, BehavioralPolicy.protocolAction, observe,
            Sum.elim_inl, Sum.elim_inr, dite_true, OwnAction.disclosure, step,
            FinDist.bind_bind, FinDist.pure_bind, continuationLaw, continuationLaw_entry,
            runFrom_reveal, revealKernel, Config.view] at law ⊢
          convert law using 1
          rfl
      | inr rest =>
          simpa only [step, continuationLaw, Sum.elim_inr, FinDist.bind_bind,
            FinDist.bind_map] using
            continuationLaw_behavioral_step next (fun who => (profile who).2)
              rest running joint marginal

end ProtocolState

/-- Behavioral play agrees with the source continuation at every legal history,
including histories that the supplied profile would never reach. -/
theorem protocol_runBehavioralFrom_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : BehavioralProfile program)
    (permitted : ∀ who, (profile who).Admitted program admission) (fuel : Nat)
    (history : (executionProtocol program admission initial).History)
    (enough : ProtocolState.remaining program history.state ≤ fuel) :
    ((informationModel program admission initial).runSingleMoverBehavioralFrom
      (protocol_singleMover program admission initial)
      (fun who => (profile who).toProtocol program admission (permitted who)) fuel history).map
        (fun final => ProtocolState.readout program final.state) =
      (ProtocolState.continuationLaw program profile history.state).map some := by
  unfold InformationModel.runSingleMoverBehavioralFrom
  refine runRandomizedFor_readout_eq
    (E := executionProtocol program admission initial) _ (ProtocolState.remaining program)
    ?_ ?_ (ProtocolState.readout program)
    (fun state => (ProtocolState.continuationLaw program profile state).map some)
    ?_ ?_ fuel history enough
  · intro state zero
    exact (ProtocolState.remaining_zero_iff_terminal program state).mp zero
  · intro before joint after reached
    have consumed := ProtocolState.remaining_step program before.state after joint.1 joint.2.1
      reached
    omega
  · exact fun state stopped =>
      ProtocolState.continuationLaw_terminal program profile state stopped
  · intro before running
    let law := (informationModel program admission initial).singleMoverJoint
      (protocol_singleMover program admission initial)
      (fun who => (profile who).toProtocol program admission (permitted who)) before running
    have marginal (who : Player) :
        (law.map Subtype.val).map (fun actions => actions who) =
          (profile who).protocolAction program
            (ProtocolState.observe who program before.state) := by
      rw [FinDist.map_comp]
      change (law.map (fun actions => actions.1 who)) = _
      rw [InformationModel.singleMoverJoint_marginal]
      change ((profile who).toProtocol program admission (permitted who)
        ((protocolSignals program admission initial).infoOf who before.trace)).map Subtype.val = _
      rw [protocol_info, BehavioralPolicy.toProtocol_map_val]
    have stepLaw := congrArg (fun result => result.map some)
      (ProtocolState.continuationLaw_behavioral_step program profile before.state running
        (law.map Subtype.val) marginal)
    change law.bind (fun joint => (ProtocolState.step program before.state joint.1).bind
      (fun state => (ProtocolState.continuationLaw program profile state).map some)) = _
    simpa only [FinDist.map_bind, FinDist.bind_bind, FinDist.bind_map] using stepLaw

theorem protocol_runBehavioral_eq {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (profile : BehavioralProfile program)
    (permitted : ∀ who, (profile who).Admitted program admission) :
    ((informationModel program admission initial).runSingleMoverBehavioralFrom
      (protocol_singleMover program admission initial)
      (fun who => (profile who).toProtocol program admission (permitted who))
      (instructionCount program) (executionProtocol program admission initial).initHistory).map
        (fun final => ProtocolState.readout program final.state) =
      (runFrom program profile initial).map some := by
  rw [protocol_runBehavioralFrom_eq program admission initial profile permitted
    (instructionCount program) _ (by simp [executionProtocol, ExecutionProtocol.initHistory])]
  exact congrArg (fun law => law.map some)
    (ProtocolState.continuationLaw_entry program profile initial)

end Vegas.SourceProgram
