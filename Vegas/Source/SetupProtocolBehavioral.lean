/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolEvaluation
import Vegas.Source.ProtocolBehavioralEvaluation

/-! # Behavioral play with private setup

The setup draw is a chance step. Policies use the same observation-local
source decisions across every draw, and continuations retain the drawn types.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def toProtocolBehavioralPolicy (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (policy : BehavioralPolicy who setup.program)
    (permitted : policy.Admitted setup.program admission) :
    (setup.informationModel admission).BehavioralPolicy who
  | none => FinDist.pure ⟨none, rfl⟩
  | some view => policy.toProtocol setup.program admission permitted view

theorem toProtocolBehavioralPolicy_map_val (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player)
    (policy : BehavioralPolicy who setup.program)
    (permitted : policy.Admitted setup.program admission) (view : setup.ProtocolView who) :
    (setup.toProtocolBehavioralPolicy admission who policy permitted view).map Subtype.val =
      view.elim (FinDist.pure none) (policy.protocolAction setup.program) := by
  cases view with
  | none => exact FinDist.map_pure _ _
  | some view =>
      exact BehavioralPolicy.toProtocol_map_val setup.program admission policy permitted _

/-- The inverse translates an arbitrary legal behavioral deviation to one
whole source policy, uniformly over private setup draws. -/
def behavioralPolicyEquiv (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (who : Player) :
    {policy : BehavioralPolicy who setup.program // policy.Admitted setup.program admission} ≃
      (setup.informationModel admission).BehavioralPolicy who where
  toFun policy := setup.toProtocolBehavioralPolicy admission who policy.1 policy.2
  invFun policy :=
    ⟨BehavioralPolicy.fromProtocol setup.program admission (fun view => policy (some view)),
      BehavioralPolicy.admitted_fromProtocol setup.program admission
        (fun view => policy (some view))⟩
  left_inv policy :=
    Subtype.ext (BehavioralPolicy.from_toProtocol setup.program admission policy.1 policy.2)
  right_inv policy := by
    funext view
    apply FinDist.map_injective Subtype.val_injective
    cases view with
    | none =>
        dsimp only [toProtocolBehavioralPolicy]
        rw [FinDist.map_pure]
        symm
        calc
          _ = (policy none).map (fun _ => none) :=
            FinDist.map_congr_of_eq_on_support (fun choice _ => choice.2)
          _ = _ := by simp [FinDist.map_eq_bind]
    | some view =>
        dsimp only [toProtocolBehavioralPolicy]
        rw [BehavioralPolicy.toProtocol_map_val, BehavioralPolicy.protocolAction_fromProtocol]
        rfl

theorem continuationLaw_behavioral_step (setup : Setup (Player := Player) (L := L))
    (profile : BehavioralProfile setup.program) (state : setup.ProtocolState)
    (running : ¬ state.elim False (SourceProgram.ProtocolState.terminal setup.program))
    (joint : FinDist (Player → Option (OwnAction Player L)))
    (marginal : ∀ who, joint.map (fun actions => actions who) =
      (setup.protocolObserve who state).elim (FinDist.pure none)
        ((profile who).protocolAction setup.program)) :
    (joint.bind (setup.protocolStep state)).bind (setup.continuationLaw profile) =
      setup.continuationLaw profile state := by
  cases state with
  | none =>
      simp [protocolStep, continuationLaw, FinDist.bind_const, FinDist.bind_map,
        run, initialConfig, SourceProgram.run, SourceProgram.runFrom]
  | some state =>
      simpa only [protocolStep, continuationLaw, FinDist.bind_bind, FinDist.bind_map] using
        SourceProgram.ProtocolState.continuationLaw_behavioral_step setup.program profile state
          running joint marginal

theorem protocol_runBehavioralFrom_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) (fuel : Nat)
    (history : (setup.executionProtocol admission).History)
    (enough : setup.protocolRemaining history.state ≤ fuel) :
    ((setup.informationModel admission).runSingleMoverBehavioralFrom
      (setup.protocol_singleMover admission)
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
      fuel history).map (fun final => setup.protocolReadout final.state) =
      (setup.continuationLaw profile history.state).map some := by
  unfold InformationModel.runSingleMoverBehavioralFrom
  refine runRandomizedFor_readout_eq (E := setup.executionProtocol admission)
    _ setup.protocolRemaining ?_ ?_ setup.protocolReadout
    (fun state => (setup.continuationLaw profile state).map some) ?_ ?_ fuel history enough
  · intro state zero
    cases state with
    | none => simp [protocolRemaining] at zero
    | some state =>
        exact (SourceProgram.ProtocolState.remaining_zero_iff_terminal setup.program state).mp zero
  · intro before joint after reached
    have consumed := setup.protocol_remaining_step before.state after joint.1 joint.2.1 reached
    omega
  · exact fun state stopped => setup.continuationLaw_terminal profile state stopped
  · intro before running
    let law := (setup.informationModel admission).singleMoverJoint
      (setup.protocol_singleMover admission)
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
      before running
    have marginal (who : Player) :
        (law.map Subtype.val).map (fun actions => actions who) =
          (setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who)
            (setup.protocolObserve who before.state)).map Subtype.val := by
      rw [FinDist.map_comp]
      change law.map (fun actions => actions.1 who) = _
      rw [InformationModel.singleMoverJoint_marginal]
      change (setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who)
        ((setup.protocolSignals admission).infoOf who before.trace)).map Subtype.val = _
      rw [protocol_info]
    have stepLaw := congrArg (fun result => result.map some)
      (setup.continuationLaw_behavioral_step profile before.state running (law.map Subtype.val)
        (fun who => (marginal who).trans (setup.toProtocolBehavioralPolicy_map_val
          admission who (profile who) (permitted who) _)))
    change law.bind (fun joint => (setup.protocolStep before.state joint.1).bind
      (fun state => (setup.continuationLaw profile state).map some)) = _
    simpa only [FinDist.map_bind, FinDist.bind_bind, FinDist.bind_map] using stepLaw

theorem protocol_runBehavioral_eq (setup : Setup (Player := Player) (L := L))
    (admission : CommitmentInterface setup.program) (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission) :
    ((setup.informationModel admission).runSingleMoverBehavioralFrom
      (setup.protocol_singleMover admission)
      (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
      (instructionCount setup.program + 1) (setup.executionProtocol admission).initHistory).map
        (fun final => setup.protocolReadout final.state) = (setup.run profile).map some := by
  exact setup.protocol_runBehavioralFrom_eq admission profile permitted _ _ (Nat.le_refl _)

end Vegas.SourceProgram.Setup
