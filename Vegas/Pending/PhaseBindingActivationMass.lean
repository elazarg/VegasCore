/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveEnvironmentMass
import Vegas.Pending.PhaseBindingRepairObservationStep

/-! # Actual activation transition atoms under directed physical repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired next image : (phaseApplication runtime leaks).Execution}

local notation "app" => phaseApplication runtime leaks

/-- Actual activation atoms agree at paired physical endpoints, including
possible aliases among pending-message observation draws. -/
theorem activation_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner next image) (active : Player)
    (leftMoved : next ∈ (original.environmentStep (app) (.activate active)).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) (.activate active)).support) :
    (original.environmentStep (app) (.activate active)) next =
      (repaired.environmentStep (app) (.activate active)) image := by
  rw [(app).environmentStep_activate_apply original next active leftMoved,
    (app).environmentStep_activate_apply repaired image active rightMoved, frame.network,
    afterFrame.network]

/-- The real protocol activation atom retains exactly the same scheduler
factor and conditional physical network mass on both repaired prefixes. -/
theorem activation_transition_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner next image)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (active : Player)
    (leftMoved : next ∈ (original.environmentStep (app) (.activate active)).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) (.activate active)).support)
    (firstJoint secondJoint : Player → Option (app).Action) :
    ((app).transition initial horizon scheduler (some ⟨remaining + 1, none, original⟩) firstJoint)
        (some ⟨remaining, some active, next⟩) =
      ((app).transition initial horizon scheduler
        (some ⟨remaining + 1, none, repaired⟩) secondJoint)
        (some ⟨remaining, some active, image⟩) := by
  have firstMass := (app).transition_environment_apply initial horizon scheduler remaining original
    next (.activate active) leftMoved firstJoint
  have secondMass := (app).transition_environment_apply initial horizon scheduler remaining repaired
    image (.activate active) rightMoved secondJoint
  simp only [ReactiveApplication.Command.actor?] at firstMass secondMass
  rw [firstMass, secondMass, frame.scheduler_law scheduler,
    frame.activation_apply afterFrame active leftMoved rightMoved]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
