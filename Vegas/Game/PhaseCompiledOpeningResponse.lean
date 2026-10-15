/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicyLaw
import Vegas.Pending.PhaseNativePlayerInput
import Vegas.Pending.ReactiveDisclosure

/-! # Physical disclosure laws under clear phase-address erasure -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Any disclosing action kernel materializes the same authentic packet as the
canonical phase dispatcher when the current guarded publication succeeds. -/
theorem phaseSourcePolicy_opening_erasure_of_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall who), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (timely : control.execution.application.current.native.WithinDeadline runtime event)
    (resolved : EventCode.resolveOutput? binding checks true
      control.execution.application.current.native.config.store = some (.success value))
    (law : PMF ((serviceGraph setup mode).Action event))
    (discloses : ∀ action ∈ law.support,
      cast (congrArg EventField.Action outputEq) action = true) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      law.map (fun action => runtime.reactiveDecision
        (PhaseNativeProjection.nativeLeaks leaks plan) who event action
        (control.execution.application.current.native.playerView who)) := by
  classical
  obtain ⟨candidate, accepted, actualLaw⟩ := phaseSourcePolicy_opening_of_history setup mode
    runtime leaks bounds wellFormed assessment plan inputs horizon scheduler trace who event
      payload binding checks outputEq codeEq node request unsent value stored values timely
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon scheduler trace
  have valid := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  rw [actualLaw, PMF.pure_map]
  symm
  calc
    _ = law.map (fun _ => PhaseNativeProjection.action runtime leaks plan
        (PhaseCount.phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩)) := by
      apply map_congr_on_support
      intro action positive
      obtain ⟨other, associated, _owned, _verified, packet⟩ :=
        reactiveResolutionPacket_provenance runtime (PhaseNativeProjection.nativeLeaks leaks plan)
          control.execution.application.current.native valid who event payload binding checks
            outputEq action (discloses action positive) value resolved
      have same : other = candidate := Option.some.inj (associated.symm.trans accepted)
      subst other
      unfold EventGraphRuntime.reactiveDecision
      rw [node]
      dsimp only
      change (⟨_⟩ : (runtime.reactiveApplication
        (PhaseNativeProjection.nativeLeaks leaks plan)).Action) = ⟨_⟩
      have normal := reactiveResolutionSubmission_normal runtime
        (PhaseNativeProjection.nativeLeaks leaks plan) _ valid who event payload binding checks
          outputEq action
      dsimp only [reactiveApplication] at normal packet
      rw [normal, packet]
      rfl
    _ = _ := PMF.map_const _ _

end Vegas
