/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingActivationMass
import Vegas.Pending.PhaseBindingSampleMass
import Vegas.Pending.PhaseBindingApplicationReplay

/-! # Every real environment transition atom under directed repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired after image : (phaseApplication runtime leaks).Execution}

local notation "app" => phaseApplication runtime leaks

private theorem application_pure_of_native_pure (physical : (app).Execution)
    (chosen : EnvironmentCommand graph) (native : State graph)
    (nativePure : environmentStep runtime physical.application.current.native chosen =
      PMF.pure native) :
    ∃ next, physical.environmentStep (app) (.application chosen) = PMF.pure next := by
  unfold ReactiveApplication.Execution.environmentStep
  change ∃ next, ((physical.application.environment runtime chosen).map _).map _ = PMF.pure next
  unfold PhaseRuntimeState.environment
  split
  · rw [nativePure, PMF.pure_map, PMF.pure_map, PMF.pure_map]
    exact ⟨_, rfl⟩
  · rw [PMF.pure_map, PMF.pure_map]
    exact ⟨_, rfl⟩

private theorem application_pure_of_disallowed (physical : (app).Execution)
    (chosen : EnvironmentCommand graph)
    (denied : physical.application.commandAllowed chosen = false) :
    ∃ next, physical.environmentStep (app) (.application chosen) = PMF.pure next := by
  simp only [ReactiveApplication.Execution.environmentStep]
  change ∃ next, ((physical.application.environment runtime chosen).map _).map _ = PMF.pure next
  rw [PhaseRuntimeState.environment, denied]
  simp only [Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
  exact ⟨_, rfl⟩

private theorem atom_eq_one_of_pure {α : Type} (law : PMF α) (value : α)
    (supported : value ∈ law.support) (pure : ∃ next, law = PMF.pure next) : law value = 1 := by
  obtain ⟨next, rfl⟩ := pure
  cases (PMF.mem_support_pure_iff _ _).mp supported
  exact PMF.pure_apply_self _

/-- Every application-command atom is derived from actual supported endpoints.
Only a ready admitted public sample is random; its actual public draw is read
back after clear normalization. All other command laws are deterministic. -/
theorem application_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image) (chosen : EnvironmentCommand graph)
    (leftMoved : after ∈ (original.environmentStep (app) (.application chosen)).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) (.application chosen)).support) :
    (original.environmentStep (app) (.application chosen)) after =
      (repaired.environmentStep (app) (.application chosen)) image := by
  have deterministic
      (left : ∃ next, original.environmentStep (app) (.application chosen) = PMF.pure next)
      (right : ∃ next, repaired.environmentStep (app) (.application chosen) = PMF.pure next) :
      (original.environmentStep (app) (.application chosen)) after =
        (repaired.environmentStep (app) (.application chosen)) image := by
    rw [atom_eq_one_of_pure _ _ leftMoved left, atom_eq_one_of_pure _ _ rightMoved right]
  cases chosen with
  | advanceClock =>
      apply deterministic
      · exact application_pure_of_native_pure original _ _ rfl
      · exact application_pure_of_native_pure repaired _ _ rfl
  | expire event =>
      apply deterministic
      · exact application_pure_of_native_pure original _ _ rfl
      · exact application_pure_of_native_pure repaired _ _ rfl
  | executeSample event =>
      by_cases allowed : original.application.commandAllowed (.executeSample event) = true
      · have beforePublic : original.application.current.native.publicView =
            repaired.application.current.native.publicView := frame.live.publicView
        by_cases ready : original.application.current.native.config.cut.Ready event
        · have rightReady : repaired.application.current.native.config.cut.Ready event := by
            rw [← State.publicView_eventReady, ← beforePublic, State.publicView_eventReady]
            exact ready
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              exact frame.sample_apply afterFrame event ready payload law outputEq codeEq node
                allowed leftMoved rightMoved
          | bind actor payload outputEq codeEq =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro _ _ _ _ impossible
                rw [node] at impossible
                cases impossible
              apply deterministic
              · exact application_pure_of_native_pure original _ _
                  (environmentStep_executeSample_of_nonsample runtime _ event ready nonsample)
              · exact application_pure_of_native_pure repaired _ _
                  (environmentStep_executeSample_of_nonsample runtime _ event rightReady nonsample)
          | resolve actor payload binding checks outputEq codeEq =>
              have nonsample : ∀ payload law outputEq codeEq,
                  nodeView graph event ≠ .sample payload law outputEq codeEq := by
                intro _ _ _ _ impossible
                rw [node] at impossible
                cases impossible
              apply deterministic
              · exact application_pure_of_native_pure original _ _
                  (environmentStep_executeSample_of_nonsample runtime _ event ready nonsample)
              · exact application_pure_of_native_pure repaired _ _
                  (environmentStep_executeSample_of_nonsample runtime _ event rightReady nonsample)
        · have rightReady : ¬repaired.application.current.native.config.cut.Ready event := by
            rw [← State.publicView_eventReady, ← beforePublic, State.publicView_eventReady]
            exact ready
          apply deterministic
          · exact application_pure_of_native_pure original _ _
              (environmentStep_executeSample_of_not_ready runtime _ event ready)
          · exact application_pure_of_native_pure repaired _ _
              (environmentStep_executeSample_of_not_ready runtime _ event rightReady)
      · have denied := Bool.eq_false_iff.mpr allowed
        have rightDenied : repaired.application.commandAllowed (.executeSample event) = false :=
          (frame.command_admission _).symm.trans denied
        exact deterministic (application_pure_of_disallowed original _ denied)
          (application_pure_of_disallowed repaired _ rightDenied)

/-- Real conditional environment masses agree under the physical frame at both
actual endpoints, for every command, not merely the chosen replay support. -/
theorem environment_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image) (chosen : (app).Command)
    (leftMoved : after ∈ (original.environmentStep (app) chosen).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) chosen).support) :
    (original.environmentStep (app) chosen) after =
      (repaired.environmentStep (app) chosen) image := by
  cases chosen with
  | activate active => exact frame.activation_apply afterFrame active leftMoved rightMoved
  | application chosen => exact frame.application_apply afterFrame chosen leftMoved rightMoved
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep,
        PMF.pure_map] at leftMoved rightMoved ⊢
      cases (PMF.mem_support_pure_iff _ _).mp leftMoved
      cases (PMF.mem_support_pure_iff _ _).mp rightMoved
      rw [PMF.pure_apply_self, PMF.pure_apply_self]
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep,
        PMF.pure_map] at leftMoved rightMoved ⊢
      cases (PMF.mem_support_pure_iff _ _).mp leftMoved
      cases (PMF.mem_support_pure_iff _ _).mp rightMoved
      rw [PMF.pure_apply_self, PMF.pure_apply_self]

/-- Full scheduler transition atoms are equal on actual directed paired
command outcomes. The command is isolated by its real appended environment
record; no transition mass equality is assumed. -/
theorem environment_transition_apply (frame : Frame runtime leaks memory owner original repaired)
    (afterFrame : Frame runtime leaks memory owner after image)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (chosen : (app).Command)
    (leftMoved : after ∈ (original.environmentStep (app) chosen).support)
    (rightMoved : image ∈ (repaired.environmentStep (app) chosen).support)
    (firstJoint secondJoint : Player → Option (app).Action) :
    ((app).transition initial horizon scheduler (some ⟨remaining + 1, none, original⟩) firstJoint)
        (some ⟨remaining, chosen.actor? (app), after⟩) =
      ((app).transition initial horizon scheduler
        (some ⟨remaining + 1, none, repaired⟩) secondJoint)
        (some ⟨remaining, chosen.actor? (app), image⟩) := by
  rw [(app).transition_environment_apply initial horizon scheduler remaining original after chosen
    leftMoved firstJoint,
    (app).transition_environment_apply initial horizon scheduler remaining repaired image chosen
      rightMoved secondJoint, frame.scheduler_law scheduler,
    frame.environment_apply afterFrame chosen leftMoved rightMoved]

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
