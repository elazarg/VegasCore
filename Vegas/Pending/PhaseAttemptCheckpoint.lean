/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseResolution
import Interaction.ReactiveResponseMenu
import Interaction.ReactiveServiceInvariant
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Saved checkpoints and authored packets inside one actual attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Retaining the physical namespace retains the very same saved checkpoint. -/
theorem phaseApplication_sameAttempt_entry :
    (app).StepRelation (fun before after => before.Ordered → before.attempt = after.attempt →
      after.entry = before.entry) where
  refl _ _ _ := rfl
  submit _ _ _ _ _ := rfl
  handle state message next accepted ordered same := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      have settled := PhaseRuntimeState.settle_of_same_namespace state.phases state.generation
        state.entry (state.current.inclusionResult message.payload.packet.call native)
          state.retired ordered same
      have saved := congrArg PhaseRuntimeState.entry settled
      exact saved
    · cases accepted
  environment state command next reached ordered same := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      have settled := PhaseRuntimeState.settle_of_same_namespace state.phases state.generation
        state.entry (state.current.environmentResult command native) state.retired ordered same
      have saved := congrArg PhaseRuntimeState.entry settled
      exact saved
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl

/-- Monotone namespaces rule out a restore at an intermediate actual prefix. -/
theorem phase_entry_of_same_attempt_prefix
    (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (before after : (app).Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (trace : (menu.protocol initial horizon scheduler).Trace (some after))
    (retained : TracePrefix prior trace) (ordered : before.execution.application.Ordered)
    (same : before.execution.application.attempt = after.execution.application.attempt) :
    before.execution.application.entry = after.execution.application.entry := by
  have along : ∀ {target} {targetTrace : (menu.protocol initial horizon scheduler).Trace target},
      TracePrefix prior targetTrace → ∃ next : (app).Control, target = some next ∧
        next.execution.application.Ordered ∧
        before.execution.application.attempt.generation ≤
          next.execution.application.attempt.generation ∧
        before.execution.application.attempt.phase ≤ next.execution.application.attempt.phase ∧
        (before.execution.application.attempt = next.execution.application.attempt →
          next.execution.application.entry = before.execution.application.entry) := by
    intro target targetTrace kept
    induction kept with
    | refl => exact ⟨before, rfl, ordered, le_rfl, le_rfl, fun _ => rfl⟩
    | @extend source target earlier kept joint legal reached ih =>
        obtain ⟨middle, rfl, middleOrdered, lowerGen, lowerPhase, previous⟩ := ih
        have realized : target ∈ ((app).transition initial horizon scheduler (some middle)
            joint).support := reached
        obtain ⟨next, rfl, _⟩ := (app).transition_recall_prefix initial horizon scheduler
          middle target joint realized
        have nextOrdered := (phaseApplication_seedOrder runtime leaks).transition initial
          horizon scheduler initialized (some middle) (some next) joint middleOrdered realized
        have progress := (phaseApplication_namespace_progress runtime leaks).transition initial
          horizon scheduler middle next joint realized middleOrdered
        refine ⟨next, rfl, nextOrdered, lowerGen.trans progress.1,
          lowerPhase.trans progress.2, ?_⟩
        intro finalSame
        have intermediate : before.execution.application.attempt =
            middle.execution.application.attempt := by
          have generation := congrArg CommitAttemptId.generation finalSame
          have phase := congrArg CommitAttemptId.phase finalSame
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
              cases second : middle.execution.application.attempt with
              | mk secondPhase secondGeneration =>
                  simp only [first, second] at lowerGen lowerPhase progress generation phase ⊢
                  congr 1 <;> omega
        exact ((phaseApplication_sameAttempt_entry runtime leaks).transition initial horizon
          scheduler middle next joint realized middleOrdered
            (intermediate.symm.trans finalSame)).trans (previous intermediate)
  obtain ⟨next, equality, _ordered, _gen, _phase, result⟩ := along retained
  cases Option.some.inj equality
  exact (result same).symm

/-- An actual emitted packet retains the namespace in its original full callback
view. This statement covers arbitrary raw responses and all earlier attempts. -/
theorem phase_recalled_emission_attempt
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    {control : (app).Control} (trace : ((app).protocol initial horizon scheduler).Trace
      (some control)) (who : Player) (entry : (app).PlayerEntry)
    (retained : entry ∈ control.execution.recall who)
    (message : Message Player (CommitAttemptPacket graph))
    (emitted : entry.emitted = some message) :
    message.payload.attempt = entry.beforeView.application.2.attempt := by
  let property := fun execution : (app).Execution => ∀ who, ∀ entry ∈ execution.recall who,
    ∀ message, entry.emitted = some message →
      message.payload.attempt = entry.beforeView.application.2.attempt
  have invariant : (app).ServiceInvariant scheduler property := {
    respond := by
      intro execution actor action valid observer found member packet sent
      simp only [ReactiveApplication.Execution.respond] at member
      split at member
      · rename_i sameOwner
        subst observer
        rcases List.mem_append.mp member with old | new
        · exact valid actor found old packet sent
        · obtain rfl := List.mem_singleton.mp new
          rcases action with ⟨_ | material⟩
          · cases sent
          · cases Option.some.inj sent
            rfl
      · exact valid observer found member packet sent
    environment := by
      intro execution next command valid _chosen reached observer found member packet sent
      rw [(app).environmentStep_recall execution next command reached] at member
      exact valid observer found member packet sent }
  exact invariant.history initial horizon (by
    intro state _ observer found member
    cases member) trace who entry retained message emitted

end Vegas.EventGraphRuntime
