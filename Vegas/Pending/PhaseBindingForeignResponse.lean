/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCheckpointSubmission

/-! # Arbitrary counted foreign responses during phased private repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- An unchanged foreign action is legal at the actual repaired full input;
both private application frontiers and all physical recall remain paired. -/
theorem foreign_response (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (actor : Player) (foreign : actor ≠ owner)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (original.recall actor) (original.observe (phaseApplication runtime leaks) actor)) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds actor (repaired.recall actor)
        (repaired.observe (phaseApplication runtime leaks) actor) ∧
      Frame runtime leaks memory owner
        (original.respond (phaseApplication runtime leaks) actor response)
        (repaired.respond (phaseApplication runtime leaks) actor response) := by
  let app := phaseApplication runtime leaks
  let nativeApp := runtime.reactiveApplication (nativeLeaks (graph := graph))
  have sameInput := frame.foreign_input actor foreign
  have samePast : original.recall actor = repaired.recall actor := congrArg Prod.fst sameInput
  have sameView : original.observe app actor = repaired.observe app actor :=
    congrArg Prod.snd sameInput
  have legal : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (repaired.recall actor) (repaired.observe app actor) := by
    rw [← samePast, ← sameView]
    exact member
  refine ⟨legal, ?_⟩
  have live : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (execution runtime leaks (original.respond app actor response))
      (execution runtime leaks (repaired.respond app actor response)) := by
    rw [execution_respond_of_onePacket runtime leaks bounds original actor response member,
      execution_respond_of_onePacket runtime leaks bounds repaired actor response legal]
    exact frame.live.foreign_response actor foreign (action runtime leaks response)
  have oldSaved := frame.saved.foreign_response actor foreign (action runtime leaks response)
  have saved : BindingMemory.Frame runtime (nativeLeaks (graph := graph)) memory owner
      (checkpoint runtime leaks (original.respond app actor response))
      (checkpoint runtime leaks (repaired.respond app actor response)) := by
    apply checkpointFrame live
      (checkpoint runtime leaks (original.respond app actor response)).application
      (checkpoint runtime leaks (repaired.respond app actor response)).application
    · rw [checkpoint_response_application, checkpoint_response_application]
      exact congrArg ReactiveApplication.PlayerView.application oldSaved.observed
    · rw [checkpoint_response_application, checkpoint_response_application]
      exact oldSaved.views
    · rw [checkpoint_response_application, checkpoint_response_application]
      exact oldSaved.slots
    · rw [checkpoint_response_application, checkpoint_response_application]
      exact oldSaved.successful
  have physics : (original.respond app actor response).network =
      (repaired.respond app actor response).network ∧
      ∀ who, who ≠ owner → (original.respond app actor response).recall who =
        (repaired.respond app actor response).recall who := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        refine ⟨frame.network, ?_⟩
        intro who different
        by_cases active : who = actor
        · subst who
          simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
          change original.recall actor ++ [⟨original.observe app actor, ⟨none⟩, none⟩] =
            repaired.recall actor ++ [⟨repaired.observe app actor, ⟨none⟩, none⟩]
          rw [samePast, sameView]
        · rw [app.respond_recall_other original actor who active,
            app.respond_recall_other repaired actor who active]
          exact frame.foreignRecall who different
    | some material =>
        have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks original
          left.1 left.2.1 actor material
        have envelopeRight := PhaseCount.localEnvelope_eq_of_recall runtime leaks repaired
          right.1 right.2.1 actor material
        have localEq : PhaseCount.localEnvelope runtime leaks actor (original.recall actor)
            (original.observe app actor) material =
            PhaseCount.localEnvelope runtime leaks actor (repaired.recall actor)
              (repaired.observe app actor) material := by rw [samePast, sameView]
        have messages := envelope.symm.trans (localEq.trans envelopeRight)
        have packets : app.packet (app.submit original.application actor material) actor
            (original.network.known actor) material =
            app.packet (app.submit repaired.application actor material) actor
              (repaired.network.known actor) material := congrArg Message.payload messages
        have sent : (original.network.submit actor
            (app.packet (app.submit original.application actor material) actor
              (original.network.known actor) material)).1 =
            (repaired.network.submit actor
              (app.packet (app.submit repaired.application actor material) actor
                (repaired.network.known actor) material)).1 := messages
        refine ⟨?_, ?_⟩
        · change (original.network.submit actor _).2 = (repaired.network.submit actor _).2
          exact congrArg₂ (fun pool packet => (pool.submit actor packet).2) frame.network packets
        · intro who different
          by_cases active : who = actor
          · subst who
            simp only [ReactiveApplication.Execution.respond, ↓reduceIte]
            change original.recall actor ++
                [⟨original.observe app actor, ⟨some material⟩, some _⟩] =
              repaired.recall actor ++
                [⟨repaired.observe app actor, ⟨some material⟩, some _⟩]
            rw [samePast, sameView, sent]
          · rw [app.respond_recall_other original actor who active,
              app.respond_recall_other repaired actor who active]
            exact frame.foreignRecall who different
  refine ⟨live, saved, ?_, ?_, ?_, ?_, ?_, ?_, physics.1, ?_, physics.2⟩
  all_goals
    rcases response with ⟨transmission⟩
    cases transmission <;> first
      | exact frame.phases
      | exact frame.generation
      | exact frame.clearOriginal
      | exact frame.clearRepaired
      | exact frame.archiveOriginal
      | exact frame.archiveRepaired
      | exact frame.service

/-- A foreign callback extends the actual repaired one-packet history. Both
recall premises are extracted from the two genuine prefixes. -/
theorem foreign_response_trace (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (remaining : Nat) (actor : Player) (foreign : actor ≠ owner)
    (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, original⟩))
    (right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some actor, repaired⟩))
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ PhaseCount.onePacketActions runtime leaks bounds actor
      (original.recall actor) (original.observe (phaseApplication runtime leaks) actor)) :
    Nonempty (((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, none,
          repaired.respond (phaseApplication runtime leaks) actor response⟩)) ∧
      Frame runtime leaks memory owner
        (original.respond (phaseApplication runtime leaks) actor response)
        (repaired.respond (phaseApplication runtime leaks) actor response) := by
  have paired := frame.foreign_response bounds
    (PhaseCount.countRecall_history runtime leaks
      ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ left))
    (PhaseCount.countRecall_history runtime leaks
      ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ right))
    actor foreign response member
  exact ⟨(PhaseCount.onePacketMenu runtime leaks bounds).trace_respond
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler remaining repaired actor
      response right paired.1, paired.2⟩

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
