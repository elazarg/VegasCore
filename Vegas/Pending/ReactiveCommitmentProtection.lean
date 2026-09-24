/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveSafety
import Vegas.Pending.ReactiveStateInvariant
import Interaction.MessageNetworkInvariant
import Interaction.ReactiveServiceInvariant

/-! # Fresh binding candidates cannot be consumed by another event

Every owned commitment retained by the wire already has a fixed meaning.
A compiler response chooses a fresh candidate, so an earlier retained packet
cannot mention that candidate as an owned commitment. Later prescribed
responses also allocate fresh candidates. These facts provide cross-event
protection, in addition to the per-event packet uniqueness theorem.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def ReactiveCommitmentsFixed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.network.Satisfies (fun message => ∀ event candidate,
    message.payload.call = .commitment event candidate → candidate.1 = message.sender →
      execution.application.candidates.lookup candidate ≠ .fresh)

theorem reactiveCommitmentsFixed_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution) :
    runtime.ReactiveCommitmentsFixed leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  let updated := execution.respond (runtime.reactiveApplication leaks) who action
  have prior : execution.network.Satisfies (fun message => ∀ event candidate,
      message.payload.call = .commitment event candidate → candidate.1 = message.sender →
        updated.application.candidates.lookup candidate ≠ .fresh) := by
    apply fixed.mono
    intro message retained event candidate addressed owned
    dsimp only [updated]
    rw [runtime.reactive_respond_candidate_fixed leaks execution who action candidate
      (retained event candidate addressed owned)]
    exact retained event candidate addressed owned
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact prior
  | some transmission =>
      cases transmission with
      | replay id => exact prior.replay who id
      | submit material =>
          apply prior.submit who (material.emit _ who (execution.network.known who))
          intro event candidate addressed owned
          change material.call.packet = .commitment event candidate at addressed
          change candidate.1 = who at owned
          change (submitStep (material.call.register execution.application who) who
            material.call.packet).candidates.lookup candidate ≠ .fresh
          rw [addressed]
          obtain ⟨owner, slot⟩ := candidate
          change owner = who at owned
          subst owner
          exact submitStep_commitment_fixed _ who event slot

theorem reactiveCommitmentsFixed_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) : runtime.ReactiveCommitmentsFixed leaks next := by
  have prior : execution.network.Satisfies (fun message => ∀ event candidate,
      message.payload.call = .commitment event candidate → candidate.1 = message.sender →
        next.application.candidates.lookup candidate ≠ .fresh) :=
    fixed.mono (fun message retained event candidate addressed owned => by
    rw [runtime.reactive_environment_candidate_fixed leaks execution next command candidate
      (retained event candidate addressed owned) reached]
    exact retained event candidate addressed owned)
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact prior
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact prior.learn who selected
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      have kept := prior.includePending id
      cases found : execution.network.lookup id <;>
        simpa only [ReactiveCommitmentsFixed, ReactiveApplication.Execution.includePending,
          MessageNetwork.includePending, found] using kept
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact prior

theorem reactiveCommitmentsFixed_service (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (runtime.reactiveApplication leaks).ServiceInvariant scheduler
      (runtime.ReactiveCommitmentsFixed leaks) where
  respond := runtime.reactiveCommitmentsFixed_respond leaks
  environment execution next command valid _ reached :=
    runtime.reactiveCommitmentsFixed_environment leaks execution next command valid reached

/-- Malformed traffic and arbitrary player deviations still fix any candidate
that a packet names under its actual owner. -/
theorem reactiveCommitmentsFixed_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : FinDist (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state} (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      state) :
    ReactiveApplication.serviceInvariant (runtime.ReactiveCommitmentsFixed leaks) state :=
  (runtime.reactiveCommitmentsFixed_service leaks scheduler).history initial horizon
    (fun _ _ => MessageNetwork.Satisfies.empty) trace

theorem reactiveDecision_commitment_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (choice : graph.Action event)
    (view : ReactivePlayerView graph) (material : WitnessedSubmission graph)
    (emits : (runtime.reactiveDecision leaks who event choice view).transmission =
      some (.submit material)) (target : graph.EventId) (candidate : Handle graph)
    (packet : material.call.packet = .commitment target candidate) :
    ∃ serial, candidate = (who, .prepared serial) ∧
      view.candidates (.prepared serial) = .fresh := by
  unfold reactiveDecision at emits
  split at emits
  · cases emits
  · cases allocated : reactiveFreshSlot view with
    | none => simp only [allocated, Option.map_none] at emits; cases emits
    | some serial =>
        simp only [allocated, Option.map_some, Option.some.injEq,
          ReactiveApplication.Transmission.submit.injEq] at emits
        subst material
        have same := Payload.commitment.inj packet
        exact ⟨serial, same.2.symm, reactiveFreshSlot_spec view serial allocated⟩
  · rename_i owner payload binding checks outputEq codeEq nodeEq
    simp only [Option.some.injEq, ReactiveApplication.Transmission.submit.injEq] at emits
    subst material
    change reactiveResolutionPacket who event payload binding outputEq choice view =
      .commitment target candidate at packet
    dsimp only [reactiveResolutionPacket] at packet
    split at packet
    · split at packet
      · split at packet
        · split at packet <;> cases packet
        · cases packet
      · cases packet
      · cases packet
    · cases packet

theorem prescribedReactivePolicy_commitment_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.prescribedReactivePolicy leaks who policy history view).support)
    (material : WitnessedSubmission graph) (sent : action.transmission = some (.submit material))
    (target : graph.EventId) (candidate : Handle graph)
    (packet : material.call.packet = .commitment target candidate) :
    ∃ serial, candidate = (who, .prepared serial) ∧
      view.application.candidates (.prepared serial) = .fresh := by
  rw [prescribedReactivePolicy_apply] at supported
  obtain ⟨intentions, _, produced⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  obtain ⟨⟨response, intention⟩, issued, rfl⟩ := FinDist.support_map .. ▸ produced
  unfold prescribedReactiveResponse at issued
  split at issued
  · cases FinDist.mem_support_pure.mp issued; cases sent
  · rename_i event grant
    split at issued
    · cases FinDist.mem_support_pure.mp issued; cases sent
    · split at issued
      · split at issued
        · split at issued
          · obtain ⟨choice, _, image⟩ := FinDist.support_map .. ▸ issued
            have responseEq := congrArg Prod.fst image
            dsimp only at responseEq
            subst response
            exact runtime.reactiveDecision_commitment_fresh leaks who event choice
              view.application material sent target candidate packet
          · cases FinDist.mem_support_pure.mp issued; cases sent
        · cases FinDist.mem_support_pure.mp issued; cases sent
      · cases FinDist.mem_support_pure.mp issued; cases sent

def CommitmentFor (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (message : Message Player (WitnessedPacket graph)) : Prop :=
  ∀ target, message.sender = who → message.payload.call = .commitment target candidate →
    target = event

structure ReactiveCandidateProtection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop where
  fixed : execution.application.candidates.lookup candidate ≠ .fresh
  packets : execution.network.Satisfies (CommitmentFor who event candidate)
  unused : event ∉ execution.application.config.cut.completed →
    execution.application.HandleUnused candidate

/-- A freshly chosen candidate has no earlier owned packet in the wire. -/
theorem reactiveBinding_protection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (fixed : runtime.ReactiveCommitmentsFixed leaks execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh)
    (unused : execution.application.HandleUnused (who, .prepared serial)) :
    runtime.ReactiveCandidateProtection leaks who event (who, .prepared serial)
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact submitStep_commitment_fixed _ who event (.prepared serial)
  · have prior : execution.network.Satisfies (CommitmentFor who event (who, .prepared serial)) :=
      fixed.mono (fun message retained target authored addressed => by
      exact False.elim (retained target (who, .prepared serial) addressed
        (by simp only [authored]) fresh))
    apply prior.submit who _
    intro target _ addressed
    exact (Payload.commitment.inj addressed).1.symm
  · intro _ field associated
    apply unused field
    have publicEq := congrArg PublicView.accepted
      (runtime.reactive_respond_application leaks execution who
        (runtime.reactiveBinding leaks who event payload result serial)).2
    exact (congrFun publicEq field).symm.trans associated

theorem handle_unused_of_commitmentFor (runtime : EventGraphRuntime graph)
    (before after : State graph) (message : Message Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (owned : candidate.1 = who) (protection : CommitmentFor who event candidate message)
    (unused : before.HandleUnused candidate)
    (accepted : handle runtime before ⟨message.id, message.payload.call⟩ = some after)
    (unfinished : event ∉ after.config.cut.completed) : after.HandleUnused candidate := by
  obtain ⟨id, packet, evidence⟩ := message
  cases packet with
  | malformed raw => simp [handle] at accepted
  | opening target selected raw | withhold target =>
      rw [State.HandleUnused,
        (handle_resolution_tables runtime before after _ (by intros; simp) accepted).1]
      exact unused
  | commitment target selected =>
      obtain ⟨_, tables, author⟩ :=
        handle_commitment_tables runtime before after id target selected accepted
      have distinct : selected ≠ candidate := by
        intro same
        subst selected
        have eventEq := protection target (author.symm.trans owned) rfl
        subst target
        obtain ⟨actual, address, ready, action, supported⟩ :=
          handle_config_mem_step runtime before after ⟨id, .commitment event candidate⟩ accepted
        have sameEvent : actual = event := by simpa only [Payload.event?, Option.some.injEq]
          using address.symm
        subst actual
        apply unfinished
        rw [before.config.step_cut event ready action after.config supported]
        exact Finset.mem_insert_self _ _
      intro field associated
      by_cases targetField : field = .inr target
      · subst field
        rw [tables, Function.update_self] at associated
        exact distinct (Option.some.inj associated)
      · apply unused field
        simpa only [tables, Function.update_of_ne targetField] using associated

theorem reactiveCandidateProtection_respond (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (policy : graph.BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution) (actor : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (protection : runtime.ReactiveCandidateProtection leaks who event candidate execution)
    (prescribed : actor = who → action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    runtime.ReactiveCandidateProtection leaks who event candidate
      (execution.respond (runtime.reactiveApplication leaks) actor action) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [runtime.reactive_respond_candidate_fixed leaks execution actor action candidate
      protection.fixed]
    exact protection.fixed
  · rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact protection.packets
    | some transmission =>
        cases transmission with
        | replay id => exact protection.packets.replay actor id
        | submit material =>
            apply protection.packets.submit actor _
            intro target authored addressed
            change actor = who at authored
            subst actor
            have fresh := runtime.prescribedReactivePolicy_commitment_fresh leaks who policy
              _ _ _ (prescribed rfl) material rfl target candidate addressed
            obtain ⟨serial, same, fresh⟩ := fresh
            change execution.application.candidates.lookup (who, .prepared serial) = .fresh
              at fresh
            exact False.elim (protection.fixed (by rw [same]; exact fresh))
  · intro unfinished field associated
    have oldUnfinished : event ∉ execution.application.config.cut.completed := by
      rwa [(runtime.reactive_respond_application leaks execution actor action).1] at unfinished
    apply protection.unused oldUnfinished field
    have publicEq := congrArg PublicView.accepted
      (runtime.reactive_respond_application leaks execution actor action).2
    exact (congrFun publicEq field).symm.trans associated

theorem reactiveCandidateProtection_environment (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (owned : candidate.1 = who)
    (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (protection : runtime.ReactiveCandidateProtection leaks who event candidate execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    runtime.ReactiveCandidateProtection leaks who event candidate next := by
  refine ⟨?_, ?_, ?_⟩
  · rw [runtime.reactive_environment_candidate_fixed leaks execution next command candidate
      protection.fixed reached]
    exact protection.fixed
  · cases command with
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        exact protection.packets
    | activate actor =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact protection.packets.learn actor selected
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        have kept := protection.packets.includePending id
        cases found : execution.network.lookup id <;>
          simpa only [ReactiveApplication.Execution.includePending,
            MessageNetwork.includePending, found] using kept
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨state, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact protection.packets
  · intro unfinished
    cases command with
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        exact protection.unused unfinished
    | activate actor =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
        exact protection.unused unfinished
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure] at reached
        cases FinDist.mem_support_pure.mp reached
        unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
          at unfinished ⊢
        cases found : execution.network.lookup id with
        | none =>
            simp only [found] at unfinished ⊢
            exact protection.unused unfinished
        | some message =>
            simp only [found] at unfinished ⊢
            change ((handle runtime execution.application
              ⟨message.id, message.payload.call⟩).getD execution.application).HandleUnused candidate
            change event ∉ ((handle runtime execution.application
              ⟨message.id, message.payload.call⟩).getD execution.application).config.cut.completed
              at unfinished
            cases accepted : handle runtime execution.application
                ⟨message.id, message.payload.call⟩ with
            | none =>
                simp only [accepted, Option.getD_none] at unfinished ⊢
                exact protection.unused unfinished
            | some state =>
                simp only [accepted, Option.getD_some] at unfinished ⊢
                apply runtime.handle_unused_of_commitmentFor execution.application state message
                  who event candidate owned (protection.packets.lookup id message found) _
                  accepted unfinished
                apply protection.unused
                intro completed
                exact unfinished (handle_completed_subset runtime _ state _ accepted completed)
    | application command =>
        obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
        obtain ⟨state, changed, rfl⟩ := FinDist.support_map .. ▸ supported
        change state.HandleUnused candidate
        rw [State.HandleUnused, (environmentStep_tables runtime _ state command changed).1]
        apply protection.unused
        intro completed
        exact unfinished
          (environmentStep_completed_subset runtime _ state command changed completed)

/-- After submission, arbitrary opponents, partial leaks, replay, and arbitrary
service commands cannot use this candidate for another event while its owner
continues the prescribed policy. -/
theorem reactiveCandidateProtection_policy (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (candidate : Handle graph)
    (owned : candidate.1 = who) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (prescribed : players who = runtime.prescribedReactivePolicy leaks who policy) :
    (runtime.reactiveApplication leaks).PolicyInvariant players
      (runtime.ReactiveCandidateProtection leaks who event candidate) where
  respond execution actor action valid supported := by
    apply runtime.reactiveCandidateProtection_respond leaks who event candidate policy
      execution actor action valid
    intro same
    subst actor
    rwa [prescribed] at supported
  environment execution next command valid reached :=
    runtime.reactiveCandidateProtection_environment leaks who event candidate owned
      execution next command valid reached

end Vegas.EventGraphRuntime
