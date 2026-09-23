/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy

/-! # A prescribed response submits only for a previously unsent event -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem reactiveResolutionPacket_event {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : ReactivePlayerView graph) :
    (reactiveResolutionPacket who event payload binding checks outputEq action
      view).event? graph =
      some event := by
  dsimp only [reactiveResolutionPacket]
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
    · rfl
  · rfl

theorem reactiveDecision_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player)
    (event : graph.EventId) (action : graph.Action event) (view : ReactivePlayerView graph) :
    (runtime.reactiveDecision leaks who event action view).transmission = none ∨
      ∃ material, (runtime.reactiveDecision leaks who event action view).transmission =
        some (.submit material) ∧ material.packet.event? graph = some event := by
  unfold reactiveDecision
  split
  · exact Or.inl rfl
  · cases selected : reactiveFreshSlot view with
    | none => exact Or.inl rfl
    | some serial => exact Or.inr ⟨_, rfl, rfl⟩
  · rename_i owner payload binding checks outputEq codeEq nodeEq
    exact Or.inr ⟨_, rfl,
      reactiveResolutionPacket_event who event payload binding checks outputEq action view⟩

/-- No replay and no second submission for an event, regardless of how often
the scheduler activates the player or which public grant it offers. -/
theorem compileReactivePolicy_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈ (runtime.compileReactivePolicy leaks who policy history view).support) :
    action.transmission = none ∨ ∃ event material,
      action.transmission = some (.submit material) ∧ material.packet.event? graph = some event ∧
        runtime.reactiveAlreadySubmitted leaks history event = false := by
  unfold compileReactivePolicy at supported
  split at supported
  · cases FinDist.mem_support_pure.mp supported; exact Or.inl rfl
  · rename_i event grant
    split at supported
    · cases FinDist.mem_support_pure.mp supported; exact Or.inl rfl
    · rename_i unsent
      have absent : runtime.reactiveAlreadySubmitted leaks history event = false :=
        Bool.eq_false_iff.mpr unsent
      split at supported
      · split at supported
        · split at supported
          · obtain ⟨choice, _, rfl⟩ := FinDist.support_map .. ▸ supported
            rcases runtime.reactiveDecision_transmission leaks who event choice
              view.application with
              silent | ⟨material, sent, addressed⟩
            · exact Or.inl silent
            · exact Or.inr ⟨event, material, sent, addressed, absent⟩
          · cases FinDist.mem_support_pure.mp supported; exact Or.inl rfl
        · cases FinDist.mem_support_pure.mp supported; exact Or.inl rfl
      · cases FinDist.mem_support_pure.mp supported; exact Or.inl rfl

def reactiveSubmittedEvents (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) : List graph.EventId :=
  history.filterMap fun entry => entry.emitted.bind (fun message => message.payload.event? graph)

theorem reactiveAlreadySubmitted_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId) :
    runtime.reactiveAlreadySubmitted leaks history event = true ↔
      event ∈ runtime.reactiveSubmittedEvents leaks history := by
  simp only [reactiveAlreadySubmitted, reactiveSubmittedEvents, List.any_eq_true,
    List.mem_filterMap, Option.any_eq_true, Option.bind_eq_some_iff, decide_eq_true_eq]

theorem reactiveSubmittedEvents_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (Payload graph)) (event : graph.EventId)
    (member : message ∈ (runtime.reactiveApplication leaks).outputs history)
    (addressed : message.payload.event? graph = some event) :
    event ∈ runtime.reactiveSubmittedEvents leaks history := by
  obtain ⟨entry, retained, emitted⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr
    ⟨entry, retained, by simp only [emitted, Option.bind_some, addressed]⟩

theorem reactiveSubmittedEvents_unique (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (once : (runtime.reactiveSubmittedEvents leaks history).Nodup)
    (first second : Message Player (Payload graph)) (event : graph.EventId)
    (firstMem : first ∈ (runtime.reactiveApplication leaks).outputs history)
    (secondMem : second ∈ (runtime.reactiveApplication leaks).outputs history)
    (firstEvent : first.payload.event? graph = some event)
    (secondEvent : second.payload.event? graph = some event) : first = second := by
  obtain ⟨left, leftMem, leftOutput⟩ := List.mem_filterMap.mp firstMem
  obtain ⟨right, rightMem, rightOutput⟩ := List.mem_filterMap.mp secondMem
  let address (entry : (runtime.reactiveApplication leaks).PlayerEntry) :=
    entry.emitted.bind (fun message => message.payload.event? graph)
  have separated : history.Pairwise (fun a b =>
      ∀ e, address a = some e → ∀ f, address b = some f → e ≠ f) :=
    List.pairwise_filterMap.mp once
  have identity : history.Pairwise (fun a b =>
      address a = some event → address b = some event → a = b) :=
    separated.imp fun apart ha hb => (apart event ha event hb rfl).elim
  have same : left = right := List.Pairwise.forall_of_forall_of_flip
    (fun _ _ _ _ => rfl) identity
    (identity.imp fun eq ha hb => (eq hb ha).symm) leftMem rightMem
    (by simp only [address, leftOutput, Option.bind_some, firstEvent])
    (by simp only [address, rightOutput, Option.bind_some, secondEvent])
  subst right
  exact Option.some.inj (leftOutput.symm.trans rightOutput)

end Vegas.EventGraphRuntime
