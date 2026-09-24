/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecall
import Vegas.Pending.EventPlayerAction
import Vegas.Pending.EventBindingAction

/-! # The event application under explicit network scheduling

One activation optionally transmits one packet. Private strategy memory is
absent from game actions. Fresh commitment material is fixed by submission. The scheduler
receives the broadcaster and envelope, while the player retains its own output.
No private staging command is a strategic action of this protocol.
An independent observation rule supplies partial knowledge of foreign pending
packets at activation; its samples are hidden from scheduling.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The semantic application observation used at an activation. -/
structure ReactivePlayerView (graph : Vegas.EventGraph Player L) where
  who : Player
  publicView : PublicView graph
  observation : graph.PlayerObservation who
  candidates : CandidateSlot graph → CommitmentCandidate (Raw L)

def reactiveApplication (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) : ReactiveApplication
      Player where
  State := State graph
  Payload := Payload graph
  Submission := Submission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := ReactivePlayerView graph
  PublicObservation := PublicView graph
  packet := Submission.packet
  submit state who submission := submitStep (submission.register state who) who submission.packet
  handle := handle runtime
  environment := environmentStep runtime
  observePlayer state who := ⟨who, state.publicView, graph.playerObserve who state.config,
    fun slot => state.candidates.lookup (who, slot)⟩
  observePublic := State.publicView
  observePending := leaks

/-- Atomically fix a fresh candidate and transmit its handle. Only the packet
field enters the network; the opening is private submission material. -/
def reactiveBinding (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload)) (serial : Nat) :
    (runtime.reactiveApplication leaks).Action where
  transmission := some (.submit
    ⟨.commitment event (who, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩)

theorem reactiveBinding_result (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (fresh : execution.application.candidates.lookup (who, .prepared serial) = .fresh) :
    let next := execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload result serial)
    next.application.bindingResult (who, .prepared serial) payload = result := by
  cases result with
  | failure =>
      change (submitStep execution.application who
        (.commitment event (who, .prepared serial))).bindingResult _ _ = _
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, fresh]
  | success value =>
      change (submitStep
        (Submission.register ⟨.commitment event (who, .prepared serial), some ⟨payload, value⟩⟩
          execution.application who) who (.commitment event (who, .prepared
            serial))).bindingResult
            (who, .prepared serial) payload = .success value
      simp only [Submission.register, ↓reduceIte]
      rw [submitStep_bindingResult]
      simp only [State.bindingResult, CommitmentCandidates.lookup_prepare_self,
        fresh, Raw.as?_mk, Option.elim_some]

/-- The environment receives the same envelope and public application state
for all private binding meanings, including an unopenable candidate. -/
theorem reactiveBinding_observation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph))
    (who : Player)
    (event : graph.EventId) (payload : L.Ty)
    (first second : PublicationResult (L.Val payload)) (serial : Nat)
    (execution : (runtime.reactiveApplication leaks).Execution) :
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload first serial)).observeEnvironment
        (runtime.reactiveApplication leaks) =
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload second serial)).observeEnvironment
        (runtime.reactiveApplication leaks) := by
  have unchanged (result : PublicationResult (L.Val payload)) :
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload result serial)).application.publicView =
          execution.application.publicView := by
    change (submitStep (Submission.register _ execution.application who) who _).publicView = _
    rw [submitStep_publicView]
    exact (Submission.register_facts _ who execution.application).2.2
  change ReactiveApplication.EnvironmentView.mk (app := (runtime.reactiveApplication leaks)) _
    (execution.respond (runtime.reactiveApplication leaks) who
      (runtime.reactiveBinding leaks who event payload first serial)).application.publicView _ =
    ReactiveApplication.EnvironmentView.mk (app := (runtime.reactiveApplication leaks)) _
      (execution.respond (runtime.reactiveApplication leaks) who
        (runtime.reactiveBinding leaks who event payload second serial)).application.publicView _
  rw [unchanged first, unchanged second]
  rfl

end Vegas.EventGraphRuntime
