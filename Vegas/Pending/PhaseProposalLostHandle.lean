/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingAcceptance

/-! # A missing submitted association cannot have another accepted use

Counted global freshness identifies a prepared handle with its one literal
signed commitment. This includes canceled attempts and old retained packets.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An actually submitted prepared handle cannot be accepted at an unrelated
field. Absence at its own event therefore gives actual global nonassociation,
without a ready/clear-state assumption or a private-meaning premise. -/
theorem submitted_handle_unused_of_unaccepted
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (serial : Nat)
    (message : Message Player (CommitAttemptPacket graph))
    (member : message ∈ control.execution.network.inputs)
    (event : graph.EventId)
    (call : message.payload.packet.call = .commitment event (owner, .prepared serial))
    (absent : control.execution.application.current.native.accepted (.inr event) = none) :
    control.execution.application.current.native.HandleUnused (owner, .prepared serial) := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have recalled := (app).history_inputRecall initial horizon scheduler raw
  have signed := phaseSignedBindings_history runtime leaks plan inputs horizon scheduler raw
  have clean := (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
    (fun state _ => countClean_initial runtime leaks state) trace
  have unique := (app).uniqueIds_history scheduler initial horizon control raw
  have allowed := (permits_eq_true_iff _ _).mp (clean.2 message member)
  intro field accepted
  cases field with
  | inl input =>
      have kind := signed.2.1 input (owner, .prepared serial) accepted
      cases kind
  | inr other =>
      obtain ⟨previous, output, previousSender, previousCall⟩ :=
        signed.2.2 other (owner, .prepared serial) accepted
      have input : previous ∈ control.execution.network.inputs := by
        change previous ∈ (app).outputs (control.execution.recall owner) at output
        rw [← recalled owner] at output
        exact (List.mem_filter.mp output).1
      have previousAllowed := (permits_eq_true_iff _ _).mp (clean.2 previous input)
      have same := commitment_eq_of_handle control.execution.network.inputs message previous
        allowed previousAllowed member input (fun left leftInput right rightInput identified =>
          (unique.inputs right rightInput).inputs left leftInput identified) call previousCall
      have sameEvent : event = other := by
        rw [← same, call] at previousCall
        exact (Payload.commitment.inj previousCall).1
      subst other
      rw [absent] at accepted
      cases accepted

end Vegas.EventGraphRuntime.PhaseCount
