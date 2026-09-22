/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventCommitmentBinding
import Interaction.MessageApplicationPolicies
import Interaction.MessageApplicationResponse

/-! # A transmitted commitment stays fixed while messages are in flight

Submission freezes an unprepared handle as unopenable. The owner can still
read another delivered packet and react before inclusion, but cannot use that
reaction to assign the original handle a value. This checks native transitions,
not service scheduling or subgame perfection.
-/

namespace VegasTests.InFlightCommitment

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

noncomputable section

private abbrev order : EventOrder where
  eventCount := 1
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev inputs : Fin 0 → EventGraph.EventField Bool simpleExpr := Fin.elim0
private abbrev outputs : Fin 1 → EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev graph : EventGraph Bool simpleExpr where
  inputCount := 0
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.bind
    (layout := EventGraph.fieldLayout inputs outputs) false .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private abbrev app := runtime.application
private abbrev candidate : Handle graph := (false, .prepared 0)
private abbrev commitment : Payload graph := .commitment 0 candidate

private def initial : app.State :=
  MessageApplication.State.initial app (State.initial (graph := graph) (fun input => nomatch input))

private def submitted : app.State :=
  { initial with
    application := submitStep initial.application false commitment
    pool := (initial.pool.submit false commitment).2 }

private def seen (bit : Bool) : app.State :=
  let signal := (submitted.pool.submit true (.malformed ⟨.bool, bit⟩)).2
  let deliveredCommitment := (signal.deliver true (false, 0)).state
  { submitted with pool := (deliveredCommitment.deliver false (true, 0)).state }

private def prepared (bit : Bool) : app.State :=
  { seen bit with
    application := privateStep (seen bit).application false (.prepare 0 ⟨.bool, bit⟩) }

private def messages (bit : Bool) : List app.Action :=
  [.submit false commitment, .submit true (.malformed ⟨.bool, bit⟩),
    .deliver true (false, 0), .deliver false (true, 0)]

/-- The states arise from actual submission and delivery transitions. -/
theorem prefix_run (bit : Bool) : app.run (messages bit) initial = FinDist.pure (seen bit) := by
  simp only [messages, MessageApplication.run, MessageApplication.step,
    FinDist.pure_bind]
  rfl

/-- Both packets have been delivered, but neither has been included. -/
theorem messages_visible_before_inclusion (bit : Bool) :
    ((seen bit).pool.observe true).inbox = [⟨(false, 0), commitment⟩] ∧
    ((seen bit).pool.observe false).inbox = [⟨(true, 0), .malformed ⟨.bool, bit⟩⟩] ∧
    (seen bit).pool.ledger = [] ∧ (seen bit).receipts = [] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Transmission has permanently fixed the missing opening. -/
theorem delivered_handle_unopenable (bit : Bool) :
    (seen bit).application.candidates.lookup candidate = .unopenable := rfl

private def readSignal (view : app.View) : Bool :=
  match view.messages.inbox.head? with
  | some ⟨_, .malformed raw⟩ => (raw.as? .bool).getD false
  | _ => false

private def respondToSignal : app.PlayerPolicy := fun _ view =>
  FinDist.pure (.privateCommand (.prepare 0 ⟨.bool, readSignal view⟩))

/-- One information-local policy chooses its preparation from the received
packet, rather than taking the hidden bit as an extra input. -/
theorem preparation_reads_delivered_signal (bit : Bool) :
    respondToSignal [] (MessageApplication.State.observe app (seen bit) false) =
      FinDist.pure (.privateCommand (.prepare 0 ⟨.bool, bit⟩)) := by
  rfl

/-- The response can actually execute after delivery, while the original
commitment envelope stays pending. -/
theorem prepare_after_delivery (bit : Bool) :
    app.step (seen bit) (.privateCommand false (.prepare 0 ⟨.bool, bit⟩)) =
      FinDist.pure (prepared bit) ∧
    (prepared bit).pool.lookup (false, 0) = some ⟨(false, 0), commitment⟩ := by
  exact ⟨rfl, rfl⟩

/-- A late preparation based on a delivered bit cannot repair this commitment. -/
theorem pending_commitment_cannot_change_meaning (bit : Bool) :
    (handle runtime (prepared bit).application ⟨(false, 0), commitment⟩).map
      (fun state => state.config.outputs 0) = some (some .failure) := by
  have ready : (prepared bit).application.config.cut.Ready 0 := by
    change (EventOrder.Cut.empty order).Ready 0
    decide
  have timely : (prepared bit).application.WithinDeadline runtime 0 := by
    change 0 < 2
    decide
  have unused : (prepared bit).application.HandleUnused candidate := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event => intro h; cases h
  rw [commitment, handle_commitment_eq runtime (prepared bit).application
    (false, 0) 0 candidate false .bool rfl rfl rfl ready timely rfl rfl rfl unused]
  rfl

private def preparedSubmission (bit : Bool) : app.State :=
  let ready := privateStep initial.application false (.prepare 0 ⟨.bool, bit⟩)
  { initial with
    application := submitStep ready false commitment
    pool := (initial.pool.submit false commitment).2 }

/-- A prepared commitment is transmitted with its value already fixed. -/
theorem prepared_submission_run (bit : Bool) :
    app.run [.privateCommand false (.prepare 0 ⟨.bool, bit⟩), .submit false commitment]
      initial = FinDist.pure (preparedSubmission bit) := by
  simp only [MessageApplication.run, MessageApplication.step, FinDist.pure_bind]
  rfl

/-- Every later native continuation retains the prepared value, including
attempted replacement after learning another player's message. -/
theorem prepared_submission_binding (bit : Bool) (actions : List app.Action)
    (next : app.State) (supported : next ∈ (app.run actions (preparedSubmission bit)).support) :
    next.application.candidates.lookup candidate = .openable ⟨.bool, bit⟩ := by
  exact run_candidate_fixed runtime (preparedSubmission bit) next actions candidate
    (by intro impossible; cases impossible) supported

/-- A forged reference cannot reserve somebody else's fresh candidate. -/
theorem foreign_reference_cannot_freeze :
    (submitStep initial.application true commitment).candidates.lookup candidate = .fresh := rfl

private def freshReaction (bit : Bool) : app.State :=
  let ready := privateStep (seen bit).application false (.prepare 1 ⟨.bool, bit⟩)
  let packet : Payload graph := .commitment 0 (false, .prepared 1)
  { seen bit with
    application := submitStep ready false packet
    pool := ((seen bit).pool.submit false packet).2 }

/-- Reading in flight still permits a new commitment chosen from the received
bit. Both commitment packets remain pending, with independently fixed meanings. -/
theorem fresh_commitment_after_delivery (bit : Bool) :
    app.run [.privateCommand false (.prepare 1 ⟨.bool,
        readSignal (MessageApplication.State.observe app (seen bit) false)⟩),
      .submit false (.commitment 0 (false, .prepared 1))] (seen bit) =
        FinDist.pure (freshReaction bit) ∧
    (freshReaction bit).pool.lookup (false, 0) = some ⟨(false, 0), commitment⟩ ∧
    (freshReaction bit).pool.lookup (false, 1) =
      some ⟨(false, 1), .commitment 0 (false, .prepared 1)⟩ ∧
    (freshReaction bit).application.candidates.lookup candidate = .unopenable ∧
    (freshReaction bit).application.candidates.lookup (false, .prepared 1) =
      .openable ⟨.bool, bit⟩ := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  simp only [MessageApplication.run, MessageApplication.step, FinDist.pure_bind]
  rfl

private def atomicReaction : app.ResponsePolicy := fun _ view =>
  FinDist.pure ⟨[.prepare 1 ⟨.bool, readSignal view⟩],
    .submit (.commitment 0 (false, .prepared 1))⟩

/-- Reading the delivered bit, preparing its fresh candidate, and sending it
requires one response invocation. No time elapses and no packet is included. -/
theorem atomic_reaction_after_delivery (bit : Bool) :
    (app.invokeResponse false atomicReaction
      (MessageApplication.PolicyExecution.initial app (seen bit))).map
        MessageInterface.PolicyExecution.native = FinDist.pure (freshReaction bit) ∧
      (freshReaction bit).application.clock = (seen bit).application.clock ∧
      (freshReaction bit).pool.ledger = [] ∧ (freshReaction bit).receipts = [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [MessageApplication.invokeResponse, atomicReaction, FinDist.pure_bind,
    MessageApplication.responseStep_submit, FinDist.map_pure]
  rfl

end

end VegasTests.InFlightCommitment
