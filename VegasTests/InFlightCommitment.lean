/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.EventCommitmentBinding
import Interaction.MessageApplicationPolicies
import Vegas.Pending.NativeProtocolSafety
import Vegas.Pending.EventBindingAction

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

private def readSignal (view : MessagePool.View Bool (Payload graph)) : Bool :=
  match view.inbox.head? with
  | some ⟨_, .malformed raw⟩ => (raw.as? .bool).getD false
  | _ => false

private def respondToSignal : app.PlayerPolicy := fun _ view =>
  FinDist.pure (.privateCommand (.prepare 0 ⟨.bool, readSignal view.messages⟩))

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
        readSignal (MessageApplication.State.observe app (seen bit) false).messages⟩),
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

private def reactToSignal : NativePolicy graph := fun _ view =>
  FinDist.pure (bindingAction false 0 .bool (.success (readSignal view.messages)) 1)

/-- The player reads a delivered bit and sends a commitment in one action.
Its private opening data does not enter the network. -/
theorem action_after_delivery (bit : Bool) :
    (runtime.invokeNative false reactToSignal
      (NativeExecution.initial runtime (seen bit))).map
        NativeExecution.native = FinDist.pure (freshReaction bit) ∧
      (freshReaction bit).application.clock = (seen bit).application.clock ∧
      (freshReaction bit).pool.ledger = [] ∧ (freshReaction bit).receipts = [] := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [invokeNative, reactToSignal, FinDist.pure_bind, actionStep, FinDist.map_pure]
  rfl

/-- Existing network-submission, wire, and reaction opportunities are retained. -/
example : eventServicePlan (graph := graph) [true, false] 2 0 =
    [.grant 0, .player false, .player false, .player false,
      .wire, .player true, .player false, .wire, .player true, .player false,
      .includeLatest 0 false, .sample 0] := rfl

private def nativePlayers : Bool → NativePolicy graph
  | false => reactToSignal
  | true => fun _ _ => FinDist.pure PlayerAction.wait

private def remainingReaction (bit : Bool) : NativeControl runtime :=
  ⟨0, [.player false, .includeLatest 0 false, .sample 0, .tick, .expire 0],
    NativeExecution.initial runtime (seen bit)⟩

/-- The actual service kernel invokes this policy before reserved inclusion. -/
theorem service_reaction_before_inclusion (bit : Bool) :
    (runtime.nativeControlStep
      (FinDist.pure (fun input => nomatch input)) [true, false] 2 nativePlayers
      (fun _ _ => FinDist.pure .wait)
      (fun _ _ => FinDist.pure (ServiceOrder.increasing graph))
      (some (remainingReaction bit))).map
        (fun state => state.map (fun control => control.execution.native)) =
      FinDist.pure (some (freshReaction bit)) := by
  simp only [nativeControlStep, remainingReaction, nativePlayers, invokeNative,
    reactToSignal, FinDist.pure_bind, actionStep, FinDist.map_pure]
  rfl

example (bit : Bool) (firstEpochs secondEpochs : Nat)
    (firstRest secondRest : List (ServiceInstruction graph)) :
    runtime.nativeObserve false
        (some ⟨firstEpochs, .player false :: firstRest, (remainingReaction bit).execution⟩) =
      runtime.nativeObserve false
        (some ⟨secondEpochs, .player false :: secondRest, (remainingReaction bit).execution⟩) := by
  rw [nativeObserve_player, nativeObserve_player]

private def rememberBit (bit : Bool) : NativeExecution runtime :=
  runtime.takeAction false (NativeExecution.initial runtime initial)
    ⟨[.inl (if bit then 1 else 0)], none⟩

/-- Private memory can retain a random choice even when the action sends nothing. -/
theorem private_memory_only (bit : Bool) :
    (rememberBit bit).native = initial ∧
      ((rememberBit bit).principalHistory false).length = 1 ∧
      (rememberBit bit).native.application.remembered 0 = none := by
  cases bit <;> exact ⟨rfl, rfl, rfl⟩

private def sendRemembered : NativePolicy graph := fun history _ =>
  let bit := match history.getLast? with
    | some entry => match entry.action.memory with
      | [.inl 1] => true
      | _ => false
    | none => false
  FinDist.pure (bindingAction false 0 .bool (.success bit) 0)

/-- Future behavior can depend on the retained private bit. No preparation
catalogue or first-write cache is involved. -/
theorem private_memory_recalled (bit : Bool) :
    sendRemembered ((rememberBit bit).principalHistory false)
        (runtime.nativeView (rememberBit bit).native false) =
      FinDist.pure (bindingAction (graph := graph) false 0 .bool (.success bit) 0) := by
  cases bit <;> rfl

/-- Another player's complete invocation input does not reveal the private bit. -/
theorem private_memory_hidden :
    ((rememberBit false).principalHistory true,
      runtime.nativeView (rememberBit false).native true) =
    ((rememberBit true).principalHistory true,
      runtime.nativeView (rememberBit true).native true) := rfl

private def oldBinding : NativeExecution runtime :=
  runtime.takeAction false (NativeExecution.initial runtime initial)
    (bindingAction false 0 .bool (.success false) 0)

private def newBinding : NativeExecution runtime :=
  runtime.takeAction false oldBinding (bindingAction false 0 .bool (.success true) 1)

/-- Supplying a different opening for an existing handle cannot rebind it. -/
example :
    let next := runtime.takeAction false oldBinding (bindingAction false 0 .bool (.success true) 0)
    next.native.application.bindingResult candidate .bool = .success false := rfl

/-- A missing opening at submission cannot be supplied on a later turn. -/
example :
    let failed := runtime.takeAction false (NativeExecution.initial runtime initial)
      (bindingAction false 0 .bool .failure 0)
    let next := runtime.takeAction false failed (bindingAction false 0 .bool (.success true) 0)
    next.native.application.candidates.lookup candidate = .unopenable := rfl

/-- A new submission can use a fresh handle without changing the old one. -/
theorem binding_material_recovers :
    newBinding.native.application.bindingResult (false, .prepared 1) .bool = .success true ∧
      newBinding.native.application.candidates.lookup candidate = .openable ⟨.bool, false⟩ := by
  refine ⟨?_, rfl⟩
  exact runtime.bindingAction_result false 0 .bool (.success true) 1 oldBinding rfl

/-- Exactly two decisions have occurred, with no preparation entries in recall. -/
example : (newBinding.principalHistory false).length = 2 := rfl

/-- Fresh material does not cancel the earlier packet. -/
theorem competing_packets_remain :
    newBinding.native.pool.lookup (false, 0) = some ⟨(false, 0), commitment⟩ ∧
      newBinding.native.pool.lookup (false, 1) =
        some ⟨(false, 1), .commitment 0 (false, .prepared 1)⟩ ∧
      newBinding.native.pool.ledger = [] := ⟨rfl, rfl, rfl⟩

private theorem include_binding_value (serial nonce : Nat) (bit : Bool)
    (pending : newBinding.native.pool.lookup (false, nonce) =
      some ⟨(false, nonce), .commitment 0 (false, .prepared serial)⟩)
    (value : newBinding.native.application.bindingResult (false, .prepared serial) .bool =
      .success bit) :
    (app.includePending newBinding.native (false, nonce)).application.config.outputs 0 =
      some (.success bit) := by
  have ready : newBinding.native.application.config.cut.Ready 0 := by
    change (EventOrder.Cut.empty order).Ready 0
    decide
  have timely : newBinding.native.application.WithinDeadline runtime 0 := by
    change 0 < 2
    decide
  have unused : newBinding.native.application.HandleUnused (false, .prepared serial) := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event => intro impossible; cases impossible
  have accepted := handle_commitment_eq runtime newBinding.native.application
    (false, nonce) 0 (false, .prepared serial) false .bool rfl rfl rfl
    ready timely rfl rfl rfl unused
  rw [app.includePending_accept newBinding.native (false, nonce) _ _ pending accepted]
  change (newBinding.native.application.config.complete 0 ready _
    (newBinding.native.application.bindingResult (false, .prepared serial) .bool)).outputs 0 = _
  rw [EventGraph.Config.complete_output_same, value]

theorem new_packet_can_win :
    (app.includePending newBinding.native (false, 1)).application.config.outputs 0 =
      some (.success true) := include_binding_value 1 1 true rfl binding_material_recovers.1

theorem earlier_packet_can_win :
    (app.includePending newBinding.native (false, 0)).application.config.outputs 0 =
      some (.success false) := include_binding_value 0 0 false rfl rfl

end

end VegasTests.InFlightCommitment
