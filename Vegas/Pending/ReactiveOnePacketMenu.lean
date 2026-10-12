/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCountAudit
import Vegas.Pending.ReactiveRiskMenu
import Vegas.Pending.EvidenceNormalization
import Interaction.ReactiveMenuInvariant
import Interaction.ReactiveMenuRestriction

/-! # The one-packet menu

At every local input the menu keeps silence and every bounded effective
response that transmits a packet the count verdict permits against the
player's own earlier packets. That packet is the signed envelope computed from
own recall and the current view, so the test reads only local data. It keeps
unopenable and wrongly typed bindings, every timing choice and every handle
slot: the verdict restricts the signed packet, not the private material behind
it.

Own recall and the view reconstruct the actual next envelope, and the
player's earlier packets in the actual traffic are exactly those in own
recall. So a response of this menu emits a permitted packet, and earlier
packets keep their verdicts because the new packet has the highest serial of
its sender. At every history of the one-packet game, under any scheduler, the
count audit therefore charges nobody.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Own recall and the current view reconstruct the envelope an actual
submission emits, at every execution whose own recall matches its network. -/
theorem localEnvelope_eq_of_recall (execution : (runtime.reactiveApplication leaks).Execution)
    (input : execution.InputRecall (runtime.reactiveApplication leaks))
    (serial : execution.SerialRecall (runtime.reactiveApplication leaks)) (who : Player)
    (material : (runtime.reactiveApplication leaks).Submission) :
    runtime.localEnvelope leaks who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who) material =
      ⟨(who, execution.network.nextSerial who), (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit execution.application who material) who
          (execution.network.known who) material⟩ := by
  let app := runtime.reactiveApplication leaks
  have known : ReactiveApplication.ResponseMenu.knownPackets (execution.recall who)
      (execution.observe app who) = execution.network.known who :=
    (app.known_from_recall execution who input).symm
  unfold localEnvelope
  change Message.mk (who, app.submissionCount (execution.recall who)) _ = _
  rw [← serial who, known]
  apply congrArg (Message.mk (who, execution.network.nextSerial who))
  change WitnessedPacket.mk _ _ _ = material.emit
    (app.submit execution.application who material) who (execution.network.known who)
  rw [WitnessedSubmission.emit_eq_resolve, runtime.reactiveApplication_submit_publicView leaks]
  have candidates : (fun slot => (app.submit execution.application who
      material).candidates.lookup (who, slot)) =
      material.call.candidateAfter who (execution.observe app who).application.candidates := by
    funext slot
    exact material.call.candidateAfter_eq who execution.application slot
  rw [candidates]
  rfl

/-- A response transmitting a packet the count verdict permits against the
player's own earlier packets, as reconstructed from own recall and view. -/
def OnePacketResponse (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    countPermits ((runtime.reactiveApplication leaks).outputs past)
      (runtime.localEnvelope leaks who past view material) = true

/-- The local recall facts under which a submission's verdict is the local one. -/
def CountRecall (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.InputRecall (runtime.reactiveApplication leaks) ∧
    execution.SerialRecall (runtime.reactiveApplication leaks) ∧
    execution.InputSerialsInOrder (runtime.reactiveApplication leaks)

theorem countRecall_history {initial : PMF (runtime.reactiveApplication leaks).State}
    {horizon : Nat} {scheduler : (runtime.reactiveApplication leaks).Scheduler}
    {control : (runtime.reactiveApplication leaks).Control}
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    runtime.CountRecall leaks control.execution :=
  ⟨(runtime.reactiveApplication leaks).history_inputRecall initial horizon scheduler trace,
    (runtime.reactiveApplication leaks).serialRecall_history scheduler initial horizon trace,
    (runtime.reactiveApplication leaks).inputSerialsInOrder_history scheduler initial horizon
      trace⟩

/-- **A submission is judged locally.** The submitted envelope is the local
envelope; it is judged on the new inputs exactly as against the submitter's own
recalled outputs, and every earlier input keeps its verdict. -/
theorem countPermits_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : runtime.CountRecall leaks execution) (who : Player)
    (material : (runtime.reactiveApplication leaks).Submission) :
    let next := execution.respond (runtime.reactiveApplication leaks) who ⟨some material⟩
    let message : Message Player (runtime.reactiveApplication leaks).Payload :=
      runtime.localEnvelope leaks who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who) material
    next.network.inputs = execution.network.inputs ++ [message] ∧
      countPermits next.network.inputs message =
        countPermits ((runtime.reactiveApplication leaks).outputs (execution.recall who))
          message ∧
      ∀ other ∈ execution.network.inputs,
        countPermits next.network.inputs other = countPermits execution.network.inputs other := by
  intro next message
  let app := runtime.reactiveApplication leaks
  obtain ⟨input, serial, order⟩ := recalled
  have envelope := runtime.localEnvelope_eq_of_recall leaks execution input serial who material
  have inputs : next.network.inputs = execution.network.inputs ++ [message] := by
    change (execution.respond app who ⟨some material⟩).network.inputs =
      List.append execution.network.inputs [runtime.localEnvelope leaks who
        (execution.recall who) (execution.observe app who) material]
    rw [envelope]
    rfl
  have senderEq : message.sender = who := rfl
  have serialEq : message.id.2 = execution.network.nextSerial who := (serial who).symm
  refine ⟨inputs, ?_, ?_⟩
  · rw [inputs, countPermits_append_self]
    apply countPermits_congr
    intro other
    have outputs := input who
    constructor
    · rintro ⟨member, owner, lower⟩
      rw [← outputs]
      exact ⟨List.mem_filter.mpr ⟨member, by simpa [senderEq] using owner⟩, owner, lower⟩
    · rintro ⟨member, owner, _⟩
      rw [← outputs] at member
      have retained := (List.mem_filter.mp member).1
      refine ⟨retained, owner, ?_⟩
      rw [serialEq, ← senderEq, ← owner]
      exact order.serial_lt retained
  · intro other present
    rw [inputs]
    apply countPermits_append_later
    intro newer member owner
    rw [List.mem_singleton.mp member] at owner ⊢
    rw [serialEq, ← senderEq, owner]
    exact (order.serial_lt present).le

theorem countRecall_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (recalled : runtime.CountRecall leaks execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action) :
    runtime.CountRecall leaks (execution.respond (runtime.reactiveApplication leaks) who action) :=
  ⟨(runtime.reactiveApplication leaks).respond_inputRecall execution who action recalled.1,
    (runtime.reactiveApplication leaks).respond_serialRecall execution who action recalled.2.1,
    ((runtime.reactiveApplication leaks).inputSerialsInOrderInvariant
      (fun _ _ => PMF.pure .wait)).respond execution who action recalled.2.2⟩

/-- Every input is permitted by the count verdict on the current inputs. -/
def CountClean (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  runtime.CountRecall leaks execution ∧
    ∀ message ∈ execution.network.inputs, countPermits execution.network.inputs message = true

/-- Clean traffic stays clean under silence and under one-packet responses. -/
theorem countClean_respond (execution : (runtime.reactiveApplication leaks).Execution)
    (clean : runtime.CountClean leaks execution) (who : Player)
    (action : (runtime.reactiveApplication leaks).Action)
    (allowed : action.transmission = none ∨
      runtime.OnePacketResponse leaks who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who) action) :
    runtime.CountClean leaks
      (execution.respond (runtime.reactiveApplication leaks) who action) := by
  refine ⟨runtime.countRecall_respond leaks execution clean.1 who action, ?_⟩
  rcases action with ⟨transmission⟩
  rcases allowed with silent | ⟨material, sent, permitted⟩
  · change transmission = none at silent
    subst silent
    exact clean.2
  · change transmission = some material at sent
    subst sent
    obtain ⟨inputs, fresh, kept⟩ := runtime.countPermits_respond leaks execution clean.1 who
      material
    intro message member
    rw [inputs] at member
    rcases List.mem_append.mp member with old | new
    · rw [kept message old]
      exact clean.2 message old
    · rw [List.mem_singleton.mp new, fresh]
      exact permitted

theorem countClean_environment (execution next : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (clean : runtime.CountClean leaks execution)
    (moved : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      command).support) :
    runtime.CountClean leaks next := by
  let app := runtime.reactiveApplication leaks
  refine ⟨⟨app.environment_inputRecall execution next command clean.1.1 moved,
    app.environment_serialRecall execution next command clean.1.2.1 moved, fun observer => by
      rw [app.environmentStep_inputs execution next command moved,
        app.environmentStep_nextSerial execution next command moved]
      exact clean.1.2.2 observer⟩, ?_⟩
  rw [app.environmentStep_inputs execution next command moved]
  exact clean.2

theorem countClean_initial (state : (runtime.reactiveApplication leaks).State) :
    runtime.CountClean leaks
      (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state) :=
  ⟨⟨(runtime.reactiveApplication leaks).initial_inputRecall state,
    (runtime.reactiveApplication leaks).initial_serialRecall state, fun _ => rfl⟩,
    fun _ member => (List.not_mem_nil member).elim⟩

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph)

open Classical in
/-- **The one-packet menu.** Silence and every bounded effective response
transmitting a permitted packet. -/
def onePacketActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  ((bounds.menu runtime leaks).actions who past view).filter fun response =>
    response.transmission = none ∨ runtime.OnePacketResponse leaks who past view response

theorem mem_onePacketActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    response ∈ bounds.onePacketActions runtime leaks who past view ↔
      response ∈ (bounds.menu runtime leaks).actions who past view ∧
        (response.transmission = none ∨
          runtime.OnePacketResponse leaks who past view response) := by
  classical
  simp only [onePacketActions, Finset.mem_filter]

theorem silence_onePacket (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (⟨none⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.onePacketActions runtime leaks who past view :=
  (bounds.mem_onePacketActions runtime leaks who past view _).mpr
    ⟨bounds.canonicalActions_effective runtime leaks who past view
      (bounds.silence_canonical runtime leaks who past view), Or.inl rfl⟩

def onePacketMenu : (runtime.reactiveApplication leaks).ResponseMenu where
  actions := bounds.onePacketActions runtime leaks
  nonempty who past view := ⟨_, bounds.silence_onePacket runtime leaks who past view⟩

theorem onePacketMenu_in_effective :
    (bounds.onePacketMenu runtime leaks).IncludedIn (bounds.menu runtime leaks) :=
  fun who past view _response member =>
    ((bounds.mem_onePacketActions runtime leaks who past view _).mp member).1

theorem onePacketMenu_in_raw :
    (bounds.onePacketMenu runtime leaks).IncludedIn (bounds.rawMenu runtime leaks) :=
  fun who past view _response member => bounds.menu_in_raw runtime leaks who past view
    (bounds.onePacketMenu_in_effective runtime leaks who past view member)

/-- **An excluded response transmits a forbidden packet.** A bounded effective
response outside the one-packet menu transmits, and the count verdict forbids
its local envelope against the player's own earlier packets. -/
theorem onePacket_extra (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions who past view)
    (absent : response ∉ bounds.onePacketActions runtime leaks who past view) :
    ∃ material, response.transmission = some material ∧
      countPermits ((runtime.reactiveApplication leaks).outputs past)
        (runtime.localEnvelope leaks who past view material) = false := by
  rw [mem_onePacketActions] at absent
  cases sent : response.transmission with
  | none => exact (absent ⟨available, Or.inl sent⟩).elim
  | some material =>
      refine ⟨material, rfl, ?_⟩
      cases verdict : countPermits ((runtime.reactiveApplication leaks).outputs past)
          (runtime.localEnvelope leaks who past view material) with
      | false => rfl
      | true => exact (absent ⟨available, Or.inr ⟨material, sent, verdict⟩⟩).elim

/-- Responses of the one-packet menu keep the traffic clean, under every
scheduler. -/
theorem onePacketMenu_countClean (scheduler : (runtime.reactiveApplication leaks).Scheduler) :
    (bounds.onePacketMenu runtime leaks).ServiceInvariant scheduler
      (runtime.CountClean leaks) where
  respond execution who action clean member :=
    runtime.countClean_respond leaks execution clean who action
      ((bounds.mem_onePacketActions runtime leaks who _ _ action).mp member).2
  environment execution next command clean _ moved :=
    runtime.countClean_environment leaks execution next command clean moved

/-- **Soundness.** At every history of the one-packet game, under any scheduler
and any initial law, the count audit charges nobody. -/
theorem onePacketMenu_countCharge_zero (initial : PMF (runtime.reactiveApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (service : EvidenceReportService (CountEvidence graph))
    (history : ((bounds.onePacketMenu runtime leaks).protocol initial horizon scheduler).History)
    (who : Player) :
    TerminalAudit.charge (runtime.reactiveApplication leaks).stateTraffic
      (runtime.countAudit leaks service.sample) history.state who = 0 := by
  let app := runtime.reactiveApplication leaks
  have clean := (bounds.onePacketMenu_countClean runtime leaks scheduler).history initial horizon
    (fun state _ => runtime.countClean_initial leaks state) history.trace
  have inputs := app.stateTraffic_inputs initial horizon scheduler
    ((bounds.onePacketMenu runtime leaks).toRawTrace initial horizon scheduler history.trace)
  change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
    history.state.elim [] (fun control => control.execution.network.inputs) at inputs
  unfold TerminalAudit.charge
  apply runtime.countAudit_charge_zero leaks service
  intro record present
  cases current : history.state with
  | none =>
      rw [current] at present
      exact (List.not_mem_nil present).elim
  | some control =>
      rw [current] at present inputs clean
      change _ = control.execution.network.inputs at inputs
      rw [inputs]
      have member : record.envelope ∈ control.execution.network.inputs := by
        rw [← inputs]
        exact List.mem_map_of_mem present
      exact clean.2 record.envelope member

end MessageBounds

end Vegas.EventGraphRuntime
