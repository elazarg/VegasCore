/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveCountAudit
import Vegas.Pending.ReactiveRiskMenu

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
  (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Own recall and the current view reconstruct the envelope an actual
submission emits, at every execution whose own recall matches its network. -/
theorem localEnvelope_eq_of_recall (execution : ((reactiveApplication timeouts) leaks).Execution)
    (input : execution.InputRecall ((reactiveApplication timeouts) leaks))
    (serial : execution.SerialRecall ((reactiveApplication timeouts) leaks)) (who : Player)
    (material : ((reactiveApplication timeouts) leaks).Submission) :
    (localEnvelope timeouts) leaks who (execution.logs who)
        (execution.observe ((reactiveApplication timeouts) leaks) who) material =
      ⟨(who, execution.network.nextSerial who), ((reactiveApplication timeouts) leaks).packet
        (((reactiveApplication timeouts) leaks).submit execution.application who material) who
          (execution.network.known who) material⟩ := by
  let app := (reactiveApplication timeouts) leaks
  have known : ReactiveApplication.ResponseMenu.knownPackets (execution.logs who)
      (execution.observe app who) = execution.network.known who :=
    (app.known_from_recall execution who input).symm
  unfold localEnvelope
  change Message.mk (who, app.submissionCount (execution.logs who)) _ = _
  rw [← serial who, known]
  apply congrArg (Message.mk (who, execution.network.nextSerial who))
  change WitnessedPacket.mk _ _ _ = material.emit
    (app.submit execution.application who material) who (execution.network.known who)
  rw [WitnessedSubmission.emit_eq_resolve, (reactiveApplication_submit_publicView timeouts) leaks]
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
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    countPermits (((reactiveApplication timeouts) leaks).outputs past)
      ((localEnvelope timeouts) leaks who past view material) = true

/-- The local recall facts under which a submission's verdict is the local one. -/
def CountRecall (execution : ((reactiveApplication timeouts) leaks).Execution) : Prop :=
  execution.InputRecall ((reactiveApplication timeouts) leaks) ∧
    execution.SerialRecall ((reactiveApplication timeouts) leaks) ∧
    execution.InputSerialsInOrder ((reactiveApplication timeouts) leaks)

theorem countRecall_history {initial : PMF ((reactiveApplication timeouts) leaks).State}
    {horizon : Nat} {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : (((reactiveApplication timeouts) leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    (CountRecall timeouts) leaks control.execution :=
  ⟨((reactiveApplication timeouts) leaks).history_inputRecall initial horizon scheduler trace,
    ((reactiveApplication timeouts) leaks).serialRecall_history scheduler initial horizon trace,
    ((reactiveApplication timeouts) leaks).inputSerialsInOrder_history scheduler initial horizon
      trace⟩

/-- **A submission is judged locally.** The submitted envelope is the local
envelope; it is judged on the new inputs exactly as against the submitter's own
recalled outputs, and every earlier input keeps its verdict. -/
theorem countPermits_respond (execution : ((reactiveApplication timeouts) leaks).Execution)
    (recalled : (CountRecall timeouts) leaks execution) (who : Player)
    (material : ((reactiveApplication timeouts) leaks).Submission) :
    let next := execution.respond ((reactiveApplication timeouts) leaks) who ⟨some material⟩
    let message : Message Player ((reactiveApplication timeouts) leaks).Payload :=
      (localEnvelope timeouts) leaks who (execution.logs who)
        (execution.observe ((reactiveApplication timeouts) leaks) who) material
    next.network.inputs = execution.network.inputs ++ [message] ∧
      countPermits next.network.inputs message =
        countPermits (((reactiveApplication timeouts) leaks).outputs (execution.logs who))
          message ∧
      ∀ other ∈ execution.network.inputs,
        countPermits next.network.inputs other = countPermits execution.network.inputs other := by
  intro next message
  let app := (reactiveApplication timeouts) leaks
  obtain ⟨input, serial, order⟩ := recalled
  have envelope := (localEnvelope_eq_of_recall timeouts) leaks execution input serial who material
  have inputs : next.network.inputs = execution.network.inputs ++ [message] := by
    change (execution.respond app who ⟨some material⟩).network.inputs =
      List.append execution.network.inputs [(localEnvelope timeouts) leaks who
        (execution.logs who) (execution.observe app who) material]
    rw [envelope]
    rfl
  have senderEq : message.sender = who := rfl
  have serialEq : message.id.2 = execution.network.nextSerial who := (serial who).symm
  refine ⟨inputs, ?_, ?_⟩
  · rw [inputs, countPermits_append_self]
    apply countPermits_congr
    exact input.earlier_inputs_iff_outputs message
  · intro other present
    rw [inputs]
    apply countPermits_append_later
    intro newer member owner
    rw [List.mem_singleton.mp member] at owner ⊢
    rw [serialEq, ← senderEq, owner]
    exact (order.serial_lt present).le

theorem countRecall_respond (execution : ((reactiveApplication timeouts) leaks).Execution)
    (recalled : (CountRecall timeouts) leaks execution) (who : Player)
    (action : ((reactiveApplication timeouts) leaks).Action) :
    (CountRecall timeouts) leaks (execution.respond ((reactiveApplication timeouts) leaks) who
      action) :=
  ⟨((reactiveApplication timeouts) leaks).respond_inputRecall execution who action recalled.1,
    ((reactiveApplication timeouts) leaks).respond_serialRecall execution who action recalled.2.1,
    (((reactiveApplication timeouts) leaks).inputSerialsInOrderInvariant
      (fun _ _ => PMF.pure .wait)).respond execution who action recalled.2.2⟩

/-- Every input is permitted by the count verdict on the current inputs. -/
def CountClean (execution : ((reactiveApplication timeouts) leaks).Execution) : Prop :=
  (CountRecall timeouts) leaks execution ∧
    ∀ message ∈ execution.network.inputs, countPermits execution.network.inputs message = true

/-- Clean traffic stays clean under silence and under one-packet responses. -/
theorem countClean_respond (execution : ((reactiveApplication timeouts) leaks).Execution)
    (clean : (CountClean timeouts) leaks execution) (who : Player)
    (action : ((reactiveApplication timeouts) leaks).Action)
    (allowed : action.transmission = none ∨
      (OnePacketResponse timeouts) leaks who (execution.logs who)
        (execution.observe ((reactiveApplication timeouts) leaks) who) action) :
    (CountClean timeouts) leaks
      (execution.respond ((reactiveApplication timeouts) leaks) who action) := by
  refine ⟨(countRecall_respond timeouts) leaks execution clean.1 who action, ?_⟩
  rcases action with ⟨transmission⟩
  rcases allowed with silent | ⟨material, sent, permitted⟩
  · change transmission = none at silent
    subst silent
    exact clean.2
  · change transmission = some material at sent
    subst sent
    obtain ⟨inputs, fresh, kept⟩ := (countPermits_respond timeouts) leaks execution clean.1 who
      material
    intro message member
    rw [inputs] at member
    rcases List.mem_append.mp member with old | new
    · rw [kept message old]
      exact clean.2 message old
    · rw [List.mem_singleton.mp new, fresh]
      exact permitted

theorem countClean_environment (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (clean : (CountClean timeouts) leaks execution)
    (moved : next ∈ (execution.environmentStep ((reactiveApplication timeouts) leaks)
      command).support) :
    (CountClean timeouts) leaks next := by
  let app := (reactiveApplication timeouts) leaks
  refine ⟨⟨app.environment_inputRecall execution next command clean.1.1 moved,
    app.environment_serialRecall execution next command clean.1.2.1 moved, fun observer => by
      rw [app.environmentStep_inputs execution next command moved,
        app.environmentStep_nextSerial execution next command moved]
      exact clean.1.2.2 observer⟩, ?_⟩
  rw [app.environmentStep_inputs execution next command moved]
  exact clean.2

theorem countClean_initial (state : ((reactiveApplication timeouts) leaks).State) :
    (CountClean timeouts) leaks
      (ReactiveApplication.Execution.initial ((reactiveApplication timeouts) leaks) state) :=
  ⟨⟨((reactiveApplication timeouts) leaks).initial_inputRecall state,
    ((reactiveApplication timeouts) leaks).initial_serialRecall state, fun _ => rfl⟩,
    fun _ member => (List.not_mem_nil member).elim⟩

namespace MessageBounds

variable [Fintype Player] (bounds : MessageBounds graph)

open Classical in
/-- **The one-packet menu.** Silence and every bounded effective response
transmitting a permitted packet. -/
def onePacketActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  ((bounds.menu timeouts leaks).actions who past view).filter fun response =>
    response.transmission = none ∨ (OnePacketResponse timeouts) leaks who past view response

theorem mem_onePacketActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action) :
    response ∈ bounds.onePacketActions timeouts leaks who past view ↔
      response ∈ (bounds.menu timeouts leaks).actions who past view ∧
        (response.transmission = none ∨
          (OnePacketResponse timeouts) leaks who past view response) := by
  classical
  simp only [onePacketActions, Finset.mem_filter]

theorem silence_onePacket (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (⟨none⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
      bounds.onePacketActions timeouts leaks who past view :=
  (bounds.mem_onePacketActions timeouts leaks who past view _).mpr
    ⟨bounds.canonicalActions_effective timeouts leaks who past view
      (bounds.silence_canonical timeouts leaks who past view), Or.inl rfl⟩

def onePacketMenu : ((reactiveApplication timeouts) leaks).ResponseMenu where
  actions := bounds.onePacketActions timeouts leaks
  nonempty who past view := ⟨_, bounds.silence_onePacket timeouts leaks who past view⟩

theorem onePacketMenu_in_effective :
    (bounds.onePacketMenu timeouts leaks).IncludedIn (bounds.menu timeouts leaks) :=
  fun who past view _response member =>
    ((bounds.mem_onePacketActions timeouts leaks who past view _).mp member).1

theorem onePacketMenu_in_raw :
    (bounds.onePacketMenu timeouts leaks).IncludedIn (bounds.rawMenu timeouts leaks) :=
  fun who past view _response member => bounds.menu_in_raw timeouts leaks who past view
    (bounds.onePacketMenu_in_effective timeouts leaks who past view member)

/-- **An excluded response transmits a forbidden packet.** A bounded effective
response outside the one-packet menu transmits, and the count verdict forbids
its local envelope against the player's own earlier packets. -/
theorem onePacket_extra (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (available : response ∈ (bounds.menu timeouts leaks).actions who past view)
    (absent : response ∉ bounds.onePacketActions timeouts leaks who past view) :
    ∃ material, response.transmission = some material ∧
      countPermits (((reactiveApplication timeouts) leaks).outputs past)
        ((localEnvelope timeouts) leaks who past view material) = false := by
  rw [mem_onePacketActions] at absent
  cases sent : response.transmission with
  | none => exact (absent ⟨available, Or.inl sent⟩).elim
  | some material =>
      refine ⟨material, rfl, ?_⟩
      cases verdict : countPermits (((reactiveApplication timeouts) leaks).outputs past)
          ((localEnvelope timeouts) leaks who past view material) with
      | false => rfl
      | true => exact (absent ⟨available, Or.inr ⟨material, sent, verdict⟩⟩).elim

/-- Responses of the one-packet menu keep the traffic clean, under every
scheduler. -/
theorem onePacketMenu_countClean (scheduler : ((reactiveApplication timeouts) leaks).Scheduler) :
    (bounds.onePacketMenu timeouts leaks).ServiceInvariant scheduler
      ((CountClean timeouts) leaks) where
  respond execution who action clean member :=
    (countClean_respond timeouts) leaks execution clean who action
      ((bounds.mem_onePacketActions timeouts leaks who _ _ action).mp member).2
  environment execution next command clean _ moved :=
    (countClean_environment timeouts) leaks execution next command clean moved

/-- **Soundness.** At every history of the one-packet game, under any scheduler
and any initial law, the count audit charges nobody. -/
theorem onePacketMenu_countCharge_zero (initial : PMF ((reactiveApplication timeouts) leaks).State)
    (horizon : Nat) (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (service : EvidenceReportService (CountEvidence graph))
    (history : ((bounds.onePacketMenu timeouts leaks).protocol initial horizon scheduler).History)
    (who : Player) :
    TerminalAudit.charge ((reactiveApplication timeouts) leaks).stateTraffic
      ((countAudit timeouts) leaks service.sample) history.state who = 0 := by
  let app := (reactiveApplication timeouts) leaks
  have clean := (bounds.onePacketMenu_countClean timeouts leaks scheduler).history initial horizon
    (fun state _ => (countClean_initial timeouts) leaks state) history.trace
  have inputs := app.stateTraffic_inputs initial horizon scheduler
    ((bounds.onePacketMenu timeouts leaks).toRawTrace initial horizon scheduler history.trace)
  change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
    history.state.elim [] (fun control => control.execution.network.inputs) at inputs
  unfold TerminalAudit.charge
  apply (countAudit_charge_zero timeouts) leaks service
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

/-- A retained canonical response lies in the one-packet menu when every packet
it transmits is permitted against the owner's earlier packets. -/
theorem canonical_mem_onePacket (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (retained : response ∈ bounds.canonicalActions timeouts leaks who past view)
    (permitted : ∀ material, response.transmission = some material →
      countPermits (((reactiveApplication timeouts) leaks).outputs past)
        ((localEnvelope timeouts) leaks who past view material) = true) :
    response ∈ bounds.onePacketActions timeouts leaks who past view := by
  refine (bounds.mem_onePacketActions timeouts leaks who past view response).mpr
    ⟨bounds.canonicalActions_effective timeouts leaks who past view retained, ?_⟩
  cases sent : response.transmission with
  | none => exact Or.inl rfl
  | some material => exact Or.inr ⟨material, sent, permitted material sent⟩

end MessageBounds

end Vegas.EventGraphRuntime
