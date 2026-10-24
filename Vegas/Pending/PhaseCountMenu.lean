/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountProjection

/-! # Bounded physical one-packet menus and permanent count soundness

Actual local recall reconstructs the signed next envelope. Its count verdict
remains fixed across inclusion, automatic voiding, retries and future phases.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

def OnePacketResponse (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    permits ((phaseApplication runtime leaks).outputs past)
      (localEnvelope runtime leaks who past view material) = true

/-- The local recall facts under which a submission's verdict is the local one. -/
def CountRecall (execution : (phaseApplication runtime leaks).Execution) : Prop :=
  execution.InputRecall (phaseApplication runtime leaks) ∧
    execution.SerialRecall (phaseApplication runtime leaks) ∧
    execution.InputSerialsInOrder (phaseApplication runtime leaks)

theorem countRecall_history {initial : PMF (phaseApplication runtime leaks).State}
    {horizon : Nat} {scheduler : (phaseApplication runtime leaks).Scheduler}
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((phaseApplication runtime leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    CountRecall runtime leaks control.execution :=
  ⟨(phaseApplication runtime leaks).history_inputRecall initial horizon scheduler trace,
    (phaseApplication runtime leaks).serialRecall_history scheduler initial horizon trace,
    (phaseApplication runtime leaks).inputSerialsInOrder_history scheduler initial horizon
      trace⟩

/-- **A submission is judged locally.** The submitted envelope is the local
envelope; it is judged on the new inputs exactly as against the submitter's own
recalled outputs, and every earlier input keeps its verdict. -/
theorem permits_respond (execution : (phaseApplication runtime leaks).Execution)
    (recalled : CountRecall runtime leaks execution) (who : Player)
    (material : (phaseApplication runtime leaks).Submission) :
    let next := execution.respond (phaseApplication runtime leaks) who ⟨some material⟩
    let message : Message Player (phaseApplication runtime leaks).Payload :=
      localEnvelope runtime leaks who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) material
    next.network.inputs = execution.network.inputs ++ [message] ∧
      permits next.network.inputs message =
        permits ((phaseApplication runtime leaks).outputs (execution.recall who))
          message ∧
      ∀ other ∈ execution.network.inputs,
        permits next.network.inputs other = permits execution.network.inputs other := by
  intro next message
  let app := phaseApplication runtime leaks
  obtain ⟨input, serial, order⟩ := recalled
  have envelope := localEnvelope_eq_of_recall runtime leaks execution input serial who material
  have inputs : next.network.inputs = execution.network.inputs ++ [message] := by
    change (execution.respond app who ⟨some material⟩).network.inputs =
      List.append execution.network.inputs [localEnvelope runtime leaks who
        (execution.recall who) (execution.observe app who) material]
    rw [envelope]
    rfl
  have senderEq : message.sender = who := rfl
  have serialEq : message.id.2 = execution.network.nextSerial who := (serial who).symm
  refine ⟨inputs, ?_, ?_⟩
  · rw [inputs, permits_append_self]
    apply permits_congr
    exact input.earlier_inputs_iff_outputs message
  · intro other present
    rw [inputs]
    apply permits_append_later
    intro newer member owner
    rw [List.mem_singleton.mp member] at owner ⊢
    rw [serialEq, ← senderEq, owner]
    exact (order.serial_lt present).le

theorem countRecall_respond (execution : (phaseApplication runtime leaks).Execution)
    (recalled : CountRecall runtime leaks execution) (who : Player)
    (action : (phaseApplication runtime leaks).Action) :
    CountRecall runtime leaks (execution.respond (phaseApplication runtime leaks) who action) :=
  ⟨(phaseApplication runtime leaks).respond_inputRecall execution who action recalled.1,
    (phaseApplication runtime leaks).respond_serialRecall execution who action recalled.2.1,
    ((phaseApplication runtime leaks).inputSerialsInOrderInvariant
      (fun _ _ => PMF.pure .wait)).respond execution who action recalled.2.2⟩

/-- Every input is permitted by the count verdict on the current inputs. -/
def CountClean (execution : (phaseApplication runtime leaks).Execution) : Prop :=
  CountRecall runtime leaks execution ∧
    ∀ message ∈ execution.network.inputs, permits execution.network.inputs message = true

/-- Clean traffic stays clean under silence and under one-packet responses. -/
theorem countClean_respond (execution : (phaseApplication runtime leaks).Execution)
    (clean : CountClean runtime leaks execution) (who : Player)
    (action : (phaseApplication runtime leaks).Action)
    (allowed : action.transmission = none ∨
      OnePacketResponse runtime leaks who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) action) :
    CountClean runtime leaks
      (execution.respond (phaseApplication runtime leaks) who action) := by
  refine ⟨countRecall_respond runtime leaks execution clean.1 who action, ?_⟩
  rcases action with ⟨transmission⟩
  rcases allowed with silent | ⟨material, sent, permitted⟩
  · change transmission = none at silent
    subst silent
    exact clean.2
  · change transmission = some material at sent
    subst sent
    obtain ⟨inputs, fresh, kept⟩ := permits_respond runtime leaks execution clean.1 who
      material
    intro message member
    rw [inputs] at member
    rcases List.mem_append.mp member with old | new
    · rw [kept message old]
      exact clean.2 message old
    · rw [List.mem_singleton.mp new, fresh]
      exact permitted

theorem countClean_environment (execution next : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (clean : CountClean runtime leaks execution)
    (moved : next ∈ (execution.environmentStep (phaseApplication runtime leaks)
      command).support) :
    CountClean runtime leaks next := by
  let app := phaseApplication runtime leaks
  refine ⟨⟨app.environment_inputRecall execution next command clean.1.1 moved,
    app.environment_serialRecall execution next command clean.1.2.1 moved, fun observer => by
      rw [app.environmentStep_inputs execution next command moved,
        app.environmentStep_nextSerial execution next command moved]
      exact clean.1.2.2 observer⟩, ?_⟩
  rw [app.environmentStep_inputs execution next command moved]
  exact clean.2

theorem countClean_initial (state : (phaseApplication runtime leaks).State) :
    CountClean runtime leaks
      (ReactiveApplication.Execution.initial (phaseApplication runtime leaks) state) :=
  ⟨⟨(phaseApplication runtime leaks).initial_inputRecall state,
    (phaseApplication runtime leaks).initial_serialRecall state, fun _ => rfl⟩,
    fun _ member => (List.not_mem_nil member).elim⟩

/-- Full signed evidence sampled by the existing authenticated audit service. -/
abbrev Evidence (graph : Vegas.EventGraph Player L) :=
  List (Message Player (CommitAttemptPacket graph)) × Message Player (CommitAttemptPacket graph)

def evidence (traffic : List (phaseApplication runtime leaks).TrafficRecord)
    (record : (phaseApplication runtime leaks).TrafficRecord) : Evidence graph :=
  (traffic.map ReactiveApplication.TrafficRecord.envelope, record.envelope)

def audit (sample : List (Evidence graph) → PMF (List (Evidence graph)))
    (traffic : List (phaseApplication runtime leaks).TrafficRecord) : PMF (Player → Bool) :=
  (phaseApplication runtime leaks).sampledTrafficAudit (evidence runtime leaks traffic)
    (fun evidence => evidence.2.sender) (fun evidence => permits evidence.1 evidence.2)
    sample traffic

theorem audit_charge_zero (service : EvidenceReportService (Evidence graph))
    (traffic : List (phaseApplication runtime leaks).TrafficRecord)
    (clean : ∀ record ∈ traffic,
      permits (traffic.map ReactiveApplication.TrafficRecord.envelope) record.envelope = true)
    (who : Player) :
    (((audit runtime leaks service.sample traffic).map
      (fun verdict => verdict who)) true).toReal = 0 :=
  (phaseApplication runtime leaks).sampledTrafficAudit_sound _ _ _ _ traffic who
    (fun observed supported => service.sample_authentic _ observed supported)
    (fun record present _ => clean record present)

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Every bounded submission remains in the raw action syntax, including
malformed, premature and obsolete-event calls and arbitrary private preparations. -/
def rawMenu : (phaseApplication runtime leaks).ResponseMenu :=
  ReactiveApplication.ResponseMenu.fromSubmissions fun _ past view =>
    bounds.submissions
      ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage)

open Classical in
/-- The local count filter is applied to the actual reconstructed signed packet. -/
def onePacketActions (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    Finset (phaseApplication runtime leaks).Action :=
  ((rawMenu runtime leaks bounds).actions who past view).filter fun response =>
    response.transmission = none ∨ OnePacketResponse runtime leaks who past view response

theorem mem_onePacketActions (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action) :
    response ∈ onePacketActions runtime leaks bounds who past view ↔
      response ∈ (rawMenu runtime leaks bounds).actions who past view ∧
        (response.transmission = none ∨
          OnePacketResponse runtime leaks who past view response) := by
  classical
  exact Finset.mem_filter

theorem silence_onePacket (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    (⟨none⟩ : (phaseApplication runtime leaks).Action) ∈
      onePacketActions runtime leaks bounds who past view := by
  rw [mem_onePacketActions]
  refine ⟨?_, Or.inl rfl⟩
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  trivial

def onePacketMenu : (phaseApplication runtime leaks).ResponseMenu where
  actions := onePacketActions runtime leaks bounds
  nonempty who past view := ⟨_, silence_onePacket runtime leaks bounds who past view⟩

theorem onePacketMenu_in_raw :
    (onePacketMenu runtime leaks bounds).IncludedIn (rawMenu runtime leaks bounds) :=
  fun who past view response member =>
    ((mem_onePacketActions runtime leaks bounds who past view response).mp member).1

/-- The count-clean invariant is proved on actual responses and environment
steps; normalization may retire attempts without deleting their signed inputs. -/
theorem onePacketMenu_countClean (scheduler : (phaseApplication runtime leaks).Scheduler) :
    (onePacketMenu runtime leaks bounds).ServiceInvariant scheduler
      (CountClean runtime leaks) where
  respond execution who action clean member :=
    countClean_respond runtime leaks execution clean who action
      ((mem_onePacketActions runtime leaks bounds who _ _ action).mp member).2
  environment execution next command clean _ moved :=
    countClean_environment runtime leaks execution next command clean moved

/-- At EVERY actual bounded one-packet history, under arbitrary scheduling,
the authenticated count audit charges nobody, including across retired attempts. -/
theorem onePacketMenu_countCharge_zero (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (service : EvidenceReportService (Evidence graph))
    (history : ((onePacketMenu runtime leaks bounds).protocol initial horizon scheduler).History)
    (who : Player) :
    TerminalAudit.charge (phaseApplication runtime leaks).stateTraffic
      (audit runtime leaks service.sample) history.state who = 0 := by
  let app := phaseApplication runtime leaks
  have clean := (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
    (fun state _ => countClean_initial runtime leaks state) history.trace
  have inputs := app.stateTraffic_inputs initial horizon scheduler
    ((onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler history.trace)
  change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
    history.state.elim [] (fun control => control.execution.network.inputs) at inputs
  unfold TerminalAudit.charge
  apply audit_charge_zero runtime leaks service
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

end Vegas.EventGraphRuntime.PhaseCount
