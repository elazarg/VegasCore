/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ExclusionProjection
import Vegas.Pending.ReactiveOnePacketMenu

/-! # Packet accounting with permanent exclusion

The next signed envelope is reconstructed from actual recall and the current
local view, including the exclusion mask on readiness tokens. The count
invariant therefore applies after exclusions as well as before them.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.Recovery

open Interaction GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

def maskPacket (excluded : Finset Player) (packet : WitnessedPacket graph) :
    WitnessedPacket graph :=
  if (match packet.call.event? graph with
      | none => false
      | some event => (graph.actor? event).any fun owner => decide (owner ∈ excluded)) then
    { packet with token := none }
  else packet

def normalization : (runtime.recoveryApplication leaks).SubmissionNormalization where
  normalize who view := WitnessedSubmission.normalizeReactive who view.1
  idempotent who view := WitnessedSubmission.normalizeReactive_idempotent who view.1
  packet state who known material := by
    change maskPacket state.excluded _ = maskPacket state.excluded _
    apply congrArg (maskPacket state.excluded)
    exact WitnessedSubmission.normalizeReactive_emit runtime leaks state.native who known material
  submit state who known material := by
    change RecoveryState.mk _ state.excluded = RecoveryState.mk _ state.excluded
    apply congrArg (fun native => RecoveryState.mk native state.excluded)
    exact (runtime.reactiveNormalization leaks).submit state.native who known material

def localEnvelope (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (material : (runtime.recoveryApplication leaks).Submission) :
    Message Player (WitnessedPacket graph) :=
  let envelope := runtime.localEnvelope leaks who
    (past.map (RecoveryProjection.playerEntry runtime leaks))
    (RecoveryProjection.playerView runtime leaks view) material
  ⟨envelope.id, maskPacket view.application.2 envelope.payload⟩

theorem localEnvelope_eq_of_recall (execution : (runtime.recoveryApplication leaks).Execution)
    (input : execution.InputRecall (runtime.recoveryApplication leaks))
    (serial : execution.SerialRecall (runtime.recoveryApplication leaks)) (who : Player)
    (material : (runtime.recoveryApplication leaks).Submission) :
    localEnvelope runtime leaks who (execution.recall who)
        (execution.observe (runtime.recoveryApplication leaks) who) material =
      ⟨(who, execution.network.nextSerial who), (runtime.recoveryApplication leaks).packet
        ((runtime.recoveryApplication leaks).submit execution.application who material) who
          (execution.network.known who) material⟩ := by
  have native := runtime.localEnvelope_eq_of_recall leaks
    (RecoveryProjection.execution runtime leaks execution)
    (RecoveryProjection.inputRecall runtime leaks execution input)
    (RecoveryProjection.serialRecall runtime leaks execution serial) who material
  rw [RecoveryProjection.observe] at native
  exact congrArg (fun envelope : Message Player (WitnessedPacket graph) =>
    (⟨envelope.id, maskPacket execution.application.excluded envelope.payload⟩ :
      Message Player (WitnessedPacket graph))) native

/-- A response transmitting a packet the count verdict permits against the
player's own earlier packets, as reconstructed from own recall and view. -/
def OnePacketResponse (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) : Prop :=
  ∃ material, response.transmission = some material ∧
    countPermits ((runtime.recoveryApplication leaks).outputs past)
      (localEnvelope runtime leaks who past view material) = true

/-- The local recall facts under which a submission's verdict is the local one. -/
def CountRecall (execution : (runtime.recoveryApplication leaks).Execution) : Prop :=
  execution.InputRecall (runtime.recoveryApplication leaks) ∧
    execution.SerialRecall (runtime.recoveryApplication leaks) ∧
    execution.InputSerialsInOrder (runtime.recoveryApplication leaks)

theorem countRecall_history {initial : PMF (runtime.recoveryApplication leaks).State}
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {control : (runtime.recoveryApplication leaks).Control}
    (trace : ((runtime.recoveryApplication leaks).protocol initial horizon scheduler).Trace
      (some control)) :
    CountRecall runtime leaks control.execution :=
  ⟨(runtime.recoveryApplication leaks).history_inputRecall initial horizon scheduler trace,
    (runtime.recoveryApplication leaks).serialRecall_history scheduler initial horizon trace,
    (runtime.recoveryApplication leaks).inputSerialsInOrder_history scheduler initial horizon
      trace⟩

/-- **A submission is judged locally.** The submitted envelope is the local
envelope; it is judged on the new inputs exactly as against the submitter's own
recalled outputs, and every earlier input keeps its verdict. -/
theorem countPermits_respond (execution : (runtime.recoveryApplication leaks).Execution)
    (recalled : CountRecall runtime leaks execution) (who : Player)
    (material : (runtime.recoveryApplication leaks).Submission) :
    let next := execution.respond (runtime.recoveryApplication leaks) who ⟨some material⟩
    let message : Message Player (runtime.recoveryApplication leaks).Payload :=
      localEnvelope runtime leaks who (execution.recall who)
        (execution.observe (runtime.recoveryApplication leaks) who) material
    next.network.inputs = execution.network.inputs ++ [message] ∧
      countPermits next.network.inputs message =
        countPermits ((runtime.recoveryApplication leaks).outputs (execution.recall who))
          message ∧
      ∀ other ∈ execution.network.inputs,
        countPermits next.network.inputs other = countPermits execution.network.inputs other := by
  intro next message
  let app := runtime.recoveryApplication leaks
  obtain ⟨input, serial, order⟩ := recalled
  have envelope := localEnvelope_eq_of_recall runtime leaks execution input serial who material
  have inputs : next.network.inputs = execution.network.inputs ++ [message] := by
    change (execution.respond app who ⟨some material⟩).network.inputs =
      List.append execution.network.inputs [localEnvelope runtime leaks who
        (execution.recall who) (execution.observe app who) material]
    rw [envelope]
    rfl
  have senderEq : message.sender = who := rfl
  have serialEq : message.id.2 = execution.network.nextSerial who := by
    change (runtime.reactiveApplication leaks).submissionCount
      ((execution.recall who).map (RecoveryProjection.playerEntry runtime leaks)) = _
    rw [RecoveryProjection.submissionCount]
    exact (serial who).symm
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

theorem countRecall_respond (execution : (runtime.recoveryApplication leaks).Execution)
    (recalled : CountRecall runtime leaks execution) (who : Player)
    (action : (runtime.recoveryApplication leaks).Action) :
    CountRecall runtime leaks (execution.respond (runtime.recoveryApplication leaks) who action) :=
  ⟨(runtime.recoveryApplication leaks).respond_inputRecall execution who action recalled.1,
    (runtime.recoveryApplication leaks).respond_serialRecall execution who action recalled.2.1,
    ((runtime.recoveryApplication leaks).inputSerialsInOrderInvariant
      (fun _ _ => PMF.pure .wait)).respond execution who action recalled.2.2⟩

/-- Every input is permitted by the count verdict on the current inputs. -/
def CountClean (execution : (runtime.recoveryApplication leaks).Execution) : Prop :=
  CountRecall runtime leaks execution ∧
    ∀ message ∈ execution.network.inputs, countPermits execution.network.inputs message = true

/-- Clean traffic stays clean under silence and under one-packet responses. -/
theorem countClean_respond (execution : (runtime.recoveryApplication leaks).Execution)
    (clean : CountClean runtime leaks execution) (who : Player)
    (action : (runtime.recoveryApplication leaks).Action)
    (allowed : action.transmission = none ∨
      OnePacketResponse runtime leaks who (execution.recall who)
        (execution.observe (runtime.recoveryApplication leaks) who) action) :
    CountClean runtime leaks
      (execution.respond (runtime.recoveryApplication leaks) who action) := by
  refine ⟨countRecall_respond runtime leaks execution clean.1 who action, ?_⟩
  rcases action with ⟨transmission⟩
  rcases allowed with silent | ⟨material, sent, permitted⟩
  · change transmission = none at silent
    subst silent
    exact clean.2
  · change transmission = some material at sent
    subst sent
    obtain ⟨inputs, fresh, kept⟩ := countPermits_respond runtime leaks execution clean.1 who
      material
    intro message member
    rw [inputs] at member
    rcases List.mem_append.mp member with old | new
    · rw [kept message old]
      exact clean.2 message old
    · rw [List.mem_singleton.mp new, fresh]
      exact permitted

theorem countClean_environment (execution next : (runtime.recoveryApplication leaks).Execution)
    (command : (runtime.recoveryApplication leaks).Command)
    (clean : CountClean runtime leaks execution)
    (moved : next ∈ (execution.environmentStep (runtime.recoveryApplication leaks)
      command).support) :
    CountClean runtime leaks next := by
  let app := runtime.recoveryApplication leaks
  refine ⟨⟨app.environment_inputRecall execution next command clean.1.1 moved,
    app.environment_serialRecall execution next command clean.1.2.1 moved, fun observer => by
      rw [app.environmentStep_inputs execution next command moved,
        app.environmentStep_nextSerial execution next command moved]
      exact clean.1.2.2 observer⟩, ?_⟩
  rw [app.environmentStep_inputs execution next command moved]
  exact clean.2

theorem countClean_initial (state : (runtime.recoveryApplication leaks).State) :
    CountClean runtime leaks
      (ReactiveApplication.Execution.initial (runtime.recoveryApplication leaks) state) :=
  ⟨⟨(runtime.recoveryApplication leaks).initial_inputRecall state,
    (runtime.recoveryApplication leaks).initial_serialRecall state, fun _ => rfl⟩,
    fun _ member => (List.not_mem_nil member).elim⟩


/-- Count evidence depends only on actual signed envelopes. -/
def countEvidence (traffic : List (runtime.recoveryApplication leaks).TrafficRecord)
    (record : (runtime.recoveryApplication leaks).TrafficRecord) : CountEvidence graph :=
  (traffic.map ReactiveApplication.TrafficRecord.envelope, record.envelope)

def countAudit (sample : List (CountEvidence graph) → PMF (List (CountEvidence graph)))
    (traffic : List (runtime.recoveryApplication leaks).TrafficRecord) : PMF (Player → Bool) :=
  (runtime.recoveryApplication leaks).sampledTrafficAudit (countEvidence runtime leaks traffic)
    (fun evidence => evidence.2.sender) (fun evidence => countPermits evidence.1 evidence.2)
    sample traffic

theorem countAudit_charge_zero (service : EvidenceReportService (CountEvidence graph))
    (traffic : List (runtime.recoveryApplication leaks).TrafficRecord)
    (clean : ∀ record ∈ traffic,
      countPermits (traffic.map ReactiveApplication.TrafficRecord.envelope) record.envelope = true)
    (who : Player) :
    (((countAudit runtime leaks service.sample traffic).map
      (fun verdict => verdict who)) true).toReal = 0 :=
  (runtime.recoveryApplication leaks).sampledTrafficAudit_sound _ _ _ _ traffic who
    (fun observed supported => service.sample_authentic _ observed supported)
    (fun record present _ => clean record present)

variable [Fintype Player] (bounds : MessageBounds graph)

def rawMenu : (runtime.recoveryApplication leaks).ResponseMenu :=
  ReactiveApplication.ResponseMenu.fromSubmissions (fun _ past view =>
    bounds.submissions (ReactiveApplication.ResponseMenu.knownPackets past view))

def menu : (runtime.recoveryApplication leaks).ResponseMenu :=
  (normalization runtime leaks).menu (rawMenu runtime leaks bounds)

theorem rawMenu_closed (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action)
    (member : response ∈ (rawMenu runtime leaks bounds).actions who past view) :
    (normalization runtime leaks).action who past view response ∈
      (rawMenu runtime leaks bounds).actions who past view := by
  classical
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member ⊢
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some submission => exact bounds.normalize_submission_mem who view.application.1 _ _ member

theorem menu_in_raw :
    (menu runtime leaks bounds).IncludedIn (rawMenu runtime leaks bounds) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ := (normalization runtime leaks).menu_mem
    (rawMenu runtime leaks bounds) who past view response |>.mp member
  rw [← normal]
  exact rawMenu_closed runtime leaks bounds who past view original allowed

theorem silence_menu (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView) :
    (⟨none⟩ : (runtime.recoveryApplication leaks).Action) ∈
      (menu runtime leaks bounds).actions who past view := by
  classical
  apply (normalization runtime leaks).menu_mem _ who past view _ |>.mpr
  refine ⟨⟨none⟩, ?_, rfl⟩
  exact Finset.mem_insert_self _ _

open Classical in
/-- **The one-packet menu.** Silence and every bounded effective response
transmitting a permitted packet. -/
def onePacketActions (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView) :
    Finset (runtime.recoveryApplication leaks).Action :=
  ((menu runtime leaks bounds).actions who past view).filter fun response =>
    response.transmission = none ∨ OnePacketResponse runtime leaks who past view response

theorem mem_onePacketActions (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action) :
    response ∈ onePacketActions runtime leaks bounds who past view ↔
      response ∈ (menu runtime leaks bounds).actions who past view ∧
        (response.transmission = none ∨
          OnePacketResponse runtime leaks who past view response) := by
  classical
  simp only [onePacketActions, Finset.mem_filter]

theorem silence_onePacket (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView) :
    (⟨none⟩ : (runtime.recoveryApplication leaks).Action) ∈
      onePacketActions runtime leaks bounds who past view :=
  (mem_onePacketActions runtime leaks bounds who past view _).mpr
    ⟨silence_menu runtime leaks bounds who past view, Or.inl rfl⟩

def onePacketMenu : (runtime.recoveryApplication leaks).ResponseMenu where
  actions := onePacketActions runtime leaks bounds
  nonempty who past view := ⟨_, silence_onePacket runtime leaks bounds who past view⟩

theorem onePacketMenu_in_effective :
    (onePacketMenu runtime leaks bounds).IncludedIn (menu runtime leaks bounds) :=
  fun who past view _response member =>
    ((mem_onePacketActions runtime leaks bounds who past view _).mp member).1

theorem onePacketMenu_in_raw :
    (onePacketMenu runtime leaks bounds).IncludedIn (rawMenu runtime leaks bounds) :=
  fun who past view _response member => menu_in_raw runtime leaks bounds who past view
    (onePacketMenu_in_effective runtime leaks bounds who past view member)

/-- **An excluded response transmits a forbidden packet.** A bounded effective
response outside the one-packet menu transmits, and the count verdict forbids
its local envelope against the player's own earlier packets. -/
theorem onePacket_extra (who : Player)
    (past : List (runtime.recoveryApplication leaks).PlayerEntry)
    (view : (runtime.recoveryApplication leaks).PlayerView)
    (response : (runtime.recoveryApplication leaks).Action)
    (available : response ∈ (menu runtime leaks bounds).actions who past view)
    (absent : response ∉ onePacketActions runtime leaks bounds who past view) :
    ∃ material, response.transmission = some material ∧
      countPermits ((runtime.recoveryApplication leaks).outputs past)
        (localEnvelope runtime leaks who past view material) = false := by
  rw [mem_onePacketActions] at absent
  cases sent : response.transmission with
  | none => exact (absent ⟨available, Or.inl sent⟩).elim
  | some material =>
      refine ⟨material, rfl, ?_⟩
      cases verdict : countPermits ((runtime.recoveryApplication leaks).outputs past)
          (localEnvelope runtime leaks who past view material) with
      | false => rfl
      | true => exact (absent ⟨available, Or.inr ⟨material, sent, verdict⟩⟩).elim

/-- Responses of the one-packet menu keep the traffic clean, under every
scheduler. -/
theorem onePacketMenu_countClean (scheduler : (runtime.recoveryApplication leaks).Scheduler) :
    (onePacketMenu runtime leaks bounds).ServiceInvariant scheduler
      (CountClean runtime leaks) where
  respond execution who action clean member :=
    countClean_respond runtime leaks execution clean who action
      ((mem_onePacketActions runtime leaks bounds who _ _ action).mp member).2
  environment execution next command clean _ moved :=
    countClean_environment runtime leaks execution next command clean moved

/-- **Soundness.** At every history of the one-packet game, under any scheduler
and any initial law, the count audit charges nobody. -/
theorem onePacketMenu_countCharge_zero (initial : PMF (runtime.recoveryApplication leaks).State)
    (horizon : Nat) (scheduler : (runtime.recoveryApplication leaks).Scheduler)
    (service : EvidenceReportService (CountEvidence graph))
    (history : ((onePacketMenu runtime leaks bounds).protocol initial horizon scheduler).History)
    (who : Player) :
    TerminalAudit.charge (runtime.recoveryApplication leaks).stateTraffic
      (countAudit runtime leaks service.sample) history.state who = 0 := by
  let app := runtime.recoveryApplication leaks
  have clean := (onePacketMenu_countClean runtime leaks bounds scheduler).history initial horizon
    (fun state _ => countClean_initial runtime leaks state) history.trace
  have inputs := app.stateTraffic_inputs initial horizon scheduler
    ((onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler history.trace)
  change (app.stateTraffic history.state).map ReactiveApplication.TrafficRecord.envelope =
    history.state.elim [] (fun control => control.execution.network.inputs) at inputs
  unfold TerminalAudit.charge
  apply countAudit_charge_zero runtime leaks service
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

end Vegas.EventGraphRuntime.Recovery
