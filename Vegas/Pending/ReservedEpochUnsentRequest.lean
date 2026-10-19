/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochActivationWord
import Vegas.Pending.ReservedEpochReceiptTiming
import Vegas.Pending.PhaseTimelyResolution
import Vegas.Pending.ReservedEpochResolution
import Interaction.ReactiveRoundBoundary

/-! # Literal unsent requests before the next actual owner offer -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private theorem expiry_command_view_independent {length : Nat} (budget : Nat)
    (tape : Tape Player length) (cursor : Nat) (left right : (app).EnvironmentView)
    (event : graph.EventId)
    (selected : command runtime leaks budget tape cursor left = .application (.expire event)) :
    command runtime leaks budget tape cursor right = .application (.expire event) := by
  dsimp only [command] at selected ⊢
  split_ifs at selected ⊢ <;> first
    | exact selected
    | cases selected
    | (unfold process at selected; split at selected <;> cases selected)
    | (unfold sample at selected; split at selected <;> first
        | cases selected
        | (split_ifs at selected; cases selected))

/-- The first due check is a real expiry command of the reserved service.
Earlier expiry checks for this same event are necessarily still timely. This
includes an already overdue anchor whose next owner offer may occur too late. -/
theorem first_due_check {length : Nat} (budget : Nat) (tape : Tape Player length)
    (start entered : Nat) (event : graph.EventId) (reference : (app).EnvironmentView) :
    ∃ cursor, start ≤ cursor ∧
      (∀ view, command runtime leaks budget tape cursor view = .application (.expire event)) ∧
      runtime.deadline event ≤ cursor / cycleWidth (graph := graph) budget - entered ∧
      (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
        command runtime leaks budget tape earlier view = .application (.expire event) →
          earlier / cycleWidth (graph := graph) budget - entered < runtime.deadline event) := by
  classical
  let width := cycleWidth (graph := graph) budget
  let cycle := max (start / width + 1) (entered + runtime.deadline event)
  let slot := budget + Fintype.card Player + 1 + event.val
  let dueCursor := cycle * width + slot
  have slotBound : slot < width := by
    dsimp [slot, width, cycleWidth]
    omega
  have cycleLower : start / width + 1 ≤ cycle := Nat.le_max_left _ _
  have pastStart : start < (start / width + 1) * width := by
    have decomposition := Nat.mod_add_div start width
    have remainder := Nat.mod_lt start (cycleWidth_pos (graph := graph) budget)
    change start % width < width at remainder
    rw [Nat.mul_comm width] at decomposition
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have dueLower : start ≤ dueCursor := by
    have multiplication := Nat.mul_le_mul_right width cycleLower
    dsimp only [dueCursor]
    omega
  have selected : command runtime leaks budget tape dueCursor reference =
      .application (.expire event) := expiry_at runtime leaks budget tape cycle event reference
  have due : runtime.deadline event ≤ dueCursor / width - entered := by
    have lower : entered + runtime.deadline event ≤ cycle := Nat.le_max_right _ _
    rw [show dueCursor / width = cycle from cursor_div budget cycle slot slotBound]
    omega
  have existsCheck : ∃ cursor, start ≤ cursor ∧
      command runtime leaks budget tape cursor reference = .application (.expire event) ∧
      runtime.deadline event ≤ cursor / width - entered := ⟨dueCursor, dueLower, selected, due⟩
  let cursor := Nat.find existsCheck
  have first := Nat.find_spec existsCheck
  refine ⟨cursor, first.1, ?_, first.2.2, ?_⟩
  · intro view
    exact expiry_command_view_independent runtime leaks budget tape cursor reference view event
      first.2.1
  · intro earlier lower upper view chosen
    by_contra late
    have atReference := expiry_command_view_independent runtime leaks budget tape earlier view
      reference event chosen
    have minimum := Nat.find_min' existsCheck ⟨lower, atReference, Nat.le_of_not_gt late⟩
    omega

/-- The first next owner offer is determined by the tape, including its
variable owner order and masks. The reference view is immaterial: actor
selection is independent of every application and pending-packet field. -/
theorem first_owner_offer {length : Nat} (budget cycles : Nat)
    (tape : Tape Player length) (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps cycles activationGap processingGap)
    (start : Nat) (owner : Player) (reference : (app).EnvironmentView)
    (running : start / cycleWidth (graph := graph) budget + 1 < cycles) :
    ∃ cursor, start ≤ cursor ∧
      (∀ view, (command runtime leaks budget tape cursor view).actor? app = some owner) ∧
      (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
        (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
      cursor < (start / cycleWidth (graph := graph) budget + 1 + activationGap) *
        cycleWidth (graph := graph) budget := by
  classical
  let width := cycleWidth (graph := graph) budget
  obtain ⟨cycle, lower, upper, activated⟩ :=
    gaps.activation (start / width + 1) running owner
  obtain ⟨position, positionEq⟩ := every_owner_position tape cycle owner
  let offered := cycle * width + (budget + position.val)
  have slotBound : budget + position.val < width := by
    dsimp [width, cycleWidth]
    omega
  have startLower : start < (start / width + 1) * width := by
    have decomposition := Nat.mod_add_div start width
    have remainder := Nat.mod_lt start (cycleWidth_pos (graph := graph) budget)
    change start % width < width at remainder
    rw [Nat.mul_comm width] at decomposition
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have offeredLower : start ≤ offered := by
    have multiplication := Nat.mul_le_mul_right width lower
    dsimp only [offered]
    omega
  have actualOffer : (command runtime leaks budget tape offered reference).actor? app =
      some owner := by
    have action := activation_at runtime leaks budget tape cycle position reference (by
      rwa [positionEq])
    rw [positionEq] at action
    rw [action]
    rfl
  have existsOffer : ∃ cursor, start ≤ cursor ∧
      (command runtime leaks budget tape cursor reference).actor? app = some owner :=
    ⟨offered, offeredLower, actualOffer⟩
  let cursor := Nat.find existsOffer
  have first := Nat.find_spec existsOffer
  refine ⟨cursor, first.1, ?_, ?_, ?_⟩
  · intro view
    rw [command_actor_view_independent runtime leaks budget tape cursor view reference]
    exact first.2
  · intro earlier lowerEarlier upperEarlier view selected
    have atReference := (command_actor_view_independent runtime leaks budget tape
      earlier reference view).trans selected
    have minimum := Nat.find_min' existsOffer ⟨lowerEarlier, atReference⟩
    omega
  · have minimum := Nat.find_min' existsOffer ⟨offeredLower, actualOffer⟩
    have multiplication := Nat.mul_le_mul_right width (show cycle + 1 ≤
      start / width + 1 + activationGap by omega)
    dsimp only [offered] at minimum
    rw [Nat.add_mul, Nat.one_mul] at multiplication
    change cursor < (start / width + 1 + activationGap) * width
    omega

private theorem recall_before_next_offer {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (count : Nat) (before after : (app).Execution) (owner : Player)
    (quiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      (command runtime leaks budget tape cursor view).actor? app ≠ some owner)
    (reached : after ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support) : after.recall owner = before.recall owner := by
  induction count generalizing before with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, first, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨selected, choice, dispatched⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ first)
      have selectedEq := (family_support runtime leaks budget tape _ _ selected).mp choice
      have inactive : selected.actor? app ≠ some owner := by
        rw [selectedEq]
        exact quiet before.environmentRecall.length le_rfl (by omega) _
      obtain ⟨observed, moved, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have observedRecall := (app).environmentStep_recall before observed selected moved
      have firstRecall : middle.recall owner = before.recall owner := by
        cases actor : selected.actor? app with
        | none =>
            rw [actor] at resumed
            cases (PMF.mem_support_pure_iff _ _).mp resumed
            exact congrFun observedRecall owner
        | some other =>
            have different : owner ≠ other := fun same => inactive (by rw [actor, same])
            rw [actor] at resumed
            obtain ⟨response, _supported, rfl⟩ := PMF.support_map .. ▸ resumed
            rw [(app).respond_recall_other observed other owner different response,
              observedRecall]
      have length := (app).round_environmentRecall_length (family runtime leaks budget tape)
        players before middle first
      have remainingQuiet : ∀ cursor, middle.environmentRecall.length ≤ cursor →
          cursor < middle.environmentRecall.length + count → ∀ view,
          (command runtime leaks budget tape cursor view).actor? app ≠ some owner := by
        intro cursor lower upper view
        exact quiet cursor (by omega) (by omega) view
      exact (ih middle remainingQuiet rest).trans firstRecall

/-- Before its next real owner offer, an unsent original request cannot
disappear before its first due expiry check. Previously recorded WAITs
are permitted: absence of an emitted packet, rather than absence of a response,
is the condition used here. Foreign responses remain arbitrary. -/
theorem unsent_request_before_next_offer {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon remaining count : Nat)
    (before after : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks budget tape)).Trace (some ⟨remaining, none, before⟩))
    (within : count ≤ remaining) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate)
    (entered : Nat)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (quiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      (command runtime leaks budget tape cursor view).actor? app ≠ some owner)
    (reached : after ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support)
    (positive : 0 < runtime.deadline coordinate.event)
    (expiryOpen : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      command runtime leaks budget tape cursor view = .application (.expire coordinate.event) →
        cursor / cycleWidth (graph := graph) budget - entered < runtime.deadline coordinate.event) :
    after.application.SeedRequest owner coordinate := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks budget tape
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler trace
  have ordering := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (fun state positive => by
      obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan input) trace
  have bound : ClosedCoordinateBound runtime entered entered coordinate before.application :=
    ⟨valid.active.activated_le _ entered stamp, le_rfl, by rw [request.1],
      by rw [request.1], fun _ => Or.inr ⟨request.2.2.1, stamp, by simpa using positive⟩⟩
  by_contra lost
  obtain ⟨used, tail, prior, middle, resumed, selected, lengths, path, requested, chosen,
      moved, disappeared, _responded, _future⟩ :=
    (app).runRounds_environment_boundary scheduler players
      (fun current => current.application.SeedRequest owner coordinate)
      (fun current who response present => respond_request runtime leaks current who response
        owner coordinate present) count before after request reached lost
  have usedLe : used ≤ remaining := by omega
  obtain ⟨priorTrace⟩ := (app).raw_trace_runRounds initial horizon scheduler players
    (remaining - used) used before prior (by
      simpa only [Nat.sub_add_cancel usedLe] using trace) path
  have retained := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
    used before prior valid ordering entered entered coordinate bound path
  have priorStamp : prior.application.current.native.activatedAt coordinate.event =
      some entered := by
    rcases retained.event requested.1 with completed | active
    · exact (requested.2.2.1.1 completed).elim
    · exact active.2.1
  have elapsed := (app).runRounds_environmentRecall_length scheduler players used before prior path
  have clock := clock_history runtime leaks budget tape plan inputs horizon
    ⟨remaining - used, none, prior⟩ priorTrace
  obtain ⟨currentDraw, priorValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs
    horizon scheduler priorTrace
  have resolved := environment_request_or_own_resolution runtime leaks ordered prior middle
    priorValid owner coordinate requested selected moved
  have included : ∃ (id : MessageId Player) (message : Message Player (CommitAttemptPacket graph))
      (native : State graph) (ready : prior.application.current.native.config.cut.Ready
        coordinate.event) (action : graph.Action coordinate.event),
      selected = .include id ∧ prior.network.lookup id = some message ∧
      message.sender = owner ∧ message.payload.packet.call.event? graph = some coordinate.event ∧
      handle runtime prior.application.current.native ⟨message.id, message.payload.packet.call⟩ =
        some native ∧
      native.config ∈ (prior.application.current.native.config.step coordinate.event ready
        action).support ∧
      middle.application = ({ prior.application with
        current := prior.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
    rcases resolved with kept | expiry | accepted
    · exact (disappeared kept).elim
    · have selectedActual := (family_support runtime leaks budget tape
        prior.environmentRecall (prior.observeEnvironment app) selected).mp chosen
      have timelyPrior : prior.application.current.native.WithinDeadline runtime
          coordinate.event := by
        rw [State.WithinDeadline, priorStamp, clock]
        exact expiryOpen prior.environmentRecall.length (by omega) (by omega)
          (prior.observeEnvironment app) (selectedActual.symm.trans expiry)
      have expiryMoved := moved
      rw [expiry] at expiryMoved
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expiryMoved
      obtain ⟨state, stateMoved, rfl⟩ := PMF.support_map .. ▸ expiryMoved
      exact (disappeared (PhaseRuntimeState.expiry_request_before_deadline runtime
        prior.application state owner coordinate requested timelyPrior stateMoved)).elim
    · exact accepted
  obtain ⟨id, message, native, _ready, _action, selectedEq, found, sender, named,
      _handled, _stepped, _normalized⟩ := included
  have handled : ∃ following, prior.application.handle runtime message = some following := by
    rw [selectedEq] at moved
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
    cases (PMF.mem_support_pure_iff _ _).mp moved
    cases result : prior.application.handle runtime message with
    | none =>
        apply False.elim
        apply disappeared
        simpa only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found, show (app).handle prior.application message = none from result,
          Option.getD_none] using requested
    | some following => exact ⟨following, rfl⟩
  obtain ⟨following, handled⟩ := handled
  have sameAttempt := PhaseRuntimeState.handle_attempt_eq runtime prior.application following
    message handled
  have pending := List.mem_of_find?_eq_some found
  have input := ((app).retained_envelopes_mem_inputs prior
    ((app).history_provenance initial horizon scheduler priorTrace)
    ((app).history_inputRecall initial horizon scheduler priorTrace)).pending message pending
  have output : message ∈ (app).outputs (prior.recall owner) := by
    rw [← (app).history_inputRecall initial horizon scheduler priorTrace owner]
    exact List.mem_filter.mpr ⟨input, by simp only [sender, decide_true]⟩
  have priorQuiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + used → ∀ view,
      (command runtime leaks budget tape cursor view).actor? app ≠ some owner := by
    intro cursor lower upper view
    exact quiet cursor lower (by omega) view
  rw [recall_before_next_offer runtime leaks budget tape players used before prior owner
    priorQuiet path] at output
  apply unsent message output
  change (message.payload.packet.call.event? graph).map
    (fun event => (⟨message.payload.attempt, event⟩ : CommitAttemptEvent graph)) = some coordinate
  rw [named, Option.map_some, sameAttempt, ← requested.1]

/-- At the next actual activation, the old unsent coordinate, entered stamp,
and literal own emission history are still present. This does not assert that
an offer precedes the first due check: every earlier actual expiry must still
be timely, as supplied by the exogenous first-due-check selector. -/
theorem unsent_request_at_owner_offer {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon remaining count : Nat)
    (before offered active : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks budget tape)).Trace (some ⟨remaining, none, before⟩))
    (within : count ≤ remaining) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate)
    (entered : Nat)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (quiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      (command runtime leaks budget tape cursor view).actor? app ≠ some owner)
    (reached : offered ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support)
    (activation : active ∈ (offered.environmentStep app (.activate owner)).support)
    (positive : 0 < runtime.deadline coordinate.event)
    (expiryOpen : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      command runtime leaks budget tape cursor view = .application (.expire coordinate.event) →
        cursor / cycleWidth (graph := graph) budget - entered < runtime.deadline coordinate.event) :
    active.application.SeedRequest owner coordinate ∧
      active.application.current.native.activatedAt coordinate.event = some entered ∧
      active.recall owner = before.recall owner ∧
      (∀ message ∈ (app).outputs (active.recall owner),
        PhaseCount.event? message.payload ≠ some coordinate) := by
  have offeredRequest := unsent_request_before_next_offer runtime leaks budget tape players
    plan ordered inputs horizon remaining count before offered trace within owner coordinate
      request entered stamp unsent quiet reached positive expiryOpen
  have recalledEq := recall_before_next_offer runtime leaks budget tape players count before offered
    owner quiet reached
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks budget tape
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler trace
  have ordering := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (fun state positive => by
      obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ positive
      exact PhaseRuntimeState.initial_ordered plan input) trace
  have bound : ClosedCoordinateBound runtime entered entered coordinate before.application :=
    ⟨valid.active.activated_le _ entered stamp, le_rfl, by rw [request.1],
      by rw [request.1], fun _ => Or.inr ⟨request.2.2.1, stamp, by simpa using positive⟩⟩
  have retained := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
    count before offered valid ordering entered entered coordinate bound reached
  have offeredStamp : offered.application.current.native.activatedAt coordinate.event =
      some entered := by
    rcases retained.event offeredRequest.1 with completed | ready
    · exact (offeredRequest.2.2.1.1 completed).elim
    · exact ready.2.1
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at activation
  obtain ⟨sample, _supported, rfl⟩ := PMF.support_map .. ▸ activation
  exact ⟨offeredRequest, offeredStamp, recalledEq, fun message member =>
    unsent message (recalledEq ▸ member)⟩

/-- If the real due check precedes the next offer, the original unsent
coordinate expires without an accepting binding under every later raw
continuation. The original stamp is transported to the actual expiry input;
neither a retry nor an eventual later callback can rescue that coordinate. -/
theorem unsent_due_check_before_offer {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon remaining count tail : Nat)
    (before due expired final : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks budget tape)).Trace (some ⟨remaining, none, before⟩))
    (within : count ≤ remaining) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate)
    (entered : Nat)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (quiet : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      (command runtime leaks budget tape cursor view).actor? app ≠ some owner)
    (reached : due ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support)
    (positive : 0 < runtime.deadline coordinate.event)
    (expiryOpen : ∀ cursor, before.environmentRecall.length ≤ cursor →
      cursor < before.environmentRecall.length + count → ∀ view,
      command runtime leaks budget tape cursor view = .application (.expire coordinate.event) →
        cursor / cycleWidth (graph := graph) budget - entered < runtime.deadline coordinate.event)
    (dueTime : runtime.deadline coordinate.event ≤ (before.environmentRecall.length + count) /
      cycleWidth (graph := graph) budget - entered)
    (expiry : expired ∈ (due.environmentStep app (.application (.expire coordinate.event))).support)
    (future : final ∈ ((app).runRounds (family runtime leaks budget tape)
      players tail expired).support) :
    ¬ PhaseService.BindingAccepted runtime leaks coordinate owner final := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := family runtime leaks budget tape
  have dueRequest := unsent_request_before_next_offer runtime leaks budget tape players plan
    ordered inputs horizon remaining count before due trace within owner coordinate request entered
      stamp unsent quiet reached positive expiryOpen
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler trace
  have ordering := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨input, _positive, rfl⟩ := PMF.support_map .. ▸ supported
      exact PhaseRuntimeState.initial_ordered plan input) trace
  have bound : ClosedCoordinateBound runtime entered entered coordinate before.application :=
    ⟨valid.active.activated_le _ entered stamp, le_rfl, by rw [request.1],
      by rw [request.1], fun _ => Or.inr ⟨request.2.2.1, stamp, by simpa using positive⟩⟩
  have retained := PhaseSeedCalendar.retained_bound_runRounds runtime leaks scheduler players
    count before due valid ordering entered entered coordinate bound reached
  have dueStamp : due.application.current.native.activatedAt coordinate.event = some entered := by
    rcases retained.event dueRequest.1 with completed | ready
    · exact (dueRequest.2.2.1.1 completed).elim
    · exact ready.2.1
  obtain ⟨dueTrace⟩ := (app).raw_trace_runRounds initial horizon scheduler players
    (remaining - count) count before due (by
      simpa only [Nat.sub_add_cancel within] using trace) reached
  have elapsed := (app).runRounds_environmentRecall_length scheduler players count before due
    reached
  have clock := clock_history runtime leaks budget tape plan inputs horizon
    ⟨remaining - count, none, due⟩ dueTrace
  have dueNow : runtime.deadline coordinate.event ≤ due.application.current.native.clock -
      (due.application.current.native.activatedAt coordinate.event).getD
        due.application.current.native.clock := by
    rw [dueStamp, Option.getD_some]
    change due.application.current.native.clock =
      due.environmentRecall.length / cycleWidth (graph := graph) budget at clock
    rw [clock, elapsed]
    exact dueTime
  exact PhaseService.not_bindingAccepted_runRounds_after_expire runtime leaks plan inputs horizon
    scheduler dueTrace coordinate owner dueRequest dueNow expired expiry players tail final future

end Vegas.EventGraphRuntime.ReservedEpoch
