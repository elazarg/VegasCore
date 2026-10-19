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

/-- Qualification of an old unsent episode is determined by its first
owner offer before any due expiry and the next finite reserved processing epoch.
The predicate has no source value, policy, equilibrium or ending-clock input. -/
def UnsentQualification {length : Nat} (budget cycles : Nat) (tape : Tape Player length)
    (start entered : Nat) (owner : Player) (event : graph.EventId) : Prop :=
  ∃ cursor epoch, start ≤ cursor ∧
    (∀ view, (command runtime leaks budget tape cursor view).actor? app = some owner) ∧
    (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
      (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
    (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
      command runtime leaks budget tape earlier view = .application (.expire event) →
        earlier / cycleWidth (graph := graph) budget - entered < runtime.deadline event) ∧
    tape.nextProcessingEpoch (cursor / cycleWidth (graph := graph) budget + 1) = some epoch ∧
    epoch < cycles ∧ epoch - entered < runtime.deadline event

/-- A literal first due-expiry race makes the old unsent episode's
qualification predicate false. No offer beyond the actual exit is needed. -/
theorem not_unsentQualification_of_due {length : Nat} (budget cycles : Nat)
    (tape : Tape Player length) (start entered cursor : Nat) (owner : Player)
    (event : graph.EventId) (reference : (app).EnvironmentView) (lower : start ≤ cursor)
    (expired : ∀ view, command runtime leaks budget tape cursor view =
      .application (.expire event))
    (late : runtime.deadline event ≤ cursor / cycleWidth (graph := graph) budget - entered)
    (quiet : ∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
      (command runtime leaks budget tape earlier view).actor? app ≠ some owner) :
    ¬ UnsentQualification runtime leaks budget cycles tape start entered owner event := by
  rintro ⟨offer, epoch, offeredLower, offered, noEarlier, expiryOpen, _next, _bound, _timely⟩
  rcases lt_trichotomy offer cursor with earlier | same | later
  · exact quiet offer offeredLower earlier reference (offered reference)
  · have actor := offered reference
    rw [same, expired reference] at actor
    cases actor
  · have timely := expiryOpen cursor lower later reference (expired reference)
    omega

/-- At a literal first owner offer, old qualification is exactly the finite
next-processing-epoch test. Earlier original-deadline expiry checks remain open. -/
theorem unsentQualification_iff_first_offer {length : Nat} (budget cycles : Nat)
    (tape : Tape Player length) (start entered cursor : Nat) (owner : Player)
    (event : graph.EventId) (reference : (app).EnvironmentView) (lower : start ≤ cursor)
    (offered : ∀ view, (command runtime leaks budget tape cursor view).actor? app = some owner)
    (quiet : ∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
      (command runtime leaks budget tape earlier view).actor? app ≠ some owner)
    (expiryOpen : ∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
      command runtime leaks budget tape earlier view = .application (.expire event) →
        earlier / cycleWidth (graph := graph) budget - entered < runtime.deadline event) :
    UnsentQualification runtime leaks budget cycles tape start entered owner event ↔
      ∃ epoch, tape.nextProcessingEpoch (cursor / cycleWidth (graph := graph) budget + 1) =
        some epoch ∧ epoch < cycles ∧ epoch - entered < runtime.deadline event := by
  constructor
  · rintro ⟨other, epoch, otherLower, otherOffer, otherQuiet, _otherExpiry, next, bound, timely⟩
    have same : other = cursor := by
      rcases lt_trichotomy other cursor with earlier | same | later
      · exact (quiet other otherLower earlier reference (otherOffer reference)).elim
      · exact same
      · exact (otherQuiet cursor lower later reference (offered reference)).elim
    exact ⟨epoch, by simpa only [same] using next, bound, timely⟩
  · rintro ⟨epoch, next, bound, timely⟩
    exact ⟨cursor, epoch, lower, offered, quiet, expiryOpen, next, bound, timely⟩

/-- The literal finite service race for an old unsent request ends at its
next owner offer, first due expiry, or the physical horizon. Both absence of
an earlier owner callback and timeliness of earlier expiry commands follow
from the SAME minimum; no future offer or extra horizon slack is assumed. -/
theorem first_owner_offer_or_due {length : Nat} (budget : Nat)
    (tape : Tape Player length) (start horizon entered : Nat) (owner : Player)
    (event : graph.EventId) (reference : (app).EnvironmentView) (within : start ≤ horizon) :
    ∃ cursor, start ≤ cursor ∧ cursor ≤ horizon ∧
      (cursor = horizon ∨
        (∀ view, (command runtime leaks budget tape cursor view).actor? app = some owner) ∨
        ((∀ view, command runtime leaks budget tape cursor view =
            .application (.expire event)) ∧
          runtime.deadline event ≤ cursor / cycleWidth (graph := graph) budget - entered)) ∧
      (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
        (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
      (∀ earlier, start ≤ earlier → earlier < cursor → ∀ view,
        command runtime leaks budget tape earlier view = .application (.expire event) →
          earlier / cycleWidth (graph := graph) budget - entered < runtime.deadline event) := by
  classical
  let stops := fun cursor => start ≤ cursor ∧
    (cursor = horizon ∨
      (command runtime leaks budget tape cursor reference).actor? app = some owner ∨
      (command runtime leaks budget tape cursor reference = .application (.expire event) ∧
        runtime.deadline event ≤ cursor / cycleWidth (graph := graph) budget - entered))
  have available : ∃ cursor, stops cursor := ⟨horizon, within, Or.inl rfl⟩
  let cursor := Nat.find available
  have first := Nat.find_spec available
  have bounded : cursor ≤ horizon := Nat.find_min' available ⟨within, Or.inl rfl⟩
  refine ⟨cursor, first.1, bounded, ?_, ?_, ?_⟩
  · rcases first.2 with horizonCase | offered | expired
    · exact Or.inl horizonCase
    · exact Or.inr (Or.inl (fun view =>
        (command_actor_view_independent runtime leaks budget tape cursor view reference).trans
          offered))
    · exact Or.inr (Or.inr ⟨fun view => expiry_command_view_independent runtime leaks budget
        tape cursor reference view event expired.1, expired.2⟩)
  · intro earlier lower upper view offered
    have actual := (command_actor_view_independent runtime leaks budget tape earlier
      reference view).trans offered
    have least := Nat.find_min' available ⟨lower, Or.inr (Or.inl actual)⟩
    omega
  · intro earlier lower upper view expired
    by_contra late
    have actual := expiry_command_view_independent runtime leaks budget tape earlier view
      reference event expired
    have least := Nat.find_min' available
      ⟨lower, Or.inr (Or.inr ⟨actual, Nat.le_of_not_gt late⟩)⟩
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

/-- An old unsent request cannot cross an actual namespace exit without
first reaching its owner's next offer or a due expiry. The finite cut is the
ACTUAL reached execution's cursor, rather than a presumed later callback. -/
theorem unsent_first_offer_or_due_before_exit {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon remaining count : Nat)
    (before closed : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks budget tape)).Trace (some ⟨remaining, none, before⟩))
    (within : count ≤ remaining) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate) (entered : Nat)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (reached : closed ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support)
    (positive : 0 < runtime.deadline coordinate.event)
    (retired : closed.application.attempt ≠ before.application.attempt) :
    ∃ cursor, before.environmentRecall.length ≤ cursor ∧
      cursor < closed.environmentRecall.length ∧
      ((∀ view, (command runtime leaks budget tape cursor view).actor? app = some owner) ∨
        ((∀ view, command runtime leaks budget tape cursor view =
            .application (.expire coordinate.event)) ∧
          runtime.deadline coordinate.event ≤
            cursor / cycleWidth (graph := graph) budget - entered)) ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        command runtime leaks budget tape earlier view =
            .application (.expire coordinate.event) →
          earlier / cycleWidth (graph := graph) budget - entered <
            runtime.deadline coordinate.event) := by
  have elapsed := (app).runRounds_environmentRecall_length
    (family runtime leaks budget tape) players count before closed reached
  obtain ⟨cursor, lower, upper, selected, quiet, expiryOpen⟩ := first_owner_offer_or_due
    runtime leaks budget tape before.environmentRecall.length closed.environmentRecall.length
      entered owner coordinate.event (before.observeEnvironment app) (by omega)
  have notEnd : cursor ≠ closed.environmentRecall.length := by
    intro atEnd
    have kept := unsent_request_before_next_offer runtime leaks budget tape players plan ordered
      inputs horizon remaining count before closed trace within owner coordinate request entered
        stamp unsent (by simpa only [atEnd, elapsed] using quiet) reached positive
          (by simpa only [atEnd, elapsed] using expiryOpen)
    exact retired (kept.1.symm.trans request.1)
  refine ⟨cursor, lower, by omega, ?_, quiet, expiryOpen⟩
  rcases selected with ended | offered | expired
  · exact (notEnd ended).elim
  · exact Or.inl offered
  · exact Or.inr expired

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

/-- Decompose the ACTUAL supported stopped path at the first old-episode
race. A due check permanently precludes acceptance; an owner offer retains the
literal old request, stamp, recall, actual response and remaining path. -/
theorem unsent_race_response_before_exit {length : Nat} (budget : Nat)
    (tape : Tape Player length) (players : Player → (app).Policy)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (inputs : PMF graph.Inputs) (horizon remaining count : Nat)
    (before closed : (app).Execution)
    (trace : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      (family runtime leaks budget tape)).Trace (some ⟨remaining, none, before⟩))
    (within : count ≤ remaining) (owner : Player) (coordinate : CommitAttemptEvent graph)
    (request : before.application.SeedRequest owner coordinate) (entered : Nat)
    (stamp : before.application.current.native.activatedAt coordinate.event = some entered)
    (unsent : ∀ message ∈ (app).outputs (before.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (reached : closed ∈ ((app).runRounds (family runtime leaks budget tape)
      players count before).support)
    (positive : 0 < runtime.deadline coordinate.event)
    (retired : closed.application.attempt ≠ before.application.attempt) :
    (∃ cursor, before.environmentRecall.length ≤ cursor ∧
      cursor < closed.environmentRecall.length ∧
      (∀ view, command runtime leaks budget tape cursor view =
        .application (.expire coordinate.event)) ∧
      runtime.deadline coordinate.event ≤
        cursor / cycleWidth (graph := graph) budget - entered ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
      (∀ earlier, before.environmentRecall.length ≤ earlier → earlier < cursor → ∀ view,
        command runtime leaks budget tape earlier view = .application (.expire coordinate.event) →
          earlier / cycleWidth (graph := graph) budget - entered <
            runtime.deadline coordinate.event) ∧
      ¬ PhaseService.BindingAccepted runtime leaks coordinate owner closed) ∨
      ∃ used tail offered active response,
        used + 1 + tail = count ∧
        offered ∈ ((app).runRounds (family runtime leaks budget tape) players used before).support ∧
        command runtime leaks budget tape offered.environmentRecall.length
          (offered.observeEnvironment app) = .activate owner ∧
        active ∈ (offered.environmentStep app (.activate owner)).support ∧
        response ∈ (players owner (active.recall owner) (active.observe app owner)).support ∧
        closed ∈ ((app).runRounds (family runtime leaks budget tape) players tail
          (active.respond app owner response)).support ∧
        active.application.SeedRequest owner coordinate ∧
        active.application.current.native.activatedAt coordinate.event = some entered ∧
        active.recall owner = before.recall owner ∧
        (∀ message ∈ (app).outputs (active.recall owner),
          PhaseCount.event? message.payload ≠ some coordinate) ∧
        (∀ earlier, before.environmentRecall.length ≤ earlier →
          earlier < before.environmentRecall.length + used → ∀ view,
          (command runtime leaks budget tape earlier view).actor? app ≠ some owner) ∧
        (∀ earlier, before.environmentRecall.length ≤ earlier →
          earlier < before.environmentRecall.length + used → ∀ view,
          command runtime leaks budget tape earlier view =
              .application (.expire coordinate.event) →
            earlier / cycleWidth (graph := graph) budget - entered <
              runtime.deadline coordinate.event) := by
  let scheduler := family runtime leaks budget tape
  obtain ⟨cursor, lower, upper, selected, quiet, expiryOpen⟩ :=
    unsent_first_offer_or_due_before_exit runtime leaks budget tape players plan ordered inputs
      horizon remaining count before closed trace within owner coordinate request entered stamp
        unsent reached positive retired
  have elapsed := (app).runRounds_environmentRecall_length scheduler players count before closed
    reached
  let used := cursor - before.environmentRecall.length
  let tail := count - used - 1
  have cursorEq : cursor = before.environmentRecall.length + used := by dsimp [used]; omega
  have lengths : used + 1 + tail = count := by dsimp [tail]; omega
  have usedWithin : used ≤ remaining := by omega
  have quietUsed : ∀ earlier, before.environmentRecall.length ≤ earlier →
      earlier < before.environmentRecall.length + used → ∀ view,
      (command runtime leaks budget tape earlier view).actor? app ≠ some owner := by
    simpa only [cursorEq] using quiet
  have expiryUsed : ∀ earlier, before.environmentRecall.length ≤ earlier →
      earlier < before.environmentRecall.length + used → ∀ view,
      command runtime leaks budget tape earlier view = .application (.expire coordinate.event) →
        earlier / cycleWidth (graph := graph) budget - entered <
          runtime.deadline coordinate.event := by
    simpa only [cursorEq] using expiryOpen
  have split : count = used + (tail + 1) := by omega
  rw [split, (app).runRounds_add scheduler players used (tail + 1), PMF.support_bind] at reached
  obtain ⟨offered, initialPath, afterPath⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.runRounds, PMF.support_bind] at afterPath
  obtain ⟨resumed, roundPath, future⟩ := Set.mem_iUnion₂.mp afterPath
  simp only [ReactiveApplication.round, ReactiveApplication.dispatch, PMF.support_bind] at roundPath
  obtain ⟨command, chosen, dispatched⟩ := Set.mem_iUnion₂.mp roundPath
  obtain ⟨active, moved, responsePath⟩ := Set.mem_iUnion₂.mp dispatched
  have offeredCursor : offered.environmentRecall.length = cursor := by
    have counted := (app).runRounds_environmentRecall_length scheduler players used before offered
      initialPath
    omega
  have commandEq := (family_support runtime leaks budget tape _ _ command).mp chosen
  rw [offeredCursor] at commandEq
  rcases selected with offeredNow | expiredNow
  · have actor : command.actor? app = some owner := by
      rw [commandEq]
      exact offeredNow _
    have activate : command = .activate owner := by
      cases command with
      | activate who =>
          have same : who = owner := Option.some.inj actor
          cases same
          rfl
      | «include» id => cases actor
      | application action => cases actor
      | wait => cases actor
    rw [activate] at moved responsePath
    have activatedCommand := commandEq.symm.trans activate
    have retained := unsent_request_at_owner_offer runtime leaks budget tape players plan ordered
      inputs horizon remaining used before offered active trace usedWithin owner coordinate request
        entered stamp unsent quietUsed initialPath moved positive expiryUsed
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      ReactiveApplication.invoke, PMF.support_map] at responsePath
    obtain ⟨response, chosenResponse, equal⟩ := responsePath
    subst resumed
    exact Or.inr ⟨used, tail, offered, active, response, lengths, initialPath,
      by simpa only [offeredCursor] using activatedCommand, moved, chosenResponse, future,
      retained.1, retained.2.1, retained.2.2.1, retained.2.2.2, quietUsed, expiryUsed⟩
  · have expire : command = .application (.expire coordinate.event) := by
      rw [commandEq]
      exact expiredNow.1 _
    rw [expire] at moved responsePath
    simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
      PMF.mem_support_pure_iff] at responsePath
    subst resumed
    exact Or.inl ⟨cursor, lower, upper, expiredNow.1, expiredNow.2, quiet, expiryOpen,
      unsent_due_check_before_offer runtime leaks budget tape players plan ordered inputs horizon
        remaining used tail before offered active closed trace usedWithin owner coordinate request
          entered stamp unsent quietUsed initialPath positive expiryUsed
            (by simpa only [cursorEq] using expiredNow.2) moved future⟩

end Vegas.EventGraphRuntime.ReservedEpoch
