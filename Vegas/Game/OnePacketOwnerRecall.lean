/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerInfo

/-! # What a player's recall records along one-packet histories

Along every history of the one-packet game:

* every initial handle carries the meaning of its input
  (`Vegas.initialCandidates_of_trace`): a one-packet commitment names a
  prepared handle, so no submission and no inclusion touches an initial one;
* each recalled entry of a player was taken at an application state that the
  current state grows from (`Vegas.StateGrows`: stored values and completions
  persist and fixed meanings stay), at which the player's prepared handles were
  fresh exactly when unnamed by its packets before that entry, and its recorded
  response is recorded at the current state (`Vegas.recallRecord_of_trace`):
  the response emits its call, its evidence request is the canonical request of
  the emitted evidence, and a commitment's handle holds the value it prepared.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

section Transitions

/-- **A one-packet transition** is a one-packet response of the actor, a
scheduler command, or a stutter. -/
theorem onePacket_transition_cases {current next : (application setup runtime leaks).Control}
    {joint : Player → Option (application setup runtime leaks).Action}
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal (some current)
      joint)
    (reached : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support) :
    (∃ who action, action ∈ bounds.onePacketActions runtime leaks who
        (current.execution.recall who) (current.execution.observe (application setup runtime
          leaks) who) ∧
      next.execution = current.execution.respond (application setup runtime leaks) who action) ∨
    (∃ command, next.execution ∈
      (current.execution.environmentStep (application setup runtime leaks) command).support) ∨
    next.execution = current.execution := by
  rcases current with ⟨remaining, actor, execution⟩
  cases actor with
  | some who =>
      have localLegal := legal.2 who
      cases selected : joint who with
      | none =>
          simp only [selected] at localLegal
          exact absurd rfl localLegal
      | some action =>
          rw [selected] at localLegal
          have nextEq := Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
          refine Or.inl ⟨who, action, localLegal.2, ?_⟩
          rw [nextEq]
          simp only [selected, Option.getD_some]
  | none =>
      cases remaining with
      | zero =>
          right; right
          rw [Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)]
      | succ remaining =>
          obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          obtain ⟨after, supported, same⟩ := PMF.support_map .. ▸ moved
          cases Option.some.inj same
          exact Or.inr (Or.inl ⟨command, supported⟩)

/-- A one-packet commitment names a prepared handle of its sender. -/
theorem onePacket_commitment_handle {who : Player}
    {past : List (application setup runtime leaks).PlayerEntry}
    {view : (application setup runtime leaks).PlayerView} {response : (application setup runtime
      leaks).Action}
    (member : response ∈ bounds.onePacketActions runtime leaks who past view)
    {material : (application setup runtime leaks).Submission}
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {handle : Handle (graph setup)} (packet : material.call.packet = .commitment event handle) :
    ∃ serial, handle = (who, .prepared serial) := by
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions runtime leaks who _ _
    response).mp member
  rcases permitted with silent | ⟨other, otherSends, counted⟩
  · rw [sends] at silent
    cases silent
  rw [sends] at otherSends
  cases Option.some.inj otherSends
  have correct := ((countPermits_eq_true_iff _ _).mp counted).2.1
  have callEq : (runtime.localEnvelope leaks who past view material).payload.call =
      material.call.packet := rfl
  unfold CountCallCorrect at correct
  rw [callEq, packet] at correct
  obtain ⟨_, _, owner, ⟨serial, prepared⟩, _⟩ := correct
  exact ⟨serial, Prod.ext owner prepared⟩

end Transitions

section Initial

variable (setup runtime) in
/-- Every initial handle carries the meaning of its input. -/
def InitialCandidates (state : EventGraphRuntime.State (graph setup)) : Prop :=
  ∀ player input, state.candidates.lookup (player, .initial input) =
    State.candidateOfValue player ((graph setup).inputLayout input) (state.config.inputs input)

omit [Fintype Player] in
/-- Registering a submission keeps every initial handle. -/
private theorem register_lookup_initial (submission : Submission (graph setup))
    (state : EventGraphRuntime.State (graph setup)) (who player : Player)
    (input : (graph setup).InputId) :
    (submission.register state who).candidates.lookup (player, .initial input) =
      state.candidates.lookup (player, .initial input) := by
  rcases submission with ⟨packet, opening⟩
  unfold Submission.register
  split
  · split
    · apply CommitmentCandidates.lookup_prepare_other
      intro same
      cases congrArg Prod.snd same
    · rfl
  · rfl

/-- A one-packet response keeps every initial handle. -/
theorem respond_lookup_initial (execution : (application setup runtime leaks).Execution) (who :
  Player)
    (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who))
    (player : Player) (input : (graph setup).InputId) :
    (execution.respond (application setup runtime leaks) who action).application.candidates.lookup
        (player, .initial input) =
      execution.application.candidates.lookup (player, .initial input) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      change (submitStep (material.call.register execution.application who) who
        material.call.packet).candidates.lookup (player, .initial input) = _
      rw [← register_lookup_initial material.call execution.application who player input]
      cases packet : material.call.packet with
      | opening | malformed => simp only [submitStep]
      | commitment event handle =>
          obtain ⟨serial, rfl⟩ := onePacket_commitment_handle (runtime := runtime) member rfl packet
          simp only [submitStep, ↓reduceIte]
          apply CommitmentCandidates.lookup_freeze_other
          intro same
          cases congrArg Prod.snd same

omit [Fintype Player] in
/-- A scheduler command of the one-packet game keeps every initial handle. -/
theorem environment_lookup_initial (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    (facts : SettledFacts setup leaks execution)
    (clean : runtime.CountClean leaks execution)
    (player : Player) (input : (graph setup).InputId) :
    next.application.candidates.lookup (player, .initial input) =
      execution.application.candidates.lookup (player, .initial input) := by
  cases command with
  | activate who =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      rw [PMF.support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      rfl
  | wait =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      rfl
  | application command =>
      obtain ⟨changed, _⟩ := applicationStep_facts execution next command reached
      rw [(environmentStep_tables runtime _ _ command changed).2]
  | «include» id =>
      unfold ReactiveApplication.Execution.environmentStep at reached
      rw [PMF.support_map] at reached
      obtain ⟨updated, supported, rfl⟩ := reached
      cases (PMF.mem_support_pure_iff _ _).mp supported
      change (execution.includePending (application setup runtime leaks)
        id).application.candidates.lookup _ = _
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found]
      | some message =>
          obtain ⟨_, present, _⟩ := includePending_found execution.network id message found
          cases accepted : (application setup runtime leaks).handle execution.application message
            with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_none]
          | some after =>
              have applicationEq :
                  (execution.includePending (application setup runtime leaks) id).application =
                    after := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              rw [applicationEq]
              have call := reactiveHandle_call accepted
              cases packet : message.payload.call with
              | malformed raw =>
                  rw [packet] at call
                  simp [handle] at call
              | opening event handle raw =>
                  rw [packet] at call
                  rw [(handle_resolution_tables runtime _ _ _
                    (fun _ _ same => by cases same) call).2]
              | commitment event handle =>
                  rw [packet] at call
                  obtain ⟨frozen, _, _⟩ :=
                    handle_commitment_tables runtime _ _ _ event handle call
                  rw [frozen]
                  have input' := facts.carried.pending message present
                  have correct := ((countPermits_eq_true_iff _ _).mp (clean.2 message input')).2.1
                  unfold CountCallCorrect at correct
                  rw [packet] at correct
                  obtain ⟨_, _, _, ⟨serial, prepared⟩, _⟩ := correct
                  apply CommitmentCandidates.lookup_freeze_other
                  intro same
                  rw [← same] at prepared
                  cases prepared

/-- **Initial handles carry their inputs** along every history of the one-packet
game. -/
theorem initialCandidates_of_trace {state}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state) :
    ∀ control : (application setup runtime leaks).Control, state = some control →
      InitialCandidates setup control.execution.application := by
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro control initialized
      subst initialized
      cases before with
      | none =>
          change some control ∈ ((application setup runtime leaks).transition (initialLaw setup)
            horizon scheduler none joint).support at realized
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, drawnMember, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          have drawnSupport : drawn ∈ (initialLaw setup).support := drawnMember
          rw [initialLaw, serviceInitialLaw, PMF.support_map] at drawnSupport
          obtain ⟨initial, _, rfl⟩ := drawnSupport
          intro player input
          exact State.initial_candidate _ player (.initial input)
      | some current =>
          have previous := ih current rfl
          have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace
            (initialLaw setup) horizon scheduler prior
          have step := transition_configStep (initialLaw setup) horizon
            scheduler current
            control joint realized
          have sameInputs : control.execution.application.config.inputs =
              current.execution.application.config.inputs := by
            rcases step with same | ⟨other, ready, action, completed⟩
            · rw [same]
            · rw [EventGraph.Config.step, PMF.support_map] at completed
              obtain ⟨_, _, completedEq⟩ := completed
              exact (congrArg EventGraph.Config.inputs completedEq).symm
          intro player input
          rw [sameInputs, ← previous player input]
          rcases onePacket_transition_cases (runtime := runtime) legal realized with
            ⟨who, action, member, nextEq⟩ | ⟨command, moved⟩ | same
          · rw [nextEq]
            exact respond_lookup_initial (runtime := runtime) current.execution who action member
              player input
          · exact environment_lookup_initial (runtime := runtime) current.execution _ command moved
              (settledFacts_history (initialLaw setup) horizon scheduler rawTrace)
              ((bounds.onePacketMenu_countClean runtime leaks scheduler).history
                (initialLaw setup) horizon
                (fun state _ => runtime.countClean_initial leaks state) prior)
              player input
          · rw [same]

end Initial

section Grows

variable (setup runtime) in
/-- An application state grows into another: stored fields stay stored, fixed
meanings stay, and the history only grows. -/
def StateGrows (before after : EventGraphRuntime.State (graph setup)) : Prop :=
  KeepsStore before after ∧ KeepsFixedCandidates before after ∧
    before.config.history <+: after.config.history

omit [Fintype Player] in
theorem StateGrows.refl (state : EventGraphRuntime.State (graph setup)) :
    StateGrows setup state state :=
  ⟨fun _ _ stored => stored, fun _ _ => rfl, List.prefix_refl _⟩

omit [Fintype Player] in
theorem StateGrows.trans {first second third : EventGraphRuntime.State (graph setup)}
    (left : StateGrows setup first second) (right : StateGrows setup second third) :
    StateGrows setup first third := by
  refine ⟨fun field value stored => right.1 field value (left.1 field value stored),
    fun handle fixed => ?_, left.2.2.trans right.2.2⟩
  have middle := left.2.1 handle fixed
  rw [right.2.1 handle (by rw [middle]; exact fixed), middle]

omit [Fintype Player] in
/-- Every transition of the supplied runtime grows the application state. -/
theorem stateGrows_transition {current next : (application setup runtime leaks).Control}
    {joint : Player → Option (application setup runtime leaks).Action}
    (reached : some next ∈ ((application setup runtime leaks).transition (initialLaw setup) horizon
      scheduler (some current) joint).support) :
    StateGrows setup current.execution.application next.execution.application := by
  refine ⟨(keepsStore_step runtime leaks).transition (initialLaw setup) horizon scheduler
      current next joint reached,
    (keepsFixedCandidates_step runtime leaks).transition (initialLaw setup) horizon
      scheduler current next joint reached, ?_⟩
  rcases transition_configStep (initialLaw setup) horizon scheduler current
    next joint reached with
    same | ⟨event, ready, action, member⟩
  · rw [same]
  · rw [EventGraph.Config.step_history _ _ _ _ _ member]
    exact List.prefix_append _ _

omit [Fintype Player] in
/-- A grown state is later than the state it grew from. -/
theorem StateGrows.ownerEarlier {before after : EventGraphRuntime.State (graph setup)}
    (grows : StateGrows setup before after) (who : Player) {named : Nat → Prop}
    (fresh : ∀ serial, before.candidates.lookup (who, .prepared serial) = .fresh ↔ ¬ named serial)
    (initial : InitialCandidates setup before) : OwnerEarlier who named before after where
  store := grows.1
  history := grows.2.2
  fixed slot fixed := grows.2.1 (who, slot) fixed
  fresh := fresh
  initial input := initial who input

omit [Fintype Player] in
/-- A recorded response stays recorded as the state grows. -/
theorem RecordedResponse.grow {who : Player} {before after : EventGraphRuntime.State (graph setup)}
    {known : List (Message Player (WitnessedPacket (graph setup)))}
    {entry : (application setup runtime leaks).PlayerEntry}
    (recorded : RecordedResponse (runtime := runtime) who before known entry)
    (keeps : KeepsFixedCandidates before after) : RecordedResponse (runtime := runtime) who after
      known entry := by
  rcases entry with ⟨view, ⟨transmission⟩, emitted⟩
  cases transmission with
  | none => exact recorded
  | some submission =>
      rcases submission with ⟨⟨packet, opening⟩, request⟩
      obtain ⟨message, sent, call, evidence, prepared⟩ := recorded
      refine ⟨message, sent, call, evidence, ?_⟩
      cases packet with
      | commitment event handle =>
          obtain ⟨serial, handleEq, meaning⟩ := prepared
          refine ⟨serial, handleEq, ?_⟩
          change before.candidates.lookup handle = _ at meaning
          rw [keeps handle (by rw [meaning]; cases opening <;> simp), meaning]
      | opening | malformed => exact prepared

end Grows

section Record

/-- Along every history, a player's prepared handles are fresh exactly when
unnamed by its own packets. -/
theorem freshExact_of_trace {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (player : Player) (serial : Nat) :
    control.execution.application.candidates.lookup (player, .prepared serial) = .fresh ↔
      ¬ NamedSlot player ((application setup runtime leaks).outputs (control.execution.recall
        player))
        serial := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have recalled := runtime.countRecall_history leaks rawTrace
  rw [preparedFresh_history (runtime := runtime) horizon scheduler rawTrace player serial]
  apply not_congr
  rw [← recalled.1 player]
  constructor
  · rintro ⟨message, member, sender, event, call⟩
    exact ⟨message, List.mem_filter.mpr ⟨member, by simpa using sender⟩, event, call⟩
  · rintro ⟨message, member, event, call⟩
    obtain ⟨present, sender⟩ := List.mem_filter.mp member
    exact ⟨message, present, by simpa using sender, event, call⟩

/-- A one-packet commitment names a slot that is fresh before the response. -/
theorem onePacket_commitment_slotFresh {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (who : Player) (response : (application setup runtime leaks).Action)
    (member : response ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    (material : (application setup runtime leaks).Submission)
    (sends : response.transmission = some material) {event : (graph setup).EventId}
    {serial : Nat} (packet : material.call.packet = .commitment event (who, .prepared serial)) :
    control.execution.application.candidates.lookup (who, .prepared serial) = .fresh := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have recalled := runtime.countRecall_history leaks rawTrace
  obtain ⟨_, permitted⟩ := (bounds.mem_onePacketActions runtime leaks who _ _
    response).mp member
  have verdict : CountPermits ((application setup runtime leaks).outputs (control.execution.recall
    who))
      (runtime.localEnvelope leaks who (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who) material) := by
    rcases permitted with silent | ⟨other, otherSends, counted⟩
    · rw [sends] at silent
      cases silent
    · rw [sends] at otherSends
      cases Option.some.inj otherSends
      exact (countPermits_eq_true_iff _ _).mp counted
  have callEq : (runtime.localEnvelope leaks who (control.execution.recall who)
      (control.execution.observe (application setup runtime leaks) who) material).payload.call =
      material.call.packet := rfl
  have correct := verdict.2.1
  unfold CountCallCorrect at correct
  rw [callEq, packet] at correct
  obtain ⟨_, _, _, _, unused⟩ := correct
  refine (freshExact_of_trace (runtime := runtime) trace who serial).mpr ?_
  rintro ⟨message, output, committed, call⟩
  have earlier := earlierOwnPacket_of_output rawTrace who
    ((application setup runtime leaks).packet ((application setup runtime leaks).submit
      control.execution.application who material) who (control.execution.network.known who)
        material) message output
  rw [← runtime.localEnvelope_eq_of_recall leaks control.execution recalled.1
    recalled.2.1 who material] at earlier
  exact unused message earlier committed call

/-- **A response is recorded.** The entry a one-packet response appends to the
responder's recall is recorded at the state after the response. -/
theorem recordedResponse_respond {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (who : Player) (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who)) :
    RecordedResponse (runtime := runtime) who (control.execution.respond (application setup
      runtime leaks) who
        action).application
      (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
        (control.execution.observe (application setup runtime leaks) who))
      ⟨control.execution.observe (application setup runtime leaks) who, action,
        action.transmission.map fun material =>
          ⟨(who, control.execution.network.nextSerial who), (application setup runtime leaks).packet
            ((application setup runtime leaks).submit control.execution.application who material)
              who
              (control.execution.network.known who) material⟩⟩ := by
  have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have recalled := runtime.countRecall_history leaks rawTrace
  obtain ⟨effective, _⟩ := (bounds.mem_onePacketActions runtime leaks who _ _
    action).mp member
  have normal := (runtime.reactiveNormalization leaks).menu_normal
    (bounds.rawMenu runtime leaks) who _ _ action effective
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have materialNormal : material.normalizeReactive who
          (control.execution.observe (application setup runtime leaks) who).application
          (ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who)) = material :=
        Option.some.inj (congrArg ReactiveApplication.Action.transmission normal)
      have known : control.execution.network.known who =
          ReactiveApplication.ResponseMenu.knownPackets (control.execution.recall who)
            (control.execution.observe (application setup runtime leaks) who) :=
        (application setup runtime leaks).known_from_recall control.execution who recalled.1
      have candidates : (fun slot => ((application setup runtime leaks).submit
          control.execution.application who material).candidates.lookup (who, slot)) =
          material.call.candidateAfter who
            (fun slot => control.execution.application.candidates.lookup (who, slot)) :=
        funext (material.call.candidateAfter_eq who control.execution.application)
      refine ⟨_, rfl, rfl, ?_, ?_⟩
      · have evidence := congrArg WitnessedSubmission.evidence materialNormal
        change EvidenceRequest.canonical _ (material.evidence.resolve who
          (material.call.candidateAfter who
            (fun slot => control.execution.application.candidates.lookup (who, slot))) _) =
          material.evidence at evidence
        change material.evidence = EvidenceRequest.canonical _
          (material.emit ((application setup runtime leaks).submit control.execution.application who
            material) who (control.execution.network.known who)).evidence
        rw [WitnessedSubmission.emit_eq_resolve, candidates, known]
        exact evidence.symm
      · have call := congrArg WitnessedSubmission.call materialNormal
        change material.call.normalizeReactive who _ = material.call at call
        have openingEq := congrArg Submission.opening call
        change PreparationRecorded who ((application setup runtime leaks).submit
          control.execution.application who material) material.call
        cases packet : material.call.packet with
        | commitment event handle =>
            obtain ⟨serial, rfl⟩ := onePacket_commitment_handle (runtime := runtime) member rfl
              packet
            have fresh := onePacket_commitment_slotFresh (runtime := runtime) trace who _ member
              material rfl packet
            unfold PreparationRecorded
            rw [packet]
            refine ⟨serial, rfl, ?_⟩
            have after := material.call.candidateAfter_eq who control.execution.application
              (.prepared serial)
            change (submitStep (material.call.register control.execution.application who) who
              material.call.packet).candidates.lookup (who, .prepared serial) = _
            rw [after]
            unfold Submission.candidateAfter
            rw [packet]
            simp only [true_and, ↓reduceIte, fresh]
            cases material.call.opening <;> rfl
        | opening event handle raw =>
            unfold PreparationRecorded
            rw [packet]
            rw [← openingEq]
            simp only [Submission.normalizeReactive, packet, openingEffective, ↓reduceIte]
        | malformed raw =>
            unfold PreparationRecorded
            rw [packet]
            rw [← openingEq]
            simp only [Submission.normalizeReactive, packet, openingEffective, ↓reduceIte]

variable (setup runtime leaks) in
/-- **A recorded entry.** A recall entry of `player` taken after the entries
`past` was taken at a state the current state grows from, at which the
player's prepared handles were fresh exactly when unnamed by the packets of
`past` and its initial handles carried their inputs, and its response is
recorded at the current state. -/
def RecalledAt (player : Player) (past : List (application setup runtime leaks).PlayerEntry)
    (entry : (application setup runtime leaks).PlayerEntry)
    (current : EventGraphRuntime.State (graph setup)) : Prop :=
  ∃ before : EventGraphRuntime.State (graph setup),
    entry.beforeView.application = before.playerView player ∧
    StateGrows setup before current ∧
    (∀ serial, before.candidates.lookup (player, .prepared serial) = .fresh ↔
      ¬ NamedSlot player ((application setup runtime leaks).outputs past) serial) ∧
    InitialCandidates setup before ∧
    RecordedResponse (runtime := runtime) player current
      (ReactiveApplication.ResponseMenu.knownPackets past entry.beforeView) entry

omit [Fintype Player] in
theorem RecalledAt.grow {player : Player} {past : List (application setup runtime
  leaks).PlayerEntry}
    {entry : (application setup runtime leaks).PlayerEntry}
    {current next : EventGraphRuntime.State (graph setup)}
    (recalled : RecalledAt setup runtime leaks player past entry current)
    (grows : StateGrows setup current next) : RecalledAt setup runtime leaks player past entry
      next := by
  obtain ⟨before, view, beforeGrows, fresh, initial, recorded⟩ := recalled
  exact ⟨before, view, beforeGrows.trans grows, fresh, initial, recorded.grow
    grows.2.1⟩

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem forall_take_append {α : Type} {property : List α → α → Prop} {list : List α}
    {last : α} (old : ∀ k (inside : k < list.length), property (list.take k) list[k])
    (new : property list last) :
    ∀ k (inside : k < (list ++ [last]).length),
      property ((list ++ [last]).take k) (list ++ [last])[k] := by
  intro k inside
  by_cases lower : k < list.length
  · rw [List.getElem_append_left lower, List.take_append_of_le_length lower.le]
    exact old k lower
  · have equal : k = list.length := by
      simp only [List.length_append, List.length_singleton] at inside
      omega
    subst equal
    rw [List.getElem_append_right (Nat.le_refl _), List.take_left' rfl]
    simpa using new

/-- **Every recall entry is recorded** along every history of the one-packet
game. -/
theorem recallRecord_of_trace {state}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace state) :
    ∀ control : (application setup runtime leaks).Control, state = some control →
      ∀ player k (inside : k < (control.execution.recall player).length),
        RecalledAt setup runtime leaks player ((control.execution.recall player).take k)
          (control.execution.recall player)[k] control.execution.application := by
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint legal realized ih =>
      intro control initialized
      subst initialized
      cases before with
      | none =>
          change some control ∈ ((application setup runtime leaks).transition (initialLaw setup)
            horizon scheduler none joint).support at realized
          rw [ReactiveApplication.transition, PMF.support_map] at realized
          obtain ⟨drawn, _, drawnEq⟩ := realized
          cases Option.some.inj drawnEq
          intro player k inside
          exact absurd inside (Nat.not_lt_zero _)
      | some current =>
          have previous := ih current rfl
          have grows := stateGrows_transition (runtime := runtime) (horizon := horizon) realized
          have kept : ∀ player k (inside : k < (current.execution.recall player).length),
              RecalledAt setup runtime leaks player ((current.execution.recall player).take k)
                (current.execution.recall player)[k] control.execution.application :=
            fun player k inside => (previous player k inside).grow grows
          rcases onePacket_transition_cases (runtime := runtime) legal realized with
            ⟨who, action, member, nextEq⟩ | ⟨command, moved⟩ | same
          · intro player
            have recallEq := runtime.respond_recall leaks current.execution who player
              action
            rw [← nextEq] at recallEq
            rw [recallEq]
            split
            · rename_i same
              subst same
              apply forall_take_append (property := fun past entry =>
                RecalledAt setup runtime leaks player past entry control.execution.application)
                (kept player)
              refine ⟨current.execution.application, rfl, grows, ?_,
                initialCandidates_of_trace (runtime := runtime) prior current rfl, ?_⟩
              · exact freshExact_of_trace (runtime := runtime) prior player
              · rw [nextEq]
                exact recordedResponse_respond (runtime := runtime) prior player action member
            · exact kept player
          · intro player
            rw [(application setup runtime leaks).environmentStep_recall _ _ command moved]
            exact kept player
          · intro player
            rw [same]
            exact previous player

end Record

end Vegas
