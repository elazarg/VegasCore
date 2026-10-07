/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationPhase
import Vegas.Game.ServiceBlockCongruence
import Vegas.Game.SourceServiceCanonicalSlots

/-! # The phase of another owner against one deviating player

In the phase of an event owned by another player, that owner decides one fixed
source action at its first turn while the deviator follows an arbitrary native
policy and every other player is silent. The deviator's traffic at the end of
the phase has a law that depends on the execution only through its traffic at
the start and on the owner's action only through its public effect: the
owner's packet for the event is the same public envelope whatever private value
it binds, and an opening carries exactly the value the completion publishes.

* `Vegas.runUntil_map_congr_of_rounds` turns a congruence of single rounds,
  under per-side invariants, into a congruence of whole stopped runs;
* `Vegas.foreignRound_readout_congr` is the round congruence, given that the
  owner's two responses leave equal deviator traffic and that the owner's
  packets are handled alike for the deviator;
* `Vegas.decidedReveal_readout_congr` is the phase congruence for another
  owner's disclosure, when both sides disclose alike and publish the same
  value; the congruence for blocks of bindings is
  `Vegas.decidedBlock_readout_congr`.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime


variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Round

/-- The readout compared across the phase of another owner: the deviator's
traffic, the owner's turns at the event and whether the owner has submitted for
it. -/
def foreignReadout (who owner : Player) (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :=
  ((serviceRuntime setup mode deadline).bindingTraffic leaks who execution,
      ownerTurns owner event execution,
    (serviceRuntime setup mode deadline).eventRecorded leaks (execution.recall owner) event)

/-- A law on which the owner's recall stays that of `execution` has the
compared readout of its traffic. -/
theorem map_foreignReadout_of_recall (who owner : Player) (event :
    (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (law : PMF (serviceApplication setup mode deadline leaks).Execution)
    (kept : ∀ next ∈ law.support, next.recall owner = execution.recall owner) :
    law.map (foreignReadout (leaks := leaks) who owner event) =
      (law.map ((serviceRuntime setup mode deadline).bindingTraffic leaks who)).map fun traffic =>
        (traffic, ownerTurns owner event execution,
          (serviceRuntime setup mode deadline).eventRecorded leaks
              (execution.recall owner) event) := by
  rw [PMF.map_comp]
  apply map_congr_on_support _
  intro next member
  simp only [Function.comp_apply, foreignReadout, ownerTurns, kept next member]

/-- **One round of another owner's phase.** While `event`, owned by `owner`,
is the ready event, the deviator plays against silence except the owner. If the
owner's responses at every activation leave equal deviator traffic and submit
alike, and the owner's packets are handled alike for the deviator, one round
gives equal laws of the compared readout. -/
theorem foreignRound_readout_congr (scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {event : (serviceGraph setup mode).EventId} {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner) (foreign : owner ≠ who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (first second : (serviceApplication setup mode deadline leaks).Policy)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (same : foreignReadout (leaks := leaks) who owner event left =
      foreignReadout (leaks := leaks) who owner event right)
    (matched : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
        (scheduler
        left.environmentRecall (left.observeEnvironment
            (serviceApplication setup mode deadline leaks))).support →
      ∀ sample ∈
          ((serviceApplication setup mode deadline leaks).observePending
            owner left.network.pending).support,
      let leftActive := left.sampledActivation
          (serviceApplication setup mode deadline leaks) owner sample
      let rightActive := right.sampledActivation
          (serviceApplication setup mode deadline leaks) owner sample
      ∃ leftResponse rightResponse,
        first (leftActive.recall owner)
            (leftActive.observe
                (serviceApplication setup mode deadline leaks) owner) = PMF.pure leftResponse ∧
        second (rightActive.recall owner)
            (rightActive.observe
                (serviceApplication setup mode deadline leaks) owner) = PMF.pure rightResponse ∧
        (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
          (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (leftActive.respond (serviceApplication setup mode deadline leaks) owner leftResponse) =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (rightActive.respond
                (serviceApplication setup mode deadline leaks) owner rightResponse))
    (included : ∀ id message, left.network.lookup id = some message →
      message.sender = owner →
      Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) left.application ⟨message.id,
              message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle (serviceRuntime setup mode deadline) right.application ⟨message.id,
              message.payload.call⟩)) :
    ((serviceApplication setup mode deadline leaks).round scheduler
        (Function.update (focalPlayers setup leaks who deviation) owner first) left).map
        (foreignReadout (leaks := leaks) who owner event) =
      ((serviceApplication setup mode deadline leaks).round scheduler
        (Function.update (focalPlayers setup leaks who deviation) owner second) right).map
        (foreignReadout (leaks := leaks) who owner event) := by
  let app := serviceApplication setup mode deadline leaks
  let players := fun policy : app.Policy =>
    Function.update (focalPlayers setup leaks who deviation) owner policy
  have sameTraffic : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right := congrArg Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (left.recall owner) event =
      (serviceRuntime setup mode deadline).eventRecorded leaks (right.recall owner) event :=
    congrArg (fun value => value.2.2) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have observed := observeEnvironment_eq_of_bindingTraffic who sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) sameTraffic
  have whoOwner : who ≠ owner := fun equal => foreign equal.symm
  have kept (execution : app.Execution) (law : PMF app.Execution)
      (unchanged : ∀ next ∈ law.support, next.recall owner = execution.recall owner) :=
    map_foreignReadout_of_recall (leaks := leaks) who owner event execution law unchanged
  -- Including a pending packet keeps equal deviator traffic.
  have includeTraffic (id : MessageId Player) :
      (serviceRuntime setup mode deadline).bindingTraffic leaks who (left.includePending app id) =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who
            (right.includePending app id) := by
    apply include_bindingTraffic_of_handled sameTraffic id
    intro message found
    by_cases fromWho : message.sender = who
    · exact handle_playerView_congr_of_sender (serviceRuntime setup mode deadline) left.application
        right.application who ⟨message.id, message.payload.call⟩ views fromWho
    · by_cases fromOwner : message.sender = owner
      · exact included id message found fromOwner
      · rw [handle_foreign_sender_none left.application
            (fun other otherReady => by
              rw [alone _ other leftReady otherReady]
              exact Or.inr owned)
            ⟨message.id, message.payload.call⟩ fromOwner,
          handle_foreign_sender_none right.application
            (fun other otherReady => by
              rw [alone _ other rightReady otherReady]
              exact Or.inr owned)
            ⟨message.id, message.payload.call⟩ fromOwner]
  unfold ReactiveApplication.round
  rw [environments, observed, PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro command selected
  unfold ReactiveApplication.dispatch
  cases command with
  | activate actor =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, ReactiveApplication.Execution.activation_samples,
        PMF.bind_map, PMF.map_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro sample sampled
      let leftActive := left.sampledActivation app actor sample
      let rightActive := right.sampledActivation app actor sample
      have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
        bindingTraffic_activation
            (serviceRuntime setup mode deadline) leaks left right who actor sameTraffic sample
      have leftRecall : leftActive.recall = left.recall := rfl
      have rightRecall : rightActive.recall = right.recall := rfl
      change ((players first actor (leftActive.recall actor)
          (leftActive.observe app actor)).map (leftActive.respond app actor)).map _ =
        ((players second actor (rightActive.recall actor)
          (rightActive.observe app actor)).map (rightActive.respond app actor)).map _
      by_cases isOwner : actor = owner
      · subst actor
        obtain ⟨leftResponse, rightResponse, leftPure, rightPure, submitted, traffic⟩ :=
          matched (by rw [environments, observed]; exact selected) sample
            (by rw [networks]; exact sampled)
        simp only [players, Function.update_self]
        rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
        apply congrArg PMF.pure
        obtain ⟨leftEmitted, leftRecalled, _⟩ := respond_recall_self setup leaks leftActive owner
          leftResponse
        obtain ⟨rightEmitted, rightRecalled, _⟩ := respond_recall_self setup leaks rightActive
          owner rightResponse
        refine Prod.ext traffic (Prod.ext ?_ ?_)
        · change ownerTurns owner event (leftActive.respond app owner leftResponse) =
            ownerTurns owner event (rightActive.respond app owner rightResponse)
          unfold ownerTurns
          rw [leftRecalled, rightRecalled, leftRecall, rightRecall, List.countP_append,
            List.countP_append]
          unfold ownerTurns at sameTurns
          rw [sameTurns]
          congr 1
          have activeViews :
              (leftActive.observe
                  (serviceApplication setup mode deadline leaks) owner).application.publicView =
                (rightActive.observe
                    (serviceApplication setup mode deadline leaks) owner).application.publicView :=
            publics
          simp only [List.countP_singleton]
          rw [activeViews]
        · change (serviceRuntime setup mode deadline).eventRecorded leaks
              ((leftActive.respond app owner leftResponse).recall owner) event =
            (serviceRuntime setup mode deadline).eventRecorded leaks
              ((rightActive.respond app owner rightResponse).recall owner) event
          unfold EventGraphRuntime.eventRecorded
          rw [leftRecalled, rightRecalled, leftRecall, rightRecall, List.any_append,
            List.any_append]
          unfold EventGraphRuntime.eventRecorded at sameRecorded
          rw [sameRecorded]
          simp only [List.any_cons, List.any_nil, Bool.or_false, submitted]
      · by_cases isWho : actor = who
        · subst actor
          have recalled : leftActive.recall who = rightActive.recall who :=
            congrArg (fun value => value.2.2.2.1) activated
          simp only [players, Function.update_of_ne isOwner, focalPlayers, Function.update_self]
          rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
          apply map_congr_on_support _
          intro response _
          refine Prod.ext (bindingTraffic_owner_response
              (serviceRuntime setup mode deadline) leaks leftActive
            rightActive who activated response) ?_
          change (ownerTurns owner event (leftActive.respond app who response),
              (serviceRuntime setup mode deadline).eventRecorded leaks
                ((leftActive.respond app who response).recall owner) event) =
            (ownerTurns owner event (rightActive.respond app who response),
              (serviceRuntime setup mode deadline).eventRecorded leaks
                ((rightActive.respond app who response).recall owner) event)
          unfold ownerTurns
          rw [app.respond_recall_other leftActive who owner (Ne.symm isOwner) response,
            app.respond_recall_other rightActive who owner (Ne.symm isOwner) response,
            leftRecall, rightRecall]
          unfold ownerTurns at sameTurns
          rw [sameTurns, sameRecorded]
        · simp only [players, Function.update_of_ne isOwner, focalPlayers,
            Function.update_of_ne isWho, ReactiveApplication.silentPolicy_apply, PMF.pure_map]
          apply congrArg PMF.pure
          refine Prod.ext (bindingTraffic_silent
              (serviceRuntime setup mode deadline) leaks leftActive rightActive who
            actor activated ⟨none⟩ rfl) ?_
          change (ownerTurns owner event (leftActive.respond app actor ⟨none⟩),
              (serviceRuntime setup mode deadline).eventRecorded leaks
                ((leftActive.respond app actor ⟨none⟩).recall owner) event) =
            (ownerTurns owner event (rightActive.respond app actor ⟨none⟩),
              (serviceRuntime setup mode deadline).eventRecorded leaks
                ((rightActive.respond app actor ⟨none⟩).recall owner) event)
          unfold ownerTurns
          rw [app.respond_recall_other leftActive actor owner (Ne.symm isOwner) _,
            app.respond_recall_other rightActive actor owner (Ne.symm isOwner) _,
            leftRecall, rightRecall]
          unfold ownerTurns at sameTurns
          rw [sameTurns, sameRecorded]
  | «include» id =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      have includedTraffic := includeTraffic id
      have leftKeeps : (left.includePending app id).recall = left.recall := by
        unfold ReactiveApplication.Execution.includePending
        generalize left.network.includePending id = pair
        rcases pair with ⟨_ | _, _⟩ <;> rfl
      have rightKeeps : (right.includePending app id).recall = right.recall := by
        unfold ReactiveApplication.Execution.includePending
        generalize right.network.includePending id = pair
        rcases pair with ⟨_ | _, _⟩ <;> rfl
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · change (serviceRuntime setup mode deadline).bindingTraffic leaks who
            { left.includePending app id with environmentRecall := _ } =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who
            { right.includePending app id with environmentRecall := _ }
        rw [environments, observed]
        exact bindingTraffic_with_environmentRecall who includedTraffic _
      · change ownerTurns owner event { left.includePending app id with environmentRecall := _ } =
          ownerTurns owner event { right.includePending app id with environmentRecall := _ }
        unfold ownerTurns
        change ((left.includePending app id).recall owner).countP _ =
          ((right.includePending app id).recall owner).countP _
        rw [leftKeeps, rightKeeps]
        exact sameTurns
      · change (serviceRuntime setup mode deadline).eventRecorded leaks
          ((left.includePending app id).recall owner)
            event = (serviceRuntime setup mode deadline).eventRecorded leaks
            ((right.includePending app id).recall owner) event
        rw [leftKeeps, rightKeeps]
        exact sameRecorded
  | application command =>
      change ((left.environmentStep app (.application command)).bind
          (app.resume (players first) none)).map _ =
        ((right.environmentStep app (.application command)).bind
          (app.resume (players second) none)).map _
      rw [show app.resume (players first) none = PMF.pure from rfl,
        show app.resume (players second) none = PMF.pure from rfl, PMF.bind_pure, PMF.bind_pure,
        kept left _ (fun next reached => by
          rw [app.environmentStep_recall left next _ reached]),
        kept right _ (fun next reached => by
          rw [app.environmentStep_recall right next _ reached]),
        application_environmentStep_traffic_congr sameTraffic command]
      unfold ownerTurns at sameTurns ⊢
      rw [sameTurns, sameRecorded]
  | wait =>
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
      apply congrArg PMF.pure
      refine Prod.ext (bindingTraffic_record (leaks := leaks) who sameTraffic .wait) ?_
      change (ownerTurns owner event left, (serviceRuntime setup mode deadline).eventRecorded leaks
          (left.recall owner) event) =
        (ownerTurns owner event right, (serviceRuntime setup mode deadline).eventRecorded leaks
          (right.recall owner) event)
      rw [sameTurns, sameRecorded]

end Round

section Decided

/-- **The decided run.** Facts along the phase in which `owner` decides
`action` at its first turn at `event` from the boundary `start`, with `count`
rounds still to run: a raw trace, the decided-phase facts, the owner's
submissions at its turns, answered activations, an unchanged configuration
until the event completes, and the owner's used slots while it has not yet had
a turn at the event. -/
structure DecidedRun (horizon : Nat) (scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat) (start :
        (serviceApplication setup mode deadline leaks).Execution)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (action :
        (serviceGraph setup mode).Action event)
    (count : Nat) (execution :
        (serviceApplication setup mode deadline leaks).Execution) : Prop where
  trace : ∃ remaining, Nonempty (((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon
    scheduler).Trace (some ⟨remaining + count, none, execution⟩))
  phase : DecidedPhase delay bound start owner event action execution
  own : OwnSubmissionsAtTurn setup leaks execution owner
  answered : ActivationsAnswered setup leaks execution
  config : execution.application.config = start.application.config ∨
    event ∈ execution.application.config.cut.completed
  slots : ownerTurns owner event execution = 0 → CanonicalSlotsUsed setup leaks execution owner

/-- A running decided run is at the boundary configuration. -/
theorem DecidedRun.same {horizon : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat} {start :
        (serviceApplication setup mode deadline leaks).Execution}
    {owner : Player} {event : (serviceGraph setup mode).EventId} {action :
        (serviceGraph setup mode).Action event}
    {count : Nat} {execution : (serviceApplication setup mode deadline leaks).Execution}
    (run : DecidedRun horizon scheduler delay bound start owner event action count execution)
    (running : event ∉ execution.application.config.cut.completed) :
    execution.application.config = start.application.config := by
  rcases run.config with same | done
  · exact same
  · exact (running done).elim

/-- **The decided run is kept** by every round before completion, whatever the
other players do. -/
theorem DecidedRun.round {horizon : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    {start : (serviceApplication setup mode deadline leaks).Execution} {owner : Player}
    {event : (serviceGraph setup mode).EventId} {action : (serviceGraph setup mode).Action event}
    (untouched : Untouched setup leaks event start)
    (ready : start.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (effective : EffectiveAction start.application.config event action)
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    (follows : players owner = decidedTurnPolicy setup leaks bound owner event action)
    {count : Nat} {execution next : (serviceApplication setup mode deadline leaks).Execution}
    (run : DecidedRun horizon scheduler delay bound start owner event action (count + 1)
      execution)
    (running : event ∉ execution.application.config.cut.completed)
    (reached : next ∈
        ((serviceApplication setup mode deadline leaks).round scheduler players
          execution).support) :
    DecidedRun horizon scheduler delay bound start owner event action count next := by
  let app := serviceApplication setup mode deadline leaks
  have same := run.same running
  obtain ⟨remaining, ⟨trace⟩⟩ := run.trace
  rw [show remaining + (count + 1) = (remaining + count) + 1 by omega] at trace
  obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler players
    (remaining + count) execution next trace reached
  have atTurn : SubmitsAtTurn setup leaks (players owner) owner := by
    rw [follows]
    exact decidedTurnPolicy_submitsAtTurn setup leaks bound owner event action
  refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_, round_ownSubmissionsAtTurn setup leaks atTurn run.own
    reached, round_activationsAnswered setup leaks run.answered reached, ?_, ?_⟩
  · exact run.phase.round contract timely trace run.own run.answered same ready owned effective
      follows reached
  · by_cases unchanged : next.application.config = start.application.config
    · exact Or.inl unchanged
    · right
      have completed := run.phase.complete_round contract timely trace run.own run.answered
        untouched same ready owned alone reached unchanged
      rw [start.application.config.step_cut event ready action _ completed,
        EventOrder.Cut.mem_complete]
      exact Or.inl rfl
  · intro fresh
    obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
    have recallEq := app.environmentStep_recall execution middle command moved
    have middleSlots (first : ownerTurns owner event execution = 0) :
        CanonicalSlotsUsed setup leaks middle owner :=
      canonicalSlotsUsed_environment moved owner (run.slots first)
    rcases cases with ⟨_, rfl⟩ | ⟨responder, active, response, _, rfl⟩
    · apply middleSlots
      unfold ownerTurns at fresh ⊢
      rw [← recallEq]
      exact fresh
    · by_cases isOwner : responder = owner
      · exfalso
        subst responder
        have activate : command = .activate owner := by
          cases command with
          | activate actor => cases active; rfl
          | «include» => cases active
          | application => cases active
          | wait => cases active
        subst activate
        have sameApp := activation_application setup leaks execution middle owner moved
        obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle owner response
        unfold ownerTurns at fresh
        rw [recalled, List.countP_append, recallEq] at fresh
        have turn : (middle.observe (serviceApplication setup mode deadline leaks)
            owner).application.publicView.ownTurn? owner = some event := by
          change middle.application.publicView.ownTurn? owner = some event
          rw [sameApp]
          exact serviceOwnTurn?_of_ready setup execution.application (by rw [same]; exact ready)
            owned
        simp only [List.countP_singleton, turn, decide_true, ↓reduceIte] at fresh
        omega
      · have different : owner ≠ responder := fun equal => isOwner equal.symm
        apply canonicalSlotsUsed_respond_other middle different response
        apply middleSlots
        unfold ownerTurns at fresh ⊢
        rw [app.respond_recall_other middle responder owner different, recallEq] at fresh
        exact fresh

end Decided

section Binding

/-- **The decided run starts at the boundary.** At a completion boundary of any
players at which the owner of the ready event submitted only at its turns and
has used only its counted slots, the decided run holds with all rounds to the
horizon still to run. -/
theorem DecidedRun.initial {horizon : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    {reachers : Player → (serviceApplication setup mode deadline leaks).Policy}
    {event : (serviceGraph setup mode).EventId} (start :
        (serviceApplication setup mode deadline leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler reachers event.val start)
    (bounded : start.environmentRecall.length ≤ horizon) (owner : Player)
    (ownStart : OwnSubmissionsAtTurn setup leaks start owner)
    (slotsStart : CanonicalSlotsUsed setup leaks start owner)
    (action : (serviceGraph setup mode).Action event) :
    DecidedRun horizon scheduler delay bound start owner event action
      (horizon - start.environmentRecall.length) start := by
  obtain ⟨trace⟩ := (serviceApplication setup mode deadline leaks).raw_trace_roundsFrom
      (serviceInitialLaw setup mode) horizon
    scheduler reachers _ bounded start boundary.supported
  exact ⟨⟨0, ⟨by simpa only [Nat.zero_add] using trace⟩⟩,
    DecidedPhase.initial delay bound action (boundary.untouched event le_rfl) ownStart,
    ownStart, roundsFrom_activationsAnswered _ start boundary.supported, Or.inl rfl,
    fun _ => slotsStart⟩

end Binding

section Disclosure

/-- An opening of a valid handle for a ready disclosure is handled alike for
any observer whose views agree, when both states hold the same opened value:
acceptance reads only public fields, the owner's verified candidate and the
bound value, and the result publishes that value through public guards. -/
theorem handle_opening_playerView_congr {event : (serviceGraph setup mode).EventId} {owner : Player}
    {payload : L.Ty} {binding : EventGraph.FieldRef (serviceGraph setup mode).layout
        (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView
        (serviceGraph setup mode) event = .resolve owner payload binding checks outputEq codeEq)
    (left right : EventGraphRuntime.State (serviceGraph setup mode)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (id : MessageId Player) (sender : id.1 = owner) (candidate : Handle (serviceGraph setup mode))
    (handleOwner : candidate.1 = owner) (value : L.Val payload)
    (leftValid : left.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (rightValid : right.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value)) :
    Option.map (fun state => state.playerView focal)
        (handle (serviceRuntime setup mode deadline) left ⟨id, .opening event candidate ⟨payload,
            value⟩⟩) =
      Option.map (fun state => state.playerView focal)
        (handle (serviceRuntime setup mode deadline) right ⟨id, .opening event candidate
            ⟨payload, value⟩⟩) := by
  have publics : left.publicView = right.publicView := congrArg PlayerView.publicView views
  have accepted : left.accepted = right.accepted := congrArg PublicView.accepted publics
  have clocks : left.clock = right.clock := congrArg PublicView.clock publics
  have activations : left.activatedAt = right.activatedAt :=
    congrArg PublicView.activatedAt publics
  have stores : (serviceGraph setup mode).publicStore left.config.store =
      (serviceGraph setup mode).publicStore right.config.store :=
    congrArg (fun view : PublicView (serviceGraph setup mode) => view.observation.store) publics
  have resolveEq : EventGraph.EventCode.resolveOutput? binding checks true left.config.store =
      EventGraph.EventCode.resolveOutput? binding checks true right.config.store := by
    unfold EventGraph.EventCode.resolveOutput?
    rw [leftStored, rightStored]
    simp only [Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
    rw [← EventGraph.GuardCheck.allAccepted?_publicStore checks left.config.store,
      ← EventGraph.GuardCheck.allAccepted?_publicStore checks right.config.store, stores]
  by_cases timely : left.WithinDeadline (serviceRuntime setup mode deadline) event
  · have rightTimely : right.WithinDeadline (serviceRuntime setup mode deadline) event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    by_cases associated : left.accepted binding.field = some candidate
    · have rightAssociated : right.accepted binding.field = some candidate := by
        rw [← accepted]
        exact associated
      have available : (EventGraph.EventCode.resolveOutput? binding checks true
          left.config.store).isSome = true := by
        apply EventGraph.EventCode.resolveOutput?_isSome
        intro field member
        apply left.config.read_available leftReady
        rw [← EventGraph.EventCode.readFields_cast outputEq
            ((serviceGraph setup mode).nodes event), codeEq]
        exact member
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp available
      rw [handle_opening_eq
          (serviceRuntime setup mode deadline) left id event candidate owner payload binding checks
          outputEq codeEq node leftReady timely sender handleOwner associated value leftValid
          leftStored result resolved,
        handle_opening_eq
            (serviceRuntime setup mode deadline) right id event candidate owner payload
              binding checks
          outputEq codeEq node rightReady rightTimely sender handleOwner rightAssociated value
          rightValid rightStored result (resolveEq ▸ resolved)]
      simp only [Option.map_some]
      exact congrArg some (State.complete_playerView_congr left right focal publics
        (left.playerView_observation_eq right focal views) (congrArg PlayerView.candidates views)
        event leftReady rightReady _ _ _ _ (fun _ => rfl) (fun _ => rfl))
    · have rightUnassociated : ¬ right.accepted binding.field = some candidate := by
        rw [← accepted]
        exact associated
      simp [handle, leftReady, rightReady, timely, rightTimely, node, Message.sender, sender,
        handleOwner, associated, rightUnassociated]
  · have rightLate : ¬ right.WithinDeadline (serviceRuntime setup mode deadline) event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    simp [handle, leftReady, rightReady, timely, rightLate]

/-- At an unrecorded first turn that fits the deadline, a decided effective
disclosure of `true` transmits the certified opening of the accepted handle with
the bound value. -/
theorem decidedReveal_response {horizon : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView
        (serviceGraph setup mode) event = .resolve owner payload binding checks outputEq codeEq)
    (value : L.Val payload) {remaining : Nat} {current :
        (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩))
    (ready : current.application.config.cut.Ready event)
    (resolved : EventGraph.EventCode.resolveOutput? binding checks true
      current.application.config.store = some (.success value))
    (selected : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
        (scheduler
      current.environmentRecall (current.observeEnvironment
          (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈
      ((serviceApplication setup mode deadline leaks).observePending
        owner current.network.pending).support)
    (first : ownerTurns owner event current = 0)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (current.recall owner) event = false)
    (fits : current.application.publicView.InclusionFitsDeadline
        (serviceRuntime setup mode deadline) bound event) :
    let app := serviceApplication setup mode deadline leaks
    let active := current.sampledActivation app owner sample
    ∃ handle material, current.application.accepted binding.field = some handle ∧
      decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) true) (active.recall owner)
          (active.observe app owner) = PMF.pure ⟨some material⟩ ∧
      app.packet (app.submit active.application owner material) owner
          (active.network.known owner) material =
        ⟨.opening event handle ⟨payload, value⟩, some ⟨handle, ⟨payload, value⟩⟩,
          current.application.publicView.tokenFor (.opening event handle ⟨payload, value⟩)⟩ := by
  intro app active
  have owned :
      (serviceGraph setup mode).actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  have moved : active ∈ (current.environmentStep app (.activate owner)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, sampled, rfl⟩
  obtain ⟨activeTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon scheduler
    remaining current active (.activate owner) trace selected moved
  have facts := legalFacts setup leaks horizon scheduler _ activeTrace
  have stored := EventGraph.EventCode.binding_success_of_resolve_success binding checks true
    active.application.config.store value resolved
  obtain ⟨handle, associated, handleOwner, fixed⟩ :=
    facts.binding.success_provenance binding value stored
  have decision :=
      ((serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks owner
    (active.recall owner) (active.observe app owner) event _
    (fun _ _ _ _ bind => by rw [node] at bind; cases bind)).trans
      ((serviceRuntime setup mode deadline).serviceDecision_successful_opening leaks
        active facts.inputs
        owner event payload binding checks outputEq codeEq node handle value associated
        handleOwner fixed resolved)
  let material : app.Submission :=
    (disclosureSubmission (.opening event handle ⟨payload, value⟩)).normalizeReactive owner
      (app.observePlayer active.application owner) (active.network.known owner)
  refine ⟨handle, material, associated, ?_, ?_⟩
  · rw [decidedTurnPolicy_open _ active ready owned first,
      decidedOpportunity_transmits _ active unrecorded fits material decision]
  · have emitted := WitnessedSubmission.normalizeReactive_emit
      (serviceRuntime setup mode deadline) leaks
      active.application owner (active.network.known owner)
        (disclosureSubmission (.opening event handle ⟨payload, value⟩))
    have packet :=
        (serviceRuntime setup mode deadline).windowOpening_packet leaks owner event handle
      ⟨payload, value⟩ active.application (active.network.known owner) handleOwner fixed
    exact emitted.trans packet

/-- A decided disclosure of `false` is silent at every input. -/
theorem decidedReveal_silent {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView
        (serviceGraph setup mode) event = .resolve owner payload binding checks outputEq codeEq)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event) :
    decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)
        (execution.recall owner) (execution.observe
            (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨none⟩ := by
  have owned :
      (serviceGraph setup mode).actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  by_cases opened : ownerTurns owner event execution = 0 ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks
          (execution.recall owner) event = false ∧
      execution.application.publicView.InclusionFitsDeadline
          (serviceRuntime setup mode deadline) bound event
  · rw [decidedTurnPolicy_open _ execution ready owned opened.1]
    apply decidedOpportunity_silent
    apply canonicalServiceDecision_silent
    unfold SilentAction
    rw [node]
    simp only [cast_cast, cast_eq]
  · exact decidedTurnPolicy_closed _ execution ready owned opened

/-- A transmitted response names the event of the packet it emits. -/
theorem submittedEvent_some_eq_packet (material :
    (serviceApplication setup mode deadline leaks).Submission)
    (state : EventGraphRuntime.State (serviceGraph setup mode)) (who : Player)
    (known : List (Message Player (WitnessedPacket (serviceGraph setup mode)))) :
    (serviceRuntime setup mode deadline).submittedEvent? leaks ⟨some material⟩ =
      ((serviceApplication setup mode deadline leaks).packet state who known
        material).call.event? (serviceGraph setup mode) :=
  rfl

/-- Along a decided disclosure run, every pending opening of the owner for the
event opens the owner's verified handle with the value bound at the boundary. -/
theorem DecidedRun.opening_valid {horizon : Nat} {scheduler :
    (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat} {start :
        (serviceApplication setup mode deadline leaks).Execution}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView
        (serviceGraph setup mode) event = .resolve owner payload binding checks outputEq codeEq)
    {action : (serviceGraph setup mode).Action event} {count : Nat}
    {current : (serviceApplication setup mode deadline leaks).Execution}
    (run : DecidedRun horizon scheduler delay bound start owner event action count current)
    (running : event ∉ current.application.config.cut.completed)
    (id : MessageId Player) (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (found : current.network.lookup id = some message) (sender : message.sender = owner)
    (candidate : Handle (serviceGraph setup mode)) (raw : Raw L)
    (call : message.payload.call = .opening event candidate raw) :
    ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧ candidate.1 = owner ∧
      current.application.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
      binding.get? current.application.config.store = some (.success value) := by
  obtain ⟨remaining, ⟨trace⟩⟩ := run.trace
  have facts := legalFacts setup leaks horizon scheduler _ trace
  obtain ⟨entry, member, material, transmission, emittedEq, _, _, packet⟩ :=
    facts.provenance.pending message (List.mem_of_find?_eq_some found)
  rw [sender] at member
  have submitted :
      (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action = some event := by
    rw [issued_submittedEvent transmission packet, call]
    rfl
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  obtain ⟨packetMessage, emittedP, _, realized⟩ :=
    run.phase.submitted before entry after split submitted
  rw [emittedEq] at emittedP
  cases Option.some.inj emittedP
  unfold RealizesAt at realized
  rw [node] at realized
  obtain ⟨_, handle, value, callEq, handleOwner, _, fixed, stored, _⟩ := realized
  rw [call] at callEq
  injection callEq with _ handleEq rawEq
  subst handleEq rawEq
  refine ⟨value, rfl, handleOwner, fixed, ?_⟩
  rw [run.same running]
  exact stored

/-- **Another owner's disclosure phase.** While another player's disclosure
event is the ready event, let the owner decide the same disclosure at its first
turn on each of two executions, while the deviator plays against silence; when
it discloses, let both boundaries bind the same value, which then publishes.
From equal compared readouts the two stopped runs have equal laws of the
compared readout. -/
theorem decidedReveal_readout_congr {horizon : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (who : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (foreign : owner ≠ who)
    (node : nodeView
        (serviceGraph setup mode) event = .resolve owner payload binding checks outputEq
      codeEq)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (serviceApplication setup mode deadline leaks).Execution)
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftUntouched : Untouched setup leaks event leftStart)
    (rightUntouched : Untouched setup leaks event rightStart)
    (disclose : Bool)
    (published : disclose = true → ∃ value : L.Val payload,
      EventGraph.EventCode.resolveOutput? binding checks true leftStart.application.config.store =
          some (.success value) ∧
        EventGraph.EventCode.resolveOutput? binding checks true
          rightStart.application.config.store = some (.success value)) :
    let action := cast (congrArg EventGraph.EventField.Action outputEq.symm) disclose
    ∀ count left right,
      DecidedRun horizon scheduler delay bound leftStart owner event action count left →
      DecidedRun horizon scheduler delay bound rightStart owner event action count right →
      foreignReadout (leaks := leaks) who owner event left =
        foreignReadout (leaks := leaks) who owner event right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (Function.update (focalPlayers setup leaks who deviation) owner
            (decidedTurnPolicy setup leaks bound owner event action))
          (fun final => event ∈ final.application.config.cut.completed) count left).map
          (foreignReadout (leaks := leaks) who owner event) =
        ((serviceApplication setup mode deadline leaks).runUntil scheduler
          (Function.update (focalPlayers setup leaks who deviation) owner
            (decidedTurnPolicy setup leaks bound owner event action))
          (fun final => event ∈ final.application.config.cut.completed) count right).map
          (foreignReadout (leaks := leaks) who owner event) := by
  intro action
  let app := serviceApplication setup mode deadline leaks
  have owned :
      (serviceGraph setup mode).actor? event = some owner := nodeView_resolve_actor outputEq codeEq
  have effectiveOf (start : app.Execution)
      (side : disclose = true → ∃ value : L.Val payload,
        EventGraph.EventCode.resolveOutput? binding checks true start.application.config.store =
          some (.success value)) :
      EffectiveAction start.application.config event action := by
    unfold EffectiveAction
    rw [node]
    intro isTrue
    simp only [action, cast_cast, cast_eq] at isTrue
    exact side isTrue
  have leftEffective := effectiveOf leftStart fun isTrue =>
    (published isTrue).elim fun value both => ⟨value, both.1⟩
  have rightEffective := effectiveOf rightStart fun isTrue =>
    (published isTrue).elim fun value both => ⟨value, both.2⟩
  have trafficOf {left right : app.Execution}
      (same : foreignReadout (leaks := leaks) who owner event left =
        foreignReadout (leaks := leaks) who owner event right) :
      (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who right
          := congrArg Prod.fst same
  apply runUntil_map_congr_of_rounds app scheduler _ _ _ _
    (fun count execution => DecidedRun horizon scheduler delay bound leftStart owner event
      action count execution)
    (fun count execution => DecidedRun horizon scheduler delay bound rightStart owner event
      action count execution)
  · intro n left right _ _ same
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (trafficOf same)
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftRun rightRun same running
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) (trafficOf same)
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have leftSame := leftRun.same running
    have rightSame := rightRun.same rightRunning
    have leftNow : left.application.config.cut.Ready event := by
      rw [leftSame]
      exact leftReady
    have rightNow : right.application.config.cut.Ready event := by
      rw [rightSame]
      exact rightReady
    have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
      congrArg (fun value => value.2.1) same
    have sameRecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (left.recall owner) event =
        (serviceRuntime setup mode deadline).eventRecorded leaks (right.recall owner) event :=
      congrArg (fun value => value.2.2) same
    have views : left.application.playerView who = right.application.playerView who :=
      congrArg (fun value => value.2.2.2.2.1) (trafficOf same)
    apply foreignRound_readout_congr scheduler who deviation owned foreign alone _ _ leftNow
      rightNow same
    · intro selected sample sampled
      dsimp only
      let leftActive := left.sampledActivation app owner sample
      let rightActive := right.sampledActivation app owner sample
      have leftActiveReady : leftActive.application.config.cut.Ready event := leftNow
      have rightActiveReady : rightActive.application.config.cut.Ready event := rightNow
      have activeTraffic :
          (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
          (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
        bindingTraffic_activation
            (serviceRuntime setup mode deadline) leaks left right who owner (trafficOf same)
          sample
      have rightSelected : (.activate owner : app.Command) ∈ (scheduler
          right.environmentRecall (right.observeEnvironment app)).support := by
        have environments : left.environmentRecall = right.environmentRecall :=
          congrArg (fun value => value.2.2.1) (trafficOf same)
        rw [← environments, ← observeEnvironment_eq_of_bindingTraffic who (trafficOf same)]
        exact selected
      have rightSampled : sample ∈ (app.observePending owner right.network.pending).support := by
        have networks : left.network = right.network := congrArg Prod.fst (trafficOf same)
        rw [← networks]
        exact sampled
      cases disclose with
      | false =>
          refine ⟨⟨none⟩, ⟨none⟩, decidedReveal_silent node leftActive leftActiveReady,
            decidedReveal_silent node rightActive rightActiveReady, rfl, ?_⟩
          exact bindingTraffic_respond_other (Ne.symm foreign) activeTraffic ⟨none⟩ ⟨none⟩
            (Or.inl ⟨rfl, rfl⟩)
      | true =>
          by_cases opened : ownerTurns owner event left = 0 ∧
              (serviceRuntime setup mode deadline).eventRecorded leaks
                  (left.recall owner) event = false ∧
              left.application.publicView.InclusionFitsDeadline
                  (serviceRuntime setup mode deadline) bound event
          · obtain ⟨first, unrecorded, fits⟩ := opened
            have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
            have rightUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
                (right.recall owner)
                event = false := sameRecorded ▸ unrecorded
            have rightFits : right.application.publicView.InclusionFitsDeadline
                (serviceRuntime setup mode deadline)
                bound event := publics ▸ fits
            obtain ⟨value, leftResolved, rightResolved⟩ := published rfl
            obtain ⟨leftRemaining, ⟨leftTrace⟩⟩ := leftRun.trace
            rw [show leftRemaining + (n + 1) = (leftRemaining + n) + 1 by omega] at leftTrace
            obtain ⟨rightRemaining, ⟨rightTrace⟩⟩ := rightRun.trace
            rw [show rightRemaining + (n + 1) = (rightRemaining + n) + 1 by omega] at rightTrace
            obtain ⟨leftHandle, leftMaterial, leftAssociated, leftPolicy, leftPacket⟩ :=
              decidedReveal_response node value leftTrace leftNow
                (by rw [leftSame]; exact leftResolved) selected sample sampled first unrecorded
                fits
            obtain ⟨rightHandle, rightMaterial, rightAssociated, rightPolicy, rightPacket⟩ :=
              decidedReveal_response node value rightTrace rightNow
                (by rw [rightSame]; exact rightResolved) rightSelected sample rightSampled
                rightFirst rightUnrecorded rightFits
            have handles : leftHandle = rightHandle := by
              have accepted : left.application.accepted = right.application.accepted :=
                congrArg PublicView.accepted publics
              rw [accepted] at leftAssociated
              exact Option.some.inj (leftAssociated.symm.trans rightAssociated)
            subst handles
            refine ⟨⟨some leftMaterial⟩, ⟨some rightMaterial⟩, leftPolicy, rightPolicy, ?_, ?_⟩
            · rw [submittedEvent_some_eq_packet leftMaterial
                  (app.submit leftActive.application owner leftMaterial) owner
                  (leftActive.network.known owner),
                submittedEvent_some_eq_packet rightMaterial
                  (app.submit rightActive.application owner rightMaterial) owner
                  (rightActive.network.known owner), leftPacket, rightPacket]
            · exact bindingTraffic_respond_other (Ne.symm foreign) activeTraffic _ _
                (Or.inr ⟨_, _, rfl, rfl, by rw [leftPacket, rightPacket, publics]⟩)
          · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
                (serviceRuntime setup mode deadline).eventRecorded leaks
                    (right.recall owner) event = false ∧
                right.application.publicView.InclusionFitsDeadline
                    (serviceRuntime setup mode deadline) bound
                  event) := by
              rw [← sameTurns, ← sameRecorded, ← publics]
              exact opened
            refine ⟨⟨none⟩, ⟨none⟩, ?_, ?_, rfl, ?_⟩
            · exact decidedTurnPolicy_closed _ leftActive leftActiveReady owned opened
            · exact decidedTurnPolicy_closed _ rightActive rightActiveReady owned rightClosed
            · exact bindingTraffic_respond_other (Ne.symm foreign) activeTraffic ⟨none⟩ ⟨none⟩
                (Or.inl ⟨rfl, rfl⟩)
    · intro id message found sender
      rcases message with ⟨messageId, packet, evidence, token⟩
      cases packet with
      | commitment other candidate =>
          exact handle_commitment_playerView_congr
              (serviceRuntime setup mode deadline) left.application
            right.application who messageId other candidate views
      | malformed raw => simp [handle]
      | opening other candidate raw =>
          change Option.map _ (handle (serviceRuntime setup mode deadline) left.application
              ⟨messageId, .opening other candidate raw⟩) =
            Option.map _ (handle (serviceRuntime setup mode deadline) right.application
              ⟨messageId, .opening other candidate raw⟩)
          by_cases otherReady : left.application.config.cut.Ready other
          · have otherIs : other = event := alone _ other leftNow otherReady
            subst otherIs
            have rightFound : right.network.lookup id =
                some ⟨messageId, ⟨.opening other candidate raw, evidence, token⟩⟩ := by
              have networks : left.network = right.network := congrArg Prod.fst (trafficOf same)
              rw [← networks]
              exact found
            obtain ⟨value, rawEq, handleOwner, leftValid, leftStored⟩ :=
              leftRun.opening_valid node running id _ found sender candidate raw rfl
            obtain ⟨rightValue, rightRawEq, _, rightValid, rightStored⟩ :=
              rightRun.opening_valid node rightRunning id _ rightFound sender candidate raw rfl
            subst rawEq
            have values : rightValue = value := by
              have injected := Raw.mk.inj rightRawEq
              exact (eq_of_heq injected.2).symm
            subst values
            exact handle_opening_playerView_congr node left.application right.application who
              views leftNow rightNow messageId sender candidate handleOwner rightValue leftValid
              rightValid leftStored rightStored
          · have rightNot : ¬ right.application.config.cut.Ready other := by
              rw [← cut_eq_of_publicView_eq publics]
              exact otherReady
            simp [handle, otherReady, rightNot]
  · intro n left leftRun running next reached
    exact leftRun.round contract timely leftUntouched leftReady owned alone leftEffective
      (by simp only [Function.update_self]) running reached
  · intro n right rightRun running next reached
    exact rightRun.round contract timely rightUntouched rightReady owned alone rightEffective
      (by simp only [Function.update_self]) running reached

end Disclosure

end Vegas
