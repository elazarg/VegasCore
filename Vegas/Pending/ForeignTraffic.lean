module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.FocalTraffic
public import Vegas.Pending.ExecutionFacts
public import Vegas.Pending.ReactiveSubmissionRecall
public import Interaction.ReactiveRoundCongruence

@[expose] public section

/-! # Native traffic across another owner's round -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

local notation "app" => reactiveApplication timeouts leaks

/-- The owner's recorded turns at `event`. -/
def ownerTurns (owner : Player) (event : graph.EventId)
    (execution : (app).Execution) : Nat :=
  (execution.logs owner).countP fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? owner = some event)

/-- At the owner's selected event, its input is counted by its recorded turns. -/
theorem serviceTurn_of_turn {owner : Player} {event : graph.EventId}
    (execution : (app).Execution)
    (selected : execution.application.publicView.ownTurn? owner = some event) :
    turnIndex timeouts leaks owner event (execution.logs owner)
        (execution.observe (app) owner) =
      some (ownerTurns owner event execution) := by
  unfold EventGraphRuntime.turnIndex ownerTurns
  split
  · rfl
  · rename_i idle
    exact (idle selected).elim



/-- Another player's response that transmits the same packet as its
counterpart, or is silent with it, keeps equal deviator traffic. -/
theorem bindingTraffic_respond_other {who actor : Player} (different : who ≠ actor)
    {left right : (app).Execution}
    (same : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right)
    (leftResponse rightResponse : (app).Action)
    (packets : (leftResponse.transmission = none ∧ rightResponse.transmission = none) ∨
      ∃ leftMaterial rightMaterial, leftResponse = ⟨some leftMaterial⟩ ∧
        rightResponse = ⟨some rightMaterial⟩ ∧
        (app).packet
            ((app).submit left.application actor
              leftMaterial) actor (left.network.known actor) leftMaterial =
          (app).packet
            ((app).submit right.application actor
              rightMaterial) actor (right.network.known actor) rightMaterial) :
    (bindingTraffic timeouts) leaks who
        (left.respond (app) actor leftResponse) =
      (bindingTraffic timeouts) leaks who
        (right.respond (app) actor rightResponse) := by
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.logs who = right.logs who := congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  have kept (execution : (app).Execution) (response : (app).Action) :
      (execution.respond app actor response).application.playerView who =
        execution.application.playerView who := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some material =>
        exact (submitStep_playerView_other (material.call.register execution.application actor)
          actor who different material.call.packet).trans
            (material.call.register_other execution.application actor who different)
  have afterViews : (left.respond app actor leftResponse).application.playerView who =
      (right.respond app actor rightResponse).application.playerView who := by
    rw [kept, kept, views]
  have afterNetworks : (left.respond app actor leftResponse).network =
      (right.respond app actor rightResponse).network := by
    rcases packets with ⟨leftQuiet, rightQuiet⟩ | ⟨leftMaterial, rightMaterial, rfl, rfl, packet⟩
    · rcases leftResponse with ⟨leftTransmission⟩
      rcases rightResponse with ⟨rightTransmission⟩
      change leftTransmission = none at leftQuiet
      change rightTransmission = none at rightQuiet
      subst leftQuiet rightQuiet
      exact networks
    · simp only [ReactiveApplication.Execution.respond]
      rw [packet, networks]
  refine Prod.ext afterNetworks (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_
    (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))
  · exact receipts
  · exact environments
  · change (left.respond app actor leftResponse).logs who =
      (right.respond app actor rightResponse).logs who
    rw [(app).respond_recall_other left actor who different,
      (app).respond_recall_other right actor who different, recalled]


section Round

/-- The readout compared across the phase of another owner: the deviator's
traffic, the owner's turns at the event and whether the owner has submitted for
it. -/
def foreignReadout (who owner : Player) (event : graph.EventId)
    (execution : (app).Execution) :=
  ((bindingTraffic timeouts) leaks who execution,
      ownerTurns owner event execution,
    (eventRecorded timeouts) leaks (execution.logs owner) event)

/-- A law on which the owner's recall stays that of `execution` has the
compared readout of its traffic. -/
theorem map_foreignReadout_of_recall (who owner : Player) (event :
    graph.EventId)
    (execution : (app).Execution)
    (law : PMF (app).Execution)
    (kept : ∀ next ∈ law.support, next.logs owner = execution.logs owner) :
    law.map (foreignReadout (leaks := leaks) who owner event) =
      (law.map ((bindingTraffic timeouts) leaks who)).map fun
        traffic =>
        (traffic, ownerTurns owner event execution,
          (eventRecorded timeouts) leaks
              (execution.logs owner) event) := by
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
    (app).Scheduler)
    (who : Player) (deviation : (app).Policy)
    {event : graph.EventId} {owner : Player}
    (owned : graph.actor? event = some owner) (foreign : owner ≠ who)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (first second : (app).Policy)
    {left right : (app).Execution}
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (same : foreignReadout (leaks := leaks) who owner event left =
      foreignReadout (leaks := leaks) who owner event right)
    (matched : (.activate owner : (app).Command) ∈
        (scheduler
        left.environmentRecall (left.observeEnvironment
            (app))).support →
      ∀ sample ∈
          ((app).observePending
            owner left.network.pending).support,
      let leftActive := left.sampledActivation
          (app) owner sample
      let rightActive := right.sampledActivation
          (app) owner sample
      ∃ leftResponse rightResponse,
        first (leftActive.logs owner)
            (leftActive.observe
                (app) owner) = PMF.pure leftResponse ∧
        second (rightActive.logs owner)
            (rightActive.observe
                (app) owner) = PMF.pure rightResponse ∧
        (submittedEvent? timeouts) leaks leftResponse =
          (submittedEvent? timeouts) leaks rightResponse ∧
        (bindingTraffic timeouts) leaks who
            (leftActive.respond (app) owner leftResponse) =
          (bindingTraffic timeouts) leaks who
            (rightActive.respond
                (app) owner rightResponse))
    (included : ∀ id message, left.network.lookup id = some message →
      message.sender = owner →
      Option.map (fun state => state.playerView who)
          (handle timeouts left.application ⟨message.id,
              message.payload.call⟩) =
        Option.map (fun state => state.playerView who)
          (handle timeouts right.application ⟨message.id,
              message.payload.call⟩)) :
    ((app).round scheduler
        (Function.update
          (focalPlayers timeouts leaks who deviation) owner first)
        left).map
        (foreignReadout (leaks := leaks) who owner event) =
      ((app).round scheduler
        (Function.update
          (focalPlayers timeouts leaks who deviation) owner second)
        right).map
        (foreignReadout (leaks := leaks) who owner event) := by
  let players := fun policy : (app).Policy =>
    Function.update
      (focalPlayers timeouts leaks who deviation) owner policy
  have sameTraffic : (bindingTraffic timeouts) leaks who left =
      (bindingTraffic timeouts) leaks who right := congrArg
        Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : (eventRecorded timeouts) leaks
      (left.logs owner) event =
      (eventRecorded timeouts) leaks (right.logs owner) event :=
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
  have kept (execution : (app).Execution) (law : PMF (app).Execution)
      (unchanged : ∀ next ∈ law.support, next.logs owner = execution.logs owner) :=
    map_foreignReadout_of_recall (leaks := leaks) who owner event execution law unchanged
  -- Including a pending packet keeps equal deviator traffic.
  have includeTraffic (id : MessageId Player) :
      (bindingTraffic timeouts) leaks who (left.includePending app
        id) =
        (bindingTraffic timeouts) leaks who
            (right.includePending app id) := by
    apply include_bindingTraffic_of_handled sameTraffic id
    intro message found
    by_cases fromWho : message.sender = who
    · exact handle_playerView_congr_of_sender timeouts left.application
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
  refine (app).round_map_congr scheduler _ _ left right _ environments observed networks ?_ ?_
  · intro actor selected sample sampled
    let leftActive := left.sampledActivation app actor sample
    let rightActive := right.sampledActivation app actor sample
    have activated : (bindingTraffic timeouts) leaks who leftActive =
        (bindingTraffic timeouts) leaks who rightActive :=
      bindingTraffic_activation
          timeouts leaks left right who actor sameTraffic sample
    have leftRecall : leftActive.logs = left.logs := rfl
    have rightRecall : rightActive.logs = right.logs := rfl
    change ((players first actor (leftActive.logs actor)
        (leftActive.observe app actor)).map (leftActive.respond app actor)).map _ =
      ((players second actor (rightActive.logs actor)
        (rightActive.observe app actor)).map (rightActive.respond app actor)).map _
    by_cases isOwner : actor = owner
    · subst actor
      obtain ⟨leftResponse, rightResponse, leftPure, rightPure, submitted, traffic⟩ :=
        matched (by rw [environments, observed]; exact selected) sample
          (by rw [networks]; exact sampled)
      simp only [players, Function.update_self]
      rw [leftPure, rightPure, PMF.pure_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]
      apply congrArg PMF.pure
      obtain ⟨leftEmitted, leftRecalled, _⟩ := respond_recall_self _ leaks leftActive owner
        leftResponse
      obtain ⟨rightEmitted, rightRecalled, _⟩ := respond_recall_self _ leaks rightActive
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
                (app) owner).application.publicView =
              (rightActive.observe
                  (app) owner).application.publicView :=
          publics
        simp only [List.countP_singleton]
        rw [activeViews]
      · change (eventRecorded timeouts) leaks
            ((leftActive.respond app owner leftResponse).logs owner) event =
          (eventRecorded timeouts) leaks
            ((rightActive.respond app owner rightResponse).logs owner) event
        unfold EventGraphRuntime.eventRecorded
        rw [leftRecalled, rightRecalled, leftRecall, rightRecall, List.any_append,
          List.any_append]
        unfold EventGraphRuntime.eventRecorded at sameRecorded
        rw [sameRecorded]
        simp only [List.any_cons, List.any_nil, Bool.or_false, submitted]
    · by_cases isWho : actor = who
      · subst actor
        have recalled : leftActive.logs who = rightActive.logs who :=
          congrArg (fun value => value.2.2.2.1) activated
        simp only [players, Function.update_of_ne isOwner, focalPlayers, Function.update_self]
        rw [recalled, observe_eq_of_bindingTraffic who activated, PMF.map_comp, PMF.map_comp]
        apply map_congr_on_support _
        intro response _
        refine Prod.ext (bindingTraffic_owner_response
            timeouts leaks leftActive
          rightActive who activated response) ?_
        change (ownerTurns owner event (leftActive.respond app who response),
            (eventRecorded timeouts) leaks
              ((leftActive.respond app who response).logs owner) event) =
          (ownerTurns owner event (rightActive.respond app who response),
            (eventRecorded timeouts) leaks
              ((rightActive.respond app who response).logs owner) event)
        unfold ownerTurns
        rw [(app).respond_recall_other leftActive who owner (Ne.symm isOwner) response,
          (app).respond_recall_other rightActive who owner (Ne.symm isOwner) response,
          leftRecall, rightRecall]
        unfold ownerTurns at sameTurns
        rw [sameTurns, sameRecorded]
      · simp only [players, Function.update_of_ne isOwner, focalPlayers,
          Function.update_of_ne isWho, ReactiveApplication.silentPolicy_apply, PMF.pure_map]
        apply congrArg PMF.pure
        refine Prod.ext (bindingTraffic_silent
            timeouts leaks leftActive rightActive who
          actor activated ⟨none⟩ rfl) ?_
        change (ownerTurns owner event (leftActive.respond app actor ⟨none⟩),
            (eventRecorded timeouts) leaks
              ((leftActive.respond app actor ⟨none⟩).logs owner) event) =
          (ownerTurns owner event (rightActive.respond app actor ⟨none⟩),
            (eventRecorded timeouts) leaks
              ((rightActive.respond app actor ⟨none⟩).logs owner) event)
        unfold ownerTurns
        rw [(app).respond_recall_other leftActive actor owner (Ne.symm isOwner) _,
          (app).respond_recall_other rightActive actor owner (Ne.symm isOwner) _,
          leftRecall, rightRecall]
        unfold ownerTurns at sameTurns
        rw [sameTurns, sameRecorded]
  · intro command selected inactive
    cases command with
    | activate actor => cases inactive
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        have includedTraffic := includeTraffic id
        have leftKeeps := ReactiveApplication.Execution.includePending_recall app left id
        have rightKeeps := ReactiveApplication.Execution.includePending_recall app right id
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · change (bindingTraffic timeouts) leaks who
              { left.includePending app id with environmentRecall := _ } =
            (bindingTraffic timeouts) leaks who
              { right.includePending app id with environmentRecall := _ }
          rw [environments, observed]
          exact bindingTraffic_with_environmentRecall who includedTraffic _
        · change ownerTurns owner event { left.includePending app id with environmentRecall := _ } =
            ownerTurns owner event { right.includePending app id with environmentRecall := _ }
          unfold ownerTurns
          change ((left.includePending app id).logs owner).countP _ =
            ((right.includePending app id).logs owner).countP _
          rw [leftKeeps, rightKeeps]
          exact sameTurns
        · change (eventRecorded timeouts) leaks
            ((left.includePending app id).logs owner)
              event = (eventRecorded timeouts) leaks
              ((right.includePending app id).logs owner) event
          rw [leftKeeps, rightKeeps]
          exact sameRecorded
    | application command =>
        rw [kept left _ (fun next reached => by
            rw [(app).environmentStep_recall left next _ reached]),
          kept right _ (fun next reached => by
            rw [(app).environmentStep_recall right next _ reached]),
          application_environmentStep_traffic_congr sameTraffic command]
        unfold ownerTurns at sameTurns ⊢
        rw [sameTurns, sameRecorded]
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        refine Prod.ext (bindingTraffic_record (leaks := leaks) who sameTraffic .wait) ?_
        change (ownerTurns owner event left,
          (eventRecorded timeouts) leaks
            (left.logs owner) event) =
          (ownerTurns owner event right, (eventRecorded timeouts) leaks
            (right.logs owner) event)
        rw [sameTurns, sameRecorded]

end Round

end Vegas.EventGraphRuntime
