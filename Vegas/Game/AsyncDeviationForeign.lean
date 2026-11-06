/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFirstTurnCompletion
import Vegas.Game.SourceServiceDeviationChoice
import Vegas.Game.SourceServiceCanonicalSlots
import Interaction.ReactiveRoundCongruence
import Vegas.Pending.EventActivationOrigin
import Vegas.Pending.EventBindingInvariant
import Vegas.Pending.ReactiveGuardedResponse

/-! # Foreign source choices and native traffic

An honest foreign owner decides once at its first ready callback. The focal
player's traffic is compared through actual native rounds and automatic completion;
public omission stays distinct from an accepted opaque binding. The comparison
uses actual recall, initialized binding provenance and the sole native executor.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The owner's recorded turns at `event`. -/
def ownerTurns (owner : Player) (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) : Nat :=
  (execution.logs owner).countP fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? owner = some event)

/-- While `event` is ready, an input of its owner is its turn there, counted
by the owner's recorded turns. -/
theorem serviceTurn_of_ready {owner : Player} {event : (serviceGraph setup mode).EventId}
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    serviceTurn setup mode deadline leaks owner event (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      some (ownerTurns owner event execution) := by
  unfold serviceTurn ownerTurns
  split
  · rfl
  · rename_i idle
    exact (idle (serviceOwnTurn?_of_ready setup execution.application ready owned)).elim



/-- Another player's response that transmits the same packet as its
counterpart, or is silent with it, keeps equal deviator traffic. -/
theorem bindingTraffic_respond_other {who actor : Player} (different : who ≠ actor)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : (serviceRuntime setup mode deadline).bindingTraffic leaks who left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who right)
    (leftResponse rightResponse : (serviceApplication setup mode deadline leaks).Action)
    (packets : (leftResponse.transmission = none ∧ rightResponse.transmission = none) ∨
      ∃ leftMaterial rightMaterial, leftResponse = ⟨some leftMaterial⟩ ∧
        rightResponse = ⟨some rightMaterial⟩ ∧
        (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit left.application actor
              leftMaterial) actor (left.network.known actor) leftMaterial =
          (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit right.application actor
              rightMaterial) actor (right.network.known actor) rightMaterial) :
    (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (left.respond (serviceApplication setup mode deadline leaks) actor leftResponse) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks who
        (right.respond (serviceApplication setup mode deadline leaks) actor rightResponse) := by
  let app := serviceApplication setup mode deadline leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.logs who = right.logs who := congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView who = right.application.playerView who :=
    congrArg (fun value => value.2.2.2.2.1) same
  have kept (execution : app.Execution) (response : app.Action) :
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
    rw [app.respond_recall_other left actor who different,
      app.respond_recall_other right actor who different, recalled]


section Round

/-- The readout compared across the phase of another owner: the deviator's
traffic, the owner's turns at the event and whether the owner has submitted for
it. -/
def foreignReadout (who owner : Player) (event : (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution) :=
  ((serviceRuntime setup mode deadline).bindingTraffic leaks who execution,
      ownerTurns owner event execution,
    (serviceRuntime setup mode deadline).eventRecorded leaks (execution.logs owner) event)

/-- A law on which the owner's recall stays that of `execution` has the
compared readout of its traffic. -/
theorem map_foreignReadout_of_recall (who owner : Player) (event :
    (serviceGraph setup mode).EventId)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (law : PMF (serviceApplication setup mode deadline leaks).Execution)
    (kept : ∀ next ∈ law.support, next.logs owner = execution.logs owner) :
    law.map (foreignReadout (leaks := leaks) who owner event) =
      (law.map ((serviceRuntime setup mode deadline).bindingTraffic leaks who)).map fun traffic =>
        (traffic, ownerTurns owner event execution,
          (serviceRuntime setup mode deadline).eventRecorded leaks
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
        first (leftActive.logs owner)
            (leftActive.observe
                (serviceApplication setup mode deadline leaks) owner) = PMF.pure leftResponse ∧
        second (rightActive.logs owner)
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
      (left.logs owner) event =
      (serviceRuntime setup mode deadline).eventRecorded leaks (right.logs owner) event :=
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
      (unchanged : ∀ next ∈ law.support, next.logs owner = execution.logs owner) :=
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
  refine app.round_map_congr scheduler _ _ left right _ environments observed networks ?_ ?_
  · intro actor selected sample sampled
    let leftActive := left.sampledActivation app actor sample
    let rightActive := right.sampledActivation app actor sample
    have activated : (serviceRuntime setup mode deadline).bindingTraffic leaks who leftActive =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who rightActive :=
      bindingTraffic_activation
          (serviceRuntime setup mode deadline) leaks left right who actor sameTraffic sample
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
            ((leftActive.respond app owner leftResponse).logs owner) event =
          (serviceRuntime setup mode deadline).eventRecorded leaks
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
            (serviceRuntime setup mode deadline) leaks leftActive
          rightActive who activated response) ?_
        change (ownerTurns owner event (leftActive.respond app who response),
            (serviceRuntime setup mode deadline).eventRecorded leaks
              ((leftActive.respond app who response).logs owner) event) =
          (ownerTurns owner event (rightActive.respond app who response),
            (serviceRuntime setup mode deadline).eventRecorded leaks
              ((rightActive.respond app who response).logs owner) event)
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
              ((leftActive.respond app actor ⟨none⟩).logs owner) event) =
          (ownerTurns owner event (rightActive.respond app actor ⟨none⟩),
            (serviceRuntime setup mode deadline).eventRecorded leaks
              ((rightActive.respond app actor ⟨none⟩).logs owner) event)
        unfold ownerTurns
        rw [app.respond_recall_other leftActive actor owner (Ne.symm isOwner) _,
          app.respond_recall_other rightActive actor owner (Ne.symm isOwner) _,
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
        · change (serviceRuntime setup mode deadline).bindingTraffic leaks who
              { left.includePending app id with environmentRecall := _ } =
            (serviceRuntime setup mode deadline).bindingTraffic leaks who
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
        · change (serviceRuntime setup mode deadline).eventRecorded leaks
            ((left.includePending app id).logs owner)
              event = (serviceRuntime setup mode deadline).eventRecorded leaks
              ((right.includePending app id).logs owner) event
          rw [leftKeeps, rightKeeps]
          exact sameRecorded
    | application command =>
        rw [kept left _ (fun next reached => by
            rw [app.environmentStep_recall left next _ reached]),
          kept right _ (fun next reached => by
            rw [app.environmentStep_recall right next _ reached]),
          application_environmentStep_traffic_congr sameTraffic command]
        unfold ownerTurns at sameTurns ⊢
        rw [sameTurns, sameRecorded]
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
        apply congrArg PMF.pure
        refine Prod.ext (bindingTraffic_record (leaks := leaks) who sameTraffic .wait) ?_
        change (ownerTurns owner event left,
          (serviceRuntime setup mode deadline).eventRecorded leaks
            (left.logs owner) event) =
          (ownerTurns owner event right, (serviceRuntime setup mode deadline).eventRecorded leaks
            (right.logs owner) event)
        rw [sameTurns, sameRecorded]

end Round


/-- An authentic opening of the same stored value has the same public and
focal private effect, including public default control. -/
theorem handle_opening_playerView_congr
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : EventGraphRuntime.State (serviceGraph setup mode)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (leftInvariant : left.BindingInvariant) (rightInvariant : right.BindingInvariant)
    (value : L.Val payload)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (id : MessageId Player) (candidate : Handle (serviceGraph setup mode)) (raw : Raw L) :
    (handle (serviceRuntime setup mode deadline) left ⟨id, .opening event candidate raw⟩).map
        (fun state => state.playerView focal) =
      (handle (serviceRuntime setup mode deadline) right ⟨id, .opening event candidate raw⟩).map
        (fun state => state.playerView focal) := by
  classical
  have publics := congrArg PlayerView.publicView views
  have accepted : left.accepted = right.accepted := congrArg PublicView.accepted publics
  have status : left.config.defaulted = right.config.defaulted :=
    congrArg (fun view : PublicView (serviceGraph setup mode) => view.observation.defaulted) publics
  have clocks : left.clock = right.clock := congrArg PublicView.clock publics
  have activations : left.activatedAt = right.activatedAt := congrArg PublicView.activatedAt publics
  by_cases inactive : id.1 ∈ left.config.defaulted
  · simp only [handle, Message.sender, inactive, ← status, ite_true, Option.map_none]
  have rightActive : id.1 ∉ right.config.defaulted := by rwa [← status]
  by_cases timely : left.WithinDeadline (serviceRuntime setup mode deadline) event
  · have rightTimely : right.WithinDeadline (serviceRuntime setup mode deadline) event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    by_cases sender : id.1 = owner
    · by_cases handleOwner : candidate.1 = owner
      · by_cases associated : left.accepted binding.field = some candidate
        · have rightAssociated : right.accepted binding.field = some candidate := by
            rwa [← accepted]
          obtain ⟨leftHandle, leftAccepted, _leftOwner, leftLookup⟩ :=
            leftInvariant.success_provenance binding value leftStored
          have leftHandleEq : leftHandle = candidate :=
            Option.some.inj (leftAccepted.symm.trans associated)
          subst leftHandle
          obtain ⟨rightHandle, rightAccepted, _rightOwner, rightLookup⟩ :=
            rightInvariant.success_provenance binding value rightStored
          have rightHandleEq : rightHandle = candidate :=
            Option.some.inj (rightAccepted.symm.trans rightAssociated)
          subst rightHandle
          by_cases sameRaw : raw = ⟨payload, value⟩
          · subst raw
            have stores : (serviceGraph setup mode).publicStore left.config.store =
                (serviceGraph setup mode).publicStore right.config.store :=
              congrArg (fun view : PublicView (serviceGraph setup mode) =>
                view.observation.store) publics
            have resolved : EventCode.resolveOutput? binding checks true left.config.store =
                EventCode.resolveOutput? binding checks true right.config.store := by
              unfold EventCode.resolveOutput?
              rw [leftStored, rightStored]
              simp only [Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
              rw [← GuardCheck.allAccepted?_publicStore checks left.config.store,
                ← GuardCheck.allAccepted?_publicStore checks right.config.store, stores]
            have available : (EventCode.resolveOutput? binding checks true
                left.config.store).isSome = true := by
              apply EventCode.resolveOutput?_isSome
              intro field read
              apply left.config.read_available leftReady
              rw [← EventCode.readFields_cast outputEq
                ((serviceGraph setup mode).nodes event), codeEq]
              exact read
            obtain ⟨result, evaluated⟩ := Option.isSome_iff_exists.mp available
            rw [handle_opening_eq (serviceRuntime setup mode deadline) left id event candidate
                owner payload binding checks outputEq codeEq node leftReady timely inactive
                sender handleOwner associated value leftLookup leftStored result evaluated,
              handle_opening_eq (serviceRuntime setup mode deadline) right id event candidate
                owner payload binding checks outputEq codeEq node rightReady rightTimely
                rightActive sender handleOwner rightAssociated value rightLookup rightStored
                result (resolved ▸ evaluated)]
            simp only [Option.map_some]
            apply congrArg some
            apply State.complete_playerView_congr left right focal publics
              (left.playerView_observation_eq right focal views)
              (congrArg PlayerView.candidates views)
              event leftReady rightReady _ _ _ _ (fun _ => rfl) (fun _ => rfl)
            rw [left.config.completion_defaultEvent_of_code event outputEq
              (.resolve owner payload binding checks) codeEq,
              right.config.completion_defaultEvent_of_code event outputEq
                (.resolve owner payload binding checks) codeEq, status]
          · have leftFalse : left.candidates.verify candidate raw = false := by
              apply Bool.eq_false_of_not_eq_true
              intro valid
              have lookup := (CommitmentCandidates.verify_eq_true_iff _ _ _).mp valid
              rw [leftLookup] at lookup
              exact sameRaw (CommitmentCandidate.openable.inj lookup).symm
            have rightFalse : right.candidates.verify candidate raw = false := by
              apply Bool.eq_false_of_not_eq_true
              intro valid
              have lookup := (CommitmentCandidates.verify_eq_true_iff _ _ _).mp valid
              rw [rightLookup] at lookup
              exact sameRaw (CommitmentCandidate.openable.inj lookup).symm
            simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
              sender, handleOwner, associated, rightAssociated, leftFalse, rightFalse]
        · have rightUnassociated : right.accepted binding.field ≠ some candidate := by
            rwa [← accepted]
          simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
            sender, handleOwner, associated, rightUnassociated]
      · simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
          sender, handleOwner]
    · simp [handle, Message.sender, inactive, rightActive, leftReady, rightReady,
        timely, rightTimely, node, sender]
  · have rightLate : ¬ right.WithinDeadline (serviceRuntime setup mode deadline) event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    simp [handle, Message.sender, inactive, rightActive, leftReady, rightReady, timely, rightLate]


private theorem decided_policy_canonical
    (bound : (serviceGraph setup mode).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup mode).EventId) (action : (serviceGraph setup mode).Action event) :
    SubmitsCanonically (deadline := deadline)
      (decidedTurnPolicy (deadline := deadline) setup leaks bound owner event action) owner := by
  intro past view response chosen material sends
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy at chosen
  dsimp only at chosen
  split at chosen
  · rename_i first
    have turn := (sourceServiceTurn_first first).1
    unfold decidedOpportunity at chosen
    split at chosen
    · exact (silentPolicy_not_submit chosen material sends).elim
    · rename_i unrecorded
      split at chosen
      · split at chosen
        · exact (silentPolicy_not_submit chosen material sends).elim
        · rw [PMF.mem_support_pure_iff] at chosen
          subst response
          exact ⟨event, action, turn, by simpa using unrecorded, rfl⟩
      · exact (silentPolicy_not_submit chosen material sends).elim
  · exact (silentPolicy_not_submit chosen material sends).elim

private theorem binding_ready_handler
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload}
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (left right : EventGraphRuntime.State (serviceGraph setup mode)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (message : Message Player (Payload (serviceGraph setup mode))) :
    (handle (serviceRuntime setup mode deadline) left message).map
        (fun state => state.playerView focal) =
      (handle (serviceRuntime setup mode deadline) right message).map
        (fun state => state.playerView focal) := by
  classical
  obtain ⟨id, packet⟩ := message
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr _ left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have namedEq := alone _ named leftReady namedReady
        subst named
        simp [handle, leftReady, rightReady, node]
      · have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
        have rightNot : ¬right.config.cut.Ready named := by simpa only [← cuts] using namedReady
        simp [handle, namedReady, rightNot]

/-- Away from an unrecorded first turn that still fits the deadline, the
decided policy is silent. -/
theorem decidedTurnPolicy_closed {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (closed : ¬ (ownerTurns owner event execution = 0 ∧
      (serviceRuntime setup mode deadline).eventRecorded leaks (execution.logs owner) event =
        false ∧
      execution.application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event)) :
    decidedTurnPolicy setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨none⟩ := by
  have turn := serviceTurn_of_ready execution ready owned
  unfold decidedTurnPolicy
  by_cases first : ownerTurns owner event execution = 0
  · rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
      _ _ _ _ (by rw [turn, first]; rfl)]
    unfold decidedOpportunity
    by_cases recorded : (serviceRuntime setup mode deadline).eventRecorded leaks
        (execution.logs owner) event = true
    · simp only [recorded, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
    · have unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
          (execution.logs owner) event = false := by simpa using recorded
      have late : ¬ execution.application.publicView.InclusionFitsDeadline
          (serviceRuntime setup mode deadline) bound event := fun fits =>
        closed ⟨first, unrecorded, fits⟩
      have lateView : ¬ (execution.observe (serviceApplication setup mode deadline leaks)
          owner).application.publicView.InclusionFitsDeadline
            (serviceRuntime setup mode deadline) bound event := late
      simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, lateView,
        ReactiveApplication.silentPolicy_apply]
  · rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_unselected _ _ _ _ _ _
      (by
        intro slot chosen
        rw [turn]
        intro equal
        exact first ((Option.some.inj equal).trans
          ((Fin.val_eq_zero slot).trans (by rfl))))]
    rfl

/-- At an unrecorded first turn, the decided policy is its opportunity. -/
theorem decidedTurnPolicy_open {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (first : ownerTurns owner event execution = 0) :
    decidedTurnPolicy setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      decidedOpportunity setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) := by
  have turn := serviceTurn_of_ready execution ready owned
  unfold decidedTurnPolicy
  rw [(serviceApplication setup mode deadline leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
    _ _ _ _ (by rw [turn, first]; rfl)]

/-- An opportunity that transmits a given decision. -/
theorem decidedOpportunity_transmits {bound : (serviceGraph setup mode).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    (action : (serviceGraph setup mode).Action event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (execution.logs owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event)
    (material : (serviceApplication setup mode deadline leaks).Submission)
    (decision : (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
      (execution.logs owner) (execution.observe (serviceApplication setup mode deadline leaks)
        owner) event action = ⟨some material⟩) :
    decidedOpportunity setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup mode deadline leaks) owner) =
      PMF.pure ⟨some material⟩ := by
  have fitsView : (execution.observe (serviceApplication setup mode deadline leaks)
      owner).application.publicView.InclusionFitsDeadline (serviceRuntime setup mode deadline)
        bound event := fits
  unfold decidedOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsView, decision, reduceCtorEq]



private theorem decided_binding_response
    {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (result : PublicationResult (L.Val payload))
    {current : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + 1, none, current⟩))
    (own : OwnSubmissionsAtTurn setup leaks current owner)
    (slots : CanonicalSlotsUsed setup leaks current owner)
    (ready : current.application.config.cut.Ready event)
    (selected : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler current.environmentRecall
        (current.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending owner
      current.network.pending).support)
    (first : ownerTurns owner event current = 0)
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (current.logs owner) event = false)
    (fits : current.application.publicView.InclusionFitsDeadline
      (serviceRuntime setup mode deadline) bound event) :
    let active := current.sampledActivation (serviceApplication setup mode deadline leaks) owner
      sample
    decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) (some result))
        (active.logs owner) (active.observe (serviceApplication setup mode deadline leaks)
          owner) =
      PMF.pure ((serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
        result (current.application.publicView.bindingCount owner)) := by
  intro active
  let app := serviceApplication setup mode deadline leaks
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have moved : active ∈ (current.environmentStep app (.activate owner)).support := by
    rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
    exact ⟨sample, sampled, rfl⟩
  obtain ⟨activeTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
    scheduler remaining current active (.activate owner) trace selected moved
  have turn : active.application.publicView.ownTurn? owner = some event :=
    serviceOwnTurn?_of_ready setup current.application ready owned
  have fresh := canonicalSlot_fresh_of_used activeTrace owner own slots event turn unrecorded
  have canonical := canonicalFreshSlot_canonical owner (active.observe app owner).application fresh
  have activeOwner : owner ∉ active.application.config.defaulted :=
    active.application.active_of_ready_owned
      (legalFacts setup leaks horizon scheduler _ activeTrace).quiescent ready owned
  have decision := (serviceRuntime setup mode deadline).canonicalServiceDecision_binding leaks
    owner (active.logs owner) (active.observe app owner) event payload outputEq codeEq node
      activeOwner _ canonical result
  rw [decidedTurnPolicy_open _ active ready owned first,
    decidedOpportunity_transmits _ active unrecorded fits _ decision]
  rfl

private theorem binding_response_matched
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner focal : Player} {payload : L.Ty}
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn setup leaks left owner)
    (leftSlots : CanonicalSlotsUsed setup leaks left owner)
    (rightOwn : OwnSubmissionsAtTurn setup leaks right owner)
    (rightSlots : CanonicalSlotsUsed setup leaks right owner)
    (selected : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending owner
      left.network.pending).support) :
    let leftActive := left.sampledActivation (serviceApplication setup mode deadline leaks)
      owner sample
    let rightActive := right.sampledActivation (serviceApplication setup mode deadline leaks)
      owner sample
    ∃ leftResponse rightResponse,
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) leftChoice)
        (leftActive.logs owner) (leftActive.observe
          (serviceApplication setup mode deadline leaks) owner) = PMF.pure leftResponse ∧
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) rightChoice)
        (rightActive.logs owner) (rightActive.observe
          (serviceApplication setup mode deadline leaks) owner) = PMF.pure rightResponse ∧
      (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
        (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (leftActive.respond (serviceApplication setup mode deadline leaks) owner leftResponse) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (rightActive.respond (serviceApplication setup mode deadline leaks) owner
          rightResponse) := by
  intro leftActive rightActive
  let app := serviceApplication setup mode deadline leaks
  have sameTraffic : (serviceRuntime setup mode deadline).bindingTraffic leaks focal left =
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal right := congrArg
        Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (left.logs owner) event =
      (serviceRuntime setup mode deadline).eventRecorded leaks (right.logs owner) event :=
    congrArg (fun value => value.2.2) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have activated := bindingTraffic_activation (serviceRuntime setup mode deadline) leaks left
    right focal owner sameTraffic sample
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  cases leftChoice with
  | none =>
      cases rightChoice with
      | some result => cases admitted
      | none =>
          have silent : SilentAction event
              (cast (congrArg EventField.Action outputEq.symm)
                (none : Option (PublicationResult (L.Val payload)))) := by
            unfold SilentAction
            rw [node]
            simp only [cast_cast, cast_eq]
          exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_silent _ silent _ _,
            decidedTurnPolicy_silent _ silent _ _, rfl,
            bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩
  | some leftResult =>
      cases rightChoice with
      | none => cases admitted
      | some rightResult =>
          by_cases opened : ownerTurns owner event left = 0 ∧
              (serviceRuntime setup mode deadline).eventRecorded leaks (left.logs owner) event =
                false ∧ left.application.publicView.InclusionFitsDeadline
                  (serviceRuntime setup mode deadline) bound event
          · obtain ⟨first, unrecorded, fits⟩ := opened
            have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
            have rightUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
                (right.logs owner) event = false := sameRecorded ▸ unrecorded
            have rightFits : right.application.publicView.InclusionFitsDeadline
                (serviceRuntime setup mode deadline) bound event := publics ▸ fits
            have counts : left.application.publicView.bindingCount owner =
                right.application.publicView.bindingCount owner := by rw [publics]
            refine ⟨(serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
                leftResult (left.application.publicView.bindingCount owner),
              (serviceRuntime setup mode deadline).reactiveBinding leaks owner event payload
                rightResult (right.application.publicView.bindingCount owner), ?_, ?_, rfl, ?_⟩
            · exact decided_binding_response outputEq codeEq node leftResult leftTrace leftOwn
                leftSlots leftReady selected sample sampled first unrecorded fits
            · exact decided_binding_response outputEq codeEq node rightResult rightTrace rightOwn
                rightSlots rightReady (by
                  rw [← environments, ← observeEnvironment_eq_of_bindingTraffic focal sameTraffic]
                  exact selected) sample (by rw [← networks]; exact sampled) rightFirst
                  rightUnrecorded rightFits
            · apply bindingTraffic_respond_other foreign.symm activated
              refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
              have activePublics : leftActive.application.publicView =
                  rightActive.application.publicView := publics
              rw [reactiveApplication_packet_none, reactiveApplication_packet_none, counts,
                activePublics]
          · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
                (serviceRuntime setup mode deadline).eventRecorded leaks (right.logs owner)
                  event = false ∧ right.application.publicView.InclusionFitsDeadline
                    (serviceRuntime setup mode deadline) bound event) := by
              rw [← sameTurns, ← sameRecorded, ← publics]
              exact opened
            exact ⟨⟨none⟩, ⟨none⟩,
              decidedTurnPolicy_closed _ leftActive leftReady owned opened,
              decidedTurnPolicy_closed _ rightActive rightReady owned rightClosed, rfl,
              bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩


private theorem binding_stopped_readout_congr
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat)
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup mode) event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (serviceApplication setup mode deadline leaks).Execution)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn setup leaks leftStart owner)
    (leftSlots : CanonicalSlotsUsed setup leaks leftStart owner)
    (rightOwn : OwnSubmissionsAtTurn setup leaks rightStart owner)
    (rightSlots : CanonicalSlotsUsed setup leaks rightStart owner)
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    ((serviceApplication setup mode deadline leaks).runUntil scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (foreignReadout (leaks := leaks) focal owner event) =
    ((serviceApplication setup mode deadline leaks).runUntil scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (foreignReadout (leaks := leaks) focal owner event) := by
  let app := serviceApplication setup mode deadline leaks
  let players := fun choice => Function.update (focalPlayers setup leaks focal deviation) owner
    (decidedTurnPolicy setup leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) choice))
  let invariant := fun (start : app.Execution) (count : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config) ∧
    OwnSubmissionsAtTurn setup leaks current owner ∧ CanonicalSlotsUsed setup leaks current owner
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_bind_actor outputEq codeEq
  have advance (start : app.Execution) (startReady : start.application.config.cut.Ready event)
      (choice : Option (PublicationResult (L.Val payload))) (n : Nat) (current : app.Execution)
      (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed)
      (next : app.Execution)
      (reached : next ∈ (app.round scheduler (players choice) current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed, own, slots⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
      (players choice) (remaining + n) current next before reached
    obtain ⟨nextOwn, nextSlots⟩ := canonicalSlots_round (setup := setup) (mode := mode)
      (deadline := deadline) (leaks := leaks) (players := players choice) (who := owner)
      (by
        simpa only [players, Function.update_self] using
          (decided_policy_canonical (deadline := deadline) bound owner event
            (cast (congrArg EventField.Action outputEq.symm) choice)))
      (by
        simpa only [players, Function.update_self] using
          (decidedTurnPolicy_submitsAtTurn (deadline := deadline) setup leaks bound owner event
            (cast (congrArg EventField.Action outputEq.symm) choice))) before own slots reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_, nextOwn, nextSlots⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending (serviceRuntime setup mode deadline) leaks
      scheduler (players choice) event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler (players leftChoice)
    (players rightChoice)
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame, currentLeftOwn, currentLeftSlots⟩ :=
      leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame, currentRightOwn, currentRightSlots⟩ :=
      rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    have leftBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro selected sample sampled
      exact binding_response_matched foreign outputEq codeEq node leftChoice rightChoice admitted
        equal leftBefore rightBefore currentLeftReady currentRightReady
        currentLeftOwn currentLeftSlots currentRightOwn currentRightSlots selected sample sampled
    · intro id message _found _sender
      exact binding_ready_handler node left.application right.application focal
        (congrArg (fun value => value.2.2.2.2.1) traffic) currentLeftReady currentRightReady alone
        ⟨message.id, message.payload.call⟩
  · exact advance leftStart leftReady leftChoice
  · exact advance rightStart rightReady rightChoice
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl, leftOwn, leftSlots⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl, rightOwn, rightSlots⟩
  · exact same

/-- An honest foreign binding has the same focal traffic law at equal public
admission choices and equal initial focal traffic. -/
theorem sourceService_binding_traffic_congr
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup runtime leaks).Policy) (foreign : owner ≠ focal)
    (event : (graph setup).EventId) {payload : L.Ty}
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (left right : (application setup runtime leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        (runtime.bindingTraffic leaks focal)) =
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        (runtime.bindingTraffic leaks focal)) := by
  let app := application setup runtime leaks
  let players := Function.update
    (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have follows : players owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) wholeProfile owner :=
    Function.update_of_ne foreign _ _
  have facts (current : app.Execution) (boundary : CompletionBoundary setup leaks scheduler
      players event.val current) (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      OwnSubmissionsAtTurn setup leaks current owner ∧
      CanonicalSlotsUsed setup leaks current owner ∧
      ownerTurns owner event current = 0 ∧
      runtime.eventRecorded leaks (current.logs owner) event = false := by
    obtain ⟨own, slots⟩ := canonicalSlots_roundsFrom (setup := setup) (leaks := leaks) scheduler
      players owner
      (firstTurnTiming setup turns) wholeProfile follows current.environmentRecall.length current
      boundary.supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact boundary.untouched event le_rfl owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
      current.environmentRecall.length bounded current boundary.supported, own, slots, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftOwn, leftSlots, leftTurns, leftRecorded⟩ :=
    facts left leftBoundary leftBounded
  obtain ⟨⟨rightTrace⟩, rightOwn, rightSlots, rightTurns, rightRecorded⟩ :=
    facts right rightBoundary rightBounded
  have equal : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right := by
    simp only [foreignReadout, same, leftTurns, rightTurns, leftRecorded, rightRecorded]
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  rw [environments] at leftTrace
  have coupled := binding_stopped_readout_congr scheduler focal deviation bound foreign outputEq
    codeEq node leftChoice rightChoice admitted alone left right
    (leftRemaining := 0) (rightRemaining := 0)
    (by simpa only [Nat.zero_add] using leftTrace)
    (by simpa only [Nat.zero_add] using rightTrace)
    (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
    leftOwn leftSlots rightOwn rightSlots equal
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [ReactiveApplication.runUntilHorizon, environments, PMF.map_comp,
    foreignReadout, Function.comp_def] using projected

/-- Before the ready event completes, fixing its owner's first source choice
agrees with the decided client while every other honest owner is idle. -/
theorem sourceService_foreign_fixedRun
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (focal : Player)
    (deviation : (application setup runtime leaks).Policy)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (action : (graph setup).Action event)
    (execution : (application setup runtime leaks).Execution)
    (ready : execution.application.config.cut.Ready event) :
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation
    let baseline := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) profile
    let member := fun past view =>
      if serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0 then
        decidedOpportunity setup leaks bound owner event action past view
      else baseline owner past view
    ((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update players owner member)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    (application setup runtime leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers (deadline := runtime.deadline) setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  intro players baseline _member
  let app := application setup runtime leaks
  unfold ReactiveApplication.runUntilHorizon
  let first := fun past view =>
    serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
  let member := fun past view =>
    if first past view then decidedOpportunity setup leaks bound owner event action past view
    else baseline owner past view
  have alone : ∀ (cut : (graph setup).order.Cut) other, cut.Ready event → cut.Ready other →
      other = event := fun cut _ ready otherReady =>
    setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  apply app.runUntil_congr_of_agree scheduler (Function.update players owner member)
    (Function.update (focalPlayers setup leaks focal deviation) owner
      (decidedTurnPolicy setup leaks bound owner event action))
    (fun final => event ∈ final.application.config.cut.completed)
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current holds running command _ middle moved actor active
    have activateIs : command = .activate actor := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have unchanged := activation_application (setup := setup) leaks current middle actor moved
    have ready : middle.application.config.cut.Ready event := by
      rw [unchanged]
      exact holds running
    by_cases isOwner : actor = owner
    · subst actor
      simp only [Function.update_self]
      have serving := serviceOwnTurn?_of_ready setup middle.application ready owned
      dsimp only [member, first, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy]
      simp only [Fin.val_zero]
      by_cases selected : serviceTurn setup .sequential runtime.deadline leaks owner event
          (middle.logs owner) (middle.observe app owner) = some 0
      · simp only [selected, ite_true]
      · simp only [selected, ite_false]
        exact sourceServiceTurnPolicy_laterTurn owned serving selected
    · simp only [Function.update_of_ne isOwner]
      by_cases isFocal : actor = focal
      · subst actor
        simp only [players, focalPlayers, Function.update_self]
      · simp only [players, focalPlayers, Function.update_of_ne isFocal]
        have idle : (middle.observe app actor).application.publicView.ownTurn? actor = none := by
          apply ownTurn?_none_of_alone alone middle.application ready actor
          rw [owned]
          exact fun equal => isOwner (Option.some.inj equal).symm
        simp only [serviceTurnPolicy, serviceReferenceTurnPolicy, idle,
          ReactiveApplication.silentPolicy_apply]
  · intro current holds running next reached
    exact round_ready_of_pending alone (holds running) reached
  · exact fun _ => ready



/-- An honest foreign owner's stopped native law is its source head mixture
of decided native clients against the arbitrary focal policy. -/
theorem sourceService_foreign_mixture
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (focal : Player)
    (deviation : (application setup runtime leaks).Policy)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) (foreign : owner ≠ focal)
    (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (law : PMF ((graph setup).Action event))
    (callback : ∀ current : (application setup runtime leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup runtime leaks profile owner (current.logs owner)
        (current.observe (application setup runtime leaks) owner) =
      law.map (fun action => runtime.canonicalServiceDecision leaks owner (current.logs owner)
        (current.observe (application setup runtime leaks) owner) event action)) :
    let players := Function.update
      (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation
    ((application setup runtime leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    law.bind fun action => (application setup runtime leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers (deadline := runtime.deadline) setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  intro players
  let app := application setup runtime leaks
  let baseline := serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
    (firstTurnTiming setup turns) profile
  have follows : players owner = baseline owner := Function.update_of_ne foreign _ _
  have mixed := sourceService_firstTurn_mixture runtime leaks scheduler bound profile owner event
    owned players follows execution boundary bounded law callback
  rw [mixed]
  apply bind_congr_on_support _
  intro action _chosen
  unfold ReactiveApplication.runUntilHorizon
  let first := fun past view =>
    serviceTurn setup .sequential runtime.deadline leaks owner event past view = some 0
  let member := fun past view =>
    if first past view then decidedOpportunity setup leaks bound owner event action past view
    else baseline owner past view
  have alone : ∀ (cut : (graph setup).order.Cut) other, cut.Ready event → cut.Ready other →
      other = event := fun cut _ ready otherReady =>
    setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  apply app.runUntil_congr_of_agree scheduler (Function.update players owner member)
    (Function.update (focalPlayers setup leaks focal deviation) owner
      (decidedTurnPolicy setup leaks bound owner event action))
    (fun final => event ∈ final.application.config.cut.completed)
    (fun current => event ∉ current.application.config.cut.completed →
      current.application.config.cut.Ready event)
  · intro current holds running command _ middle moved actor active
    have activateIs : command = .activate actor := by
      cases command <;> simp_all [ReactiveApplication.Command.actor?]
    subst command
    have unchanged := activation_application (setup := setup) leaks current middle actor moved
    have ready : middle.application.config.cut.Ready event := by
      rw [unchanged]
      exact holds running
    by_cases isOwner : actor = owner
    · subst actor
      simp only [Function.update_self]
      have serving := serviceOwnTurn?_of_ready setup middle.application ready owned
      dsimp only [member, first, decidedTurnPolicy, ReactiveApplication.turnScheduledPolicy]
      simp only [Fin.val_zero]
      by_cases selected : serviceTurn setup .sequential runtime.deadline leaks owner event
          (middle.logs owner) (middle.observe app owner) = some 0
      · simp only [selected, ite_true]
      · simp only [selected, ite_false]
        exact sourceServiceTurnPolicy_laterTurn owned serving selected
    · simp only [Function.update_of_ne isOwner]
      by_cases isFocal : actor = focal
      · subst actor
        simp only [players, focalPlayers, Function.update_self]
      · simp only [players, focalPlayers, Function.update_of_ne isFocal]
        have idle : (middle.observe app actor).application.publicView.ownTurn? actor = none := by
          apply ownTurn?_none_of_alone alone middle.application ready actor
          rw [owned]
          exact fun equal => isOwner (Option.some.inj equal).symm
        simp only [serviceTurnPolicy, serviceReferenceTurnPolicy, idle,
          ReactiveApplication.silentPolicy_apply]
  · intro current holds running next reached
    exact round_ready_of_pending alone (holds running) reached
  · exact fun _ => boundary.ordered.ready event.isLt


private theorem canonical_opening_exact
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (recalled : execution.InputRecall (serviceApplication setup mode deadline leaks))
    (candidate : Handle (serviceGraph setup mode)) (value : L.Val payload)
    (accepted : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (active : owner ∉ execution.application.config.defaulted)
    (stored : binding.get? execution.application.config.store = some (.success value)) :
    (serviceRuntime setup mode deadline).canonicalServiceDecision leaks owner
      (execution.logs owner) (execution.observe
        (serviceApplication setup mode deadline leaks) owner) event
      (cast (congrArg EventField.Action outputEq.symm) true) =
      ⟨some ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
        owner ((serviceApplication setup mode deadline leaks).observePlayer
          execution.application owner) (execution.network.known owner))⟩ := by
  rw [(serviceRuntime setup mode deadline).canonicalServiceDecision_eq_of_not_bind leaks owner
    (execution.logs owner) (execution.observe
      (serviceApplication setup mode deadline leaks) owner) event _ (by
        intro other otherPayload otherEq otherCode same
        rw [node] at same
        cases same)]
  exact (serviceRuntime setup mode deadline).serviceDecision_authentic_opening leaks execution
    recalled owner event payload binding checks outputEq codeEq node candidate value
    accepted owned fixed active stored

private theorem opening_normal_packet
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (candidate : Handle (serviceGraph setup mode)) (raw : Raw L)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable raw) :
    let app := serviceApplication setup mode deadline leaks
    let material := (disclosureSubmission (.opening event candidate raw)).normalizeReactive
      owner (app.observePlayer execution.application owner) (execution.network.known owner)
    app.packet (app.submit execution.application owner material) owner
      (execution.network.known owner) material =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
        execution.application.publicView.tokenFor (.opening event candidate raw)⟩ := by
  intro app material
  let original := disclosureSubmission (.opening event candidate raw)
  let normal := (serviceRuntime setup mode deadline).reactiveNormalization leaks
  change app.packet (app.submit execution.application owner
      (normal.normalize owner (app.observePlayer execution.application owner)
        (execution.network.known owner) original)) owner (execution.network.known owner)
      (normal.normalize owner (app.observePlayer execution.application owner)
        (execution.network.known owner) original) = _
  rw [normal.submit, normal.packet]
  change WitnessedPacket.mk _ _ _ = WitnessedPacket.mk _ _ _
  congr 1
  exact WitnessedSubmission.emit_owned original.call
    (app.submit execution.application owner original) owner (execution.network.known owner)
    ⟨candidate, raw⟩ owned (by
      change execution.application.candidates.lookup candidate = .openable raw
      exact fixed)

private theorem opening_response_matched
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    {event : (serviceGraph setup mode).EventId} {owner focal : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (same : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (value : L.Val payload)
    (leftStored : binding.get? left.application.config.store = some (.success value))
    (rightStored : binding.get? right.application.config.store = some (.success value))
    (selected : (.activate owner : (serviceApplication setup mode deadline leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup mode deadline leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup mode deadline leaks).observePending owner
      left.network.pending).support) :
    let leftActive := left.sampledActivation (serviceApplication setup mode deadline leaks)
      owner sample
    let rightActive := right.sampledActivation (serviceApplication setup mode deadline leaks)
      owner sample
    ∃ leftResponse rightResponse,
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) true)
        (leftActive.logs owner) (leftActive.observe
          (serviceApplication setup mode deadline leaks) owner) = PMF.pure leftResponse ∧
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) true)
        (rightActive.logs owner) (rightActive.observe
          (serviceApplication setup mode deadline leaks) owner) = PMF.pure rightResponse ∧
      (serviceRuntime setup mode deadline).submittedEvent? leaks leftResponse =
        (serviceRuntime setup mode deadline).submittedEvent? leaks rightResponse ∧
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (leftActive.respond (serviceApplication setup mode deadline leaks) owner leftResponse) =
      (serviceRuntime setup mode deadline).bindingTraffic leaks focal
        (rightActive.respond (serviceApplication setup mode deadline leaks) owner
          rightResponse) := by
  intro leftActive rightActive
  let app := serviceApplication setup mode deadline leaks
  let runtime := serviceRuntime setup mode deadline
  let action := cast (congrArg EventField.Action outputEq.symm) true
  have sameTraffic : runtime.bindingTraffic leaks focal left =
      runtime.bindingTraffic leaks focal right := congrArg Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : runtime.eventRecorded leaks (left.logs owner) event =
      runtime.eventRecorded leaks (right.logs owner) event :=
    congrArg (fun value => value.2.2) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have activated := bindingTraffic_activation runtime leaks left right focal owner
    sameTraffic sample
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_resolve_actor outputEq codeEq
  by_cases opened : ownerTurns owner event left = 0 ∧
      runtime.eventRecorded leaks (left.logs owner) event = false ∧
      left.application.publicView.InclusionFitsDeadline runtime bound event
  · obtain ⟨first, unrecorded, fits⟩ := opened
    have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
    have rightUnrecorded : runtime.eventRecorded leaks (right.logs owner) event = false :=
      sameRecorded ▸ unrecorded
    have rightFits : right.application.publicView.InclusionFitsDeadline runtime bound event :=
      publics ▸ fits
    have leftMoved : leftActive ∈ (left.environmentStep app (.activate owner)).support := by
      rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
      exact ⟨sample, sampled, rfl⟩
    have rightMoved : rightActive ∈ (right.environmentStep app (.activate owner)).support := by
      rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
      exact ⟨sample, by rw [← networks]; exact sampled, rfl⟩
    obtain ⟨leftActiveTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
      scheduler leftRemaining left leftActive (.activate owner) leftTrace selected leftMoved
    obtain ⟨rightActiveTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
      scheduler rightRemaining right rightActive (.activate owner) rightTrace (by
        rw [← environments, ← observeEnvironment_eq_of_bindingTraffic focal sameTraffic]
        exact selected) rightMoved
    have leftFacts := legalFacts setup leaks horizon scheduler _ leftActiveTrace
    have rightFacts := legalFacts setup leaks horizon scheduler _ rightActiveTrace
    obtain ⟨candidate, leftAccepted, candidateOwner, leftFixed⟩ :=
      leftFacts.binding.success_provenance binding value leftStored
    have rightAccepted : rightActive.application.accepted binding.field = some candidate := by
      change right.application.accepted binding.field = _
      exact (congrFun (congrArg PublicView.accepted publics) binding.field).symm.trans
        leftAccepted
    obtain ⟨rightCandidate, acceptedOther, _, rightFixed⟩ :=
      rightFacts.binding.success_provenance binding value rightStored
    have candidateEq : rightCandidate = candidate :=
      Option.some.inj (acceptedOther.symm.trans rightAccepted)
    subst rightCandidate
    have leftActiveOwner : owner ∉ leftActive.application.config.defaulted :=
      leftActive.application.active_of_ready_owned leftFacts.quiescent leftReady owned
    have rightActiveOwner : owner ∉ rightActive.application.config.defaulted :=
      rightActive.application.active_of_ready_owned rightFacts.quiescent rightReady owned
    let leftMaterial :=
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
      owner (app.observePlayer leftActive.application owner) (leftActive.network.known owner)
    let rightMaterial :=
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
      owner (app.observePlayer rightActive.application owner) (rightActive.network.known owner)
    have leftDecision : runtime.canonicalServiceDecision leaks owner (leftActive.logs owner)
        (leftActive.observe app owner) event action = ⟨some leftMaterial⟩ :=
      canonical_opening_exact outputEq codeEq node leftActive leftFacts.inputs candidate value
        leftAccepted candidateOwner leftFixed leftActiveOwner leftStored
    have rightDecision : runtime.canonicalServiceDecision leaks owner (rightActive.logs owner)
        (rightActive.observe app owner) event action = ⟨some rightMaterial⟩ :=
      canonical_opening_exact outputEq codeEq node rightActive rightFacts.inputs candidate value
        rightAccepted candidateOwner rightFixed rightActiveOwner rightStored
    refine ⟨⟨some leftMaterial⟩, ⟨some rightMaterial⟩, ?_, ?_, ?_, ?_⟩
    · rw [decidedTurnPolicy_open action leftActive leftReady owned first,
        decidedOpportunity_transmits action leftActive unrecorded fits _ leftDecision]
    · rw [decidedTurnPolicy_open action rightActive rightReady owned rightFirst,
        decidedOpportunity_transmits action rightActive rightUnrecorded rightFits _ rightDecision]
    · rfl
    · apply bindingTraffic_respond_other foreign.symm activated
      refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
      rw [opening_normal_packet leftActive owner event candidate ⟨payload, value⟩ candidateOwner
        leftFixed, opening_normal_packet rightActive owner event candidate ⟨payload, value⟩
        candidateOwner rightFixed]
      have activePublics : leftActive.application.publicView =
          rightActive.application.publicView := publics
      rw [activePublics]
  · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
        runtime.eventRecorded leaks (right.logs owner) event = false ∧
        right.application.publicView.InclusionFitsDeadline runtime bound event) := by
      rw [← sameTurns, ← sameRecorded, ← publics]
      exact opened
    exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_closed action leftActive leftReady owned opened,
      decidedTurnPolicy_closed action rightActive rightReady owned rightClosed, rfl,
      bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩


private theorem opening_ready_handler
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    {outputEq : (serviceGraph setup mode).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks}
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : EventGraphRuntime.State (serviceGraph setup mode)) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftInvariant : left.BindingInvariant) (rightInvariant : right.BindingInvariant)
    (value : L.Val payload)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (message : Message Player (Payload (serviceGraph setup mode))) :
    (handle (serviceRuntime setup mode deadline) left message).map
        (fun state => state.playerView focal) =
      (handle (serviceRuntime setup mode deadline) right message).map
        (fun state => state.playerView focal) := by
  classical
  obtain ⟨id, packet⟩ := message
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr _ left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have namedEq := alone _ named leftReady namedReady
        subst named
        exact handle_opening_playerView_congr node left right focal views leftReady rightReady
          leftInvariant rightInvariant value leftStored rightStored id candidate raw
      · have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
        have rightNot : ¬right.config.cut.Ready named := by simpa only [← cuts] using namedReady
        simp [handle, namedReady, rightNot]

private theorem opening_stopped_readout_congr
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat)
    {event : (serviceGraph setup mode).EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload)}
    {checks : List (GuardCheck (serviceGraph setup mode).layout payload)}
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (serviceApplication setup mode deadline leaks).Execution)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (value : L.Val payload)
    (leftStored : binding.get? leftStart.application.config.store = some (.success value))
    (rightStored : binding.get? rightStart.application.config.store = some (.success value))
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    ((serviceApplication setup mode deadline leaks).runUntil scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (foreignReadout (leaks := leaks) focal owner event) =
    ((serviceApplication setup mode deadline leaks).runUntil scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (foreignReadout (leaks := leaks) focal owner event) := by
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (focalPlayers setup leaks focal deviation) owner
    (decidedTurnPolicy setup leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) true))
  let invariant := fun (start : app.Execution) (count : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config)
  have owned : (serviceGraph setup mode).actor? event = some owner :=
    nodeView_resolve_actor outputEq codeEq
  have advance (start : app.Execution) (startReady : start.application.config.cut.Ready event)
      (n : Nat) (current : app.Execution) (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed) (next : app.Execution)
      (reached : next ∈ (app.round scheduler players current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
      players (remaining + n) current next before reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending (serviceRuntime setup mode deadline) leaks
      scheduler players event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame⟩ := rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    have leftBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    have currentLeftStored : binding.get? left.application.config.store =
        some (.success value) := by rw [leftFrame running]; exact leftStored
    have currentRightStored : binding.get? right.application.config.store =
        some (.success value) := by rw [rightFrame rightRunning]; exact rightStored
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro selected sample sampled
      exact opening_response_matched foreign outputEq codeEq node equal leftBefore rightBefore
        currentLeftReady currentRightReady value currentLeftStored currentRightStored
        selected sample sampled
    · intro id message _found _sender
      exact opening_ready_handler node left.application right.application focal
        (congrArg (fun value => value.2.2.2.2.1) traffic) currentLeftReady currentRightReady alone
        (legalFacts setup leaks horizon scheduler _ leftBefore).binding
        (legalFacts setup leaks horizon scheduler _ rightBefore).binding
        value currentLeftStored currentRightStored ⟨message.id, message.payload.call⟩
  · exact advance leftStart leftReady
  · exact advance rightStart rightReady
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl⟩
  · exact same


/-- An honest true disclosure of the same bound value has equal stopped
focal traffic from equal initial focal traffic at actual initialized boundaries. -/
theorem sourceService_opening_traffic_congr
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup runtime leaks).Policy) (foreign : owner ≠ focal)
    (event : (graph setup).EventId) {payload : L.Ty}
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : (application setup runtime leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (value : L.Val payload)
    (leftStored : binding.get? left.application.config.store = some (.success value))
    (rightStored : binding.get? right.application.config.store = some (.success value))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        (runtime.bindingTraffic leaks focal)) =
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        (runtime.bindingTraffic leaks focal)) := by
  let app := application setup runtime leaks
  let players := Function.update
    (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have follows : players owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) wholeProfile owner :=
    Function.update_of_ne foreign _ _
  have facts (current : app.Execution) (boundary : CompletionBoundary setup leaks scheduler
      players event.val current) (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      ownerTurns owner event current = 0 ∧
      runtime.eventRecorded leaks (current.logs owner) event = false := by
    have atTurn : SubmitsAtTurn setup leaks (players owner) owner := by
      rw [follows]
      exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns
        (firstTurnTiming setup turns) wholeProfile owner
    have own := SubmitsAtTurn.roundsFrom setup leaks atTurn (initialLaw setup)
      current.environmentRecall.length current
      boundary.supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact boundary.untouched event le_rfl owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
      current.environmentRecall.length bounded current boundary.supported, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftTurns, leftRecorded⟩ := facts left leftBoundary leftBounded
  obtain ⟨⟨rightTrace⟩, rightTurns, rightRecorded⟩ := facts right rightBoundary rightBounded
  have equal : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right := by
    simp only [foreignReadout, same, leftTurns, rightTurns, leftRecorded, rightRecorded]
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  rw [environments] at leftTrace
  have coupled := opening_stopped_readout_congr scheduler focal deviation bound foreign outputEq
    codeEq node alone left right (leftRemaining := 0) (rightRemaining := 0)
    (by simpa only [Nat.zero_add] using leftTrace)
    (by simpa only [Nat.zero_add] using rightTrace)
    (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
    value leftStored rightStored equal
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [ReactiveApplication.runUntilHorizon, environments, PMF.map_comp,
    foreignReadout, Function.comp_def] using projected

private theorem recorded_false_round
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {players : Player → (serviceApplication setup mode deadline leaks).Policy}
    {owner : Player} (quiet : players owner =
      (serviceApplication setup mode deadline leaks).silentPolicy)
    {event : (serviceGraph setup mode).EventId}
    {before after : (serviceApplication setup mode deadline leaks).Execution}
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (before.logs owner) event = false)
    (reached : after ∈ ((serviceApplication setup mode deadline leaks).round scheduler players
      before).support) :
    (serviceRuntime setup mode deadline).eventRecorded leaks (after.logs owner) event =
      false := by
  let app := serviceApplication setup mode deadline leaks
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
  have recallEq := app.environmentStep_recall before middle command moved
  have kept : (serviceRuntime setup mode deadline).eventRecorded leaks
      (middle.logs owner) event = false := by rw [recallEq]; exact unrecorded
  rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, chosen, rfl⟩
  · exact kept
  · by_cases same : actor = owner
    · subst actor
      rw [quiet, ReactiveApplication.silentPolicy, PMF.mem_support_pure_iff] at chosen
      subst response
      simpa only [ReactiveApplication.Execution.respond, ↓reduceIte, eventRecorded,
        List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
        decide_false, Bool.false_or, Bool.or_false] using kept
    · rw [app.respond_recall_other middle actor owner (fun equal => same equal.symm) response]
      exact kept

private theorem unrecorded_ready_handler
    {horizon remaining : Nat}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {owner : Player} {event : (serviceGraph setup mode).EventId}
    {left right : (serviceApplication setup mode deadline leaks).Execution}
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace (some ⟨remaining, none, left⟩))
    (unrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (left.logs owner) event = false)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (id : MessageId Player) (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (found : left.network.lookup id = some message) (sender : message.sender = owner) :
    (handle (serviceRuntime setup mode deadline) left.application ⟨message.id,
        message.payload.call⟩).map (fun state => state.playerView owner) = none ∧
    (handle (serviceRuntime setup mode deadline) right.application ⟨message.id,
        message.payload.call⟩).map (fun state => state.playerView owner) = none := by
  have notNamed : message.payload.call.event? (serviceGraph setup mode) ≠ some event := by
    intro named
    obtain ⟨entry, present, material, transmitted, _emitted, state, known, packet⟩ :=
      (legalFacts setup leaks horizon scheduler _ trace).provenance.lookup id message found
    have old : entry ∈ left.logs owner := sender ▸ present
    have call : material.call.packet = message.payload.call :=
      congrArg (fun value => value.call) packet
    have submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
        some event := by
      simp only [EventGraphRuntime.submittedEvent?, transmitted]
      rw [call]
      exact named
    have recorded := ((serviceRuntime setup mode deadline).eventRecorded_iff leaks _ event).mpr
      ⟨entry, old, submitted⟩
    rw [unrecorded] at recorded
    cases recorded
  have rejected (state : EventGraphRuntime.State (serviceGraph setup mode))
      (ready : state.config.cut.Ready event) :
      handle (serviceRuntime setup mode deadline) state
        ⟨message.id, message.payload.call⟩ = none := by
    cases handled : handle (serviceRuntime setup mode deadline) state
        ⟨message.id, message.payload.call⟩ with
    | none => rfl
    | some next =>
        obtain ⟨query, named, queryReady, _action, _moved⟩ :=
          handle_config_mem_step (serviceRuntime setup mode deadline) state next _ handled
        have same := alone _ query ready queryReady
        subst query
        exact (notNamed named).elim
  exact ⟨by rw [rejected left.application leftReady]; rfl,
    by rw [rejected right.application rightReady]; rfl⟩

private theorem silent_foreign_stopped_readout_congr
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup mode deadline leaks).Policy)
    {event : (serviceGraph setup mode).EventId} {owner : Player}
    (owned : (serviceGraph setup mode).actor? event = some owner) (foreign : owner ≠ focal)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (serviceApplication setup mode deadline leaks).Execution)
    (leftTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (leftStart.logs owner) event = false)
    (rightUnrecorded : (serviceRuntime setup mode deadline).eventRecorded leaks
      (rightStart.logs owner) event = false)
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    let app := serviceApplication setup mode deadline leaks
    let players := Function.update (focalPlayers setup leaks focal deviation) owner app.silentPolicy
    (app.runUntil scheduler players (fun final => event ∈ final.application.config.cut.completed)
      count leftStart).map (foreignReadout (leaks := leaks) focal owner event) =
    (app.runUntil scheduler players (fun final => event ∈ final.application.config.cut.completed)
      count rightStart).map (foreignReadout (leaks := leaks) focal owner event) := by
  intro app players
  let invariant := fun (start : app.Execution) (count : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config) ∧
    (serviceRuntime setup mode deadline).eventRecorded leaks (current.logs owner) event = false
  have advance (start : app.Execution) (startReady : start.application.config.cut.Ready event)
      (n : Nat) (current : app.Execution) (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed) (next : app.Execution)
      (reached : next ∈ (app.round scheduler players current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed, unrecorded⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
      players (remaining + n) current next before reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_,
      recorded_false_round (by simp only [players, Function.update_self]; rfl)
        unrecorded reached⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending (serviceRuntime setup mode deadline) leaks
      scheduler players event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame, unrecorded⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame, _⟩ := rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro _selected sample _sampled
      refine ⟨⟨none⟩, ⟨none⟩, rfl, rfl, rfl, ?_⟩
      exact bindingTraffic_respond_other foreign.symm
        (bindingTraffic_activation (serviceRuntime setup mode deadline) leaks left right
          focal owner traffic sample) _ _ (Or.inl ⟨rfl, rfl⟩)
    · intro id message found sender
      have rejected := unrecorded_ready_handler leftCurrentTrace unrecorded currentLeftReady
        currentRightReady alone id message found sender
      have leftNone : handle (serviceRuntime setup mode deadline) left.application
          ⟨message.id, message.payload.call⟩ = none := by
        cases handled : handle (serviceRuntime setup mode deadline) left.application
            ⟨message.id, message.payload.call⟩ with
        | none => rfl
        | some after => rw [handled] at rejected; cases rejected.1
      have rightNone : handle (serviceRuntime setup mode deadline) right.application
          ⟨message.id, message.payload.call⟩ = none := by
        cases handled : handle (serviceRuntime setup mode deadline) right.application
            ⟨message.id, message.payload.call⟩ with
        | none => rfl
        | some after => rw [handled] at rejected; cases rejected.2
      rw [leftNone, rightNone]
  · exact advance leftStart leftReady
  · exact advance rightStart rightReady
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl, leftUnrecorded⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl, rightUnrecorded⟩
  · exact same


/-- An honest false disclosure emits no opening at its actual initialized
boundary, so its stopped focal traffic depends only on initial focal traffic. -/
theorem sourceService_withholding_traffic_congr
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup runtime leaks).Policy) (foreign : owner ≠ focal)
    (event : (graph setup).EventId) {payload : L.Ty}
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : (application setup runtime leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) false)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        (runtime.bindingTraffic leaks focal)) =
    (((application setup runtime leaks).runUntilHorizon scheduler
      (Function.update (focalPlayers setup leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) false)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        (runtime.bindingTraffic leaks focal)) := by
  let app := application setup runtime leaks
  let action := cast (congrArg EventField.Action outputEq.symm) false
  let players := Function.update
    (serviceTurnPolicy setup .sequential runtime.deadline leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have silent : SilentAction event action := by
    unfold SilentAction
    rw [node]
    simp only [action, cast_cast, cast_eq]
  have quiet : decidedTurnPolicy setup leaks bound owner event action = app.silentPolicy := by
    funext past view
    exact decidedTurnPolicy_silent action silent past view
  dsimp only [action] at quiet
  have follows : players owner = serviceTurnPolicy setup .sequential runtime.deadline leaks
      bound turns (firstTurnTiming setup turns) wholeProfile owner :=
    Function.update_of_ne foreign _ _
  have facts (current : app.Execution) (boundary : CompletionBoundary setup leaks scheduler
      players event.val current) (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      ownerTurns owner event current = 0 ∧
      runtime.eventRecorded leaks (current.logs owner) event = false := by
    have atTurn : SubmitsAtTurn setup leaks (players owner) owner := by
      rw [follows]
      exact sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns
        (firstTurnTiming setup turns) wholeProfile owner
    have own := SubmitsAtTurn.roundsFrom setup leaks atTurn (initialLaw setup)
      current.environmentRecall.length current boundary.supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact boundary.untouched event le_rfl owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
      current.environmentRecall.length bounded current boundary.supported, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftTurns, leftRecorded⟩ := facts left leftBoundary leftBounded
  obtain ⟨⟨rightTrace⟩, rightTurns, rightRecorded⟩ := facts right rightBoundary rightBounded
  have equal : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right := by
    simp only [foreignReadout, same, leftTurns, rightTurns, leftRecorded, rightRecorded]
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  have alone : ∀ (cut : (graph setup).order.Cut) other,
      cut.Ready event → cut.Ready other → other = event := by
    intro cut other ready otherReady
    exact setup.eventGraph.sequentialize_ready_unique cut otherReady ready
  rw [environments] at leftTrace
  have coupled := silent_foreign_stopped_readout_congr scheduler focal deviation
    (nodeView_resolve_actor outputEq codeEq) foreign alone left right
    (leftRemaining := 0) (rightRemaining := 0)
    (by simpa only [Nat.zero_add] using leftTrace)
    (by simpa only [Nat.zero_add] using rightTrace)
    (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
    leftRecorded rightRecorded equal
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [ReactiveApplication.runUntilHorizon, quiet, environments, PMF.map_comp,
    foreignReadout, Function.comp_def] using projected

end Vegas
