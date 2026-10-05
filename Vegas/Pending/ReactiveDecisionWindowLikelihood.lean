/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveDecisionWindowSettlement

/-! # Actual focal traffic through independently timed decisions

Both Boolean choices send a packet. The coupling preserves actual passive
samples and the focal player's private recall; foreign private recall may differ.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_decision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner focal : Player)
    (event : graph.EventId) (opening : Option (Handle graph × Raw L)) (disclose : Bool)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (leftValid : disclose = true → ∀ candidate raw, opening = some (candidate, raw) →
      left.application.candidates.lookup candidate = .openable raw)
    (rightValid : disclose = true → ∀ candidate raw, opening = some (candidate, raw) →
      right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    runtime.bindingTraffic leaks focal
        (left.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowDecision leaks event opening disclose)) =
      runtime.bindingTraffic leaks focal
        (right.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowDecision leaks event opening disclose)) := by
  let app := runtime.reactiveApplication leaks
  let material := windowDecisionMaterial event opening disclose
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have recalled := congrArg (fun value => value.2.2.2.1) same
  have views := congrArg (fun value => value.2.2.2.2.1) same
  have publics := congrArg (fun value => value.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments recalled views publics
  have observed : left.observe app focal = right.observe app focal := by
    have projected := congrArg (fun view : PlayerView graph =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView graph)) views
    change ReactiveApplication.PlayerView.mk _ _ _ = _
    rw [networks]
    exact congrArg₂ (fun view receipts =>
      (⟨right.network.observe focal, view, receipts⟩ : app.PlayerView)) projected receipts
  have emitted : app.packet left.application owner (left.network.known owner) material =
      app.packet right.application owner (right.network.known owner) material := by
    rw [runtime.windowDecision_packet leaks owner event opening left.application
      (left.network.known owner) disclose owned leftValid,
      runtime.windowDecision_packet leaks owner event opening right.application
        (right.network.known owner) disclose owned rightValid, publics]
  have inert (state : State graph) : app.submit state owner material = state := by
    cases disclose
    · rfl
    · cases opening <;> rfl
  have recallEq := app.respond_focal_recall_eq left right owner focal
    (runtime.windowDecision leaks event opening disclose) networks observed recalled (by
      intro submission transmitted
      have selected : material = submission := Option.some.inj transmitted
      subst submission
      rw [inert, inert]
      exact emitted)
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext recallEq (Prod.ext ?_ ?_))))
  · change (left.network.submit owner (app.packet (app.submit left.application owner material)
      owner (left.network.known owner) material)).2 =
      (right.network.submit owner (app.packet (app.submit right.application owner material)
        owner (right.network.known owner) material)).2
    rw [inert, inert, emitted, networks]
  · change ((left.respond app owner
      (runtime.windowDecision leaks event opening disclose)).application).playerView focal =
      ((right.respond app owner
        (runtime.windowDecision leaks event opening disclose)).application).playerView focal
    rw [runtime.windowDecision_application, runtime.windowDecision_application]
    exact views
  · change ((left.respond app owner
      (runtime.windowDecision leaks event opening disclose)).application).publicView =
      ((right.respond app owner
        (runtime.windowDecision leaks event opening disclose)).application).publicView
    rw [runtime.windowDecision_application, runtime.windowDecision_application]
    exact publics

/-- Scheduled decisions preserve the actual focal traffic, without equating
foreign private recall. Opening material is verified only for the true branch. -/
theorem decisionWindow_focal_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner) (offset : Nat)
    {slots : Nat} (selected : Fin slots × Bool)
    (leftValid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      left.application.candidates.lookup candidate = .openable raw)
    (rightValid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length) :
    let players := runtime.decisionWindowPlayers leaks owner event opening offset selected
    (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
      left).map (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
        right).map (runtime.bindingTraffic leaks focal) := by
  intro players
  let app := runtime.reactiveApplication leaks
  induction roster generalizing left right with
  | nil => simpa only [List.map_nil, runInteractionPlan, PMF.pure_map] using
      congrArg PMF.pure same
  | cons actor rest ih =>
      have networks : left.network = right.network := congrArg Prod.fst same
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.map_bind,
        PMF.bind_map, PMF.bind_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro sample _
      let before := left.sampledActivation app actor sample
      let after := right.sampledActivation app actor sample
      have beforeRecall : before.InputRecall app := leftRecall
      have afterRecall : after.InputRecall app := rightRecall
      have activationCounts : (before.recall owner).length = (after.recall owner).length := counts
      have matched := runtime.bindingTraffic_activation leaks left right focal actor same sample
      have silentStep :
          app.silentPolicy (before.recall actor) (before.observe app actor) =
            app.silentPolicy (after.recall actor) (after.observe app actor) := rfl
      have waiting
          (firstEq : players actor (before.recall actor) (before.observe app actor) =
            app.silentPolicy (before.recall actor) (before.observe app actor))
          (secondEq : players actor (after.recall actor) (after.observe app actor) =
            app.silentPolicy (after.recall actor) (after.observe app actor)) :
          (players actor (before.recall actor) (before.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) (before.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) =
          (players actor (after.recall actor) (after.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) (after.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) := by
        rw [firstEq, secondEq, silentStep]
        apply bind_congr_on_support _
        intro response supported
        have transport := app.silentPolicy_cases _ _ response supported
        have firstState : (before.respond app actor response).application = before.application := by
          rcases transport with rfl
          rfl
        have secondState : (after.respond app actor response).application = after.application := by
          rcases transport with rfl
          rfl
        apply ih _ _ (app.respond_inputRecall before actor response beforeRecall)
          (app.respond_inputRecall after actor response afterRecall)
        · rwa [firstState]
        · rwa [secondState]
        · exact runtime.bindingTraffic_silent leaks before after focal actor matched
            response transport
        · simpa only [app.respond_recall_length] using
            congrArg (fun length => length + if actor = owner then 1 else 0) activationCounts
      change (players actor (before.recall actor) (before.observe app actor)).bind _ =
        (players actor (after.recall actor) (after.observe app actor)).bind _
      by_cases acts : actor = owner
      · subst actor
        by_cases now : (some selected.1).map (fun slot => offset + slot.val) =
            some (before.recall owner).length
        · have nextNow : (some selected.1).map (fun slot => offset + slot.val) =
              some (after.recall owner).length := activationCounts ▸ now
          have firstNow : players owner (before.recall owner) (before.observe app owner) =
              PMF.pure (runtime.windowDecision leaks event opening selected.2) := by
            simp only [players, decisionWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_left now]
          have secondNow : players owner (after.recall owner) (after.observe app owner) =
              PMF.pure (runtime.windowDecision leaks event opening selected.2) := by
            simp only [players, decisionWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_left nextNow]
          rw [firstNow, secondNow, PMF.pure_bind, PMF.pure_bind]
          apply ih
            (before.respond app owner (runtime.windowDecision leaks event opening selected.2))
            (after.respond app owner (runtime.windowDecision leaks event opening selected.2))
            (app.respond_inputRecall before owner _ beforeRecall)
            (app.respond_inputRecall after owner _ afterRecall)
              (by simpa only [app, runtime.windowDecision_application, before,
                ReactiveApplication.Execution.sampledActivation] using leftValid)
              (by simpa only [app, runtime.windowDecision_application, after,
                ReactiveApplication.Execution.sampledActivation] using rightValid)
          · exact runtime.bindingTraffic_decision leaks before after owner focal event opening
              selected.2 owned leftValid rightValid matched
          · simpa only [app.respond_recall_length, ite_true] using
              congrArg (· + 1) activationCounts
        · have nextNot : (some selected.1).map (fun slot => offset + slot.val) ≠
              some (after.recall owner).length := by simpa only [activationCounts] using now
          apply waiting
          · simp only [players, app, decisionWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_right now]
          · simp only [players, app, decisionWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_right nextNot]
      · apply waiting <;> simp only [players, app, decisionWindowPlayers, ite_eq_right acts]

theorem bindingTraffic_include_of_handler (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : left.network.lookup id = some message)
    (handled : ((runtime.reactiveApplication leaks).handle left.application message).map
        (fun state => state.playerView focal) =
      ((runtime.reactiveApplication leaks).handle right.application message).map
        (fun state => state.playerView focal)) :
    runtime.bindingTraffic leaks focal
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingTraffic leaks focal
        (right.includePending (runtime.reactiveApplication leaks) id) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have views : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have rightFound : right.network.lookup id = some message := networks ▸ found
  simp only [bindingTraffic, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, rightFound]
  cases first : (runtime.reactiveApplication leaks).handle left.application message with
  | none =>
      cases second : (runtime.reactiveApplication leaks).handle right.application message with
      | none =>
          simp only [Option.getD_none, Option.isSome_none]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
      | some state =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          cases handled
  | some before =>
      cases second : (runtime.reactiveApplication leaks).handle right.application message with
      | none =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          cases handled
      | some after =>
          have nextViews : before.playerView focal = after.playerView focal := by
            simpa only [first, second, Option.map_some, Option.some.injEq] using handled
          simp only [Option.getD_some, Option.isSome_some]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled
              (Prod.ext nextViews (congrArg PlayerView.publicView nextViews)))))

/-- Reserved inclusion preserves focal traffic when the actual decision
packet has the same handler result in both physical states. -/
theorem decisionWindow_inclusion_focal_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (owner focal : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (selected : Fin (roster.count owner) × Bool)
    (leftValid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      left.application.candidates.lookup candidate = .openable raw)
    (rightValid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length)
    (handled : ((runtime.reactiveApplication leaks).handle left.application
        (runtime.decisionEnvelope leaks owner event opening selected.2 left)).map
          (fun state => state.playerView focal) =
      ((runtime.reactiveApplication leaks).handle right.application
        (runtime.decisionEnvelope leaks owner event opening selected.2 left)).map
          (fun state => state.playerView focal)) :
    let players := runtime.decisionWindowPlayers leaks owner event opening
      (left.recall owner).length selected
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) right).map
          (runtime.bindingTraffic leaks focal) := by
  intro players
  let app := runtime.reactiveApplication leaks
  have windows := runtime.decisionWindow_focal_coupling leaks network roster left right
    leftRecall rightRecall owner focal event opening owned (left.recall owner).length
      selected leftValid rightValid same counts
  rw [runInteractionPlan_append, runInteractionPlan_append, PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ windows
  intro before beforeSupport after afterSupport equal
  have leftStart := DecisionWindowFrame.initial runtime leaks owner event opening selected
    left leftSerials leftPublished
  have rightStart := DecisionWindowFrame.initial runtime leaks owner event opening selected
    right rightSerials rightPublished
  have first := leftStart.run runtime leaks owner event opening (left.recall owner).length
    selected 0 left left network roster before beforeSupport owned leftValid
  have second := rightStart.run runtime leaks owner event opening (right.recall owner).length
    selected 0 right right network roster after (by simpa only [← counts] using afterSupport)
      owned rightValid
  simp only [Nat.zero_add] at first second
  have firstSelection := first.selection runtime leaks owner event opening
    (left.recall owner).length selected left before leftSerials
  have secondSelection := second.selection runtime leaks owner event opening
    (right.recall owner).length selected right after rightSerials
  have networks : left.network = right.network := congrArg Prod.fst same
  have beforeNetworks : before.network = after.network := congrArg Prod.fst equal
  have beforeReceipts : before.receipts = after.receipts :=
    congrArg (fun value => value.2.1) equal
  have beforePublics : before.application.publicView = after.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) equal
  have beforeEnvironment : before.environmentRecall = after.environmentRecall :=
    congrArg (fun value => value.2.2.1) equal
  have environment : before.observeEnvironment app = after.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk before.network.publicView
      before.application.publicView before.receipts = _
    rw [beforeNetworks, beforePublics, beforeReceipts]
    rfl
  have sent : decisionPassed selected (roster.count owner) = true := by
    simpa only [decisionPassed, decide_eq_true_eq] using selected.1.isLt
  have found := first.lookup_sent runtime leaks owner event opening
    (left.recall owner).length selected (roster.count owner) left before leftSerials sent
  have views := bindingTraffic_include_of_handler runtime leaks before after focal equal
    (owner, left.network.nextSerial owner)
      (runtime.decisionEnvelope leaks owner event opening selected.2 left) found (by
        rw [first.application, second.application]
        exact handled)
  have rightSerial : right.network.nextSerial owner = left.network.nextSerial owner := by
    rw [networks]
  simp only [runInteractionPlan, PMF.bind_pure, interactionStep, interactionInstruction,
    firstSelection, secondSelection, PMF.pure_bind, rightSerial,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
    PMF.pure_map]
  dsimp only [bindingTraffic] at views ⊢
  rw [beforeEnvironment, environment]
  apply congrArg PMF.pure
  exact congrArg (fun read => (read.1, read.2.1,
    after.environmentRecall ++ [⟨after.observeEnvironment app,
      .include (owner, left.network.nextSerial owner)⟩], read.2.2.2)) views

end Vegas.EventGraphRuntime
