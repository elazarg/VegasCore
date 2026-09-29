/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSchedule
import Vegas.Pending.ReactiveOpeningSettlement
import Vegas.Pending.ReactiveRevealBlock

/-! # Opening windows after private binding histories

These couplings retain the real network, service recall, focal input and focal
private recall. They do not equate other players' earlier private submissions.
The opening response still uses authentic candidate evidence and every passive
sample and known-envelope replay remains in the actual execution.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_opening (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (owner focal : Player)
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftValid : left.application.candidates.lookup candidate = .openable raw)
    (rightValid : right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    runtime.bindingTraffic leaks focal
        (left.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowOpening leaks event candidate raw)) =
      runtime.bindingTraffic leaks focal
        (right.respond (runtime.reactiveApplication leaks) owner
          (runtime.windowOpening leaks event candidate raw)) := by
  let app := runtime.reactiveApplication leaks
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
  have emitted : app.packet left.application owner (left.network.known owner)
        (disclosureSubmission (.opening event candidate raw)) =
      app.packet right.application owner (right.network.known owner)
        (disclosureSubmission (.opening event candidate raw)) :=
    (runtime.windowOpening_packet leaks owner event candidate raw left.application
      (left.network.known owner) owned leftValid).trans
        (runtime.windowOpening_packet leaks owner event candidate raw right.application
          (right.network.known owner) owned rightValid).symm
  have recallEq := app.respond_focal_recall_eq left right owner focal
    (runtime.windowOpening leaks event candidate raw) networks observed recalled (by
      intro submission transmitted
      have selected : disclosureSubmission (.opening event candidate raw) = submission :=
        ReactiveApplication.Transmission.submit.inj (Option.some.inj transmitted)
      subst submission
      exact emitted)
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments
    (Prod.ext recallEq (Prod.ext views publics))))
  change (left.network.submit owner (app.packet left.application owner
    (left.network.known owner) (disclosureSubmission (.opening event candidate raw)))).2 = _
  rw [emitted, networks]
  rfl

/-- The actual scheduled opening window preserves this smaller focal readout.
Candidate tables and private binding submissions of every foreign player may
differ. If no slot is selected, no validity assumption is needed. -/
theorem openingWindow_focal_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner) (offset : Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (leftValid : selected.isSome → left.application.candidates.lookup candidate = .openable raw)
    (rightValid : selected.isSome → right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length) :
    let players := runtime.openingWindowPlayers leaks owner event candidate raw offset selected
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
        PMF.bind_map, PMF.bind_bind]
      rw [networks]
      apply bind_congr_on_support _
      intro sample _
      let before := left.sampledActivation app actor sample
      let after := right.sampledActivation app actor sample
      have beforeRecall : before.InputRecall app := leftRecall
      have afterRecall : after.InputRecall app := rightRecall
      have activationCounts : (before.recall owner).length = (after.recall owner).length := counts
      have matched := runtime.bindingTraffic_activation leaks left right focal actor same sample
      have replay := app.replayPolicy_eq_of_network_eq before after actor beforeRecall
        afterRecall (congrArg Prod.fst matched)
      have waiting
          (firstEq : players actor (before.recall actor) (before.observe app actor) =
            app.replayPolicy (before.recall actor) (before.observe app actor))
          (secondEq : players actor (after.recall actor) (after.observe app actor) =
            app.replayPolicy (after.recall actor) (after.observe app actor)) :
          (players actor (before.recall actor) (before.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) (before.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) =
          (players actor (after.recall actor) (after.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player) (after.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) := by
        rw [firstEq, secondEq, replay]
        apply bind_congr_on_support _
        intro response supported
        have transport := app.replayPolicy_cases _ _ response supported
        have firstState : (before.respond app actor response).application = before.application := by
          rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
        have secondState : (after.respond app actor response).application = after.application := by
          rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
        apply ih _ _ (app.respond_inputRecall before actor response beforeRecall)
          (app.respond_inputRecall after actor response afterRecall)
        · rwa [firstState]
        · rwa [secondState]
        · exact runtime.bindingTraffic_replay leaks before after focal actor matched
            response transport
        · simpa only [app.respond_recall_length] using
            congrArg (fun length => length + if actor = owner then 1 else 0) activationCounts
      change (players actor (before.recall actor) (before.observe app actor)).bind _ =
        (players actor (after.recall actor) (after.observe app actor)).bind _
      by_cases acts : actor = owner
      · subst actor
        by_cases now : selected.map (fun slot => offset + slot.val) =
            some (before.recall owner).length
        · have nextNow : selected.map (fun slot => offset + slot.val) =
              some (after.recall owner).length := activationCounts ▸ now
          have chosen : selected.isSome := by
            cases selected <;> simp_all
          have firstNow : players owner (before.recall owner) (before.observe app owner) =
              PMF.pure (runtime.windowOpening leaks event candidate raw) := by
            simp only [players, openingWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_left now]
          have secondNow : players owner (after.recall owner) (after.observe app owner) =
              PMF.pure (runtime.windowOpening leaks event candidate raw) := by
            simp only [players, openingWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_left nextNow]
          rw [firstNow, secondNow, PMF.pure_bind, PMF.pure_bind]
          apply ih (before.respond app owner (runtime.windowOpening leaks event candidate raw))
            (after.respond app owner (runtime.windowOpening leaks event candidate raw))
            (app.respond_inputRecall before owner _ beforeRecall)
            (app.respond_inputRecall after owner _ afterRecall) leftValid rightValid
          · exact runtime.bindingTraffic_opening leaks before after owner focal event candidate raw
              owned (leftValid chosen) (rightValid chosen) matched
          · simpa only [app.respond_recall_length, ite_true] using
              congrArg (· + 1) activationCounts
        · have nextNot : selected.map (fun slot => offset + slot.val) ≠
              some (after.recall owner).length := by simpa only [activationCounts] using now
          apply waiting
          · simp only [players, app, openingWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_right now]
          · simp only [players, app, openingWindowPlayers, ite_true,
              ReactiveApplication.scheduledPolicy, ite_eq_right nextNot]
      · apply waiting <;> simp only [players, app, openingWindowPlayers, ite_eq_right acts]

private theorem bindingTraffic_include_of_handler (runtime : EventGraphRuntime graph)
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

/-- Protected inclusion preserves focal likelihood once the actual canonical
handler results agree. This operational premise concerns the concrete packet;
source guards discharge it by their actual successful completion equations. -/
theorem openingWindow_inclusion_focal_coupling (runtime : EventGraphRuntime graph)
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
    (owner focal : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner) (selected : Option (Fin (roster.count owner)))
    (leftValid : selected.isSome → left.application.candidates.lookup candidate = .openable raw)
    (rightValid : selected.isSome → right.application.candidates.lookup candidate = .openable raw)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length)
    (handled : selected.isSome →
      ((runtime.reactiveApplication leaks).handle left.application
        (runtime.windowEnvelope leaks owner event candidate raw left)).map
          (fun state => state.playerView focal) =
      ((runtime.reactiveApplication leaks).handle right.application
        (runtime.windowEnvelope leaks owner event candidate raw left)).map
          (fun state => state.playerView focal)) :
    let players := runtime.openingWindowPlayers leaks owner event candidate raw
      (left.recall owner).length selected
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) right).map
          (runtime.bindingTraffic leaks focal) := by
  intro players
  let app := runtime.reactiveApplication leaks
  have windows := runtime.openingWindow_focal_coupling leaks network roster left right
    leftRecall rightRecall owner focal event candidate raw owned (left.recall owner).length
      selected leftValid rightValid same counts
  rw [runInteractionPlan_append, runInteractionPlan_append, PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ windows
  intro before beforeSupport after afterSupport equal
  have leftStart := OpeningWindowFrame.initial runtime leaks owner event candidate raw selected
    left leftSerials leftPublished
  have rightStart := OpeningWindowFrame.initial runtime leaks owner event candidate raw selected
    right rightSerials rightPublished
  have first := leftStart.run runtime leaks owner event candidate raw (left.recall owner).length
    selected 0 left left network roster before beforeSupport owned leftValid
  have second := rightStart.run runtime leaks owner event candidate raw (right.recall owner).length
    selected 0 right right network roster after (by simpa only [← counts] using afterSupport)
      owned rightValid
  simp only [Nat.zero_add] at first second
  have firstSelection := first.selection runtime leaks owner event candidate raw
    (left.recall owner).length selected left before leftSerials
  have secondSelection := second.selection runtime leaks owner event candidate raw
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
  simp only [runInteractionPlan, PMF.bind_pure, interactionStep, interactionInstruction,
    firstSelection, secondSelection, PMF.pure_bind]
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind]
      dsimp only [bindingTraffic]
      rw [beforeEnvironment, environment]
      apply congrArg PMF.pure
      exact congrArg (fun read => (read.1, read.2.1,
        after.environmentRecall ++ [⟨after.observeEnvironment app, .wait⟩], read.2.2.2)) equal
  | some slot =>
      have opened : openingPassed (some slot) (roster.count owner) = true := by
        simpa only [openingPassed, Option.any_some, decide_eq_true_eq] using slot.isLt
      have found := first.lookup_opened runtime leaks owner event candidate raw
        (left.recall owner).length (some slot) (roster.count owner) left before leftSerials opened
      have views := bindingTraffic_include_of_handler runtime leaks before after focal equal
        (owner, left.network.nextSerial owner)
          (runtime.windowEnvelope leaks owner event candidate raw left) found (by
            rw [first.application, second.application]
            exact handled rfl)
      have rightSerial : right.network.nextSerial owner = left.network.nextSerial owner := by
        rw [networks]
      simp only [Option.isSome_some, ↓reduceIte, rightSerial,
        ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind]
      dsimp only [bindingTraffic] at views ⊢
      rw [beforeEnvironment, environment]
      apply congrArg PMF.pure
      exact congrArg (fun read => (read.1, read.2.1,
        after.environmentRecall ++ [⟨after.observeEnvironment app,
          .include (owner, left.network.nextSerial owner)⟩], read.2.2.2)) views

/-- Real clock, grant and expiry commands preserve the focal traffic law.
Public chance is handled with its source sample, rather than by this lemma. -/
theorem bindingTraffic_maintenance (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (command : EnvironmentCommand graph)
    (maintenance : ∀ event, command ≠ .executeSample event) :
    (left.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingTraffic leaks focal) =
      (right.environmentStep (runtime.reactiveApplication leaks) (.application command)).map
        (runtime.bindingTraffic leaks focal) := by
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
  have environment : left.observeEnvironment app = right.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  have changes := maintenance_playerView_congr runtime left.application right.application focal
    command maintenance views
  simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
  change ((environmentStep runtime left.application command).map _) =
    ((environmentStep runtime right.application command).map _)
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_eq_of_map_eq _ _ _ _ changes
  intro before _ after _ equal
  apply congrArg PMF.pure
  dsimp only [bindingTraffic, Function.comp_apply]
  rw [networks, receipts, environments, environment, recalled, equal]
  exact congrArg (fun publicView => (right.network, right.receipts,
    right.environmentRecall ++ [⟨right.observeEnvironment app, .application command⟩],
      right.recall focal, after.playerView focal, publicView))
        (congrArg PlayerView.publicView equal)

/-- The complete clock/expiry suffix preserves the coupled readout, including
its actual scheduler observations. No response-policy equality is required. -/
theorem settlement_focal_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (ticks : Nat)
    (left right : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    (runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]) left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks players network
        (List.replicate ticks .tick ++ [.expire event]) right).map
          (runtime.bindingTraffic leaks focal) := by
  have waiting : (runtime.reactiveApplication leaks).resume players none = PMF.pure := rfl
  induction ticks generalizing left right with
  | zero =>
      simpa only [List.replicate_zero, List.nil_append, runInteractionPlan, PMF.bind_pure,
        interactionStep, interactionInstruction, PMF.pure_bind, ReactiveApplication.dispatch,
        ReactiveApplication.Command.actor?, waiting] using
        runtime.bindingTraffic_maintenance leaks left right focal same (.expire event)
          (fun _ impossible => by cases impossible)
  | succ ticks ih =>
      have step : (runtime.interactionStep leaks players network .tick left).map
          (runtime.bindingTraffic leaks focal) =
        (runtime.interactionStep leaks players network .tick right).map
          (runtime.bindingTraffic leaks focal) := by
        simpa only [interactionStep, interactionInstruction, PMF.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
          waiting, PMF.bind_pure] using
          runtime.bindingTraffic_maintenance leaks left right focal same .advanceClock
            (fun _ impossible => by cases impossible)
      simp only [List.replicate_succ, List.cons_append, runInteractionPlan, PMF.map_bind]
      apply bind_eq_of_map_eq _ _ _ _ step
      intro before _ after _ equal
      exact ih before after equal

/-- Withholding uses the real replay roster, waits at protected inclusion and
then expires. This branch needs no opening value or successful guard. -/
theorem withholdingWindow_focal_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (owner focal : Player) (event : graph.EventId) (ticks : Nat)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    let app := runtime.reactiveApplication leaks
    let phase := roster.map ServiceInstruction.player ++
      (.includeLatest event owner :: (List.replicate ticks .tick ++ [.expire event]))
    (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network phase left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network phase right).map
        (runtime.bindingTraffic leaks focal) := by
  intro app phase
  have windows := runtime.replay_window_focal_law leaks network roster focal left right
    leftRecall rightRecall same
  have stillPublished (initial final : app.Execution)
      (clean : initial.network.Satisfies fun message =>
        message.id ∈ initial.network.ledger.map Message.id)
      (reached : final ∈ (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network
        (roster.map ServiceInstruction.player) initial).support) :
      final.network.Satisfies fun message => message.id ∈ final.network.ledger.map Message.id := by
    obtain ⟨_, ledger, _, _, packets, _⟩ := runtime.replay_window_preserves leaks
      (fun _ => app.replayPolicy) network owner initial
      (fun current who response _ _ supported => app.replayPolicy_cases
        (current.recall who) (current.observe app who) response supported)
        _ clean roster final reached
    rw [ledger]
    exact packets
  dsimp only [phase]
  rw [runInteractionPlan_append, runInteractionPlan_append, PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ windows
  intro before beforeSupport after afterSupport equal
  have first := runtime.interaction_includeLatest_of_pending_published leaks
    (fun _ => app.replayPolicy) network before owner event
      (stillPublished left before leftPublished beforeSupport).pending
  have second := runtime.interaction_includeLatest_of_pending_published leaks
    (fun _ => app.replayPolicy) network after owner event
      (stillPublished right after rightPublished afterSupport).pending
  simp only [runInteractionPlan, first, second, PMF.map_bind]
  have networks : before.network = after.network := congrArg Prod.fst equal
  have receipts : before.receipts = after.receipts := congrArg (fun value => value.2.1) equal
  have environments : before.environmentRecall = after.environmentRecall :=
    congrArg (fun value => value.2.2.1) equal
  have publics : before.application.publicView = after.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) equal
  have environment : before.observeEnvironment app = after.observeEnvironment app := by
    change ReactiveApplication.EnvironmentView.mk before.network.publicView
      before.application.publicView before.receipts = _
    rw [networks, publics, receipts]
    rfl
  simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind]
  apply runtime.settlement_focal_law
  dsimp only [bindingTraffic]
  rw [environments, environment]
  exact congrArg (fun read => (read.1, read.2.1,
    after.environmentRecall ++ [⟨after.observeEnvironment app, .wait⟩], read.2.2.2)) equal

end Vegas.EventGraphRuntime
