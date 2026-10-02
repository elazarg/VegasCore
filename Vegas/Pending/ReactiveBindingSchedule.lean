/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingLikelihood
import GameTheoryExtensions.Math.Probability.Support

/-! # Scheduled opaque bindings under passive observation

A designated existing owner visit submits one canonical binding. All other
visits retain silence and known-envelope replay. The actual roster law has
the same foreign auxiliary readout for any private binding result. The owner
case requires the same private result. The policy uses only its actual response
count to choose the visit.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem bindingTraffic_activation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal actor : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (sample : Finset (MessageId Player)) :
    runtime.bindingTraffic leaks focal
        (left.sampledActivation (runtime.reactiveApplication leaks) actor sample) =
      runtime.bindingTraffic leaks focal
        (right.sampledActivation (runtime.reactiveApplication leaks) actor sample) := by
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun value => value.2.1) same
  have environments := congrArg (fun value => value.2.2.1) same
  have privateViews := congrArg (fun value => value.2.2.2) same
  have publics := congrArg (fun value => value.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts environments privateViews publics
  have observed : left.observeEnvironment (runtime.reactiveApplication leaks) =
      right.observeEnvironment (runtime.reactiveApplication leaks) := by
    change ReactiveApplication.EnvironmentView.mk left.network.publicView
      left.application.publicView left.receipts = _
    rw [networks, publics, receipts]
    rfl
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext ?_ privateViews))
  · change left.network.learn actor sample = right.network.learn actor sample
    rw [networks]
  · change left.environmentRecall ++ [⟨left.observeEnvironment _, .activate actor⟩] = _
    rw [environments, observed]
    rfl

theorem bindingTraffic_replay (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (left right : (runtime.reactiveApplication leaks).Execution) (focal actor : Player)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
    runtime.bindingTraffic leaks focal
        (left.respond (runtime.reactiveApplication leaks) actor response) =
      runtime.bindingTraffic leaks focal
        (right.respond (runtime.reactiveApplication leaks) actor response) := by
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
  have recalledAfter := app.respond_focal_recall_eq left right actor focal response
    networks observed recalled (by
      intro submission transmitted
      rcases transport with rfl | ⟨id, rfl⟩ <;> cases transmitted)
  have firstState : (left.respond app actor response).application = left.application := by
    rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
  have secondState : (right.respond app actor response).application = right.application := by
    rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
  refine Prod.ext ?_ (Prod.ext receipts (Prod.ext environments (Prod.ext recalledAfter ?_)))
  · rcases transport with rfl | ⟨id, rfl⟩
    · exact networks
    · change (left.network.replay actor id).2 = (right.network.replay actor id).2
      rw [networks]
  · change ((left.respond app actor response).application.playerView focal,
        (left.respond app actor response).application.publicView) =
      ((right.respond app actor response).application.playerView focal,
        (right.respond app actor response).application.publicView)
    rw [firstState, secondState]
    exact Prod.ext views publics

/-- One latent binding slot couples the actual whole roster, including every
earlier observation and replay. Submission results may differ for foreign
observers; the owner sees the same result on both sides. -/
theorem scheduled_binding_window_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial offset : Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length) :
    let app := runtime.reactiveApplication leaks
    let players := fun result => Function.update (fun _ => app.replayPolicy) owner
      (app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure (runtime.reactiveBinding leaks owner event payload result serial))
        app.replayPolicy)
    (runtime.runInteractionPlan leaks (players first) network
      (roster.map ServiceInstruction.player) left).map (runtime.bindingTraffic leaks focal) =
    (runtime.runInteractionPlan leaks (players second) network
      (roster.map ServiceInstruction.player) right).map (runtime.bindingTraffic leaks focal) := by
  intro app players
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
      have replay := app.replayPolicy_eq_of_network_eq before after actor
        beforeRecall afterRecall (congrArg Prod.fst matched)
      have waiting (firstLaw secondLaw : app.Policy)
          (firstEq : firstLaw (before.recall actor) (before.observe app actor) =
            app.replayPolicy (before.recall actor) (before.observe app actor))
          (secondEq : secondLaw (after.recall actor) (after.observe app actor) =
            app.replayPolicy (after.recall actor) (after.observe app actor)) :
          (firstLaw (before.recall actor) (before.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks (players first) network
              (rest.map ServiceInstruction.player) (before.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) =
          (secondLaw (after.recall actor) (after.observe app actor)).bind
            (fun response => (runtime.runInteractionPlan leaks (players second) network
              (rest.map ServiceInstruction.player) (after.respond app actor response)).map
                (runtime.bindingTraffic leaks focal)) := by
        rw [firstEq, secondEq, replay]
        apply bind_congr_on_support _
        intro response supported
        apply ih _ _ (app.respond_inputRecall before actor response beforeRecall)
          (app.respond_inputRecall after actor response afterRecall)
        · exact runtime.bindingTraffic_replay leaks before after focal actor matched response
            (app.replayPolicy_cases _ _ response supported)
        · simpa only [app.respond_recall_length] using
            congrArg (fun length => length + if actor = owner then 1 else 0) activationCounts
      change ((players first actor) (before.recall actor) (before.observe app actor)).bind _ =
        ((players second actor) (after.recall actor) (after.observe app actor)).bind _
      by_cases acts : actor = owner
      · subst actor
        by_cases now : selected.map (fun slot => offset + slot.val) =
            some (before.recall owner).length
        · have nextNow : selected.map (fun slot => offset + slot.val) =
              some (after.recall owner).length := activationCounts ▸ now
          have firstNow : players first owner (before.recall owner) (before.observe app owner) =
              PMF.pure (runtime.reactiveBinding leaks owner event payload first serial) := by
            simp only [players, Function.update_self, ReactiveApplication.scheduledPolicy,
              ite_eq_left now]
          have secondNow : players second owner (after.recall owner) (after.observe app owner) =
              PMF.pure (runtime.reactiveBinding leaks owner event payload second serial) := by
            simp only [players, Function.update_self, ReactiveApplication.scheduledPolicy,
              ite_eq_left nextNow]
          rw [firstNow, secondNow, PMF.pure_bind, PMF.pure_bind]
          apply ih _ _ (app.respond_inputRecall before owner _ beforeRecall)
            (app.respond_inputRecall after owner _ afterRecall)
          · have exactResponse := runtime.binding_replay_window_coupling leaks network []
              before after beforeRecall afterRecall owner focal event payload
                first second visible serial matched
            simp only [List.map_nil, runInteractionPlan, PMF.pure_map] at exactResponse
            have supported : runtime.bindingTraffic leaks focal
                (before.respond app owner
                  (runtime.reactiveBinding leaks owner event payload first serial)) ∈
                (PMF.pure (runtime.bindingTraffic leaks focal
                  (before.respond app owner
                    (runtime.reactiveBinding leaks owner event payload first serial)))).support :=
              (PMF.mem_support_pure_iff _ _).mpr rfl
            rw [exactResponse] at supported
            exact (PMF.mem_support_pure_iff _ _).mp supported
          · simpa only [app.respond_recall_length, ite_true] using
              congrArg (· + 1) activationCounts
        · have nextNot : selected.map (fun slot => offset + slot.val) ≠
              some (after.recall owner).length := by simpa only [activationCounts] using now
          apply waiting
          · simp only [players, Function.update_self, ReactiveApplication.scheduledPolicy,
              ite_eq_right now]
          · simp only [players, Function.update_self, ReactiveApplication.scheduledPolicy,
              ite_eq_right nextNot]
      · apply waiting
        · simp only [players, Function.update_of_ne acts]
        · simp only [players, Function.update_of_ne acts]

/-- A common timing lottery is realized as one actual behavioral policy.
Its full foreign window law is independent of the hidden binding result.
Taking `choices = timing.map some` makes the binding mandatory in the chosen
finite roster; the latent timing adds no player state to the runtime. -/
theorem scheduled_binding_mixture_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial offset : Nat)
    {slots : Nat} (choices : PMF (Option (Fin slots)))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length)
    (before : (left.recall owner).length ≤ offset) :
    let app := runtime.reactiveApplication leaks
    let family := fun result selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure (runtime.reactiveBinding leaks owner event payload result serial))
      app.replayPolicy
    let players := fun result => Function.update (fun _ => app.replayPolicy) owner
      (app.policyMixture choices (family result)).policy
    (runtime.runInteractionPlan leaks (players first) network
      (roster.map ServiceInstruction.player) left).map (runtime.bindingTraffic leaks focal) =
    (runtime.runInteractionPlan leaks (players second) network
      (roster.map ServiceInstruction.player) right).map (runtime.bindingTraffic leaks focal) := by
  intro app family players
  have realize (result : PublicationResult (L.Val payload)) (start : app.Execution)
      (earlier : (start.recall owner).length ≤ offset) :
      runtime.runInteractionPlan leaks (players result) network
          (roster.map ServiceInstruction.player) start =
        choices.bind (fun selected => runtime.runInteractionPlan leaks
          (Function.update (fun _ => app.replayPolicy) owner (family result selected)) network
            (roster.map ServiceInstruction.player) start) := by
    have actual := runtime.runInteractionPlan_policyMixture leaks choices (family result) owner
      (fun _ => app.replayPolicy) network (roster.map ServiceInstruction.player) start
    have dormant := app.policyMixture_posterior_dormant choices (family result)
      app.replayPolicy offset (fun selected past view bound =>
        app.scheduledPolicy_before offset selected _ app.replayPolicy past view bound)
          (start.recall owner) earlier
    dsimp only at actual
    rw [dormant] at actual
    exact actual.symm
  rw [realize first left before, realize second right (counts ▸ before),
    PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro selected _
  exact runtime.scheduled_binding_window_coupling leaks network roster left right
    leftRecall rightRecall owner focal event payload first second visible serial offset
      selected same counts

private theorem scheduled_binding_packets (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial offset : Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (old : List (Message Player (WitnessedPacket graph)))
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (ledger : initial.network.ledger = old)
    (packets : initial.network.Satisfies fun message => message.id ∈ old.map Message.id ∨
      ∃ token, message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩) :
    let app := runtime.reactiveApplication leaks
    let players := Function.update (fun _ => app.replayPolicy) owner
      (app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure (runtime.reactiveBinding leaks owner event payload result serial))
        app.replayPolicy)
    final ∈ (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) initial).support →
    final.network.ledger = old ∧ final.network.Satisfies fun message =>
      message.id ∈ old.map Message.id ∨
        ∃ token, message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩ := by
  intro app players reached
  induction roster generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨ledger, packets⟩
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached
      obtain ⟨sample, _, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, chosen, reached⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ reached)
      let current := initial.sampledActivation app actor sample
      have currentPackets := packets.learn actor sample
      have data : (current.respond app actor response).network.ledger = old ∧
          (current.respond app actor response).network.Satisfies fun message =>
            message.id ∈ old.map Message.id ∨
              ∃ token,
                message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩ := by
        have replay (supported : response ∈
            (app.replayPolicy (current.recall actor) (current.observe app actor)).support) :
            (current.respond app actor response).network.ledger = old ∧
            (current.respond app actor response).network.Satisfies fun message =>
              message.id ∈ old.map Message.id ∨
                ∃ token,
                  message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩ := by
          rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩
          · exact ⟨ledger, currentPackets⟩
          · refine ⟨?_, currentPackets.replay actor id⟩
            change (current.network.replay actor id).2.ledger = old
            unfold MessageNetwork.replay
            split <;> exact ledger
        by_cases acting : actor = owner
        · subst actor
          simp only [players, Function.update_self] at chosen
          unfold ReactiveApplication.scheduledPolicy at chosen
          split at chosen
          · cases (PMF.mem_support_pure_iff _ _).mp chosen
            cases result <;>
              exact ⟨ledger, currentPackets.submit owner _
                (Or.inr ⟨_, reactiveApplication_packet_none runtime leaks current.application owner
                  (current.network.known owner) _⟩)⟩
          · exact replay chosen
        · have chosenReplay : response ∈
              (app.replayPolicy (current.recall actor) (current.observe app actor)).support := by
            simpa only [players, Function.update_of_ne acting] using chosen
          exact replay chosenReplay
      exact ih (current.respond app actor response) data.1 data.2 reached

private theorem bindingTraffic_reserved (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players firstPlayers : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (focal owner : Player)
    (event : graph.EventId) (serial : Nat)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (packets : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id ∨
        ∃ token, message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩) :
    (runtime.interactionStep leaks players network (.includeLatest event owner) left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.interactionStep leaks firstPlayers network (.includeLatest event owner) right).map
        (runtime.bindingTraffic leaks focal) := by
  let app := runtime.reactiveApplication leaks
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) same
  have observed : left.observeEnvironment app = right.observeEnvironment app := by
    have observed : app.observePublic left.application = app.observePublic right.application :=
      publics
    simp only [ReactiveApplication.Execution.observeEnvironment, networks, receipts, observed]
  cases selected : left.network.pending.reverse.find? (fun message =>
      message.sender = owner ∧ message.payload.call.event? graph = some event ∧
        message.id ∉ left.network.ledger.map Message.id) with
  | none =>
      have command : runtime.reactiveLatest leaks event owner
          (left.observeEnvironment (runtime.reactiveApplication leaks)) =
          .wait := by
        simp only [reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
          MessageNetwork.publicView, ReactiveApplication.EnvironmentView.Unpublished, selected]
      have nextCommand : runtime.reactiveLatest leaks event owner
          (right.observeEnvironment (runtime.reactiveApplication leaks)) = .wait :=
        observed ▸ command
      simp only [interactionStep, interactionInstruction, command, nextCommand,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.Execution.environmentStep, ReactiveApplication.resume,
        PMF.pure_map]
      apply congrArg PMF.pure
      have privateViews := congrArg (fun value => value.2.2.2) same
      refine Prod.ext networks (Prod.ext receipts (Prod.ext ?_ privateViews))
      change left.environmentRecall ++ [⟨left.observeEnvironment app, .wait⟩] = _
      rw [environments, observed]
      rfl
  | some chosen =>
      have chosenGood : chosen.sender = owner ∧
          chosen.payload.call.event? graph = some event ∧
          chosen.id ∉ left.network.ledger.map Message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some selected
      have pending := List.mem_reverse.mp (List.mem_of_find?_eq_some selected)
      have command : runtime.reactiveLatest leaks event owner
          (left.observeEnvironment (runtime.reactiveApplication leaks)) =
          .include chosen.id := by
        simp only [reactiveLatest, ReactiveApplication.Execution.observeEnvironment,
          MessageNetwork.publicView, ReactiveApplication.EnvironmentView.Unpublished, selected]
      have nextCommand : runtime.reactiveLatest leaks event owner
          (right.observeEnvironment (runtime.reactiveApplication leaks)) = .include chosen.id :=
        observed ▸ command
      have nextEqual : runtime.bindingTraffic leaks focal (left.includePending app chosen.id) =
          runtime.bindingTraffic leaks focal (right.includePending app chosen.id) := by
        cases found : left.network.lookup chosen.id with
        | none =>
            have excluded := List.find?_eq_none.mp found chosen pending
            exact False.elim (excluded (decide_eq_true_iff.mpr rfl))
        | some packet =>
            have idEq : packet.id = chosen.id := by
              simpa only [decide_eq_true_eq] using List.find?_some found
            have shape := (packets.lookup chosen.id packet found).resolve_left
              (by simpa only [idEq] using chosenGood.2.2)
            obtain ⟨token, shape⟩ := shape
            have packetEq : packet =
                ⟨chosen.id, ⟨.commitment event (owner, .prepared serial), none, token⟩⟩ := by
              cases packet
              cases idEq
              cases shape
              rfl
            rw [packetEq] at found
            exact runtime.bindingTraffic_include leaks focal left right same chosen.id event
              (owner, .prepared serial) none token found
      have nextNetworks := congrArg Prod.fst nextEqual
      have nextReceipts := congrArg (fun value => value.2.1) nextEqual
      have nextPrivate := congrArg (fun value => value.2.2.2) nextEqual
      simp only [interactionStep, interactionInstruction, command, nextCommand,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.Execution.environmentStep, ReactiveApplication.resume,
        PMF.pure_map]
      apply congrArg PMF.pure
      refine Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext ?_ nextPrivate))
      change left.environmentRecall ++ [⟨left.observeEnvironment app, .include chosen.id⟩] = _
      rw [environments, observed]
      rfl

/-- The chosen-slot coupling includes actual protected final inclusion. The
only unspent traffic is a canonical opaque binding; all prior published copies
remain in the network. Receipt and acceptance equality are derived. -/
theorem scheduled_binding_inclusion_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial offset : Nat)
    {slots : Nat} (selected : Option (Fin slots))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length)
    (published : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id) :
    let app := runtime.reactiveApplication leaks
    let players := fun result => Function.update (fun _ => app.replayPolicy) owner
      (app.scheduledPolicy offset selected
        (fun _ _ => PMF.pure (runtime.reactiveBinding leaks owner event payload result serial))
        app.replayPolicy)
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    (runtime.runInteractionPlan leaks (players first) network phase left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks (players second) network phase right).map
        (runtime.bindingTraffic leaks focal) := by
  intro app players phase
  have prefixLaw := runtime.scheduled_binding_window_coupling leaks network roster left right
    leftRecall rightRecall owner focal event payload first second visible serial offset
      selected same counts
  dsimp only [phase]
  rw [runInteractionPlan_append, runInteractionPlan_append,
    PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ _ _ prefixLaw
  intro before beforeSupport after _afterSupport equal
  have packets := runtime.scheduled_binding_packets leaks network roster owner event payload
    first serial offset selected left.network.ledger left before rfl
      (published.mono (fun _ known => Or.inl known)) beforeSupport
  have safe : before.network.Satisfies fun message =>
      message.id ∈ before.network.ledger.map Message.id ∨
        ∃ token, message.payload = ⟨.commitment event (owner, .prepared serial), none, token⟩ := by
    apply packets.2.mono
    intro message good
    rcases good with known | canonical
    · exact Or.inl (by rw [packets.1]; exact known)
    · exact Or.inr canonical
  simpa only [runInteractionPlan, PMF.bind_pure] using
    runtime.bindingTraffic_reserved leaks (players first) (players second) network focal owner
      event serial before after equal safe

/-- Value-independent randomized binding timing and real protected inclusion
preserve the whole foreign auxiliary law. This is the behavioral realization
of the finite timing family, including all observations before submission. -/
theorem scheduled_binding_mixture_inclusion_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial offset : Nat)
    {slots : Nat} (choices : PMF (Option (Fin slots)))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (counts : (left.recall owner).length = (right.recall owner).length)
    (before : (left.recall owner).length ≤ offset)
    (published : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id) :
    let app := runtime.reactiveApplication leaks
    let family := fun result selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure (runtime.reactiveBinding leaks owner event payload result serial))
      app.replayPolicy
    let players := fun result => Function.update (fun _ => app.replayPolicy) owner
      (app.policyMixture choices (family result)).policy
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    (runtime.runInteractionPlan leaks (players first) network phase left).map
        (runtime.bindingTraffic leaks focal) =
      (runtime.runInteractionPlan leaks (players second) network phase right).map
        (runtime.bindingTraffic leaks focal) := by
  intro app family players phase
  have realize (result : PublicationResult (L.Val payload)) (start : app.Execution)
      (earlier : (start.recall owner).length ≤ offset) :
      runtime.runInteractionPlan leaks (players result) network phase start =
        choices.bind (fun selected => runtime.runInteractionPlan leaks
          (Function.update (fun _ => app.replayPolicy) owner (family result selected)) network
            phase start) := by
    have actual := runtime.runInteractionPlan_policyMixture leaks choices (family result) owner
      (fun _ => app.replayPolicy) network phase start
    have dormant := app.policyMixture_posterior_dormant choices (family result)
      app.replayPolicy offset (fun selected past view bound =>
        app.scheduledPolicy_before offset selected _ app.replayPolicy past view bound)
          (start.recall owner) earlier
    dsimp only at actual
    rw [dormant] at actual
    exact actual.symm
  rw [realize first left before, realize second right (counts ▸ before),
    PMF.map_bind, PMF.map_bind]
  apply bind_congr_on_support _
  intro selected _
  exact runtime.scheduled_binding_inclusion_coupling leaks network roster left right
    leftRecall rightRecall owner focal event payload first second visible serial offset
      selected same counts published

end Vegas.EventGraphRuntime
