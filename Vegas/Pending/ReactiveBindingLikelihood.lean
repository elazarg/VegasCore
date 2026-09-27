/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingObservation
import Vegas.Pending.ReactiveContinuationObservation
import Vegas.Pending.ReactivePolicyMixture
import Vegas.Pending.ReactiveReplaySettlement
import Interaction.ReactiveReplayPolicy

/-! # Actual communication likelihood during an opaque binding window

The auxiliary projection retains the complete network, service recall, and
focal private input. Other players' private submission parameters are absent
from this proof projection. They remain in actual runtime recall. A shared
passive sample couples arbitrary replay multiplicities without an assumption
on the observation rule.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Existing native fields sufficient for the replay window's joint law.
This is a proof readout; it is not a player's observation or extra state. -/
def bindingTraffic (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (execution : (runtime.reactiveApplication leaks).Execution) :=
  (execution.network, execution.receipts, execution.environmentRecall, execution.recall focal,
    execution.application.playerView focal, execution.application.publicView)

theorem bindingTraffic_include (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (focal : Player) (left right : (runtime.reactiveApplication leaks).Execution)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (evidence : Option (OpeningFact graph))
    (found : left.network.lookup id = some ⟨id, ⟨.commitment event candidate, evidence⟩⟩) :
    runtime.bindingTraffic leaks focal
        (left.includePending (runtime.reactiveApplication leaks) id) =
      runtime.bindingTraffic leaks focal
        (right.includePending (runtime.reactiveApplication leaks) id) := by
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
  have rightFound : right.network.lookup id =
      some ⟨id, ⟨.commitment event candidate, evidence⟩⟩ := networks ▸ found
  have handled := handle_commitment_playerView_congr runtime left.application right.application
    focal id event candidate views
  simp only [bindingTraffic, ReactiveApplication.Execution.includePending,
    MessageNetwork.includePending, found, rightFound, reactiveApplication]
  cases first : handle runtime left.application ⟨id, .commitment event candidate⟩ with
  | none =>
      cases second : handle runtime right.application ⟨id, .commitment event candidate⟩ with
      | none =>
          simp only [Option.getD_none, Option.isSome_none]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled (Prod.ext views publics))))
      | some after =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          contradiction
  | some before =>
      cases second : handle runtime right.application ⟨id, .commitment event candidate⟩ with
      | none =>
          simp only [first, second, Option.map_none, Option.map_some] at handled
          contradiction
      | some after =>
          simp only [first, second, Option.map_some, Option.some.injEq] at handled
          simp only [Option.getD_some, Option.isSome_some]
          exact Prod.ext (by rw [networks]) (Prod.ext (by rw [receipts])
            (Prod.ext environments (Prod.ext recalled
              (Prod.ext handled (congrArg PlayerView.publicView handled)))))

/-- Equality of the actual auxiliary start is preserved by a finite roster
whose physical responses are the fully supported known-replay/silence law. -/
theorem replay_window_focal_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    ((runtime.runInteractionPlan leaks (fun _ => (runtime.reactiveApplication leaks).replayPolicy)
      network (roster.map ServiceInstruction.player) left).map
        (runtime.bindingTraffic leaks focal)) =
    ((runtime.runInteractionPlan leaks (fun _ => (runtime.reactiveApplication leaks).replayPolicy)
      network (roster.map ServiceInstruction.player) right).map
        (runtime.bindingTraffic leaks focal)) := by
  let app := runtime.reactiveApplication leaks
  induction roster generalizing left right with
  | nil => simpa only [List.map_nil, runInteractionPlan, FinDist.map_pure] using
      congrArg FinDist.pure same
  | cons who rest ih =>
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
      have environmentView : left.observeEnvironment app = right.observeEnvironment app := by
        have observed : app.observePublic left.application = app.observePublic right.application :=
          publics
        simp only [ReactiveApplication.Execution.observeEnvironment, networks, receipts, observed]
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.map_bind,
        FinDist.bind_map, FinDist.bind_bind]
      rw [networks]
      apply FinDist.bind_congr
      intro sample _
      let first := left.sampledActivation app who sample
      let second := right.sampledActivation app who sample
      have firstRecall : first.InputRecall app := leftRecall
      have secondRecall : second.InputRecall app := rightRecall
      have nextNetworks : first.network = second.network := by
        change left.network.learn who sample = right.network.learn who sample
        rw [networks]
      have nextEnvironment : first.environmentRecall = second.environmentRecall := by
        change left.environmentRecall ++ [⟨left.observeEnvironment app, .activate who⟩] = _
        rw [environments, environmentView]
        rfl
      have replay := app.replayPolicy_eq_of_network_eq first second who firstRecall secondRecall
        nextNetworks
      change (app.replayPolicy (first.recall who) (first.observe app who)).bind _ =
        (app.replayPolicy (second.recall who) (second.observe app who)).bind _
      rw [replay]
      apply FinDist.bind_congr
      intro response supported
      have transport := app.replayPolicy_cases _ _ response supported
      have firstState : (first.respond app who response).application = first.application := by
        rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
      have secondState : (second.respond app who response).application = second.application := by
        rcases transport with rfl | ⟨id, rfl⟩ <;> rfl
      have afterNetworks : (first.respond app who response).network =
          (second.respond app who response).network := by
        rcases transport with rfl | ⟨id, rfl⟩
        · exact nextNetworks
        · simp only [ReactiveApplication.Execution.respond, nextNetworks]
      have observed : first.observe app focal = second.observe app focal := by
        have projected := congrArg (fun view : PlayerView graph =>
          (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
            ReactivePlayerView graph)) views
        change ReactiveApplication.PlayerView.mk _ _ _ = _
        rw [nextNetworks]
        exact congrArg₂ (fun view receipts =>
          (⟨second.network.observe focal, view, receipts⟩ : app.PlayerView)) projected receipts
      have recalledAfter := app.respond_focal_recall_eq first second who focal response
        nextNetworks observed recalled (by
          intro submission transmitted
          rcases transport with rfl | ⟨id, rfl⟩ <;> cases transmitted)
      apply ih (first.respond app who response) (second.respond app who response)
        (app.respond_inputRecall first who response firstRecall)
        (app.respond_inputRecall second who response secondRecall)
      refine Prod.ext afterNetworks (Prod.ext receipts (Prod.ext nextEnvironment
        (Prod.ext recalledAfter ?_)))
      change ((first.respond app who response).application.playerView focal,
          (first.respond app who response).application.publicView) =
        ((second.respond app who response).application.playerView focal,
          (second.respond app who response).application.publicView)
      rw [firstState, secondState]
      exact Prod.ext views publics

/-- Distinct private meanings of the same canonical submitted handle produce
the same foreign communication law throughout subsequent replay visits.
For the owner, equality of its observed private result suffices. -/
theorem binding_replay_window_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial : Nat)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right) :
    let app := runtime.reactiveApplication leaks
    FinDist.map (runtime.bindingTraffic leaks focal)
      (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network
      (roster.map ServiceInstruction.player)
        (left.respond app owner
          (runtime.reactiveBinding leaks owner event payload first serial))) =
    FinDist.map (runtime.bindingTraffic leaks focal)
      (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network
      (roster.map ServiceInstruction.player)
        (right.respond app owner
          (runtime.reactiveBinding leaks owner event payload second serial))) := by
  intro app
  apply runtime.replay_window_focal_law leaks network roster focal _ _
    (app.respond_inputRecall left owner _ leftRecall)
    (app.respond_inputRecall right owner _ rightRecall)
  have networks : left.network = right.network := congrArg Prod.fst same
  have receipts : left.receipts = right.receipts := congrArg (fun value => value.2.1) same
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) same
  have recalled : left.recall focal = right.recall focal :=
    congrArg (fun value => value.2.2.2.1) same
  have observed : left.application.playerView focal = right.application.playerView focal :=
    congrArg (fun value => value.2.2.2.2.1) same
  have afterNetworks : (left.respond app owner
        (runtime.reactiveBinding leaks owner event payload first serial)).network =
      (right.respond app owner
        (runtime.reactiveBinding leaks owner event payload second serial)).network := by
    cases first <;> cases second <;>
      change (left.network.submit owner
        ⟨.commitment event (owner, .prepared serial), none⟩).2 = _ <;> rw [networks] <;> rfl
  by_cases different : focal ≠ owner
  · have views (execution : app.Execution) (result : PublicationResult (L.Val payload)) :
        (execution.respond app owner
          (runtime.reactiveBinding leaks owner event payload result serial)).application.playerView
            focal = execution.application.playerView focal := by
      let material : Submission graph := ⟨.commitment event (owner, .prepared serial),
        match result with | .failure => none | .success value => some ⟨payload, value⟩⟩
      exact (submitStep_playerView_other (material.register execution.application owner)
        owner focal different material.packet).trans
          (material.register_other execution.application owner focal different)
    have afterViews := (views left first).trans (observed.trans (views right second).symm)
    dsimp only [bindingTraffic]
    refine Prod.ext afterNetworks (Prod.ext receipts (Prod.ext environments
      (Prod.ext ?_ (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))
    rw [app.respond_recall_other left owner focal different,
      app.respond_recall_other right owner focal different, recalled]
  · have acting : focal = owner := not_ne_iff.mp different
    subst focal
    have equal := visible rfl
    subst second
    have afterViews : (left.respond app owner
          (runtime.reactiveBinding leaks owner event payload first serial)).application.playerView
            owner = (right.respond app owner
          (runtime.reactiveBinding leaks owner event payload first serial)).application.playerView
            owner := by
      cases first <;> exact runtime.submit_playerView_congr leaks _ _ owner _ observed
    have beforeViews : left.observe app owner = right.observe app owner := by
      have projected := congrArg (fun view : PlayerView graph =>
        (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
          ReactivePlayerView graph)) observed
      change ReactiveApplication.PlayerView.mk _ _ _ = _
      rw [networks]
      exact congrArg₂ (fun view receipts =>
        (⟨right.network.observe owner, view, receipts⟩ : app.PlayerView)) projected receipts
    have afterRecall := app.respond_focal_recall_eq left right owner owner
      (runtime.reactiveBinding leaks owner event payload first serial) networks beforeViews
        recalled (by
          intro submission _transmitted
          have submitted := runtime.submit_playerView_congr leaks left.application
            right.application owner submission observed
          change submission.emit (app.submit left.application owner submission) owner
              (left.network.known owner) =
            submission.emit (app.submit right.application owner submission) owner
              (right.network.known owner)
          rw [WitnessedSubmission.emit_eq_resolve, WitnessedSubmission.emit_eq_resolve, networks]
          exact congrArg (fun table => WitnessedPacket.mk submission.call.packet
            (submission.evidence.resolve owner table (right.network.known owner)))
              (congrArg PlayerView.candidates submitted))
    exact Prod.ext afterNetworks (Prod.ext receipts (Prod.ext environments
      (Prod.ext afterRecall (Prod.ext afterViews (congrArg PlayerView.publicView afterViews)))))

private theorem binding_submitted_selection (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (serials : execution.network.SerialsBeforeNext)
    (current : (runtime.reactiveApplication leaks).Execution)
    (supported : current ∈ (runtime.runInteractionPlan leaks
      (fun _ => (runtime.reactiveApplication leaks).replayPolicy) network
      (roster.map ServiceInstruction.player) (execution.respond (runtime.reactiveApplication leaks)
        owner (runtime.reactiveBinding leaks owner event payload result serial))).support) :
    runtime.reactiveLatest leaks event owner
        (current.observeEnvironment (runtime.reactiveApplication leaks)) =
        .include (owner, execution.network.nextSerial owner) ∧
      current.network.lookup (owner, execution.network.nextSerial owner) =
        some ⟨(owner, execution.network.nextSerial owner),
          ⟨.commitment event (owner, .prepared serial), none⟩⟩ := by
  let app := runtime.reactiveApplication leaks
  let submitted := execution.respond app owner
    (runtime.reactiveBinding leaks owner event payload result serial)
  let packet : WitnessedPacket graph := ⟨.commitment event (owner, .prepared serial), none⟩
  let message : Message Player (WitnessedPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have networkEq : submitted.network = (execution.network.submit owner packet).2 := by
    cases result <;> rfl
  have ledger : submitted.network.ledger = execution.network.ledger := by
    rw [networkEq]
    rfl
  have packets : submitted.network.Satisfies fun candidate =>
      candidate.id ∈ submitted.network.ledger.map Message.id ∨ candidate = message := by
    rw [networkEq]
    apply (published.mono (fun candidate prior => Or.inl prior)).submit owner packet
    exact Or.inr rfl
  have pending : message ∈ submitted.network.pending := by
    rw [networkEq]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have unpublished : message.id ∉ submitted.network.ledger.map Message.id := by
    rw [ledger]
    exact serials.next_unpublished owner
  exact runtime.replay_window_selection leaks (fun _ => app.replayPolicy) network owner submitted
    (fun _ _ _ _ _ chosen => app.replayPolicy_cases _ _ _ chosen) event message rfl rfl
      packets pending unpublished roster current supported

/-- The likelihood equality extends through the real protected final inclusion.
All pending copies, sampled leaks and service recall are retained. The owner
case requires the same private binding result. -/
theorem binding_replay_inclusion_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (network : runtime.NetworkPolicy leaks) (roster : List Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (owner focal : Player) (event : graph.EventId)
    (payload : L.Ty) (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second) (serial : Nat)
    (same : runtime.bindingTraffic leaks focal left = runtime.bindingTraffic leaks focal right)
    (published : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (serials : left.network.SerialsBeforeNext) :
    let app := runtime.reactiveApplication leaks
    let phase := roster.map ServiceInstruction.player ++ [.includeLatest event owner]
    FinDist.map (runtime.bindingTraffic leaks focal)
      (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network phase
        (left.respond app owner (runtime.reactiveBinding leaks owner event payload first serial))) =
    FinDist.map (runtime.bindingTraffic leaks focal)
      (runtime.runInteractionPlan leaks (fun _ => app.replayPolicy) network phase
        (right.respond app owner
          (runtime.reactiveBinding leaks owner event payload second serial))) :=
    by
  intro app phase
  have prefixLaw := runtime.binding_replay_window_coupling leaks network roster left right
    leftRecall rightRecall owner focal event payload first second visible serial same
  dsimp only [phase]
  rw [runInteractionPlan_append, runInteractionPlan_append,
    FinDist.map_bind, FinDist.map_bind]
  apply FinDist.bind_eq_of_map_eq _ _ _ _ prefixLaw
  intro before beforeSupport after _afterSupport equal
  obtain ⟨selected, found⟩ := runtime.binding_submitted_selection leaks network roster left owner
    event payload first serial published serials before beforeSupport
  have networks : before.network = after.network := congrArg Prod.fst equal
  have receipts : before.receipts = after.receipts := congrArg (fun value => value.2.1) equal
  have environments : before.environmentRecall = after.environmentRecall :=
    congrArg (fun value => value.2.2.1) equal
  have publics : before.application.publicView = after.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) equal
  have observed : before.observeEnvironment app = after.observeEnvironment app := by
    have observed : app.observePublic before.application = app.observePublic after.application :=
      publics
    simp only [ReactiveApplication.Execution.observeEnvironment, networks, receipts, observed]
  have nextSelected : runtime.reactiveLatest leaks event owner
      (after.observeEnvironment (runtime.reactiveApplication leaks)) =
      .include (owner, left.network.nextSerial owner) := by
    change runtime.reactiveLatest leaks event owner (after.observeEnvironment app) = _
    rw [← observed]
    exact selected
  have nextEqual := runtime.bindingTraffic_include leaks focal before after equal
    (owner, left.network.nextSerial owner) event (owner, .prepared serial) none found
  have nextNetworks := congrArg Prod.fst nextEqual
  have nextReceipts := congrArg (fun value => value.2.1) nextEqual
  have nextPrivate := congrArg (fun value => value.2.2.2) nextEqual
  simp only [runInteractionPlan, FinDist.bind_pure, interactionStep, interactionInstruction,
    selected, nextSelected, FinDist.pure_bind, ReactiveApplication.dispatch,
    ReactiveApplication.resume,
    ReactiveApplication.Command.actor?, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure]
  apply congrArg FinDist.pure
  dsimp only [bindingTraffic]
  refine Prod.ext nextNetworks (Prod.ext nextReceipts (Prod.ext ?_ nextPrivate))
  change before.environmentRecall ++ [⟨before.observeEnvironment app, _⟩] =
    after.environmentRecall ++ [⟨after.observeEnvironment app, _⟩]
  rw [environments, observed]

end Vegas.EventGraphRuntime
