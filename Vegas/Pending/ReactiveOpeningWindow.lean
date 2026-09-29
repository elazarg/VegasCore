/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveReplayPolicy
import Interaction.ScheduledOpening
import Vegas.Pending.ReactivePolicyMixture
import Vegas.Pending.ReactivePolicy
import GameTheoryExtensions.Math.Probability.Conditioning

/-! # Coupling scheduled openings through a finite observation window

The window uses the existing player instructions and passive sampler. Every
player can replay known envelopes; the current owner may emit its canonical
opening at one selected response count. Pending observations and unpublished
replays are retained. Equal auxiliary starts can be coupled without assuming
the sampler ignores message identity or pending-copy multiplicity.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def windowOpening (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨some (.submit (disclosureSubmission (.opening event candidate raw)))⟩

def openingWindowPlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) :
    Player → (runtime.reactiveApplication leaks).Policy := fun who =>
  let app := runtime.reactiveApplication leaks
  if who = owner then app.scheduledPolicy offset selected
    (fun _ _ => PMF.pure (runtime.windowOpening leaks event candidate raw)) app.replayPolicy
  else app.replayPolicy

/-- The behavioral realization of a conditional timing law. Its private
mixture is a proof construction; the actual runtime still receives one
ordinary response policy. -/
def openingWindowMixturePlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) :
    Player → (runtime.reactiveApplication leaks).Policy :=
  let app := runtime.reactiveApplication leaks
  Function.update (fun _ => app.replayPolicy) owner
    (app.policyMixture choices (fun selected => app.scheduledPolicy offset selected
      (fun _ _ => PMF.pure (runtime.windowOpening leaks event candidate raw))
        app.replayPolicy)).policy

theorem openingWindowMixture_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots)))
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (before : (execution.recall owner).length ≤ offset) :
    runtime.runInteractionPlan leaks
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices)
        network plan execution =
      choices.bind fun selected => runtime.runInteractionPlan leaks
        (runtime.openingWindowPlayers leaks owner event candidate raw offset selected)
          network plan execution := by
  let app := runtime.reactiveApplication leaks
  let opening := fun (_ : List app.PlayerEntry) (_ : app.PlayerView) =>
    PMF.pure (runtime.windowOpening leaks event candidate raw)
  let family := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected opening app.replayPolicy
  have posterior := app.policyMixture_posterior_dormant choices family app.replayPolicy offset
    (fun selected past view earlier =>
      app.scheduledPolicy_before offset selected opening app.replayPolicy past view earlier)
    (execution.recall owner) before
  have actual := runtime.runInteractionPlan_policyMixture leaks choices family owner
    (fun _ => app.replayPolicy) network plan execution
  dsimp only at actual
  rw [posterior] at actual
  refine actual.symm.trans ?_
  apply bind_congr_on_support _
  intro selected _
  have players : Function.update (fun _ => app.replayPolicy) owner (family selected) =
      runtime.openingWindowPlayers leaks owner event candidate raw offset selected := by
    funext who past view
    by_cases active : who = owner
    · subst who
      simp only [Function.update_self, openingWindowPlayers, ↓reduceIte]
      rfl
    · simp only [Function.update_of_ne active, openingWindowPlayers, active, ↓reduceIte]
      rfl
  rw [players]

/-- Every supported first opening makes this behavioral mixture permanently
use replay/silence for the rest of the phase. Thus fully mixed approximants
have the required off-path stop behavior before taking their common limit. -/
theorem openingWindowMixture_after_open (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : PMF (Option (Fin slots))) (slot : Fin slots)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (atSlot : past.length = offset + slot.val)
    (opened : entry.action = runtime.windowOpening leaks event candidate raw)
    (supported : runtime.windowOpening leaks event candidate raw ∈
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices
        owner past entry.beforeView).support)
    (suffix : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices
      owner (past ++ [entry] ++ suffix) view =
        (runtime.reactiveApplication leaks).replayPolicy (past ++ [entry] ++ suffix) view := by
  let app := runtime.reactiveApplication leaks
  have distinct : runtime.windowOpening leaks event candidate raw ∉
      (app.replayPolicy past entry.beforeView).support := by
    intro member
    rcases app.replayPolicy_cases past entry.beforeView _ member with impossible | ⟨id, impossible⟩
    · cases impossible
    · cases impossible
  simp only [openingWindowMixturePlayers, Function.update_self] at supported ⊢
  exact app.scheduledMixture_after_open choices offset
    (runtime.windowOpening leaks event candidate raw) app.replayPolicy slot past entry
      atSlot opened distinct supported suffix view

theorem openingWindowPlayers_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected
        who past view).support) :
    (action = ⟨none⟩ ∨ ∃ id, action = ⟨some (.replay id)⟩) ∨
      (who = owner ∧ action = runtime.windowOpening leaks event candidate raw ∧
        selected.isSome) := by
  by_cases active : who = owner
  · simp only [openingWindowPlayers, active, ↓reduceIte,
      ReactiveApplication.scheduledPolicy] at supported
    split at supported
    · rename_i chosen
      refine Or.inr ⟨active, (PMF.mem_support_pure_iff _ _).mp supported, ?_⟩
      cases selected with
      | none => simp at chosen
      | some slot => rfl
    · exact Or.inl
        ((runtime.reactiveApplication leaks).replayPolicy_cases past view action supported)
  · simp only [openingWindowPlayers, active, ↓reduceIte] at supported
    exact Or.inl ((runtime.reactiveApplication leaks).replayPolicy_cases past view action supported)

theorem openingWindowPlayers_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
        (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application =
      execution.application := by
  rcases runtime.openingWindowPlayers_cases leaks owner event candidate raw offset selected
    who _ _ action supported with (rfl | ⟨id, rfl⟩) | ⟨rfl, rfl, _⟩
  · rfl
  · rfl
  · rfl

theorem openingWindowPlayers_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (networks : left.network = right.network)
    (counts : (left.recall who).length = (right.recall who).length) :
    runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
      (left.recall who) (left.observe (runtime.reactiveApplication leaks) who) =
    runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
      (right.recall who) (right.observe (runtime.reactiveApplication leaks) who) := by
  have replay := (runtime.reactiveApplication leaks).replayPolicy_eq_of_network_eq
    left right who leftRecall rightRecall networks
  by_cases active : who = owner
  · subst who
    simp only [openingWindowPlayers, ↓reduceIte,
      ReactiveApplication.scheduledPolicy, counts, replay]
  · simpa only [openingWindowPlayers, active, ↓reduceIte] using replay

theorem windowOpening_packet (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (state : State graph) (known : List (Message Player (WitnessedPacket graph)))
    (owned : candidate.1 = owner) (valid : state.candidates.lookup candidate = .openable raw) :
    (runtime.reactiveApplication leaks).packet state owner known
      (disclosureSubmission (.opening event candidate raw)) =
        ⟨.opening event candidate raw, some ⟨candidate, raw⟩⟩ := by
  have verified : state.candidates.verify candidate raw = true :=
    (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr valid
  simp only [reactiveApplication, disclosureSubmission, WitnessedSubmission.emit,
    owned, verified, and_self, ↓reduceIte]

private theorem openingWindowPlayers_packet_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots)) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected who
        (left.recall who) (left.observe (runtime.reactiveApplication leaks) who)).support)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw) :
    ∀ submission, action.transmission = some (.submit submission) →
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit left.application who submission) who
          (left.network.known who) submission =
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit right.application who submission) who
          (right.network.known who) submission := by
  intro submission transmitted
  rcases runtime.openingWindowPlayers_cases leaks owner event candidate raw offset selected
    who _ _ action supported with (rfl | ⟨id, rfl⟩) | ⟨active, rfl, chosen⟩
  · cases transmitted
  · cases transmitted
  · subst who
    simp only [windowOpening, Option.some.injEq,
      ReactiveApplication.Transmission.submit.injEq] at transmitted
    subst submission
    change (runtime.reactiveApplication leaks).packet left.application owner
      (left.network.known owner) (disclosureSubmission (.opening event candidate raw)) =
        (runtime.reactiveApplication leaks).packet right.application owner
          (right.network.known owner) (disclosureSubmission (.opening event candidate raw))
    rw [windowOpening_packet runtime leaks owner event candidate raw _ _ owned (meaning chosen).1,
      windowOpening_packet runtime leaks owner event candidate raw _ _ owned (meaning chosen).2]

/-- A scheduled opening/replay branch has the same auxiliary transcript law
across hidden application states with equal public and focal observations.
The actual pending pools are coupled, so the sampler remains unrestricted.
The never-opening branch needs no agreement on the hidden committed value. -/
theorem openingWindow_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (messages : (runtime.reactiveApplication leaks).messageView left =
      (runtime.reactiveApplication leaks).messageView right)
    (recall : left.recall focal = right.recall focal)
    (publicView : left.application.publicView = right.application.publicView)
    (privateView : (runtime.reactiveApplication leaks).observePlayer left.application focal =
      (runtime.reactiveApplication leaks).observePlayer right.application focal)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.openingWindowPlayers leaks owner event candidate raw offset selected
    (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
      left).map (fun execution => (app.messageView execution, execution.recall focal)) =
    (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
      right).map (fun execution => (app.messageView execution, execution.recall focal)) := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let players := runtime.openingWindowPlayers leaks owner event candidate raw offset selected
  induction roster generalizing left right with
  | nil =>
      simp only [List.map_nil, runInteractionPlan, PMF.pure_map]
      exact congrArg PMF.pure (Prod.ext messages recall)
  | cons who rest ih =>
      have networks : left.network = right.network := congrArg Prod.fst messages
      have sampled (ids : Finset (MessageId Player)) :
          app.messageView (left.sampledActivation app who ids) =
            app.messageView (right.sampledActivation app who ids) :=
        app.sampledActivation_messageView_eq left right who ids messages publicView
      have counts : (left.recall who).length = (right.recall who).length := by
        have histories := congrFun (congrArg (fun value => value.2.2.2) messages) who
        simpa only [ReactiveApplication.messageView, ReactiveApplication.messageRecall,
          List.length_map] using congrArg List.length histories
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.map_bind,
        PMF.bind_map, PMF.bind_bind]
      rw [networks]
      apply bind_congr_on_support _
      intro ids _
      let first := left.sampledActivation app who ids
      let second := right.sampledActivation app who ids
      have firstRecall : first.InputRecall app := leftRecall
      have secondRecall : second.InputRecall app := rightRecall
      have nextNetworks : first.network = second.network := congrArg Prod.fst (sampled ids)
      have responses := runtime.openingWindowPlayers_eq leaks owner event candidate raw offset
        selected who first second firstRecall secondRecall nextNetworks counts
      change players who (first.recall who) (first.observe app who) =
        players who (second.recall who) (second.observe app who) at responses
      change (players who (first.recall who) (first.observe app who)).bind _ =
        (players who (second.recall who) (second.observe app who)).bind _
      rw [responses]
      apply bind_congr_on_support _
      intro action supported
      have firstSupported : action ∈
          (players who (first.recall who) (first.observe app who)).support := by
        rw [responses]
        exact supported
      have firstState := runtime.openingWindowPlayers_application leaks owner event candidate raw
        offset selected who first action firstSupported
      have secondState := runtime.openingWindowPlayers_application leaks owner event candidate raw
        offset selected who second action supported
      change (first.respond app who action).application = first.application at firstState
      change (second.respond app who action).application = second.application at secondState
      have packets := runtime.openingWindowPlayers_packet_eq leaks owner event candidate raw
        offset selected who first second action firstSupported owned meaning
      have before : first.observe app focal = second.observe app focal := by
        have receipts := congrArg (fun value => value.2.1) (sampled ids)
        change first.receipts = second.receipts at receipts
        simp only [ReactiveApplication.Execution.observe, nextNetworks, receipts]
        exact congrArg (fun observed =>
          (⟨second.network.observe focal, observed, second.receipts⟩ : app.PlayerView)) privateView
      apply ih (first.respond app who action) (second.respond app who action)
      · exact app.respond_inputRecall first who action firstRecall
      · exact app.respond_inputRecall second who action secondRecall
      · exact app.respond_messageView_eq first second who action (sampled ids) packets
      · exact app.respond_focal_recall_eq first second who focal action nextNetworks before
          recall packets
      · rw [firstState, secondState]
        exact publicView
      · rw [firstState, secondState]
        exact privateView
      · intro chosen
        rw [firstState, secondState]
        exact meaning chosen

/-- Within any source-information fiber represented by these concrete starts,
the entire sampled window transcript leaves the initial hidden-state posterior
unchanged. In an opening branch the fiber also fixes the eventual opening value;
the never-opening branch imposes no such condition. The auxiliary starting
transcript is retained and coupled, not erased. -/
theorem openingWindow_posterior (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (network : runtime.NetworkPolicy leaks) (roster : List Player) (focal : Player)
    (initial : PMF (runtime.reactiveApplication leaks).Execution)
    (reference : (runtime.reactiveApplication leaks).Execution)
    (referenceRecall : reference.InputRecall (runtime.reactiveApplication leaks))
    (recalls : ∀ start ∈ initial.support,
      start.InputRecall (runtime.reactiveApplication leaks))
    (messages : ∀ start ∈ initial.support,
      (runtime.reactiveApplication leaks).messageView start =
        (runtime.reactiveApplication leaks).messageView reference)
    (recall : ∀ start ∈ initial.support, start.recall focal = reference.recall focal)
    (publicView : ∀ start ∈ initial.support,
      start.application.publicView = reference.application.publicView)
    (privateView : ∀ start ∈ initial.support,
      (runtime.reactiveApplication leaks).observePlayer start.application focal =
        (runtime.reactiveApplication leaks).observePlayer reference.application focal)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      reference.application.candidates.lookup candidate = .openable raw ∧
        ∀ start ∈ initial.support,
          start.application.candidates.lookup candidate = .openable raw)
    (observed :
      (runtime.reactiveApplication leaks).MessageReadout ×
        List (runtime.reactiveApplication leaks).PlayerEntry) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.openingWindowPlayers leaks owner event candidate raw offset selected
    let transcript := fun execution : app.Execution =>
      (app.messageView execution, execution.recall focal)
    let joint := initial.bind fun start =>
      ((runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player) start).map transcript).map
          (fun output => (output, start))
    (fiberConditional joint Prod.fst observed).map Prod.snd = initial := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let players := runtime.openingWindowPlayers leaks owner event candidate raw offset selected
  let kernel := fun start : app.Execution =>
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) start).map
        (fun execution => (app.messageView execution, execution.recall focal))
  have same (start : app.Execution) (supported : start ∈ initial.support) :
      kernel start = kernel reference := by
    exact runtime.openingWindow_coupling leaks owner event candidate raw offset selected
      network roster focal start reference (recalls start supported) referenceRecall
      (messages start supported) (recall start supported) (publicView start supported)
      (privateView start supported) owned (fun chosen =>
        ⟨(meaning chosen).2 start supported, (meaning chosen).1⟩)
  have independent : (initial.bind fun start =>
      (kernel start).map fun output => (output, start)) =
        bindPairLaw (kernel reference) (fun _ => initial) := by
    calc
      _ = initial.bind (fun start =>
          (kernel reference).map fun output => (output, start)) := by
        apply bind_congr_on_support _
        intro start supported
        rw [same start supported]
      _ = _ := by
        simp only [FinDist.product, ← PMF.bind_pure_comp, Function.comp_def]
        rw [PMF.bind_comm]
  change ((fiberConditional (initial.bind fun start =>
    (kernel start).map fun output => (output, start)) Prod.fst observed).map
      Prod.snd) = initial
  rw [independent]
  exact conditional_snd_bindPairLaw_const (kernel reference) initial observed

end Vegas.EventGraphRuntime
