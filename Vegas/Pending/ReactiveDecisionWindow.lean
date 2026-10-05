/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveMessageReadout
import Interaction.ScheduledOpening
import Vegas.Pending.ReactivePolicyMixture
import Vegas.Pending.ReactiveRevealBlock
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning
import GameTheoryExtensions.Math.Probability.Support

/-! # Coupling scheduled Boolean decisions through a finite observation window

Both source decisions select an owner response count. True emits an authentic
opening, and false emits evidence-free withholding. Earlier and later responses
wait. Actual sampled observations and packet identities remain in the coupling.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def windowDecisionMaterial (event : graph.EventId)
    (opening : Option (Handle graph × Raw L)) (disclose : Bool) : WitnessedSubmission graph :=
  match if disclose then opening else none with
  | some (candidate, raw) => disclosureSubmission (.opening event candidate raw)
  | none => ⟨⟨.withhold event, none⟩, .none⟩

def windowDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (opening : Option (Handle graph × Raw L)) (disclose : Bool) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨some (windowDecisionMaterial event opening disclose)⟩

/-- Missing opening material produces an actual withholding packet at either
private Boolean intention, without choosing any inhabitant of the payload type. -/
theorem windowDecision_none (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (event : graph.EventId) (disclose : Bool) :
    runtime.windowDecision leaks event none disclose =
      ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ := by cases disclose <;> rfl

theorem windowDecision_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (event : graph.EventId) (opening : Option (Handle graph × Raw L)) (disclose : Bool) :
    (execution.respond (runtime.reactiveApplication leaks) owner
      (runtime.windowDecision leaks event opening disclose)).application =
        execution.application := by
  cases disclose
  · rfl
  · cases opening <;> rfl

def decisionWindowPlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) :
    Player → (runtime.reactiveApplication leaks).Policy := fun who =>
  let app := runtime.reactiveApplication leaks
  if who = owner then app.scheduledPolicy offset (some selected.1)
    (fun _ _ => PMF.pure (runtime.windowDecision leaks event opening selected.2))
      app.silentPolicy
  else app.silentPolicy

/-- A private timing and Boolean draw is realized as an ordinary behavioral
response policy using the player's actual response recall. -/
def decisionWindowMixturePlayers (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (choices : PMF (Fin slots × Bool)) :
    Player → (runtime.reactiveApplication leaks).Policy :=
  let app := runtime.reactiveApplication leaks
  Function.update (fun _ => app.silentPolicy) owner
    (app.policyMixture choices (fun selected => app.scheduledPolicy offset (some selected.1)
      (fun _ _ => PMF.pure (runtime.windowDecision leaks event opening selected.2))
        app.silentPolicy)).policy

theorem decisionWindowMixture_law (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (choices : PMF (Fin slots × Bool))
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (before : (execution.recall owner).length ≤ offset) :
    runtime.runInteractionPlan leaks
      (runtime.decisionWindowMixturePlayers leaks owner event opening offset choices)
        network plan execution =
      choices.bind fun selected => runtime.runInteractionPlan leaks
        (runtime.decisionWindowPlayers leaks owner event opening offset selected)
          network plan execution := by
  let app := runtime.reactiveApplication leaks
  let family := fun selected : Fin slots × Bool =>
    app.scheduledPolicy offset (some selected.1)
      (fun _ _ => PMF.pure (runtime.windowDecision leaks event opening selected.2))
        app.silentPolicy
  have posterior := app.policyMixture_posterior_dormant choices family app.silentPolicy offset
    (fun selected past view earlier => app.scheduledPolicy_before offset (some selected.1)
      (fun _ _ => PMF.pure (runtime.windowDecision leaks event opening selected.2))
        app.silentPolicy past view earlier) (execution.recall owner) before
  have actual := runtime.runInteractionPlan_policyMixture leaks choices family owner
    (fun _ => app.silentPolicy) network plan execution
  dsimp only at actual
  rw [posterior] at actual
  refine actual.symm.trans ?_
  apply bind_congr_on_support _
  intro selected _
  have players : Function.update (fun _ => app.silentPolicy) owner (family selected) =
      runtime.decisionWindowPlayers leaks owner event opening offset selected := by
    funext who past view
    by_cases active : who = owner
    · subst who
      simp only [Function.update_self, decisionWindowPlayers, ↓reduceIte]
      rfl
    · simp only [Function.update_of_ne active, decisionWindowPlayers, active, ↓reduceIte]
      rfl
  rw [players]

theorem decisionWindowPlayers_cases (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.decisionWindowPlayers leaks owner event opening offset selected
        who past view).support) :
    action = ⟨none⟩ ∨
      (who = owner ∧ action = runtime.windowDecision leaks event opening selected.2) := by
  by_cases active : who = owner
  · simp only [decisionWindowPlayers, active, ↓reduceIte,
      ReactiveApplication.scheduledPolicy] at supported
    split at supported
    · exact Or.inr ⟨active, (PMF.mem_support_pure_iff _ _).mp supported⟩
    · exact Or.inl
        ((runtime.reactiveApplication leaks).silentPolicy_cases past view action supported)
  · simp only [decisionWindowPlayers, active, ↓reduceIte] at supported
    exact Or.inl ((runtime.reactiveApplication leaks).silentPolicy_cases past view action supported)

theorem decisionWindowPlayers_application (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (who : Player)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.decisionWindowPlayers leaks owner event opening offset selected who
        (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    (execution.respond (runtime.reactiveApplication leaks) who action).application =
      execution.application := by
  rcases runtime.decisionWindowPlayers_cases leaks owner event opening offset selected
    who _ _ action supported with rfl | ⟨active, rfl⟩
  · rfl
  · subst who
    exact runtime.windowDecision_application leaks execution owner event opening _

theorem decisionWindowPlayers_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (counts : (left.recall who).length = (right.recall who).length) :
    runtime.decisionWindowPlayers leaks owner event opening offset selected who
      (left.recall who) (left.observe (runtime.reactiveApplication leaks) who) =
    runtime.decisionWindowPlayers leaks owner event opening offset selected who
      (right.recall who) (right.observe (runtime.reactiveApplication leaks) who) := by
  by_cases active : who = owner
  · subst who
    simp only [decisionWindowPlayers, ↓reduceIte,
      ReactiveApplication.scheduledPolicy, counts]
    rfl
  · simp only [decisionWindowPlayers, active, ↓reduceIte]
    rfl

theorem windowDecision_packet (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (state : State graph) (known : List (Message Player (WitnessedPacket graph)))
    (disclose : Bool)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (valid : disclose = true → ∀ candidate raw, opening = some (candidate, raw) →
      state.candidates.lookup candidate = .openable raw) :
    (runtime.reactiveApplication leaks).packet state owner known
      (windowDecisionMaterial event opening disclose) =
      ⟨(windowDecisionMaterial event opening disclose).call.packet,
        (if disclose then opening else none).map (fun pair => ⟨pair.1, pair.2⟩),
        state.publicView.tokenFor (windowDecisionMaterial event opening disclose).call.packet⟩ := by
  cases disclose with
  | false => rfl
  | true =>
      cases opening with
      | none => rfl
      | some pair =>
          obtain ⟨candidate, raw⟩ := pair
          have verified : state.candidates.verify candidate raw = true :=
            (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr (valid rfl _ _ rfl)
          have ownerEq := owned candidate raw rfl
          simp only [windowDecisionMaterial, ↓reduceIte, reactiveApplication,
            disclosureSubmission, WitnessedSubmission.emit, ownerEq, verified, and_self,
            Option.map_some]

private theorem decisionWindowPlayers_packet_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool) (who : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.decisionWindowPlayers leaks owner event opening offset selected who
        (left.recall who) (left.observe (runtime.reactiveApplication leaks) who)).support)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (meaning : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw)
    (publicView : left.application.publicView = right.application.publicView) :
    ∀ submission, action.transmission = some submission →
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit left.application who submission) who
          (left.network.known who) submission =
      (runtime.reactiveApplication leaks).packet
        ((runtime.reactiveApplication leaks).submit right.application who submission) who
          (right.network.known who) submission := by
  intro submission transmitted
  rcases runtime.decisionWindowPlayers_cases leaks owner event opening offset selected
    who _ _ action supported with rfl | ⟨active, rfl⟩
  · cases transmitted
  · subst who
    simp only [windowDecision, Option.some.injEq] at transmitted
    subst submission
    have unchanged (execution : (runtime.reactiveApplication leaks).Execution) :
        (runtime.reactiveApplication leaks).submit execution.application owner
          (windowDecisionMaterial event opening selected.2) = execution.application :=
      runtime.windowDecision_application leaks execution owner event opening selected.2
    rw [unchanged left, unchanged right]
    have leftPacket := runtime.windowDecision_packet leaks owner event opening left.application
      (left.network.known owner) selected.2 owned
        (fun chosen candidate raw material => (meaning chosen candidate raw material).1)
    have rightPacket := runtime.windowDecision_packet leaks owner event opening right.application
      (right.network.known owner) selected.2 owned
        (fun chosen candidate raw material => (meaning chosen candidate raw material).2)
    rw [leftPacket, rightPacket, publicView]

/-- A scheduled decision branch has the same auxiliary transcript law
across hidden application states with equal public and focal observations.
The actual pending pools are coupled, so the sampler remains unrestricted.
The withholding branch needs no agreement on the hidden committed value. -/
theorem decisionWindow_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool)
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
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (meaning : selected.2 = true →
      ∀ candidate raw, opening = some (candidate, raw) →
        left.application.candidates.lookup candidate = .openable raw ∧
          right.application.candidates.lookup candidate = .openable raw) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.decisionWindowPlayers leaks owner event opening offset selected
    (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
      left).map (fun execution => (app.messageView execution, execution.recall focal)) =
    (runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
      right).map (fun execution => (app.messageView execution, execution.recall focal)) := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let players := runtime.decisionWindowPlayers leaks owner event opening offset selected
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
        PMF.bind_map, PMF.bind_bind, Function.comp_def]
      rw [networks]
      apply bind_congr_on_support _
      intro ids _
      let first := left.sampledActivation app who ids
      let second := right.sampledActivation app who ids
      have firstRecall : first.InputRecall app := leftRecall
      have secondRecall : second.InputRecall app := rightRecall
      have nextNetworks : first.network = second.network := congrArg Prod.fst (sampled ids)
      have responses := runtime.decisionWindowPlayers_eq leaks owner event opening offset
        selected who first second counts
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
      have firstState := runtime.decisionWindowPlayers_application leaks owner event opening
        offset selected who first action firstSupported
      have secondState := runtime.decisionWindowPlayers_application leaks owner event opening
        offset selected who second action supported
      change (first.respond app who action).application = first.application at firstState
      change (second.respond app who action).application = second.application at secondState
      have packets := runtime.decisionWindowPlayers_packet_eq leaks owner event opening
        offset selected who first second action firstSupported owned meaning publicView
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
      · intro chosen candidate raw material
        rw [firstState, secondState]
        exact meaning chosen candidate raw material

/-- Within any source-information fiber represented by these concrete starts,
the entire sampled window transcript leaves the initial hidden-state posterior
unchanged. In an opening branch the fiber also fixes the eventual opening value;
the withholding branch imposes no such condition. The auxiliary starting
transcript is retained and coupled, not erased. -/
theorem decisionWindow_posterior (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (offset : Nat) {slots : Nat} (selected : Fin slots × Bool)
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
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (meaning : selected.2 = true →
      ∀ candidate raw, opening = some (candidate, raw) →
        reference.application.candidates.lookup candidate = .openable raw ∧
          ∀ start ∈ initial.support,
            start.application.candidates.lookup candidate = .openable raw)
    (observed :
      (runtime.reactiveApplication leaks).MessageReadout ×
        List (runtime.reactiveApplication leaks).PlayerEntry) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.decisionWindowPlayers leaks owner event opening offset selected
    let transcript := fun execution : app.Execution =>
      (app.messageView execution, execution.recall focal)
    let joint := initial.bind fun start =>
      ((runtime.runInteractionPlan leaks players network
        (roster.map ServiceInstruction.player) start).map transcript).map
          (fun output => (output, start))
    (fiberPosterior joint Prod.fst observed).map Prod.snd = initial := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let players := runtime.decisionWindowPlayers leaks owner event opening offset selected
  let kernel := fun start : app.Execution =>
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player) start).map
        (fun execution => (app.messageView execution, execution.recall focal))
  have same (start : app.Execution) (supported : start ∈ initial.support) :
      kernel start = kernel reference := by
    exact runtime.decisionWindow_coupling leaks owner event opening offset selected
      network roster focal start reference (recalls start supported) referenceRecall
      (messages start supported) (recall start supported) (publicView start supported)
      (privateView start supported) owned (fun chosen candidate raw material =>
        ⟨(meaning chosen candidate raw material).2 start supported,
          (meaning chosen candidate raw material).1⟩)
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
        simp only [bindPairLaw, ← PMF.bind_pure_comp, Function.comp_def]
        rw [PMF.bind_comm]
  change ((fiberPosterior (initial.bind fun start =>
    (kernel start).map fun output => (output, start)) Prod.fst observed).map
      Prod.snd) = initial
  rw [independent]
  exact fiberPosterior_snd_bindPairLaw_const (kernel reference) initial observed

end Vegas.EventGraphRuntime
