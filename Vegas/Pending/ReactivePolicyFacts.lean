/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactivePolicy
import GameTheoryExtensions.Core.PendingChoice

/-! # Prescribed submissions, recovery choices, and initialized law equality -/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- An actual supported prescribed response authenticates its sampled silent
intention from the ready owned input and the physical response it generated. -/
theorem reactiveSilentDecision_of_prescribed_support (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (supported : (action, some remembered) ∈
      (runtime.prescribedReactiveResponse leaks who policy history intentions view).support)
    (silent : action.transmission = none)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (recorded : entry = ⟨view, action, none⟩) :
    runtime.ReactiveSilentDecision leaks who entry remembered := by
  subst entry
  unfold prescribedReactiveResponse at supported
  split at supported
  · simp at supported
  · rename_i event turn
    split at supported
    · simp at supported
    · split at supported
      · rename_i identity
        split at supported
        · rename_i ready
          split at supported
          · rename_i actor
            obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ supported
            have responseEq := congrArg Prod.fst image
            have intentionEq := Option.some.inj (congrArg Prod.snd image)
            dsimp only at responseEq intentionEq
            subst remembered
            exact ⟨rfl, silent, identity, turn, ready, actor, responseEq.symm⟩
          · simp at supported
        · simp at supported
      · simp at supported

/-- A silent sampled decision remains recorded independently of receipts. -/
theorem reactiveAlreadyDecided_of_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ history.zip intentions)
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered) :
    runtime.reactiveAlreadyDecided leaks who history intentions remembered.event = true := by
  classical
  simp only [reactiveAlreadyDecided, decide_eq_true_eq]
  exact ⟨entry, remembered, retained, rfl, matching⟩

/-- Repeated activation after an actual matching silent decision cannot redraw
its source action, even when no packet was submitted. -/
theorem prescribedReactiveResponse_silent_after_decision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions : List (Option graph.Completion))
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ history.zip intentions)
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered)
    (turn : view.application.publicView.ownTurn? who = some remembered.event) :
    runtime.prescribedReactiveResponse leaks who policy history intentions view =
      PMF.pure (⟨none⟩, none) := by
  have decided := runtime.reactiveAlreadyDecided_of_mem leaks who history intentions entry
    remembered retained matching
  simp only [prescribedReactiveResponse, turn, decided, Bool.or_true, ↓reduceIte]

/-- A resolution's genuine silent intention is restored without an accepting
receipt. The matcher requires its actual ready owned input and response. -/
theorem reactiveOriginal_singleton_silent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion) (receipts : List (MessageId Player × Bool))
    (sameEvent : remembered.event = completion.event)
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered)
    (resolution : (match nodeView graph completion.event with
      | .resolve .. => true | .sample .. | .bind .. => false) = true) :
    runtime.reactiveOriginal leaks who [entry] [some remembered] receipts completion =
      remembered := by
  classical
  cases node : nodeView graph completion.event with
  | sample => simp [node] at resolution
  | bind => simp [node] at resolution
  | resolve => simp [reactiveOriginal, node, sameEvent, matching]

/-- A silent entry cannot restore an intention that fails the observation or
response matcher. Private memory alone does not authenticate a choice. -/
theorem reactiveOriginal_singleton_unmatched_silent (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (remembered completion : graph.Completion) (receipts : List (MessageId Player × Bool))
    (silent : entry.emitted = none)
    (unmatched : ¬ runtime.ReactiveSilentDecision leaks who entry remembered) :
    runtime.reactiveOriginal leaks who [entry] [some remembered] receipts completion =
      completion := by
  classical
  cases node : nodeView graph completion.event <;>
    simp [reactiveOriginal, node, unmatched, silent]

/-- Every posterior memory after a positive response is an append extension of
a genuine prior memory and records the actual response's sampled intention. -/
theorem prescribedReactivePosterior_snoc_support (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry)
    (positive : entry.action ∈
      (runtime.prescribedReactivePolicy leaks who policy history entry.beforeView).support)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (history ++ [entry])).support) :
    ∃ previous ∈
        ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support,
      ∃ saved, intentions = previous ++ [saved] ∧
        (entry.action, saved) ∈
          (runtime.prescribedReactiveResponse leaks who policy history previous
            entry.beforeView).support := by
  obtain ⟨previous, prior, produced⟩ :=
    (runtime.prescribedReactiveImplementation leaks who policy).mem_support_posterior_snoc
      history entry positive intentions supported
  change (entry.action, intentions) ∈
    ((runtime.prescribedReactiveResponse leaks who policy history previous entry.beforeView).map
      (fun response => (response.1, previous ++ [response.2]))).support at produced
  obtain ⟨⟨action, saved⟩, issued, image⟩ := PMF.support_map .. ▸ produced
  have actionEq : action = entry.action := congrArg Prod.fst image
  have memoryEq : previous ++ [saved] = intentions := congrArg Prod.snd image
  subst action
  exact ⟨previous, prior, saved, memoryEq.symm, issued⟩

/-- Supported private memory has exactly one intention slot per positive own response. -/
theorem prescribedReactivePosterior_length (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    intentions.length = history.length := by
  induction consistent generalizing intentions with
  | nil =>
      have empty : intentions = [] := (PMF.mem_support_pure_iff _ _).mp supported
      exact congrArg List.length empty
  | @snoc history entry consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, _⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history entry
          positive intentions supported
      simp only [memoryEq, List.length_append, List.length_singleton, ih previous prior]

/-- Appending aligned recall and intention lists retains every recorded silent decision. -/
theorem reactiveAlreadyDecided_append (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (history later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (intentions saved : List (Option graph.Completion)) (event : graph.EventId)
    (aligned : history.length = intentions.length)
    (decided : runtime.reactiveAlreadyDecided leaks who history intentions event = true) :
    runtime.reactiveAlreadyDecided leaks who (history ++ later) (intentions ++ saved)
      event = true := by
  classical
  simp only [reactiveAlreadyDecided, decide_eq_true_eq] at decided ⊢
  obtain ⟨entry, remembered, retained, sameEvent, matching⟩ := decided
  refine ⟨entry, remembered, ?_, sameEvent, matching⟩
  rw [List.zip_append aligned]
  exact List.mem_append.mpr (Or.inl retained)

/-- A positive silent response at a fresh ready owned input leaves a genuine
silent decision in every supported posterior memory, including branches that
had already sampled the event. -/
theorem prescribedReactivePosterior_decided_after_silent
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (positive : entry.action ∈
      (runtime.prescribedReactivePolicy leaks who policy history entry.beforeView).support)
    (silent : entry.action.transmission = none) (emitted : entry.emitted = none)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (owner : entry.beforeView.application.who = who)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (unsubmitted : runtime.reactiveAlreadySubmitted leaks history event = false)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (history ++ [entry])).support) :
    runtime.reactiveAlreadyDecided leaks who (history ++ [entry]) intentions event = true := by
  classical
  obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
    runtime.prescribedReactivePosterior_snoc_support leaks who policy history entry
      positive intentions supported
  have aligned := (runtime.prescribedReactivePosterior_length leaks who policy
    consistent previous prior).symm
  rw [memoryEq]
  cases decided : runtime.reactiveAlreadyDecided leaks who history previous event with
  | true =>
      exact runtime.reactiveAlreadyDecided_append leaks who history [entry] previous [saved]
        event aligned decided
  | false =>
      have issued := produced
      simp only [prescribedReactiveResponse, turn, unsubmitted, decided, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, owner, ready, actor, ↓reduceDIte] at issued
      obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ issued
      have savedEq : saved = some (⟨event, choice⟩ : graph.Completion) :=
        (congrArg Prod.snd image).symm
      have actual : entry = ⟨entry.beforeView, entry.action, none⟩ := by
        cases entry
        simp_all only
      have matching := runtime.reactiveSilentDecision_of_prescribed_support leaks who policy
        history previous entry.beforeView entry.action ⟨event, choice⟩
        (by simpa only [savedEq] using produced) silent entry actual
      apply runtime.reactiveAlreadyDecided_of_mem leaks who _ _ entry ⟨event, choice⟩
      · rw [List.zip_append aligned, savedEq]
        exact List.mem_append.mpr (Or.inr (by simp))
      · exact matching

/-- Positive own-history extensions retain a silent decision in every supported
posterior memory; conditioning cannot replace its genuine memory prefix. -/
theorem prescribedReactivePosterior_decided_extension (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (event : graph.EventId)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (history ++ later))
    (decided : ∀ intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support,
      runtime.reactiveAlreadyDecided leaks who history intentions event = true)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (history ++ later)).support) :
    runtime.reactiveAlreadyDecided leaks who (history ++ later) intentions event = true := by
  induction later using List.reverseRecOn generalizing intentions with
  | nil =>
      simpa only [List.append_nil] using decided intentions
        (by simpa only [List.append_nil] using supported)
  | append_singleton later entry ih =>
      have consistentStep : (runtime.prescribedReactivePolicy leaks who policy).Consistent
          ((history ++ later) ++ [entry]) := by
        simpa only [List.append_assoc] using consistent
      have step := (ReactiveApplication.Policy.consistent_snoc_iff _ _ _).mp consistentStep
      have supportedStep : intentions ∈
          ((runtime.prescribedReactiveImplementation leaks who policy).posterior
            ((history ++ later) ++ [entry])).support := by
        simpa only [List.append_assoc] using supported
      obtain ⟨previous, prior, saved, memoryEq, _⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy (history ++ later)
          entry step.2 intentions supportedStep
      have previousDecided := ih step.1 previous prior
      have aligned := (runtime.prescribedReactivePosterior_length leaks who policy
        step.1 previous prior).symm
      simpa only [List.append_assoc, memoryEq] using
        runtime.reactiveAlreadyDecided_append leaks who (history ++ later) [entry]
          previous [saved] event aligned previousDecided

/-- A supported silent decision prevents behavioral redraw after any positive
own-history suffix. The result derives retention from actual posterior support. -/
theorem prescribedReactivePolicy_silent_after_supported_decision
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      ((history ++ [entry]) ++ later))
    (silent : entry.action.transmission = none) (emitted : entry.emitted = none)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (owner : entry.beforeView.application.who = who)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (unsubmitted : runtime.reactiveAlreadySubmitted leaks history event = false)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (current : view.application.publicView.ownTurn? who = some event) :
    runtime.prescribedReactivePolicy leaks who policy ((history ++ [entry]) ++ later) view =
      PMF.pure ⟨none⟩ := by
  have consistentBefore := consistent.of_append
  have step := (ReactiveApplication.Policy.consistent_snoc_iff _ _ _).mp consistentBefore
  have decision := runtime.prescribedReactivePosterior_decided_after_silent leaks who policy
    history entry event step.1 step.2 silent emitted turn owner ready actor unsubmitted
  have persists := runtime.prescribedReactivePosterior_decided_extension leaks who policy
    (history ++ [entry]) later event consistent decision
  rw [prescribedReactivePolicy_apply]
  calc
    _ = ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        ((history ++ [entry]) ++ later)).bind (fun _ => PMF.pure ⟨none⟩) := by
      apply bind_congr_on_support
      intro intentions supported
      have remembered := persists intentions supported
      simp only [prescribedReactiveResponse, current, remembered, Bool.or_true,
        ↓reduceIte, PMF.pure_map]
    _ = _ := PMF.bind_const _ _

/-- Completing the compiler after deviations does not redraw a decision along
its positive own histories. Its recovery branch is not entered there. -/
theorem compileReactivePolicy_silent_after_supported_decision
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history later : List (runtime.reactiveApplication leaks).PlayerEntry)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      ((history ++ [entry]) ++ later))
    (silent : entry.action.transmission = none) (emitted : entry.emitted = none)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event)
    (owner : entry.beforeView.application.who = who)
    (ready : entry.beforeView.application.publicView.EventReady event)
    (actor : graph.actor? event = some who)
    (unsubmitted : runtime.reactiveAlreadySubmitted leaks history event = false)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (current : view.application.publicView.ownTurn? who = some event) :
    runtime.compileReactivePolicy leaks who policy ((history ++ [entry]) ++ later) view =
      PMF.pure ⟨none⟩ := by
  rw [compileReactivePolicy, ReactiveApplication.Policy.recover_eq _ _ _ _ consistent]
  exact runtime.prescribedReactivePolicy_silent_after_supported_decision leaks who policy
    history later entry event consistent silent emitted turn owner ready actor unsubmitted
    view current

theorem reactiveResolutionPacket_event {owner : Player} (who : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (action : graph.Action event) (view : PlayerView graph) (packet : Payload graph)
    (sent : reactiveResolutionPacket who event payload binding checks outputEq action view =
      some packet) :
    packet.event? graph = some event := by
  dsimp only [reactiveResolutionPacket] at sent
  repeat' split at sent
  all_goals first
    | cases sent; rfl
    | cases sent

theorem reactiveDecision_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (event : graph.EventId) (action : graph.Action event) (view : PlayerView graph) :
    (runtime.reactiveDecision leaks who event action view).transmission = none ∨
      ∃ material, (runtime.reactiveDecision leaks who event action view).transmission =
        some material ∧ material.call.packet.event? graph = some event := by
  unfold reactiveDecision
  split
  · exact Or.inl rfl
  · cases selected : reactiveFreshSlot view with
    | none => exact Or.inl rfl
    | some serial => exact Or.inr ⟨_, rfl, rfl⟩
  · rename_i owner payload binding checks outputEq codeEq nodeEq
    cases sent : reactiveResolutionPacket who event payload binding checks outputEq action view with
    | none => exact Or.inl rfl
    | some packet =>
        exact Or.inr ⟨_, rfl,
          reactiveResolutionPacket_event who event payload binding checks outputEq action view
            packet sent⟩

/-- No second submission for an event, regardless of how often
the scheduler activates the player. -/
theorem prescribedReactivePolicy_transmission (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player)
    (policy : graph.BehavioralPolicy who)
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (action : (runtime.reactiveApplication leaks).Action)
    (supported : action ∈
      (runtime.prescribedReactivePolicy leaks who policy history view).support) :
    action.transmission = none ∨ ∃ event material,
      action.transmission = some material ∧ material.call.packet.event? graph = some
        event ∧
        runtime.reactiveAlreadySubmitted leaks history event = false := by
  rw [prescribedReactivePolicy_apply] at supported
  obtain ⟨intentions, _, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨⟨response, intention⟩, issued, rfl⟩ := PMF.support_map .. ▸ produced
  unfold prescribedReactiveResponse at issued
  split at issued
  · cases (PMF.mem_support_pure_iff _ _).mp issued; exact Or.inl rfl
  · rename_i event turn
    split at issued
    · cases (PMF.mem_support_pure_iff _ _).mp issued; exact Or.inl rfl
    · rename_i unsent
      have absent : runtime.reactiveAlreadySubmitted leaks history event = false := by
        cases submitted : runtime.reactiveAlreadySubmitted leaks history event with
        | false => rfl
        | true => simp [submitted] at unsent
      split at issued
      · split at issued
        · split at issued
          · obtain ⟨choice, _, image⟩ := PMF.support_map .. ▸ issued
            have responseEq := congrArg Prod.fst image
            dsimp only at responseEq
            subst response
            rcases runtime.reactiveDecision_transmission leaks who event choice
              view.application with
              silent | ⟨material, sent, addressed⟩
            · exact Or.inl silent
            · exact Or.inr ⟨event, material, sent, addressed, absent⟩
          · cases (PMF.mem_support_pure_iff _ _).mp issued; exact Or.inl rfl
        · cases (PMF.mem_support_pure_iff _ _).mp issued; exact Or.inl rfl
      · cases (PMF.mem_support_pure_iff _ _).mp issued; exact Or.inl rfl

def reactiveSubmittedEvents (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) : List graph.EventId :=
  history.filterMap fun entry => entry.emitted.bind (fun message => message.payload.call.event?
    graph)

theorem reactiveAlreadySubmitted_iff (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry) (event : graph.EventId) :
    runtime.reactiveAlreadySubmitted leaks history event = true ↔
      event ∈ runtime.reactiveSubmittedEvents leaks history := by
  simp only [reactiveAlreadySubmitted, reactiveSubmittedEvents, List.any_eq_true,
    List.mem_filterMap, Option.any_eq_true, Option.bind_eq_some_iff, decide_eq_true_eq]

theorem reactiveSubmittedEvents_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (member : message ∈ (runtime.reactiveApplication leaks).outputs history)
    (addressed : message.payload.call.event? graph = some event) :
    event ∈ runtime.reactiveSubmittedEvents leaks history := by
  obtain ⟨entry, retained, emitted⟩ := List.mem_filterMap.mp member
  exact List.mem_filterMap.mpr
    ⟨entry, retained, by simp only [emitted, Option.bind_some, addressed]⟩

theorem reactiveSubmittedEvents_unique (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (history : List (runtime.reactiveApplication leaks).PlayerEntry)
    (once : (runtime.reactiveSubmittedEvents leaks history).Nodup)
    (first second : Message Player (WitnessedPacket graph)) (event : graph.EventId)
    (firstMem : first ∈ (runtime.reactiveApplication leaks).outputs history)
    (secondMem : second ∈ (runtime.reactiveApplication leaks).outputs history)
    (firstEvent : first.payload.call.event? graph = some event)
    (secondEvent : second.payload.call.event? graph = some event) : first = second := by
  obtain ⟨left, leftMem, leftOutput⟩ := List.mem_filterMap.mp firstMem
  obtain ⟨right, rightMem, rightOutput⟩ := List.mem_filterMap.mp secondMem
  let address (entry : (runtime.reactiveApplication leaks).PlayerEntry) :=
    entry.emitted.bind (fun message => message.payload.call.event? graph)
  have separated : history.Pairwise (fun a b =>
      ∀ e, address a = some e → ∀ f, address b = some f → e ≠ f) :=
    List.pairwise_filterMap.mp once
  have identity : history.Pairwise (fun a b =>
      address a = some event → address b = some event → a = b) :=
    separated.imp fun apart ha hb => (apart event ha event hb rfl).elim
  have same : left = right := List.Pairwise.forall_of_forall_of_flip
    (fun _ _ _ _ => rfl) identity
    (identity.imp fun eq ha hb => (eq hb ha).symm) leftMem rightMem
    (by simp only [address, leftOutput, Option.bind_some, firstEvent])
    (by simp only [address, rightOutput, Option.bind_some, secondEvent])
  subst right
  exact Option.some.inj (leftOutput.symm.trans rightOutput)

omit [DecidableEq Player] in
/-- Every recovery choice is supported by the current source decision law,
including choices taken from private memory. -/
theorem reactiveRecoveryLaw_support (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : PMF (graph.Action event)) (action : graph.Action event)
    (supported : action ∈ (reactiveRecoveryLaw intentions event law).support) :
    action ∈ law.support := by
  classical
  dsimp only [reactiveRecoveryLaw] at supported
  split at supported
  · rename_i remembered selected found
    cases (PMF.mem_support_pure_iff _ _).mp supported
    exact of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1
  · exact supported

omit [DecidableEq Player] in
theorem reactiveRecoveryLaw_pure (intentions : List (Option graph.Completion))
    (event : graph.EventId) (action : graph.Action event) :
    reactiveRecoveryLaw intentions event (PMF.pure action) =
      PMF.pure action := by
  classical
  dsimp only [reactiveRecoveryLaw]
  split
  · rename_i remembered selected found
    have same : selected = action := (PMF.mem_support_pure_iff _ _).mp
      (of_decide_eq_true (List.find?_eq_some_iff_append.mp found).1)
    rw [same]
  · rfl

omit [DecidableEq Player] in
/-- Once a recovery response records a supported choice, another activation
reuses that choice as long as it is still supported. -/
theorem reactiveRecoveryLaw_remembered (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : PMF (graph.Action event)) (action : graph.Action event)
    (supported : action ∈ law.support) :
    reactiveRecoveryLaw (intentions ++ [some ⟨event, action⟩]) event law =
      PMF.pure action := by
  classical
  have positive : law action ≠ 0 := supported
  simp [reactiveRecoveryLaw, positive]

omit [DecidableEq Player] in
/-- Recovery either repeats one remembered action or keeps the decision law, so
its continuation is integrable when every action's and the law's are. -/
theorem reactiveRecoveryLaw_bind_integrable (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law : PMF (graph.Action event))
    {Outcome : Type} (continuation : graph.Action event → PMF Outcome) (utility : Outcome → ℝ)
    (actionIntegrable : ∀ action, PayoffIntegrable (continuation action) utility)
    (lawIntegrable : PayoffIntegrable (law.bind continuation) utility) :
    PayoffIntegrable ((reactiveRecoveryLaw intentions event law).bind continuation) utility := by
  simp only [reactiveRecoveryLaw]
  split
  · rw [PMF.pure_bind]
    exact actionIntegrable _
  · exact lawIntegrable

omit [DecidableEq Player] in
/-- The actual recovery lottery satisfies the local inclusion incentive law.
The fixed downstream kernel premise still has to be proved for a service;
this result alone does not assert native SPE. The utility must be integrable
under every compared continuation. -/
theorem reactiveRecoveryLaw_optimal_response (intentions : List (Option graph.Completion))
    (event : graph.EventId) (law retained : PMF (graph.Action event))
    {Outcome : Type} (continuation : graph.Action event → PMF Outcome)
    (utility : Outcome → ℝ) (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (actionIntegrable : ∀ action, PayoffIntegrable (continuation action) utility)
    (lawIntegrable : PayoffIntegrable (law.bind continuation) utility)
    (retainedIntegrable : PayoffIntegrable (retained.bind continuation) utility)
    (optimal : ∀ action, expect (continuation action) utility ≤
      expect (law.bind continuation) utility)
    (alternative : PMF (Option (graph.Action event)))
    (alternativeIntegrable : PayoffIntegrable
      ((GameTheory.PendingChoice.responseLaw weight nonnegative atMostOne retained
        alternative).bind continuation) utility) :
    expect ((GameTheory.PendingChoice.responseLaw weight nonnegative atMostOne retained
      alternative).bind continuation) utility ≤
    expect ((GameTheory.PendingChoice.responseLaw weight nonnegative atMostOne retained
      ((reactiveRecoveryLaw intentions event law).map some)).bind continuation)
        utility :=
  GameTheory.PendingChoice.optimal_response_of_support weight nonnegative atMostOne
    retained law _ continuation utility actionIntegrable lawIntegrable
    (reactiveRecoveryLaw_bind_integrable intentions event law continuation utility
      actionIntegrable lawIntegrable)
    retainedIntegrable optimal
    (fun _ supported => reactiveRecoveryLaw_support intentions event law _ supported)
    alternative alternativeIntegrable

/-- Policy completion preserves initialized canonical state laws playerwise.
The opponents and the observation-local scheduler remain arbitrary. -/
theorem compileReactivePolicy_canonical_run (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (initial : PMF (State graph)) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler) (fuel : Nat) :
    let app := runtime.reactiveApplication leaks
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy
        (Function.update players who (runtime.compileReactivePolicy leaks who policy) actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        GameTheory.Protocol.ExecutionProtocol.History.state) =
    (((app.information initial horizon scheduler).runSingleMoverBehavioralFrom
      (app.singleMover initial horizon scheduler) (fun actor => app.encodePolicy
        (Function.update players who (runtime.prescribedReactivePolicy leaks who policy) actor))
      fuel (app.protocol initial horizon scheduler).initHistory).map
        GameTheory.Protocol.ExecutionProtocol.History.state) := by
  simpa only [Function.update_self, Function.update_idem, compileReactivePolicy] using
    ReactiveApplication.Policy.recover_canonical_run
      (Function.update players who (runtime.prescribedReactivePolicy leaks who policy)) who
      (runtime.recoverReactivePolicy leaks who policy) initial horizon scheduler fuel

/-- The actual compiler realizes the prescribed private implementation against
arbitrary opponents and scheduling. Its intention list is absent from the game
execution, while all application state, packets, observations and recall agree. -/
theorem compileReactivePolicy_realizes (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (count : Nat) (state : State graph) :
    let app := runtime.reactiveApplication leaks
    let implementation := runtime.prescribedReactiveImplementation leaks who policy
    implementation.initial.bind (implementation.run who players scheduler count
        (ReactiveApplication.Execution.initial app state)) =
      app.runRounds scheduler
        (Function.update players who (runtime.compileReactivePolicy leaks who policy))
        count (ReactiveApplication.Execution.initial app state) := by
  dsimp only
  rw [ReactiveApplication.Implementation.realize_initial]
  have recovery := ReactiveApplication.Policy.recover_runRounds
    (Function.update players who (runtime.prescribedReactivePolicy leaks who policy)) who
    (runtime.recoverReactivePolicy leaks who policy) scheduler count
    (ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks) state) .nil
  simpa only [Function.update_self, Function.update_idem, compileReactivePolicy,
    prescribedReactivePolicy] using recovery.symm

end Vegas.EventGraphRuntime
