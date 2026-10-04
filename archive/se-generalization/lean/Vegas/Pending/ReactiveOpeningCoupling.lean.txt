/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningSettlement

/-! # Auxiliary transcript coupling through protected inclusion

This projects the actual opening-window interpreter, including its final
inclusion. The auxiliary transcript retains all pending copies, private leak
lists and action recall. It is a proof readout, not an additional observation
or an execution semantics.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

private def inclusionReadout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (initial : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    {slots : Nat} (selected : Option (Fin slots))
    (transcript : (runtime.reactiveApplication leaks).MessageReadout ×
      List (runtime.reactiveApplication leaks).PlayerEntry) :=
  let before := transcript.1
  let command := if selected.isSome then
    ReactiveApplication.Command.include (owner, initial.network.nextSerial owner)
    else ReactiveApplication.Command.wait
  let nextNetwork := if selected.isSome then
    (before.1.includePending (owner, initial.network.nextSerial owner)).2 else before.1
  let receipts := if selected.isSome then
    before.2.1 ++ [((owner, initial.network.nextSerial owner), true)] else before.2.1
  let environment := before.2.2.1 ++
    [⟨⟨before.1.publicView, initial.application.publicView, before.2.1⟩, command⟩]
  ((nextNetwork, receipts, environment, before.2.2.2), transcript.2)

private theorem framed_inclusion_readout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected : Option (Fin slots))
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected slots
      initial current) (serials : initial.network.SerialsBeforeNext)
    (accepted : selected.isSome →
      ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.windowEnvelope leaks owner event candidate raw initial)).isSome = true)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (focal : Player) :
    (runtime.interactionStep leaks players network (.includeLatest event owner) current).map
      (fun next => ((runtime.reactiveApplication leaks).messageView next, next.recall focal)) =
    PMF.pure (inclusionReadout runtime leaks initial owner selected
      ((runtime.reactiveApplication leaks).messageView current, current.recall focal)) := by
  let app := runtime.reactiveApplication leaks
  have selection := frame.selection runtime leaks owner event candidate raw offset selected
    initial current serials
  simp only [interactionStep, interactionInstruction, selection, PMF.pure_bind]
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume]
      simp only [inclusionReadout, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        ReactiveApplication.messageView, ReactiveApplication.Execution.observeEnvironment,
        frame.application]
      rfl
  | some slot =>
      have opened : openingPassed (some slot) slots = true := by
        simpa only [openingPassed, Option.any_some, decide_eq_true_eq] using slot.isLt
      have found := frame.lookup_opened runtime leaks owner event candidate raw offset (some slot)
        slots initial current serials opened
      have succeeds := accepted (by rfl)
      simp only [Option.isSome_some, ↓reduceIte, ReactiveApplication.dispatch,
        ReactiveApplication.Execution.environmentStep, PMF.pure_map, PMF.pure_bind,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume]
      simp only [inclusionReadout, Option.isSome_some, ↓reduceIte,
        ReactiveApplication.messageView, ReactiveApplication.Execution.includePending,
        MessageNetwork.includePending, found, frame.application, succeeds,
        ReactiveApplication.Execution.observeEnvironment]
      rfl

/-- Protected inclusion transforms the actual phase transcript by a fixed
public operation. The only application-dependent receipt is successful when
the selected canonical opening is accepted. -/
private theorem openingWindow_inclusion_readout (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : candidate.1 = owner)
    (valid : selected.isSome →
      initial.application.candidates.lookup candidate = .openable raw)
    (accepted : selected.isSome →
      ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.windowEnvelope leaks owner event candidate raw initial)).isSome = true)
    (network : runtime.NetworkPolicy leaks) (focal : Player) :
    let app := runtime.reactiveApplication leaks
    let players := runtime.openingWindowPlayers leaks owner event candidate raw
      (initial.recall owner).length selected
    (runtime.runInteractionPlan leaks players network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).map
        (fun next => (app.messageView next, next.recall focal)) =
      ((runtime.runInteractionPlan leaks players network (roster.map ServiceInstruction.player)
        initial).map (fun next => (app.messageView next, next.recall focal))).map
          (inclusionReadout runtime leaks initial owner selected) := by
  dsimp only
  rw [runtime.runInteractionPlan_append, PMF.map_bind, PMF.map_comp,
    ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro current reached
  have start := OpeningWindowFrame.initial runtime leaks owner event candidate raw selected
    initial serials published
  have frame := start.run runtime leaks owner event candidate raw (initial.recall owner).length
    selected 0 initial initial network roster current reached owned valid
  simp only [Nat.zero_add] at frame
  simpa only [runInteractionPlan, PMF.bind_pure, Function.comp_def] using
    framed_inclusion_readout runtime leaks owner event candidate raw
      (initial.recall owner).length selected initial current frame serials accepted _ network focal

/-- A whole opening window and its protected inclusion have identical
auxiliary transcript laws at coupled source starts. The never-opening branch
does not identify the hidden commitment meanings. Arbitrary sampling and
unpublished replay copies are retained. -/
theorem openingWindow_inclusion_coupling (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (network : runtime.NetworkPolicy leaks) (focal : Player)
    (left right : (runtime.reactiveApplication leaks).Execution)
    (leftRecall : left.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : right.InputRecall (runtime.reactiveApplication leaks))
    (leftSerials : left.network.SerialsBeforeNext)
    (rightSerials : right.network.SerialsBeforeNext)
    (leftPublished : left.network.Satisfies fun message =>
      message.id ∈ left.network.ledger.map Message.id)
    (rightPublished : right.network.Satisfies fun message =>
      message.id ∈ right.network.ledger.map Message.id)
    (messages : (runtime.reactiveApplication leaks).messageView left =
      (runtime.reactiveApplication leaks).messageView right)
    (recall : left.recall focal = right.recall focal)
    (publicView : left.application.publicView = right.application.publicView)
    (privateView : (runtime.reactiveApplication leaks).observePlayer left.application focal =
      (runtime.reactiveApplication leaks).observePlayer right.application focal)
    (owned : candidate.1 = owner)
    (meaning : selected.isSome →
      left.application.candidates.lookup candidate = .openable raw ∧
        right.application.candidates.lookup candidate = .openable raw)
    (accepted : selected.isSome →
      ((runtime.reactiveApplication leaks).handle left.application
        (runtime.windowEnvelope leaks owner event candidate raw left)).isSome = true ∧
      ((runtime.reactiveApplication leaks).handle right.application
        (runtime.windowEnvelope leaks owner event candidate raw right)).isSome = true) :
    let app := runtime.reactiveApplication leaks
    let players := fun start : app.Execution =>
      runtime.openingWindowPlayers leaks owner event candidate raw
        (start.recall owner).length selected
    (runtime.runInteractionPlan leaks (players left) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) left).map
        (fun next => (app.messageView next, next.recall focal)) =
    (runtime.runInteractionPlan leaks (players right) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) right).map
        (fun next => (app.messageView next, next.recall focal)) := by
  dsimp only
  rw [openingWindow_inclusion_readout runtime leaks owner event candidate raw roster selected left
      leftSerials leftPublished owned (fun h => (meaning h).1) (fun h => (accepted h).1),
    openingWindow_inclusion_readout runtime leaks owner event candidate raw roster selected right
      rightSerials rightPublished owned (fun h => (meaning h).2) (fun h => (accepted h).2)]
  have networks : left.network = right.network := congrArg Prod.fst messages
  have counts : (left.recall owner).length = (right.recall owner).length := by
    have histories := congrFun (congrArg (fun value => value.2.2.2) messages) owner
    simpa only [ReactiveApplication.messageView, ReactiveApplication.messageRecall,
      List.length_map] using congrArg List.length histories
  have transformed : inclusionReadout runtime leaks left owner selected =
      inclusionReadout runtime leaks right owner selected := by
    funext transcript
    simp only [inclusionReadout, networks, publicView]
  rw [transformed]
  apply congrArg (PMF.map (inclusionReadout runtime leaks right owner selected))
  simpa only [counts] using runtime.openingWindow_coupling leaks owner event candidate raw
    (left.recall owner).length selected network roster focal left right leftRecall rightRecall
      messages recall publicView privateView owned meaning

end Vegas.EventGraphRuntime
