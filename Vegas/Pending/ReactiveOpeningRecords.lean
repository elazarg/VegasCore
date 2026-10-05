/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningSettlement

/-! # Public records of a settled opening window

Protected inclusion records one canonical envelope and receipt, independently
of the selected owner visit, or passive observations.
Every author's allocation counter is accounted for.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem OpeningWindowFrame.settle_records (runtime : EventGraphRuntime graph)
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
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.interactionStep leaks players network
      (.includeLatest event owner) current).support) :
    final.network.ledger = (if selected.isSome then List.append initial.network.ledger
      [runtime.windowEnvelope leaks owner event candidate raw initial]
      else initial.network.ledger) ∧
    final.receipts = (if selected.isSome then initial.receipts ++
      [((owner, initial.network.nextSerial owner), true)] else initial.receipts) ∧
    final.network.nextSerial = fun who => initial.network.nextSerial who +
      if who = owner ∧ selected.isSome then 1 else 0 := by
  let app := runtime.reactiveApplication leaks
  have selection := frame.selection runtime leaks owner event candidate raw offset selected
    initial current serials
  simp only [interactionStep, interactionInstruction, PMF.pure_bind, selection] at reached
  cases selected with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      refine ⟨frame.ledger, frame.receipts, ?_⟩
      exact frame.counters
  | some slot =>
      have opened : openingPassed (some slot) slots = true := by
        simpa only [openingPassed, Option.any_some, decide_eq_true_eq] using slot.isLt
      have found := frame.lookup_opened runtime leaks owner event candidate raw offset (some slot)
        slots initial current serials opened
      have receipt := accepted rfl
      simp only [Option.isSome_some, ↓reduceIte,
        ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
        PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
        found, frame.application, receipt, frame.ledger, frame.receipts,
        Option.isSome_some, ↓reduceIte]
      refine ⟨rfl, True.intro, ?_⟩
      simpa only [opened] using frame.counters

theorem openingWindow_records (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (roster : List Player) (selected : Option (Fin (roster.count owner)))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : candidate.1 = owner)
    (valid : selected.isSome → initial.application.candidates.lookup candidate = .openable raw)
    (accepted : selected.isSome →
      ((runtime.reactiveApplication leaks).handle initial.application
        (runtime.windowEnvelope leaks owner event candidate raw initial)).isSome = true)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw
        (initial.recall owner).length selected) network
      (roster.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    final.network.ledger = (if selected.isSome then List.append initial.network.ledger
      [runtime.windowEnvelope leaks owner event candidate raw initial]
      else initial.network.ledger) ∧
    final.receipts = (if selected.isSome then initial.receipts ++
      [((owner, initial.network.nextSerial owner), true)] else initial.receipts) ∧
    final.network.nextSerial = fun who => initial.network.nextSerial who +
      if who = owner ∧ selected.isSome then 1 else 0 := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨current, prior, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have frame := OpeningWindowFrame.initial runtime leaks owner event candidate raw selected
    initial serials published
  have finished := frame.run runtime leaks owner event candidate raw (initial.recall owner).length
    selected 0 initial initial network roster current prior owned valid
  simp only [Nat.zero_add] at finished
  have inclusion : final ∈ (runtime.interactionStep leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw (initial.recall owner).length
        selected) network (.includeLatest event owner) current).support := by
    simpa only [runInteractionPlan, PMF.bind_pure] using reached
  exact finished.settle_records runtime leaks owner event candidate raw
    (initial.recall owner).length selected initial current serials accepted _ network final
      inclusion

end Vegas.EventGraphRuntime
