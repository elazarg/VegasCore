/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePrefix

/-! # Evaluating the source service's declared calendar

This evaluator executes the existing scheduler commands and player responses.
The segment theorem identifies it with ordinary protocol rounds at every
calendar position; it introduces no additional strategic choices or model.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory.Math.Probability

def runInstructions {Claim : Type} (players : Player → (application Claim).Policy) :
    List Instruction → (application Claim).Execution → FinDist (application Claim).Execution
  | [], execution => FinDist.pure execution
  | next :: rest, execution =>
      ((application Claim).dispatch players
        (instruction (execution.observeEnvironment (application Claim)) next) execution).bind
          (runInstructions players rest)

theorem runInstructions_append {Claim : Type} (players : Player → (application Claim).Policy)
    (before after : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (before ++ after) execution =
      (runInstructions players before execution).bind (runInstructions players after) := by
  induction before generalizing execution with
  | nil => exact (FinDist.pure_bind _ _).symm
  | cons next rest ih =>
      simp only [List.cons_append, runInstructions, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro middle _
      exact ih middle

theorem segment_rounds {Claim : Type} (players : Player → (application Claim).Policy)
    (before rest after : List Instruction) (split : calendar = before ++ rest ++ after)
    (execution : (application Claim).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (application Claim).runRounds (scheduler Claim) players rest.length execution =
      runInstructions players rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons next rest ih =>
      have selected : calendar[before.length]? = some next := by
        rw [split, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
        rfl
      have step : (application Claim).round (scheduler Claim) players execution =
          (application Claim).dispatch players
            (instruction (execution.observeEnvironment (application Claim)) next) execution := by
        simp only [ReactiveApplication.round, scheduler, position, selected,
          Option.elim_some, FinDist.pure_bind]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInstructions]
      apply FinDist.bind_congr
      intro middle supported
      apply ih (before ++ [next])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := (application Claim).dispatch_environmentRecall players
          (instruction (execution.observeEnvironment (application Claim)) next)
            execution middle supported
        simp only [advanced, List.length_append, List.length_singleton]
        omega

theorem runInstructions_application {Claim : Type}
    (players : Player → (application Claim).Policy) (cmd : Command)
    (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (.application cmd :: rest) execution =
      runInstructions players rest (effect execution (.application cmd)) := by
  simp only [runInstructions, instruction, ReactiveApplication.dispatch, effect_law,
    FinDist.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume]

theorem runInstructions_record {Claim : Type}
    (players : Player → (application Claim).Policy) (event : Event)
    (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (.record event :: rest) execution =
      runInstructions players rest
        (effect execution (latest (execution.observeEnvironment (application Claim)) event)) := by
  have passive : (latest (execution.observeEnvironment (application Claim)) event).actor?
      (application Claim) = none := by
    unfold latest
    split <;> rfl
  simp only [runInstructions, instruction, ReactiveApplication.dispatch, effect_law,
    FinDist.pure_bind, passive, ReactiveApplication.resume]

theorem runInstructions_ticks {Claim : Type}
    (players : Player → (application Claim).Policy) (count : Nat)
    (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (List.replicate count (.application .tick) ++ rest) execution =
      runInstructions players rest ((List.replicate count ()).foldl
        (fun current _ => effect current (.application .tick)) execution) := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append, runInstructions_application, ih]
      rfl

def afterResponse (event : Event) : List Instruction :=
  [.record event] ++ List.replicate (2 ^ event.val) (.application .tick) ++
    [.application (.settle event)] ++ ((List.finRange 6).drop (event.val + 1)).flatMap visit

def beforeResponse (event : Event) : List Instruction :=
  before event.val ++ [.application (.grant event)]

theorem response_split (event : Event) : calendar = beforeResponse event ++
    .player (eventOwner event) :: afterResponse event := by
  fin_cases event <;> rfl

theorem runInstructions_afterResponse {Claim : Type}
    (players : Player → (application Claim).Policy) (event : Event)
    (execution : (application Claim).Execution) :
    runInstructions players (afterResponse event) execution =
      runInstructions players (((List.finRange 6).drop (event.val + 1)).flatMap visit)
        (remainingVisit event execution) := by
  simp only [afterResponse, List.append_assoc, List.cons_append, List.nil_append]
  rw [runInstructions_record, runInstructions_ticks, runInstructions_application]
  rfl

end VegasTests.SelectiveAssociation.NamedSource
