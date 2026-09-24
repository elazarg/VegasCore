/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourceAssessmentValues

/-! # Exact source controls at the two ambient responses -/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

theorem ambient_decision_representation (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (ambient : control.execution.application.visit = none) :
    (who = alice ∧ control.remaining = horizon - 1 ∧
      control.execution = effect (root Claim) (.activate alice)) ∨
    (who = bob ∧ control.remaining = horizon - 2 ∧
      ∃ first : (application Claim).Action,
        control.execution = effect (firstResponse first) (.activate bob)) := by
  obtain ⟨accounted, supported⟩ := (menu Claim).roundSupported_uniform
    (FinDist.pure initial) horizon (scheduler Claim) trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := (application Claim).roundsFrom_recall (FinDist.pure initial) (scheduler Claim)
    (menu Claim).uniformResponses count prior priorMem
  have bounded : count < calendar.length := by
    change _ + _ = calendar.length at accounted
    omega
  have selected : (calendar[count]?).bind instructionPlayer = some who := by
    simp only [scheduler, cursor] at commandMem
    cases found : calendar[count]? with
    | none =>
        simp only [found, FinDist.mem_support_pure] at commandMem
        subst command
        cases actor
    | some next =>
        simp only [found, Option.elim_some, FinDist.mem_support_pure] at commandMem
        subst command
        simp only [Option.bind_some]
        exact (instruction_actor next _).symm.trans actor
  have positions : count = 0 ∨ count = 1 ∨ ∃ event : Event,
      count = (beforeResponse event).length ∧ who = eventOwner event := by
    have all : ∀ index : Fin calendar.length, ∀ player : Player,
        (calendar[index.val]?).bind instructionPlayer = some player →
          index.val = 0 ∨ index.val = 1 ∨ ∃ event : Event,
            index.val = (beforeResponse event).length ∧ player = eventOwner event := by decide
    exact all ⟨count, bounded⟩ who selected
  rcases positions with early | early | ⟨event, same, owner⟩
  · rw [early] at selected priorMem cursor position
    have aliceEq : who = alice := (Option.some.inj selected).symm
    subst who
    have priorEq : prior = root Claim := by
      simpa only [ReactiveApplication.roundsFrom, FinDist.pure_bind,
        ReactiveApplication.runRounds, FinDist.mem_support_pure, root] using priorMem
    subst prior
    have commandEq : command = .activate alice := by
      change command ∈ (FinDist.pure (.activate alice)).support at commandMem
      exact FinDist.mem_support_pure.mp commandMem
    subst command
    rw [effect_law, FinDist.mem_support_pure] at observed
    exact Or.inl ⟨rfl, by omega, observed⟩
  · rw [early] at selected priorMem cursor position
    have bobEq : who = bob := (Option.some.inj selected).symm
    subst who
    have firstLaw := priorMem
    change prior ∈ ((application Claim).roundsFrom (FinDist.pure initial)
      (scheduler Claim) (menu Claim).uniformResponses
        ([.player alice] : List Instruction).length).support at firstLaw
    rw [roundsFrom_prefix (menu Claim).uniformResponses [.player alice] calendar.tail rfl]
      at firstLaw
    simp only [runInstructions_player, runInstructions_nil] at firstLaw
    rw [← FinDist.map_eq_bind, FinDist.support_map] at firstLaw
    obtain ⟨first, _, firstEq⟩ := firstLaw
    have commandEq : command = .activate bob := by
      simpa only [scheduler, cursor, show calendar[1]? = some (.player bob) from rfl,
        Option.elim_some, instruction, FinDist.mem_support_pure] using commandMem
    subst command
    rw [effect_law, FinDist.mem_support_pure] at observed
    exact Or.inr ⟨rfl, by omega, first, observed.trans (congrArg
      (fun execution => effect execution (.activate bob)) firstEq.symm)⟩
  · have evaluated := priorMem
    rw [same, roundsFrom_prefix (menu Claim).uniformResponses (beforeResponse event)
      (.player (eventOwner event) :: afterResponse event) (response_split event)] at evaluated
    have visit := response_prefix_visit (menu Claim).uniformResponses event prior evaluated
    have sameVisit := activation_visit prior control.execution who (by
      cases command <;> simp only [ReactiveApplication.Command.actor?] at actor <;>
        try cases actor
      exact observed)
    rw [sameVisit, visit] at ambient
    cases ambient

theorem bob_ambient_representation (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (ambient : control.execution.application.visit = none) :
    control.remaining = horizon - 2 ∧ ∃ first : (application Claim).Action,
      control.execution = effect (firstResponse first) (.activate bob) := by
  rcases ambient_decision_representation Claim control trace bob active ambient with left | right
  · exact (by decide : bob ≠ alice) left.1 |>.elim
  · exact right.2

theorem alice_ambient_representation (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some alice) (ambient : control.execution.application.visit = none) :
    control.remaining = horizon - 1 ∧
      control.execution = effect (root Claim) (.activate alice) := by
  rcases ambient_decision_representation Claim control trace alice active ambient with left | right
  · exact left.2
  · exact (by decide : alice ≠ bob) right.1 |>.elim

theorem finish_ambient_law {Claim : Type} (players : Player → (application Claim).Policy)
    (count : Nat) (bounded : count ≤ horizon) (who : Player)
    (control : (application Claim).Control) (active : control.actor = some who)
    (remaining : control.remaining = horizon - count)
    (position : control.execution.environmentRecall.length = count) :
    (application Claim).finish (FinDist.pure initial) horizon (scheduler Claim) players
        (some control) =
      ((players who (control.execution.recall who)
        (control.execution.observe (application Claim) who)).bind
          (fun response => runInstructions players (calendar.drop count)
            (control.execution.respond (application Claim) who response))).map
              (application Claim).finished := by
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, FinDist.bind_map, remaining]
  congr 1
  apply FinDist.bind_congr
  intro response _
  rw [show horizon - count = (calendar.drop count).length by simp [horizon]]
  apply segment_rounds players (calendar.take count) (calendar.drop count) []
  · simp only [List.append_nil, List.take_append_drop]
  · rw [(application Claim).respond_environmentRecall, position, List.length_take]
    exact (Nat.min_eq_left bounded).symm

end VegasTests.SelectiveAssociation.NamedSource
