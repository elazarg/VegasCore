/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationSourcePrefixEvaluation

/-! # Decision positions at every legal source history

The public stage grant identifies the calendar position of an active player.
The result applies independently of any proposed strategy or belief support.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.NamedSource

open Vegas Interaction GameTheory GameTheory.Protocol GameTheory.Math.Probability

def instructionPlayer : Instruction → Option Player
  | .player who => some who
  | _ => none

theorem instruction_actor {Claim : Type} (next : Instruction)
    (view : (application Claim).EnvironmentView) :
    (instruction view next).actor? (application Claim) = instructionPlayer next := by
  cases next with
  | player | application => rfl
  | record event =>
      change (latest view event).actor? (application Claim) = none
      unfold latest
      split <;> rfl

private theorem player_positions (count : Nat) (who : Player) (bounded : count < calendar.length)
    (selected : (calendar[count]?).bind instructionPlayer = some who) :
    count = 0 ∨ count = 1 ∨ ∃ event : Event,
      count = (beforeResponse event).length ∧ who = eventOwner event := by
  have all : ∀ cursor : Fin calendar.length, ∀ actor : Player,
      (calendar[cursor.val]?).bind instructionPlayer = some actor →
        cursor.val = 0 ∨ cursor.val = 1 ∨ ∃ event : Event,
          cursor.val = (beforeResponse event).length ∧ actor = eventOwner event := by decide
  exact all ⟨count, bounded⟩ who selected

theorem roundsFrom_prefix {Claim : Type} (players : Player → (application Claim).Policy)
    (before after : List Instruction) (split : calendar = before ++ after) :
    (application Claim).roundsFrom (FinDist.pure initial) (scheduler Claim) players before.length =
      runInstructions players before (root Claim) := by
  rw [ReactiveApplication.roundsFrom, FinDist.pure_bind]
  exact segment_rounds players [] before after split (root Claim) rfl

theorem activation_visit {Claim : Type} (execution next : (application Claim).Execution)
    (who : Player) (reached : next ∈
      (execution.environmentStep (application Claim) (.activate who)).support) :
    next.application.visit = execution.application.visit := by
  rw [effect_law, FinDist.mem_support_pure] at reached
  subst next
  rfl

private theorem early_rounds_visit (Claim : Type) [Fintype Claim] (count : Nat)
    (early : count = 0 ∨ count = 1) (execution : (application Claim).Execution)
    (reached : execution ∈ ((application Claim).roundsFrom (FinDist.pure initial)
      (scheduler Claim) (menu Claim).uniformResponses count).support) :
    execution.application.visit = none := by
  rcases early with rfl | rfl
  · simp only [ReactiveApplication.roundsFrom, FinDist.pure_bind,
      ReactiveApplication.runRounds, FinDist.mem_support_pure] at reached
    subst execution
    rfl
  · change execution ∈ ((application Claim).roundsFrom (FinDist.pure initial)
      (scheduler Claim) (menu Claim).uniformResponses
        ([.player alice] : List Instruction).length).support at reached
    rw [roundsFrom_prefix (menu Claim).uniformResponses [.player alice] calendar.tail rfl]
      at reached
    simp only [runInstructions_player, runInstructions_nil] at reached
    rw [← FinDist.map_eq_bind] at reached
    obtain ⟨response, _, rfl⟩ := FinDist.support_map .. ▸ reached
    exact firstResponse_visit response

theorem response_prefix_visit {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) (execution : (application Claim).Execution)
    (reached : execution ∈ (runInstructions players (beforeResponse event) (root Claim)).support) :
    execution.application.visit = some event := by
  rw [beforeResponse, runInstructions_append] at reached
  obtain ⟨prior, _, moved⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  rw [runInstructions_application, runInstructions_nil, FinDist.mem_support_pure] at moved
  subst execution
  rfl

theorem decision_cursor (Claim : Type) [Fintype Claim] (event : Event)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (who : Player) (active : control.actor = some who)
    (granted : control.execution.application.visit = some event) :
    who = eventOwner event ∧
      control.execution.environmentRecall.length = (beforeResponse event).length + 1 := by
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
  have visitSame := activation_visit prior control.execution who (by
    cases command <;> simp only [ReactiveApplication.Command.actor?] at actor <;>
      try cases actor
    exact observed)
  rcases player_positions count who bounded selected with early | early | ⟨current, same, owner⟩
  · rw [visitSame, early_rounds_visit Claim count (Or.inl early) prior priorMem] at granted
    cases granted
  · rw [visitSame, early_rounds_visit Claim count (Or.inr early) prior priorMem] at granted
    cases granted
  · have evaluated := priorMem
    rw [same, roundsFrom_prefix (menu Claim).uniformResponses (beforeResponse current)
      (.player (eventOwner current) :: afterResponse current) (response_split current)] at evaluated
    have visit := response_prefix_visit (menu Claim).uniformResponses current prior evaluated
    have identified : current = event :=
      Option.some.inj (visit.symm.trans (visitSame.symm.trans granted))
    subst current
    exact ⟨owner, by omega⟩

theorem decision_predecessor (Claim : Type) [Fintype Claim] (event : Event)
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some (eventOwner event))
    (granted : control.execution.application.visit = some event) :
    ∃ prior ∈ (runInstructions (menu Claim).uniformResponses
        (beforeResponse event) (root Claim)).support,
      control.execution = effect prior (.activate (eventOwner event)) := by
  have position := (decision_cursor Claim event control trace (eventOwner event) active granted).2
  obtain ⟨_, supported⟩ := (menu Claim).roundSupported_uniform
    (FinDist.pure initial) horizon (scheduler Claim) trace
  rw [active] at supported
  obtain ⟨count, prior, command, countEq, priorMem, commandMem, actor, observed⟩ := supported
  have same : count = (beforeResponse event).length := by omega
  subst count
  refine ⟨prior, ?_, ?_⟩
  · rw [roundsFrom_prefix (menu Claim).uniformResponses (beforeResponse event)
      (.player (eventOwner event) :: afterResponse event) (response_split event)] at priorMem
    exact priorMem
  · have cursor := (application Claim).roundsFrom_recall (FinDist.pure initial) (scheduler Claim)
      (menu Claim).uniformResponses _ prior priorMem
    simp only [scheduler, cursor, beforeResponse_selected,
      FinDist.mem_support_pure] at commandMem
    subst command
    exact FinDist.mem_support_pure.mp (effect_law prior _ ▸ observed)

theorem carol_decision_representation (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some carol) (granted : control.execution.application.visit = some 1) :
    ∃ sample ∈ (bindingLaw (menu Claim).uniformResponses).support,
      control.execution = carolInput sample.first sample.second sample.binding := by
  obtain ⟨prior, reached, same⟩ := decision_predecessor Claim 1 control trace active granted
  have supported : control.execution ∈
      ((runInstructions (menu Claim).uniformResponses (beforeResponse 1) (root Claim)).map
        (fun execution => effect execution (.activate carol))).support := by
    rw [FinDist.support_map]
    exact ⟨prior, reached, same.symm⟩
  rw [carol_prefix_law, FinDist.support_map] at supported
  obtain ⟨sample, reached, same⟩ := supported
  exact ⟨sample, reached, same.symm⟩

theorem bob_decision_representation (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (granted : control.execution.application.visit = some 2) :
    ∃ sample ∈ (guessLaw (menu Claim).uniformResponses).support,
      control.execution = bobInput sample.1.first sample.1.second sample.1.binding sample.2 := by
  obtain ⟨prior, reached, same⟩ := decision_predecessor Claim 2 control trace active granted
  have supported : control.execution ∈
      ((runInstructions (menu Claim).uniformResponses (beforeResponse 2) (root Claim)).map
        (fun execution => effect execution (.activate bob))).support := by
    rw [FinDist.support_map]
    exact ⟨prior, reached, same.symm⟩
  rw [bob_prefix_law, FinDist.support_map] at supported
  obtain ⟨sample, reached, same⟩ := supported
  exact ⟨sample, reached, same.symm⟩

def totalRecall {Claim : Type} (execution : (application Claim).Execution) : Nat :=
  ∑ who, (execution.recall who).length

theorem totalRecall_effect {Claim : Type} (execution : (application Claim).Execution)
    (cmd : (application Claim).Command) :
    totalRecall (effect execution cmd) = totalRecall execution :=
  Finset.sum_congr rfl fun who _ => congrArg List.length (effect_recall execution cmd who)

theorem totalRecall_respond {Claim : Type} (execution : (application Claim).Execution)
    (who : Player) (action : (application Claim).Action) :
    totalRecall (execution.respond (application Claim) who action) = totalRecall execution + 1 :=
  (application Claim).respond_total_recall execution who action

theorem totalRecall_remainingVisit {Claim : Type} (event : Event)
    (execution : (application Claim).Execution) :
    totalRecall (remainingVisit event execution) = totalRecall execution := by
  have ticks (count : Nat) (execution : (application Claim).Execution) :
      totalRecall ((List.replicate count ()).foldl
        (fun current _ => effect current (.application .tick)) execution) =
        totalRecall execution := by
    induction count generalizing execution with
    | zero => rfl
    | succ count ih =>
        rw [List.replicate_succ, List.foldl_cons, ih, totalRecall_effect]
  rw [remainingVisit, totalRecall_effect, ticks, totalRecall_effect]

theorem carolInput_totalRecall {Claim : Type} (first second binding : (application Claim).Action) :
    totalRecall (carolInput first second binding) = 3 := by
  simp only [carolInput, totalRecall_effect, totalRecall_remainingVisit, totalRecall_respond,
    aliceInput, prelude, firstResponse]
  simp [totalRecall, root, ReactiveApplication.Execution.initial]

theorem bobInput_totalRecall {Claim : Type}
    (first second binding guess : (application Claim).Action) :
    totalRecall (bobInput first second binding guess) = 4 := by
  rw [bobInput, totalRecall_effect, totalRecall_effect, totalRecall_remainingVisit,
    totalRecall_respond, carolInput_totalRecall]

theorem carol_decision_depth (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some carol) (granted : control.execution.application.visit = some 1) :
    trace.length = 13 := by
  have located := (decision_cursor Claim 1 control trace carol active granted).2
  obtain ⟨sample, _, same⟩ := carol_decision_representation Claim control trace active granted
  have counted := (application Claim).trace_length_of_control (FinDist.pure initial) horizon
    (scheduler Claim) control ((menu Claim).toRawTrace (FinDist.pure initial)
      horizon (scheduler Claim) trace)
  rw [ReactiveApplication.ResponseMenu.toRawTrace_length] at counted
  change trace.length = 1 + control.execution.environmentRecall.length +
    totalRecall control.execution at counted
  rw [located, same, carolInput_totalRecall] at counted
  exact counted

theorem bob_decision_depth (Claim : Type) [Fintype Claim]
    (control : (application Claim).Control) (trace : (arena Claim).Trace (some control))
    (active : control.actor = some bob) (granted : control.execution.application.visit = some 2) :
    trace.length = 20 := by
  have located := (decision_cursor Claim 2 control trace bob active granted).2
  obtain ⟨sample, _, same⟩ := bob_decision_representation Claim control trace active granted
  have counted := (application Claim).trace_length_of_control (FinDist.pure initial) horizon
    (scheduler Claim) control ((menu Claim).toRawTrace (FinDist.pure initial)
      horizon (scheduler Claim) trace)
  rw [ReactiveApplication.ResponseMenu.toRawTrace_length] at counted
  change trace.length = 1 + control.execution.environmentRecall.length +
    totalRecall control.execution at counted
  rw [located, same, bobInput_totalRecall] at counted
  exact counted

theorem carol_information_depth (Claim : Type) [Fintype Claim]
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (granted : view.application.visit = some 1)
    (history : (model Claim).InformationHistory carol (some (past, view))) :
    history.1.trace.length = 13 := by
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change ((menu Claim).signals (FinDist.pure initial) horizon (scheduler Claim)).infoOf
    carol trace = some (past, view) at observed
  rw [ReactiveApplication.ResponseMenu.info] at observed
  cases state with
  | none => cases observed
  | some control =>
      change (if control.actor = some carol then some (control.execution.recall carol,
        control.execution.observe (application Claim) carol) else none) =
          some (past, view) at observed
      split at observed
      · rename_i active
        have same := congrArg Prod.snd (Option.some.inj observed)
        apply carol_decision_depth Claim control trace active
        exact (congrArg (fun localView : (application Claim).PlayerView =>
          localView.application.visit) same).trans granted
      · cases observed

theorem bob_information_depth (Claim : Type) [Fintype Claim]
    (past : List (application Claim).PlayerEntry) (view : (application Claim).PlayerView)
    (granted : view.application.visit = some 2)
    (history : (model Claim).InformationHistory bob (some (past, view))) :
    history.1.trace.length = 20 := by
  rcases history with ⟨⟨state, trace⟩, observed⟩
  change ((menu Claim).signals (FinDist.pure initial) horizon (scheduler Claim)).infoOf
    bob trace = some (past, view) at observed
  rw [ReactiveApplication.ResponseMenu.info] at observed
  cases state with
  | none => cases observed
  | some control =>
      change (if control.actor = some bob then some (control.execution.recall bob,
        control.execution.observe (application Claim) bob) else none) =
          some (past, view) at observed
      split at observed
      · rename_i active
        have same := congrArg Prod.snd (Option.some.inj observed)
        apply bob_decision_depth Claim control trace active
        exact (congrArg (fun localView : (application Claim).PlayerView =>
          localView.application.visit) same).trans granted
      · cases observed

end VegasTests.SelectiveAssociation.NamedSource
