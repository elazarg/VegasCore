/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedContinuation
import Vegas.Game.ServiceRosterEvaluation

/-! # Fully mixed timed execution reaches every retained boundary

Finite-game full mixing transfers an arbitrary legal retained prefix to the
actual physical timed evaluator. This supplies continuation laws after a
local alternative without assuming positive reach under a source equilibrium.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem mixed_run_support {E : ExecutionProtocol Player} {M : InformationModel E}
    (assessment : M.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (other : Profile M.behavioralSignature) (fuel : Nat) (start finish : E.History)
    (supported : finish ∈ (M.runBehavioralFrom other fuel start).support) :
    finish ∈ (M.runBehavioralFrom assessment.strategy fuel start).support := by
  induction fuel generalizing start with
  | zero => exact supported
  | succ fuel ih =>
      by_cases terminal : E.terminal start.state
      · simpa only [M.runBehavioralFrom_of_terminal _ _ terminal] using supported
      · rw [M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal,
          FinDist.support_bind] at supported ⊢
        obtain ⟨joint, _, reached⟩ := Set.mem_iUnion₂.mp supported
        refine Set.mem_iUnion₂.mpr ⟨joint, ?_, ?_⟩
        · exact M.mem_support_behavioralJoint assessment.strategy start.trace terminal
            joint.val joint.property (fun who => mixed.support_at_history start terminal who _)
        · rw [FinDist.support_bindOnSupport] at reached ⊢
          obtain ⟨state, realized, later⟩ := Set.mem_iUnion₂.mp reached
          exact Set.mem_iUnion₂.mpr ⟨state, realized, ih _ later⟩

omit [Fintype Player] in
/-- Every retained boundary, including those reached after a local deviation,
has positive mass in an admissible fully mixed physical implementation. The
complete native execution is preserved, including private response recall. -/
theorem roster_fullyMixed_prefix_support [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (assessment : (menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
    (strategy : assessment.strategy = fun who => menu.restrictPolicy (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
        (players who))
    (mixed : assessment.IsFullyMixed)
    (count : Nat) (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks menu.uniformResponses network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support) :
    execution ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support := by
  let _ := Fintype.ofFinite Player
  let planPrefix := rosterPlanPrefix setup rosters count
  have before := rosterPlanPrefix_isPrefix setup rosters count
  have within : planPrefix.length ≤ (rosterPlan setup rosters).length := before.length_le
  have prefixEq : (rosterPlan setup rosters).take planPrefix.length = planPrefix := by
    obtain ⟨suffix, split⟩ := before
    rw [← split]
    exact List.take_left
  have uniformCovered : ∀ who, menu.Admissible (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
        who (menu.uniformResponses who) := by
    intro who control _ _ action present
    exact (menu.uniformResponses_support who _ _ action).mp present
  have reference := roster_restrict_prefix_state setup leaks rosters network menu
    menu.uniformResponses uniformCovered planPrefix.length within
  rw [prefixEq] at reference
  have present : some ⟨(rosterPlan setup rosters).length - planPrefix.length, none, execution⟩ ∈
      (((menu.information (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network) who (menu.uniformResponses who))
        (planPrefix.length + (planPrefix.filterMap instructionActor).length + 1)).map
        History.state).support := by
    rw [reference, FinDist.support_map]
    exact ⟨execution, supported, rfl⟩
  obtain ⟨history, reached, stateEq⟩ := FinDist.support_map .. ▸ present
  have transferred := mixed_run_support assessment mixed _ _ _ history reached
  have actual := roster_restrict_prefix_state setup leaks rosters network menu players
    covered planPrefix.length within
  rw [prefixEq] at actual
  rw [strategy] at transferred
  have endpoint : history.state ∈
      (((menu.information (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) (rosterPlan setup rosters).length
          (rosterScheduler setup leaks rosters network) who (players who))
        (planPrefix.length + (planPrefix.filterMap instructionActor).length + 1)).map
        History.state).support := FinDist.support_map .. ▸ ⟨history, transferred, rfl⟩
  rw [actual, FinDist.support_map] at endpoint
  obtain ⟨finished, reached, same⟩ := endpoint
  have sameExecution : finished = execution := by
    exact congrArg (fun state => state.map (fun control => control.execution))
      (same.trans stateEq) |> Option.some.inj
  exact sameExecution ▸ reached

section

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (rosters : (graph setup).EventId → List Player)
  (network : (runtime setup).NetworkPolicy leaks)
  (menu : (application setup leaks).ResponseMenu)
  (players : Player → (application setup leaks).Policy)
  (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who (players who))
  (assessment : (menu.information (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
  (strategy : assessment.strategy = fun who => menu.restrictPolicy (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
      (players who))
  (mixed : assessment.IsFullyMixed)

include covered strategy mixed in
omit [Fintype Player] in
/-- All legal responses at an actual decision have positive physical mass in
the fully mixed implementation, independently of source reachability. -/
theorem roster_fullyMixed_response_support
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (response : (application setup leaks).Action)
    (allowed : response ∈ menu.actions who (execution.recall who)
      (execution.observe (application setup leaks) who)) :
    response ∈ (players who (execution.recall who)
      (execution.observe (application setup leaks) who)).support := by
  let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network)
  have observed : model.infoOf who trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change (menu.signals (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who trace = _
    rw [menu.info]
    simp only [ReactiveApplication.observe, ↓reduceIte]
  have permitted : some response ∈ model.menu who (model.infoOf who trace) := by
    rw [observed]
    exact ⟨response, allowed, rfl⟩
  let choice : model.Choice who (model.infoOf who trace) := ⟨some response, permitted⟩
  have running : ¬ (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).terminal
        (some ⟨remaining, some who, execution⟩) := by
    intro impossible
    have absent : (some who : Option Player) = none := impossible.2
    cases absent
  have chosen := mixed.support_at_history ⟨_, trace⟩ running who choice
  have mapped : some response ∈ ((assessment.strategy who (model.infoOf who trace)).map
      Subtype.val).support := FinDist.support_map .. ▸ ⟨choice, chosen, rfl⟩
  rw [strategy, observed, menu.restrictPolicy_map_val _ _ _ who _ _ _
    (covered who _ trace rfl), FinDist.support_map] at mapped
  obtain ⟨actual, present, same⟩ := mapped
  exact Option.some.inj same ▸ present

include covered strategy mixed in
omit [Fintype Player] in
/-- A legal response followed by any supported portion of the physical
baseline remains in the initialized baseline prefix law. Thus a local
alternative can use the same exact source continuation theorem. -/
theorem roster_fullyMixed_response_prefix_support [Finite Player]
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (count : Nat) (before tail : List (ServiceInstruction (graph setup)))
    (split : rosterPlanPrefix setup rosters count = before ++ .player who :: tail)
    (position : execution.environmentRecall.length = before.length + 1)
    (response : (application setup leaks).Action)
    (allowed : response ∈ menu.actions who (execution.recall who)
      (execution.observe (application setup leaks) who))
    (final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network tail
      (execution.respond (application setup leaks) who response)).support) :
    final ∈ ((initialLaw setup).bind fun initial =>
      (runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count)
        (ReactiveApplication.Execution.initial (application setup leaks) initial)).support := by
  let _ := Fintype.ofFinite Player
  let app := application setup leaks
  let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network)
  obtain ⟨later, complete⟩ := rosterPlanPrefix_isPrefix setup rosters count
  have full : rosterPlan setup rosters = before ++ .player who :: (tail ++ later) := by
    rw [← complete, split]
    simp only [List.append_assoc, List.cons_append]
  have selected : (rosterPlan setup rosters)[before.length]? = some (.player who) := by
    rw [full, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have prefixEq : (rosterPlan setup rosters).take before.length = before := by
    rw [full]
    exact List.take_left
  have depth := roster_decision_depth setup leaks rosters network menu who _ trace rfl
    before.length position
  have support := mixed.history_supported trace
  rw [depth, strategy] at support
  have law := roster_restrict_activation_state setup leaks rosters network menu players covered
    before.length who selected
  have mapped : some ⟨remaining, some who, execution⟩ ∈
      ((model.runBehavioral (fun actor => menu.restrictPolicy (initialLaw setup)
        (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) actor
          (players actor))
        (before.length + (((rosterPlan setup rosters).take before.length).filterMap
          instructionActor).length + 2)).map History.state).support :=
    FinDist.support_map .. ▸ ⟨⟨_, trace⟩, support, rfl⟩
  rw [law, FinDist.support_map] at mapped
  obtain ⟨activated, activatedSupport, same⟩ := mapped
  have executionEq : activated = execution := Option.some.inj
    (congrArg (fun state => state.map (fun control => control.execution)) same)
  subst activated
  rw [prefixEq, FinDist.support_bind] at activatedSupport
  obtain ⟨prior, priorSupport, activatedSupport⟩ := Set.mem_iUnion₂.mp activatedSupport
  obtain ⟨initial, initialSupport, beforeSupport⟩ := Set.mem_iUnion₂.mp
    (FinDist.support_bind .. ▸ priorSupport)
  have chosen := roster_fullyMixed_response_support setup leaks rosters network menu players
    covered assessment strategy mixed who remaining execution trace response allowed
  rw [split, FinDist.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨initial, initialSupport, ?_⟩
  rw [runInteractionPlan_append, FinDist.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨prior, beforeSupport, ?_⟩
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    FinDist.bind_bind, FinDist.support_bind]
  refine Set.mem_iUnion₂.mpr ⟨execution, activatedSupport, ?_⟩
  refine Set.mem_iUnion₂.mpr ⟨execution.respond app who response, ?_, reached⟩
  exact FinDist.support_map .. ▸ ⟨response, chosen, rfl⟩

end

end Vegas.SourceProgram.RevealService
