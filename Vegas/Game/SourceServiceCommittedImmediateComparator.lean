/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceEffectiveImmediateComparator
import GameTheoryExtensions.Protocol.CommittedContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # One chosen immediate response and the actual whole comparator

A supported immediate response is fixed at the current information site.
Decision recall leaves the comparator unchanged afterward. Actual owner slot
resources admit that same policy from its idle successor, including against
arbitrary effective opponents. The conclusion is its physical terminal law.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory GameTheory.Math.Probability
  GameTheory.Enforcement GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks
local notation "menu" => service.bounds.menu (runtime service.setup) service.leaks

open Classical in
/-- Fixing this actual immediate-supported response then follows the same
implementable immediate comparator, with its full physical terminal law. -/
theorem effectiveImmediateComparator_committed_terminal_law
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (permitted : (profile who).Admitted service.setup.program (CommitmentInterface.values _))
    (baseline : ∀ player, ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).BehavioralPolicy player)
    (history : ((menu).protocol (initialLaw service.setup) service.horizon
      service.scheduler).History)
    (remaining : Nat) (execution : (app).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (compatible : service.sourceCompatibleInfo who
      (some (execution.recall who, execution.observe (app) who)))
    (choice : ((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).Choice who (((menu).information (initialLaw service.setup)
        service.horizon service.scheduler).infoOf who history.trace))
    (response : (app).Action) (selected : choice.1 = some response)
    (chosen : response ∈ (sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who (execution.recall who) (execution.observe (app) who)).support) :
    (((menu).information (initialLaw service.setup) service.horizon
      service.scheduler).runBehavioralTerminalFrom
        ((menu).bounded (initialLaw service.setup) service.horizon
          service.scheduler).wellFoundedHistories
        (Profile.update (sig := ((menu).information (initialLaw service.setup)
          service.horizon service.scheduler).behavioralSignature) baseline who
          ((service.effectiveImmediateComparator profile who).commit
            (((menu).information (initialLaw service.setup) service.horizon
              service.scheduler).infoOf who history.trace) choice)) history).map History.state =
      (app).finish (initialLaw service.setup) service.horizon service.scheduler
        (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
          service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
            service.leaks service.bound profile who))
        (some ⟨remaining, none, execution.respond (app) who response⟩) := by
  let model := (menu).information (initialLaw service.setup) service.horizon service.scheduler
  let protocol := (menu).protocol (initialLaw service.setup) service.horizon service.scheduler
  let certificate := ((menu).bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let reference := Profile.update (sig := model.behavioralSignature) baseline who
    (service.effectiveImmediateComparator profile who)
  let committed := Profile.update (sig := model.behavioralSignature) reference who
    ((reference who).commit (model.infoOf who history.trace) choice)
  have updatedEq : committed = Profile.update (sig := model.behavioralSignature) baseline who
      ((service.effectiveImmediateComparator profile who).commit
        (model.infoOf who history.trace) choice) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [committed, reference, Profile.update_same]
    · simp only [committed, reference, Profile.update_of_ne _ _ same]
  have active : protocol.active history.state who := by
    change (app).actor history.state = some who
    rw [current]
    rfl
  have nonterminal : ¬ protocol.terminal history.state := by
    change ¬ (app).terminal history.state
    rw [current]
    simp only [ReactiveApplication.terminal, Option.some_ne_none, and_false, not_false_eq_true]
  have once : model.ActsOnceWhereItMatters := model.actsOnceWhereItMatters_of_actsOnce
    (InformationModel.actsOnce_of_decisionInformationAntichain
      ((menu).decisionRecall (initialLaw service.setup) service.horizon
        service.scheduler).decisionInformationAntichain)
  let rawTrace := (menu).toRawTrace (initialLaw service.setup) service.horizon service.scheduler
    history.trace
  have budget := (app).trace_bound (initialLaw service.setup) service.horizon service.scheduler
    rawTrace
  have traceLength : rawTrace.length = history.trace.length := (menu).toRawTrace_length ..
  have positive : 0 < (app).rank service.horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  let fuel := 2 * service.horizon + 1 - history.trace.length - 1
  have fuelEq : 0 + 1 + fuel = 2 * service.horizon + 1 - history.trace.length := by
    dsimp only [fuel]
    omega
  have first := (menu).run_commit_response (initialLaw service.setup) service.horizon
    service.scheduler reference history who remaining execution current choice response selected
  have split := model.runBehavioralFrom_commit_split once reference who _ choice history rfl
    active nonterminal 0 fuel
  change (model.runBehavioralTerminalFrom certificate _ history).map History.state = _
  rw [← updatedEq, model.runBehavioralTerminalFrom_eq_remaining certificate committed
    ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler) history,
    ← fuelEq, split, PMF.map_bind]
  have mapped : ∀ next ∈ (model.runBehavioralFrom committed 1 history).support,
      (model.runBehavioralFrom reference fuel next).map History.state =
        (app).finish (initialLaw service.setup) service.horizon service.scheduler
          (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
            service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
              service.leaks service.bound profile who)) next.state := by
    intro next supported
    have nextState : next.state =
        some ⟨remaining, none, execution.respond (app) who response⟩ := by
      have reached : next.state ∈ ((model.runBehavioralFrom committed 1 history).map
          History.state).support := PMF.support_map .. ▸ ⟨next, supported, rfl⟩
      rw [first] at reached
      exact (PMF.mem_support_pure_iff _ _).mp reached
    have path := protocol.runRandomizedFor_reachesWithin (model.randomizedChooser committed)
      1 history next supported
    have nextLength : next.trace.length = history.trace.length + 1 := by
      cases path with
      | refl => rw [current] at nextState; cases nextState
      | step joint legal realized rest =>
          have same := protocol.reachesWithin_zero_iff.mp rest
          subst next
          rfl
    have runner := model.runBehavioralTerminalFrom_eq_remaining certificate reference
      ((menu).bounded (initialLaw service.setup) service.horizon service.scheduler) next
    have nextFuel : 2 * service.horizon + 1 - next.trace.length = fuel := by
      dsimp only [fuel]
      omega
    rw [nextFuel] at runner
    rw [← runner]
    obtain ⟨_, atTurn, slots, _⟩ := service.sourceCompatibleInfo_raw_prefixFacts
      ⟨remaining, some who, execution⟩ (current ▸ rawTrace) who compatible
    obtain ⟨atStart, slotsStart⟩ := sourceServiceImmediatePolicy_canonicalSlots_respond
      (current ▸ rawTrace) atTurn slots chosen
    exact service.effectiveImmediateComparator_terminal_law profile who permitted certificate
      baseline next ⟨remaining, none, execution.respond (app) who response⟩ nextState
        atStart slotsStart
  calc
    _ = (model.runBehavioralFrom committed 1 history).bind (fun next =>
        (app).finish (initialLaw service.setup) service.horizon service.scheduler
          (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
            service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
              service.leaks service.bound profile who)) next.state) :=
      bind_congr_on_support _ mapped
    _ = ((model.runBehavioralFrom committed 1 history).map History.state).bind
        ((app).finish (initialLaw service.setup) service.horizon service.scheduler
          (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
            service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
              service.leaks service.bound profile who))) := by
      exact (PMF.bind_map (model.runBehavioralFrom committed 1 history)
        (fun next : protocol.History => next.state)
        ((app).finish (initialLaw service.setup) service.horizon service.scheduler
          (Function.update ((menu).decodeProfile (initialLaw service.setup) service.horizon
            service.scheduler baseline) who (sourceServiceImmediatePolicy service.setup
              service.leaks service.bound profile who)))).symm
    _ = _ := by rw [first, PMF.pure_bind]

end Vegas.AsyncServiceSpec
