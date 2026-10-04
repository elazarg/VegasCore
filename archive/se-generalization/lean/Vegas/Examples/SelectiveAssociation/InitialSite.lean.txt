/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace
import Vegas.Examples.ReactiveAssociationEvidence
import Vegas.Examples.SelectiveAssociation.OpeningIncentives

/-! # Alice's initial native information site has a single possible control

The statement covers every legal compatible history, independently of an
assessment's support. Alice's own recall separates her later responses from
the initial ambient response.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol ReactiveAssociationEvidence

def nativeInitialControl : nativeApp.Control := ⟨82, some alice, activatedInitial⟩

theorem native_initial_representation (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (ambient : nativeTurnEvent? alice (control.execution.recall alice).length = none) :
    control = nativeInitialControl := by
  obtain ⟨accounted, supported⟩ := nativeMenu.roundSupported_uniform
    (PMF.pure nativeInitial) nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := nativeApp.roundsFrom_recall (PMF.pure nativeInitial) nativeScheduler
    nativeMenu.uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind nativeInstructionPlayer = some alice := by
    simp only [serviceScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, PMF.mem_support_pure_iff _ _] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (native_instruction_actor instruction _ _ command commandMem).symm.trans actor
  have positions : count = 0 ∨ ∃ event : nativeGraph.EventId,
      count = (nativeBeforeResponse event).length ∧ alice = nativeOwner event := by
    have all : ∀ index : Fin nativePlan.length,
        (nativePlan[index.val]?).bind nativeInstructionPlayer = some alice →
          index.val = 0 ∨ ∃ event : nativeGraph.EventId,
            index.val = (nativeBeforeResponse event).length ∧ alice = nativeOwner event := by
      decide
    exact all ⟨count, bounded⟩ selected
  rcases positions with early | ⟨event, same, owner⟩
  · rw [early] at priorMem position
    have priorEq : prior = nativeRoot := by
      simpa only [ReactiveApplication.roundsFrom, PMF.pure_bind,
        ReactiveApplication.runRounds, PMF.mem_support_pure_iff _ _, nativeRoot] using priorMem
    subst prior
    have commandEq : command = .activate alice := by
      change command ∈ (PMF.pure (.activate alice)).support at commandMem
      exact (PMF.mem_support_pure_iff _ _).mp commandMem
    subst command
    change control.execution ∈ (initial.environmentStep app (.activate 0)).support at observed
    rw [initial_activation, PMF.mem_support_pure_iff _ _] at observed
    have remaining : control.remaining = 82 := by
      rw [native_horizon] at accounted
      omega
    cases control
    simp_all only [nativeInitialControl]
  · have turn := native_turn_of_decision_cursor event control trace (owner ▸ active)
      (same ▸ position)
    rw [turn.turnEvent?_of_active active] at ambient
    cases ambient

theorem native_initial_trace : Nonempty (nativeArena.Trace (some nativeInitialControl)) := by
  have setup : Nonempty (nativeArena.Trace (some ⟨83, none, nativeRoot⟩)) := by
    refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
    · constructor
      · change ¬False
        trivial
      · intro who
        simp [nativeArena, serviceArena, ReactiveApplication.ResponseMenu.protocol,
          ReactiveApplication.actor]
    · change _ ∈ ((PMF.pure nativeInitial).map _).support
      rw [PMF.pure_map, PMF.mem_support_pure_iff _ _]
      rfl
  obtain ⟨setupTrace⟩ := setup
  apply nativeMenu.trace_environment (PMF.pure nativeInitial) nativeHorizon nativeScheduler
    82 nativeRoot activatedInitial (.activate alice) setupTrace
  · change _ ∈ (PMF.pure (.activate alice : nativeApp.Command)).support
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · change activatedInitial ∈ (initial.environmentStep app (.activate 0)).support
    rw [initial_activation]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl

def nativeInitialSite : nativeModel.InformationSite alice := by
  let trace := native_initial_trace.some
  have information : nativeModel.infoOf alice trace =
      some (activatedInitial.recall alice, activatedInitial.observe nativeApp alice) := by
    change (nativeMenu.signals (PMF.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
      alice trace = _
    rw [nativeMenu.info]
    rfl
  refine ⟨some (activatedInitial.recall alice, activatedInitial.observe nativeApp alice),
    ⟨⟨some nativeInitialControl, trace⟩, information⟩, ?_, ?_⟩
  · change ¬(82 = 0 ∧ (some alice : Option Player) = none)
    simp
  · obtain ⟨response, available⟩ := nativeMenu.nonempty alice
      (activatedInitial.recall alice) (activatedInitial.observe nativeApp alice)
    exact ⟨response, response, available, rfl⟩

theorem native_initial_information_control
    (history : nativeModel.InformationHistory alice nativeInitialSite.1) :
    history.1.state = some nativeInitialControl := by
  obtain ⟨control, stateEq, active, recalled, _⟩ := native_information_control alice
    (activatedInitial.recall alice) (activatedInitial.observe nativeApp alice) history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  change some control = some nativeInitialControl
  apply congrArg some
  apply native_initial_representation control trace active
  rw [recalled]
  decide

end Vegas.Examples.SelectiveAssociation
