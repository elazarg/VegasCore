/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRoundTrace
import VegasTests.ReactiveAssociationEvidence
import VegasTests.SelectiveAssociationOpeningIncentives

/-! # Alice's initial native information site has a single possible control

The statement covers every legal compatible history, independently of an
assessment's support. The public grant separates later Alice responses from
the initial ambient response.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol ReactiveAssociationEvidence

def nativeInitialControl : nativeApp.Control := ⟨88, some alice, activatedInitial⟩

theorem native_initial_representation (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (active : control.actor = some alice)
    (ambient : control.execution.application.serviceGrant = none) :
    control = nativeInitialControl := by
  obtain ⟨accounted, supported⟩ := nativeMenu.roundSupported_uniform
    (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace
  rw [active] at supported
  obtain ⟨count, prior, command, position, priorMem, commandMem, actor, observed⟩ := supported
  have cursor := nativeApp.roundsFrom_recall (FinDist.pure nativeInitial) nativeScheduler
    nativeMenu.uniformResponses count prior priorMem
  have bounded : count < nativePlan.length := by
    change _ + _ = nativePlan.length at accounted
    omega
  have selected : (nativePlan[count]?).bind nativeInstructionPlayer = some alice := by
    simp only [nativeScheduler, cursor] at commandMem
    cases found : nativePlan[count]? with
    | none =>
        simp only [found, FinDist.mem_support_pure] at commandMem
        subst command
        cases actor
    | some instruction =>
        rw [found] at commandMem
        simp only [Option.bind_some]
        exact (native_instruction_actor instruction _ _ command commandMem).symm.trans actor
  have positions : count = 0 ∨ ∃ event : nativeGraph.EventId,
      count = (nativeBeforeResponse event).length := by
    have all : ∀ index : Fin nativePlan.length,
        (nativePlan[index.val]?).bind nativeInstructionPlayer = some alice →
          index.val = 0 ∨ ∃ event : nativeGraph.EventId,
            index.val = (nativeBeforeResponse event).length := by decide
    exact all ⟨count, bounded⟩ selected
  rcases positions with early | ⟨event, same⟩
  · rw [early] at priorMem position
    have priorEq : prior = nativeRoot := by
      simpa only [ReactiveApplication.roundsFrom, FinDist.pure_bind,
        ReactiveApplication.runRounds, FinDist.mem_support_pure, nativeRoot] using priorMem
    subst prior
    have commandEq : command = .activate alice := by
      change command ∈ (FinDist.pure (.activate alice)).support at commandMem
      exact FinDist.mem_support_pure.mp commandMem
    subst command
    change control.execution ∈ (initial.environmentStep app (.activate 0)).support at observed
    rw [initial_activation, FinDist.mem_support_pure] at observed
    have remaining : control.remaining = 88 := by
      rw [native_horizon] at accounted
      omega
    cases control
    simp_all only [nativeInitialControl]
  · have evaluated := priorMem
    rw [same, native_roundsFrom_prefix nativeMenu.uniformResponses (nativeBeforeResponse event)
      (.player (nativeOwner event) :: nativeAfterResponse event)
      (native_response_split event)] at evaluated
    have grant := native_response_prefix_grant nativeMenu.uniformResponses event prior evaluated
    have sameGrant := native_activation_grant prior control.execution alice (by
      cases command <;> simp only [ReactiveApplication.Command.actor?] at actor <;>
        try cases actor
      exact observed)
    rw [sameGrant, grant] at ambient
    cases ambient

theorem native_initial_trace : Nonempty (nativeArena.Trace (some nativeInitialControl)) := by
  have setup : Nonempty (nativeArena.Trace (some ⟨89, none, nativeRoot⟩)) := by
    refine ⟨.extend .start (fun _ => none) ?_ ?_⟩
    · constructor
      · change ¬False
        trivial
      · intro who
        simp [nativeArena, ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor]
    · change _ ∈ ((FinDist.pure nativeInitial).map _).support
      rw [FinDist.map_pure, FinDist.mem_support_pure]
      rfl
  obtain ⟨setupTrace⟩ := setup
  apply nativeMenu.trace_environment (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    88 nativeRoot activatedInitial (.activate alice) setupTrace
  · change _ ∈ (FinDist.pure (.activate alice : nativeApp.Command)).support
    exact FinDist.mem_support_pure.mpr rfl
  · change activatedInitial ∈ (initial.environmentStep app (.activate 0)).support
    rw [initial_activation]
    exact FinDist.mem_support_pure.mpr rfl

def nativeInitialSite : nativeModel.InformationSite alice := by
  let trace := native_initial_trace.some
  have information : nativeModel.infoOf alice trace =
      some (activatedInitial.recall alice, activatedInitial.observe nativeApp alice) := by
    change (nativeMenu.signals (FinDist.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
      alice trace = _
    rw [nativeMenu.info]
    rfl
  refine ⟨some (activatedInitial.recall alice, activatedInitial.observe nativeApp alice),
    ⟨⟨some nativeInitialControl, trace⟩, information⟩, ?_, ?_⟩
  · change ¬(88 = 0 ∧ (some alice : Option Player) = none)
    simp
  · obtain ⟨response, available⟩ := nativeMenu.nonempty alice
      (activatedInitial.recall alice) (activatedInitial.observe nativeApp alice)
    exact ⟨response, response, available, rfl⟩

theorem native_initial_information_control
    (history : nativeModel.InformationHistory alice nativeInitialSite.1) :
    history.1.state = some nativeInitialControl := by
  obtain ⟨control, stateEq, active, _, observed⟩ := native_information_control alice
    (activatedInitial.recall alice) (activatedInitial.observe nativeApp alice) history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  change some control = some nativeInitialControl
  apply congrArg some
  apply native_initial_representation control trace active
  have grant := congrArg (fun view : nativeApp.PlayerView =>
    view.application.publicView.serviceGrant) observed
  exact grant

end VegasTests.SelectiveAssociation
