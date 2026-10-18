/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingPublicationOpeningFiber
import Vegas.Examples.CommitSeedSignallingCalendarClocks

/-! # Truthful publication choices at actual continuation callbacks -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

def ownBindingRef (owner : Player) : FieldRef graph.layout (.binding owner .bool) :=
  ⟨.inr (bindingEvent owner), bindingEvent_layout owner⟩

theorem own_reveal_descriptor (owner : Player) :
    ∃ (checks : List (GuardCheck graph.layout .bool))
      (codeEq : cast (congrArg (EventCode graph.layout) (revealEvent_layout owner))
        (graph.nodes (revealEvent owner)) =
          EventCode.resolve (L := simpleExpr) (layout := graph.layout) owner BaseTy.bool
            (ownBindingRef owner) checks),
      nodeView graph (revealEvent owner) = .resolve owner .bool (ownBindingRef owner) checks
        (revealEvent_layout owner) codeEq := by
  fin_cases owner <;> exact ⟨_, rfl, rfl⟩

/-- Actual tail callbacks occur at relative clock zero, hence strictly before
their deadline. No timely-service premise is supplied by the caller. -/
theorem counted_tail_request_timely
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (coordinate : CommitAttemptEvent graph) (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate) :
    execution.application.current.native.WithinDeadline runtime coordinate.event := by
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) _ trace
  have clocks := tail_service_clocks countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seed
      ⟨remaining, some owner, execution⟩ fixed owner rfl coordinate retired request
  have current : (PhaseSeedScheduler.informationInput runtime leaks coordinate owner
      (execution.recall owner) (execution.observe app owner)).elapsed ∈
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        (execution.recall owner) (execution.observe app owner) := by
    change _ ∈ _ ++ [_]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  rw [clocks] at current
  have zero := List.mem_singleton.mp current
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have activated := (valid.active.activated_iff coordinate.event).mpr
    ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩
  obtain ⟨entered, found⟩ := Option.isSome_iff_exists.mp activated
  change execution.application.current.native.clock -
    (execution.application.current.native.activatedAt coordinate.event).getD
      execution.application.current.native.clock = 0 at zero
  rw [found, Option.getD_some] at zero
  unfold EventGraphRuntime.State.WithinDeadline
  rw [found]
  change execution.application.current.native.clock - entered < 6
  omega

/-- A surviving successful binding at a real publication callback supplies
an actual legal truthful opening, with no assumed candidate or menu witness. -/
theorem counted_tail_truthful_opening_available
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value))) :
    ∃ candidate, PhaseCount.phaseOpeningResponse runtime leaks (revealEvent owner) candidate
      ⟨.bool, value⟩ ∈ countedMenu.actions owner (execution.recall owner)
        (execution.observe app owner) := by
  classical
  have unsubmitted := counted_tail_callback_unsubmitted remaining execution owner trace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  have recalledInputs := PhaseCount.countRecall_history runtime leaks
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have unsent (message : Message Player (CommitAttemptPacket graph))
      (member : message ∈ app.outputs (execution.recall owner)) :
      PhaseCount.event? message.payload ≠
        some ⟨execution.application.attempt, revealEvent owner⟩ := by
    rw [← recalledInputs.1 owner] at member
    exact unsubmitted message (List.mem_filter.mp member).1
      (of_decide_eq_true (List.mem_filter.mp member).2)
  have typed : (ownBindingRef owner).get? execution.application.current.native.config.store =
      some (.success value) := by
    fin_cases owner <;> exact stored
  obtain ⟨checks, codeEq, node⟩ := own_reveal_descriptor owner
  obtain ⟨candidate, _accepted, literal⟩ := properPolicy_opening_response
    (fun _ _ _ => true) ⟨remaining, some owner, execution⟩ trace owner (revealEvent owner)
      (ownBindingRef owner) checks (revealEvent_layout owner) codeEq node request unsent value typed
  refine ⟨candidate, ?_⟩
  apply properPolicy_counted (fun _ _ _ => true) owner _ _ _
  rw [literal]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

open Classical in
/-- An actual successful publication callback cannot prescribe WAIT in a raw
sequential equilibrium. Candidate availability and timeliness are derived from
the original counted representative; the comparison covers its full raw fiber. -/
theorem counted_successful_publication_wait_not_supported
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (retired : execution.application.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner
      ⟨execution.application.attempt, revealEvent owner⟩)
    (value : Bool)
    (stored : execution.application.current.native.config.store (.inr (bindingEvent owner)) =
      some (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace)
    (choice : rawModel.Choice owner site.1) (selected : choice.1 = some ⟨none⟩) :
    choice ∉ (assessment.strategy owner site.1).support := by
  have trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  obtain ⟨candidate, allowed⟩ := counted_tail_truthful_opening_available remaining execution
    owner trace retired request value stored
  have timely := counted_tail_request_timely remaining execution owner trace
    ⟨execution.application.attempt, revealEvent owner⟩ retired request
  exact raw_publication_wait_not_supported assessment equilibrium source remaining execution
    owner current retired candidate value allowed request timely stored site atSite choice selected

end Vegas.Examples.CommitSeedSignalling
