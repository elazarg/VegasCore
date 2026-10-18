/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastAssessedResponse
import Vegas.Examples.CommitSeedBroadcastCountedSeedTrace
import Vegas.Examples.CommitSeedBroadcastPrivateCalendar
import Vegas.Pending.PhaseBindingMemoryCallback

/-! # An already-sent original helper has the actual assessed WAIT response -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- Every current request of an original owner names its unique original
binding. A retained original packet therefore leaves only WAIT in the menu,
independently of its hidden preparation and its eventual acceptance bit. -/
theorem original_sent_helper_menu (remaining : Nat) (execution : app.Execution) (hidden : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some hidden, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (sent : ∃ message ∈ app.outputs (execution.recall hidden),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    countedMenu.actions hidden (execution.recall hidden) (execution.observe app hidden) =
      {⟨none⟩} := by
  classical
  obtain ⟨seed, ⟨fixed⟩⟩ := menu_trace_fixed_seed countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) ⟨remaining, some hidden, execution⟩ trace
  let inputs : PMF graph.Inputs := PMF.pure (encodeInputs (Env.empty (CellVal simpleExpr)))
  have initialized : inputs.map (PhaseRuntimeState.initial plan) = initial := by
    change (PMF.pure (encodeInputs (Env.empty (CellVal simpleExpr)))).map
      (PhaseRuntimeState.initial plan) =
        PMF.pure (PhaseRuntimeState.initial plan (encodeInputs (Env.empty (CellVal simpleExpr))))
    exact PMF.pure_map _ _
  have compiled : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some ⟨remaining, some hidden, execution⟩) := by
    rw [initialized]
    exact trace
  apply PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals) inputs horizon scheduler
      remaining hidden execution compiled
  rintro ⟨coordinate, request, unsent⟩
  have named := original_request_coordinate seed ⟨remaining, some hidden, execution⟩
    (countedMenu.toRawTrace initial horizon (family seed) fixed) coordinate hidden
      (request.1.trans original) request
  subst coordinate
  obtain ⟨message, member, event⟩ := sent
  exact unsent message member event

/-- At every genuine original counted input, sequential rationality makes
the already-sent helper's actual raw response law pure WAIT. No positive
equilibrium reach or proper future policy is assumed. -/
theorem assessed_original_sent_helper_wait (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (hidden : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some hidden, execution⟩))
    (original : execution.application.attempt = originalAttempt)
    (sent : ∃ message ∈ app.outputs (execution.recall hidden),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    rawMenu.decodeProfile initial horizon scheduler assessment.strategy hidden
      (execution.recall hidden) (execution.observe app hidden) = PMF.pure ⟨none⟩ := by
  have singleton := original_sent_helper_menu remaining execution hidden trace original sent
  rw [← counted_assessment_response_law assessment equilibrium
    ⟨some ⟨remaining, some hidden, execution⟩, trace⟩ remaining execution hidden rfl]
  apply pmf_eq_pure_of_support_subset_singleton
  intro response chosen
  have offered := countedMenu.decode_embedPolicy_covered initial horizon scheduler hidden
    (countedAssessmentProfile assessment hidden) (execution.recall hidden)
      (execution.observe app hidden) response chosen
  rw [singleton] at offered
  exact Finset.mem_singleton.mp offered

end Vegas.Examples.CommitSeedBroadcast
