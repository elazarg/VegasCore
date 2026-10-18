/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperAssessedOriginalObservation
import Vegas.Examples.CommitSeedBroadcastInitialFrameSeedPosterior
import Vegas.Examples.CommitSeedBroadcastHelperOriginalFrameLaw

/-! # The unchanged assessed original kernel at public helper-frame aliases -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

/-- The initialized helper frame has read no original service coordinate,
including when its private preparation was chosen by a different initial policy. -/
theorem initial_helper_frame_original_continuation (hidden : Player)
    (material : WitnessedSubmission graph) (players : Player → app.Policy) (count : Nat) :
    (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players count
      (initialHelperFrame hidden material)) =
    app.runRounds scheduler players count (initialHelperFrame hidden material) := by
  let initialPlayers : Player → app.Policy := fun owner _ _ =>
    PMF.pure (if owner = hidden then ⟨some material⟩ else ⟨none⟩)
  let reference : Seeds := Classical.choice (inferInstance : Nonempty Seeds)
  have reached : initialHelperFrame hidden material ∈
      (app.runRounds (family reference) initialPlayers 5 initialExecution).support := by
    rw [first_five_rounds]
    simp only [initialPlayers, PMF.pure_bind, PMF.pure_map]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  exact initial_frame_original_continuation initialPlayers players reference _ reached count

/-- At a prepared single-helper frame every actual input is the helper's
retained declaration. The other two initial actions are literal WAIT. -/
theorem initial_helper_outputs_inputs (hidden : Player) (material : WitnessedSubmission graph) :
    app.outputs ((initialHelperFrame hidden material).recall hidden) =
      (initialHelperFrame hidden material).network.inputs := by
  fin_cases hidden <;> rfl

/-- The public original binding name gives the actual retained-packet premise
needed by the counted audit theorem; no receipt or usable preparation is assumed. -/
theorem initial_helper_public_sent (hidden : Player) (material : WitnessedSubmission graph)
    (sent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden material),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    ∃ message ∈ app.outputs ((initialHelperFrame hidden material).recall hidden),
      PhaseCount.event? message.payload = some (originalCoordinate hidden) := by
  classical
  rw [initial_helper_outputs_inputs]
  rcases sent with ⟨message, member, named⟩
  refine ⟨message, ?_, named⟩
  change message ∈ (afterInitialResponses
    (if alice = hidden then ⟨some material⟩ else ⟨none⟩)
    (if bob = hidden then ⟨some material⟩ else ⟨none⟩)
    (if carol = hidden then ⟨some material⟩ else ⟨none⟩)).network.inputs
  exact List.mem_toFinset.mp member

/-- The actual equilibrium continuation, with all opponents unchanged,
has one original observable kernel across counted preparation aliases of the
same helper packet. Both original seed posteriors are derived from initialization;
the helper's future WAIT law follows from the actual whole-continuation audit. -/
theorem initial_helper_assessed_original_run_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (count : Nat) (bounded : count ≤ 19)
    (first second : WitnessedSubmission graph)
    (firstTrace : countedProtocol.Trace
      (some ⟨horizon - 5, none, initialHelperFrame hidden first⟩))
    (secondTrace : countedProtocol.Trace
      (some ⟨horizon - 5, none, initialHelperFrame hidden second⟩))
    (firstSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden first),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (secondSent : ∃ message ∈ initialPublicPackets (initialHelperFrame hidden second),
      PhaseCount.event? message.payload = some (originalCoordinate hidden))
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count
      (initialHelperFrame hidden first)).map (originalHelperObservation hidden) =
    (app.runRounds scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy) count
      (initialHelperFrame hidden second)).map (originalHelperObservation hidden) := by
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let forced := Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)
  have fuel : (horizon - 5 - count) + count = horizon - 5 := by
    change (128 - 5 - count) + count = 128 - 5
    omega
  have firstAligned : countedProtocol.Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden first⟩) := by
    rw [fuel]
    exact firstTrace
  have secondAligned : countedProtocol.Trace
      (some ⟨(horizon - 5 - count) + count, none, initialHelperFrame hidden second⟩) := by
    rw [fuel]
    exact secondTrace
  have firstActual := assessed_sent_helper_original_observation_law assessment equilibrium
    hidden count (horizon - 5 - count) _ firstAligned
      (initial_helper_public_sent hidden first firstSent)
  have secondActual := assessed_sent_helper_original_observation_law assessment equilibrium
    hidden count (horizon - 5 - count) _ secondAligned
      (initial_helper_public_sent hidden second secondSent)
  change (app.runRounds scheduler players count _).map _ =
    (app.runRounds scheduler players count _).map _
  rw [firstActual, secondActual]
  rw [← initial_helper_frame_original_continuation hidden first forced count,
    ← initial_helper_frame_original_continuation hidden second forced count]
  simp only [PMF.map_bind]
  apply congrArg (fun kernel => nativeSeedLaw.bind kernel)
  funext seed
  exact initial_helper_original_run_law seed forced hidden
    (by intro past view; dsimp only [forced]; rw [Function.update_self])
    count bounded first second packet

end Vegas.Examples.CommitSeedBroadcast
