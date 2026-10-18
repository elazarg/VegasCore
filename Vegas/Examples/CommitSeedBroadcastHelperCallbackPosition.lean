/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperCallbackGap
import Vegas.Examples.CommitSeedBroadcastOriginalCallbackPrefix

/-! # The exact original helper callback positions -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The first late input of a bad owner follows its unique ordered clock-two
poll. The complete original raw prefix is used to derive the position. -/
theorem bad_firstLate_position (seed : Seeds) (remaining : Nat) (execution : app.Execution)
    (owner : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (bad : seed.2 owner = false) :
    execution.environmentRecall.length = 12 + (seed.1.symm owner).val := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seed) trace
  have original : execution.application.attempt = originalAttempt := request.1.symm
  obtain ⟨_used, _frame, before, _small, _started, _later, _framePublic, _framePosition,
    _position, observed, selected, _placement⟩ := original_first_late_run_prefix seed remaining
      execution owner (countedInRaw.trace initial horizon (family seed) trace) original clock
  have beforeRequest : before.application.SeedRequest owner (originalCoordinate owner) := by
    rw [observed] at request
    exact request
  have valid := raw_native_valid (family seed) _ raw
  have beforeValid : before.application.Invariant (encodeInputs (Env.empty (CellVal simpleExpr))) :=
    by rw [observed] at valid; exact valid
  have readyOwner : ready owner (bindingEvent owner) (before.observeEnvironment app) = true := by
    apply decide_eq_true
    change PhaseRuntimeState.requests before.application.publicView owner
      ⟨before.application.attempt, bindingEvent owner⟩
    rw [beforeRequest.1.symm]
    exact (before.application.requests_publicView beforeValid owner (originalCoordinate owner)).mpr
      beforeRequest
  have picked : .activate owner ∈ (family seed before.environmentRecall
      (before.observeEnvironment app)).support := by
    rw [selected]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  rw [family, choose_original _ _ _ beforeRequest.1.symm, PMF.mem_support_pure_iff] at picked
  have turn := (original_command_activation seed owner before.environmentRecall.length
    before.environmentRecall (before.observeEnvironment app) readyOwner).mp picked.symm
  simp only [originalTurns, bad, Bool.false_eq_true, ite_false, List.mem_cons,
    List.not_mem_nil, or_false] at turn
  have length : execution.environmentRecall.length = before.environmentRecall.length + 1 := by
    rw [observed]
    simp only [completeActivation, ReactiveApplication.Execution.sampledActivation,
      List.length_append, List.length_singleton]
  have bounds := (original_first_late_bad_iff seed _ raw owner rfl original clock).mp bad
  have upper : execution.environmentRecall.length ≤ 14 := by
    rcases original_first_late_input_placement seed _ raw owner rfl original clock with
      early | late
    · rw [bad] at early
      exact Bool.noConfusion early.2.2
    · exact late.2.1
  have ownerBound := owner.isLt
  omega

end Vegas.Examples.CommitSeedBroadcast
