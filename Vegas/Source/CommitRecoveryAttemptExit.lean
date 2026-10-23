/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryAttemptReset
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryAtom

/-! # The actual first exit of an original source commitment attempt -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

/-- An original commitment step either retains its literal saved frontier,
or exits its full attempt identifier on exactly the final source slot.
Exhausted restore is an exit even though its generation is unchanged. -/
theorem step_commit_inside_or_exit (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (committing : ProtocolState.atCommit program state.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support) :
    (next.saved = state.saved ∧ next.generation = state.generation ∧
      ProtocolState.atCommit program next.point = true ∧
      ProtocolState.remaining program next.point + 1 =
        ProtocolState.remaining program state.point ∧
      ProtocolState.commitEnd program state.saved < ProtocolState.remaining program next.point) ∨
    (next.publicAddress.2.2 ≠ state.publicAddress.2.2 ∧
      ProtocolState.remaining program state.point =
        ProtocolState.commitEnd program state.saved + 1) := by
  have savedCommit : ProtocolState.atCommit program state.saved = true := by
    rcases frontier with ⟨saved, _live, _endpoint⟩ | same
    · exact saved
    · rwa [same]
  have endpoint : ProtocolState.commitEnd program state.point =
      ProtocolState.commitEnd program state.saved := by
    rcases frontier with ⟨_saved, _live, endpoint⟩ | same
    · exact endpoint
    · rw [same]
  have savedBelow := ProtocolState.commitEnd_lt_remaining program state.saved savedCommit
  have savedBound := ProtocolState.remaining_le_instructionCount program state.saved
  have running : ¬ ProtocolState.terminal program state.point := by
    intro terminal
    have zero := (ProtocolState.remaining_zero_iff_terminal program state.point).mpr terminal
    have below := ProtocolState.commitEnd_lt_remaining program state.point committing
    omega
  obtain ⟨result, raw, rfl⟩ := state.step_raw_result joint next supported
  have consumed := ProtocolState.recoveryStep_remaining program state.point state.excluded joint
    result.1 running raw
  let installed := state.install result.1 result.2
  rcases ProtocolState.recoveryStep_commit_cursor program state.point state.excluded joint
      result.1 committing raw with ⟨inside, sameEnd⟩ | ⟨_outside, atEnd⟩
  · have beforeEnd : ProtocolState.commitEnd program state.saved <
        ProtocolState.remaining program result.1.1 := by
      have below := ProtocolState.commitEnd_lt_remaining program result.1.1 inside
      rw [sameEnd, endpoint] at below
      exact below
    have unchanged := installed.close_eq_self_of_remaining_gt savedCommit beforeEnd
    rw [unchanged]
    exact Or.inl ⟨rfl, rfl, inside, consumed, beforeEnd⟩
  · have completed : installed.Finished := ⟨savedCommit, atEnd.trans endpoint⟩
    have lastSlot : ProtocolState.remaining program state.point =
        ProtocolState.commitEnd program state.saved + 1 := by omega
    refine Or.inr ⟨?_, lastSlot⟩
    change installed.close.publicAddress.2.2 ≠ state.publicAddress.2.2
    by_cases failed : installed.NewFailure
    · by_cases survives : installed.Survives
      · rw [installed.close_of_retry completed failed survives]
        simp only [publicAddress, retry, atPoint]
        intro same
        have generations := congrArg Prod.fst same
        change state.generation + 1 = state.generation at generations
        omega
      · rw [installed.close_of_exhausted completed failed survives]
        simp only [publicAddress, exhausted, atPoint,
          ProtocolState.automaticCommitBlock_remaining, restored,
          ProtocolState.commitEnd_withHistory]
        intro same
        have ranks := congrArg Prod.snd same
        change instructionCount program - ProtocolState.commitEnd program state.saved =
          instructionCount program - ProtocolState.remaining program state.saved at ranks
        omega
    · have clean : installed.close = atPoint installed.point installed.excluded
          installed.generation := by
        simp only [close, completed, failed, ↓reduceIte]
      rw [clean]
      simp only [publicAddress, atPoint]
      intro same
      have ranks := congrArg Prod.snd same
      change instructionCount program - ProtocolState.remaining program result.1.1 =
        instructionCount program - ProtocolState.remaining program state.saved at ranks
      omega

end CommitRecoveryState

namespace Setup

variable [Fintype Player] (setup : Setup (Player := Player) (L := L))

/-- The original stopped source runner, for arbitrary behavioral play, is
exactly its remaining commitment instructions, including the real close.
Neither a supplied typed attempt nor an assumed endpoint identifies the stop. -/
theorem commitRecovery_run_until_attempt_exit
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (fuel : Nat) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point) :
    setup.commitRecoveryModel.runBehavioralUntil
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
        (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
          some current.publicAddress.2.2) ⟨some current, trace⟩ =
      setup.commitRecoveryModel.runBehavioralFrom profile fuel ⟨some current, trace⟩ := by
  classical
  induction fuel generalizing current with
  | zero =>
      have frontier := setup.commitRecovery_blockFrontier trace
      have endpoint : ProtocolState.commitEnd setup.program current.point =
          ProtocolState.commitEnd setup.program current.saved := by
        rcases frontier with ⟨_saved, _live, endpoint⟩ | same
        · exact endpoint
        · rw [same]
      have below := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
      omega
  | succ fuel ih =>
      let start : setup.commitRecoveryProtocol.History := ⟨some current, trace⟩
      let stopped : setup.commitRecoveryProtocol.History → Prop := fun history =>
        history.state.map (fun point => point.publicAddress.2.2) ≠
          some current.publicAddress.2.2
      have going : ¬ stopped start := by simp only [stopped, start, Option.map_some, ne_eq,
        not_true_eq_false, not_false_eq_true]
      have running : ¬ setup.commitRecoveryProtocol.terminal start.state := by
        intro terminal
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
          terminal
        have below := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
        omega
      change setup.commitRecoveryModel.runBehavioralUntil
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile stopped start = _
      rw [setup.commitRecoveryModel.runBehavioralUntil_of_running
        setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile going running]
      rw [show fuel + 1 = 1 + fuel by omega,
        setup.commitRecoveryModel.runBehavioralFrom_add]
      apply bind_congr_on_support
      intro next member
      obtain ⟨joint, legal, realized⟩ :=
        (setup.commitRecoveryModel.mem_support_runBehavioralFrom_one profile running member).1
      obtain ⟨target, reached, targetState⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      rcases next with ⟨nextState, nextTrace⟩
      change some target = nextState at targetState
      subst nextState
      rcases current.step_commit_inside_or_exit (setup.commitRecovery_blockFrontier trace)
          committing joint target reached with
        ⟨saved, generation, nextCommit, consumed, _beforeEnd⟩ | ⟨exited, lastSlot⟩
      · have sameKey : target.publicAddress.2.2 = current.publicAddress.2.2 := by
          simp only [CommitRecoveryState.publicAddress, saved, generation]
        have nextDistance : fuel + ProtocolState.commitEnd setup.program target.saved =
            ProtocolState.remaining setup.program target.point := by rw [saved]; omega
        simpa only [stopped, sameKey] using ih target nextTrace nextCommit nextDistance
      · have zeroFuel : fuel = 0 := by omega
        subst fuel
        have halt : stopped ⟨some target, nextTrace⟩ := by
          simpa only [stopped, Option.map_some, ne_eq, Option.some.injEq] using exited
        rw [setup.commitRecoveryModel.runBehavioralUntil_of_stopped
          setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile halt]
        rfl

/-- Every supported original behavioral window retains its actual raw joint
word, numeric public chronology and exact instruction length. The last close
is included, and the window never reads a decision from the next attempt. -/
theorem commitRecovery_run_commit_window_instructions
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (initial : Config Player L setup.context)
    (fuel : Nat) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (within : fuel + ProtocolState.commitEnd setup.program current.saved ≤
      ProtocolState.remaining setup.program current.point)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralFrom profile fuel
      ⟨some current, trace⟩).support) :
    ∃ target joints addresses, final.state = some target ∧ joints.length = fuel ∧
      CommitRecoveryState.InstructionPath setup.program initial joints addresses current target ∧
      final.trace.length = trace.length + fuel ∧
      setup.recoveryJointRecall final.trace = joints.reverse ++ setup.recoveryJointRecall trace ∧
      setup.recoveryAddressWord final.trace = setup.recoveryAddressWord trace ++ addresses := by
  classical
  induction fuel generalizing current final with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact ⟨current, [], [], rfl, rfl, .refl current, rfl,
        rfl, (List.append_nil _).symm⟩
  | succ fuel ih =>
      have running : ¬ setup.commitRecoveryProtocol.terminal (some current) := by
        intro terminal
        have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
          terminal
        have below := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
        omega
      rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile fuel running,
        PMF.mem_support_bind_iff] at supported
      obtain ⟨draw, _drawn, continued⟩ := supported
      rw [PMF.mem_support_bindOnSupport_iff] at continued
      obtain ⟨nextState, realized, child⟩ := continued
      obtain ⟨next, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
      subst nextState
      let nextTrace := trace.extend draw.1 draw.2 realized
      have sourceLegal : (SourceProgram.commitRecoveryProtocol setup.program initial).Legal
          current draw.1 := draw.2
      have sourceReached : next ∈
          ((SourceProgram.commitRecoveryProtocol setup.program initial).step current
            ⟨draw.1, sourceLegal⟩).support := reached
      rcases current.step_commit_inside_or_exit (setup.commitRecovery_blockFrontier trace)
          committing draw.1 next reached with
        ⟨saved, _generation, nextCommit, consumed, _beforeEnd⟩ | ⟨_exited, lastSlot⟩
      · have nextWithin : fuel + ProtocolState.commitEnd setup.program next.saved ≤
            ProtocolState.remaining setup.program next.point := by rw [saved]; omega
        obtain ⟨target, joints, addresses, targetState, length, path, traceLength, word, signals⟩ :=
          ih next nextTrace nextCommit nextWithin final child
        refine ⟨target, draw.1 :: joints, next.publicAddress :: addresses, targetState, ?_,
          .step sourceLegal sourceReached path, ?_, ?_, ?_⟩
        · simp only [List.length_cons, length]
        · simp only [nextTrace, Trace.length] at traceLength
          omega
        · simpa only [List.reverse_cons, nextTrace, recoveryJointRecall,
            List.append_assoc, List.singleton_append] using word
        · simpa only [nextTrace, recoveryAddressWord_extend, Option.elim_some,
            List.append_assoc, List.singleton_append] using signals
      · have zeroFuel : fuel = 0 := by omega
        subst fuel
        cases (PMF.mem_support_pure_iff _ _).mp child
        refine ⟨next, [draw.1], [next.publicAddress], rfl, rfl,
          .step sourceLegal sourceReached (.refl next), ?_, ?_, ?_⟩
        · rfl
        · rfl
        · exact setup.recoveryAddressWord_extend trace draw.1 draw.2 realized

/-- First full-identifier stopping retains the actual complete original raw
window and its public word, with exactly the remaining number of slots. -/
theorem commitRecovery_stopped_attempt_instructions
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (initial : Config Player L setup.context)
    (fuel : Nat) (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (distance : fuel + ProtocolState.commitEnd setup.program current.saved =
      ProtocolState.remaining setup.program current.point)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralUntil
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories profile
      (fun history => history.state.map (fun point => point.publicAddress.2.2) ≠
        some current.publicAddress.2.2) ⟨some current, trace⟩).support) :
    ∃ target joints addresses, final.state = some target ∧ joints.length = fuel ∧
      CommitRecoveryState.InstructionPath setup.program initial joints addresses current target ∧
      final.trace.length = trace.length + fuel ∧
      setup.recoveryJointRecall final.trace = joints.reverse ++ setup.recoveryJointRecall trace ∧
      setup.recoveryAddressWord final.trace = setup.recoveryAddressWord trace ++ addresses := by
  rw [setup.commitRecovery_run_until_attempt_exit profile fuel current trace committing distance]
    at supported
  exact setup.commitRecovery_run_commit_window_instructions profile initial fuel current trace
    committing (Nat.le_of_eq distance) final supported

end Setup
end Vegas.SourceProgram
