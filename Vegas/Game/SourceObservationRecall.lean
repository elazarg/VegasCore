/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceInformation

/-! # Source observation prefixes with private initialization

The existing source prefix decoder extends across the setup chance step. Its
input is the player's current source observation, so it recovers earlier
observations even when two histories have different correlated initial draws.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Depth zero is before initialization; later depths reuse the source's
existing observation-only prefix decoder. Future depths return `none`. -/
def viewAtDepth (who : Player) : Nat → setup.ProtocolView who → Option (setup.ProtocolView who)
  | 0, _ => some none
  | depth + 1, view => view.bind fun observed =>
      (SourceProgram.ProtocolView.atRank who setup.program depth observed).map some

theorem viewAtDepth_current (who : Player) (state : setup.ProtocolState) :
    setup.viewAtDepth who (setup.decisionDepth who (setup.protocolObserve who state))
        (setup.protocolObserve who state) = some (setup.protocolObserve who state) := by
  cases state with
  | none => rfl
  | some state =>
      change (SourceProgram.ProtocolView.atRank who setup.program
        (SourceProgram.ProtocolView.position who setup.program
          (SourceProgram.ProtocolState.observe who setup.program state))
        (SourceProgram.ProtocolState.observe who setup.program state)).map some = _
      rw [SourceProgram.ProtocolView.atRank_position]
      rfl

theorem viewAtDepth_step (who : Player) (before after : setup.ProtocolState)
    (joint : Player → Option (OwnAction Player L))
    (supported : after ∈ (setup.protocolStep before joint).support)
    (depth : Nat) (earlier : depth ≤ setup.decisionDepth who (setup.protocolObserve who before)) :
    setup.viewAtDepth who depth (setup.protocolObserve who after) =
      setup.viewAtDepth who depth (setup.protocolObserve who before) := by
  cases depth with
  | zero => rfl
  | succ depth =>
      cases before with
      | none => change depth + 1 ≤ 0 at earlier; omega
      | some before =>
          obtain ⟨after, reached, rfl⟩ := FinDist.support_map .. ▸ supported
          change (SourceProgram.ProtocolView.atRank who setup.program depth
            (SourceProgram.ProtocolState.observe who setup.program after)).map some =
            (SourceProgram.ProtocolView.atRank who setup.program depth
              (SourceProgram.ProtocolState.observe who setup.program before)).map some
          apply congrArg (Option.map some)
          apply SourceProgram.ProtocolView.atRank_step who setup.program before after joint
            reached depth
          change depth + 1 ≤ SourceProgram.ProtocolView.position who setup.program
            (SourceProgram.ProtocolState.observe who setup.program before) + 1 at earlier
          omega

theorem viewAtDepth_reaches (admission : CommitmentInterface setup.program) (who : Player)
    {fuel : Nat} {before after : (setup.executionProtocol admission).History}
    (reached : (setup.executionProtocol admission).ReachesWithin fuel before after)
    (depth : Nat) (earlier : depth ≤ before.trace.length) :
    setup.viewAtDepth who depth (setup.protocolObserve who after.state) =
      setup.viewAtDepth who depth (setup.protocolObserve who before.state) := by
  induction reached with
  | refl => rfl
  | @step fuel before after joint legal target realized rest ih =>
      have within : depth ≤ (before.extend legal realized).trace.length := by
        simp only [History.extend, Trace.length]
        omega
      refine (ih within).trans ?_
      apply setup.viewAtDepth_step who before.state target joint realized depth
      have clock := setup.decisionDepth_trace admission who before.trace
      change setup.decisionDepth who ((setup.protocolSignals admission).infoOf who before.trace) =
        before.trace.length at clock
      rw [setup.protocol_info] at clock
      rw [clock]
      exact earlier

/-- This uses the actual setup protocol, including its private initialization
chance step, rather than a separately fixed initial source configuration. -/
theorem recover_observation_prefix (admission : CommitmentInterface setup.program) (who : Player)
    {fuel : Nat} {before after : (setup.executionProtocol admission).History}
    (reached : (setup.executionProtocol admission).ReachesWithin fuel before after) :
    setup.viewAtDepth who before.trace.length (setup.protocolObserve who after.state) =
      some (setup.protocolObserve who before.state) := by
  rw [setup.viewAtDepth_reaches admission who reached _ le_rfl]
  have clock := setup.decisionDepth_trace admission who before.trace
  change setup.decisionDepth who ((setup.protocolSignals admission).infoOf who before.trace) =
    before.trace.length at clock
  rw [setup.protocol_info] at clock
  rw [← clock, setup.viewAtDepth_current]

/-- Equal current source information identifies every earlier observation at
matching depths, without identifying or resampling the initial hidden states. -/
theorem observation_prefix_eq (admission : CommitmentInterface setup.program) (who : Player)
    {leftFuel rightFuel : Nat}
    {leftBefore leftAfter rightBefore rightAfter : (setup.executionProtocol admission).History}
    (leftReached : (setup.executionProtocol admission).ReachesWithin
      leftFuel leftBefore leftAfter)
    (rightReached : (setup.executionProtocol admission).ReachesWithin
      rightFuel rightBefore rightAfter)
    (depth : leftBefore.trace.length = rightBefore.trace.length)
    (same : setup.protocolObserve who leftAfter.state =
      setup.protocolObserve who rightAfter.state) :
    setup.protocolObserve who leftBefore.state = setup.protocolObserve who rightBefore.state := by
  have left := setup.recover_observation_prefix admission who leftReached
  have right := setup.recover_observation_prefix admission who rightReached
  rw [depth, same] at left
  exact Option.some.inj (left.symm.trans right)

end Vegas.SourceProgram.Setup
