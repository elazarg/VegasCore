/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoverySourceCheckpoint
import Vegas.Source.CommitRecoveryInstructions
import GameTheory.Protocol.Backward

/-! # Legal continuation of initialized source recovery traces -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Actual legal source phase paths extend the one initialized setup trace.
The source protocol never redraws the initial private setup. -/
theorem SourceProgram.Setup.recoveryTrace_of_reaches
    (setup : Setup (Player := Player) (L := L))
    (initial : SourceProgram.Config Player L setup.context)
    {first last : CommitRecoveryState setup.program}
    (trace : setup.commitRecoveryProtocol.Trace (some first))
    (reaches : (SourceProgram.commitRecoveryProtocol setup.program initial).Reaches first last) :
    ∃ (next : setup.commitRecoveryProtocol.Trace (some last)) (fuel : Nat),
      setup.commitRecoveryProtocol.ReachesWithin fuel ⟨some first, trace⟩ ⟨some last, next⟩ := by
  induction reaches with
  | refl => exact ⟨trace, 0, .refl 0 _⟩
  | @tail middle last previous step ih =>
      obtain ⟨prior, fuel, priorReached⟩ := ih
      obtain ⟨joint, legal, supported⟩ := step
      have realized : some last ∈
          (setup.commitRecoveryProtocol.step (some middle) ⟨joint, legal⟩).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨last, supported, rfl⟩
      let next := prior.extend joint legal realized
      have one : setup.commitRecoveryProtocol.ReachesWithin 1
          ⟨some middle, prior⟩ ⟨some last, next⟩ :=
        .step joint legal realized (.refl 0 _)
      exact ⟨next, fuel + 1, priorReached.trans one⟩

/-- Extending the actual setup trace along a retained instruction path preserves
its exact original joint word, rather than merely the reachable endpoint. -/
theorem SourceProgram.Setup.recoveryTrace_of_instructions
    (setup : Setup (Player := Player) (L := L))
    (initial : SourceProgram.Config Player L setup.context)
    {first last : CommitRecoveryState setup.program}
    {joints : List (Player → Option (CommitRecoveryMove Player L))}
    (trace : setup.commitRecoveryProtocol.Trace (some first))
    (instructions : CommitRecoveryState.InstructionPath setup.program initial joints first last) :
    ∃ next : setup.commitRecoveryProtocol.Trace (some last),
      setup.commitRecoveryProtocol.ReachesWithin joints.length
        ⟨some first, trace⟩ ⟨some last, next⟩ ∧
      setup.recoveryJointRecall next = joints.reverse ++ setup.recoveryJointRecall trace := by
  induction instructions with
  | refl => exact ⟨trace, .refl 0 _, rfl⟩
  | @step first middle last joint rest legal supported later ih =>
      have realized : some middle ∈
          (setup.commitRecoveryProtocol.step (some first) ⟨joint, legal⟩).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨middle, supported, rfl⟩
      let next := trace.extend joint legal realized
      obtain ⟨finalTrace, path, word⟩ := ih next
      refine ⟨finalTrace, .step joint legal realized path, ?_⟩
      simpa only [SourceProgram.Setup.recoveryJointRecall, next, List.reverse_cons,
        List.append_assoc, List.singleton_append] using word

end Vegas
