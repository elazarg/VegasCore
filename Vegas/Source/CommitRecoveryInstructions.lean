/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryCommitStep
import GameTheory.Protocol.History

/-! # Original instruction words along source recovery paths -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

/-- A realized source path with its original joint instructions retained in
chronological order. This refines legal reachability without changing a step. -/
inductive InstructionPath {Γ : SourceCtx Player L} {O : Finset VarId}
    (whole : SourceProgram Player L Γ O) (initial : Config Player L Γ) :
    List (Player → Option (CommitRecoveryMove Player L)) →
      CommitRecoveryState whole → CommitRecoveryState whole → Prop where
  | refl (state) : InstructionPath whole initial [] state state
  | step {first middle last} {joint rest}
      (legal : (commitRecoveryProtocol whole initial).Legal first joint)
      (supported : middle ∈
        ((commitRecoveryProtocol whole initial).step first ⟨joint, legal⟩).support)
      (later : InstructionPath whole initial rest middle last) :
      InstructionPath whole initial (joint :: rest) first last

/-- Forgetting the retained instruction word gives the existing legal path. -/
theorem InstructionPath.reaches {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} {initial : Config Player L Γ}
    {joints first last} (path : InstructionPath whole initial joints first last) :
    (commitRecoveryProtocol whole initial).Reaches first last := by
  induction path with
  | refl => exact .refl _
  | step legal supported later ih => exact Reaches.step ⟨_, legal, supported⟩ ih

end CommitRecoveryState

namespace CommitPrefix.Attempt

/-- The original instructions of the existing typed attempt, including every
physical omission and automatic excluded-owner slot. -/
def joints : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    {block : CommitPrefix Γ O Δ P} → {entry : Config Player L Γ} →
    {excluded : Finset Player} → {finished : Config Player L Δ} →
    {after : Finset Player} → block.Attempt entry excluded finished after →
      List (Player → Option (CommitRecoveryMove Player L))
  | _, _, _, _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, _, _, _, .active (name := name) (owner := owner)
      (payload := payload) _ choice missed _ later =>
      (fun who => if who = owner then some ⟨.commit owner name payload choice, missed⟩
        else none) :: later.joints
  | _, _, _, _, _, _, _, _, _, .excluded _ later => (fun _ => none) :: later.joints

omit [IExpr.ResultTypes L] in
/-- An empty typed commitment prefix contributes no original instruction. -/
theorem joints_eq_nil_of_length_zero
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (zero : block.length = 0) : attempt.joints = [] := by
  cases attempt with
  | nil => rfl
  | active => simp only [CommitPrefix.length] at zero; omega
  | excluded => simp only [CommitPrefix.length] at zero; omega

omit [IExpr.ResultTypes L] in
/-- Transporting only the final excluded-set index leaves the original
instruction data of a typed attempt unchanged. -/
theorem joints_cast_after
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after next : Finset Player} (same : after = next)
    (attempt : block.Attempt entry excluded finished after) :
    (same ▸ attempt).joints = attempt.joints := by
  cases same
  rfl

end CommitPrefix.Attempt
namespace Setup

/-- The original joint instructions remembered by a genuine initialized source
trace, most recent first. Omission flags are retained before any closure. -/
def recoveryJointRecall (setup : Setup (Player := Player) (L := L)) :
    {state : setup.commitRecoveryProtocol.State} →
      setup.commitRecoveryProtocol.Trace state →
        List (Player → Option (CommitRecoveryMove Player L))
  | _, .start => []
  | _, .extend prior joint _ _ => joint :: setup.recoveryJointRecall prior

end Setup
end Vegas.SourceProgram
