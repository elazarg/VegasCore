/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryCommitStep
import GameTheory.Protocol.History

/-! # Original instruction words along source recovery paths -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

/-- The numeric public address of a genuine recovery state. Saved exclusions
remain a separate state field while a commitment interval is unfinished. -/
def publicAddress {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} (state : CommitRecoveryState whole) :
    Option Nat × (Finset Player × Nat × Nat) :=
  (some (instructionCount whole - ProtocolState.remaining whole state.point),
    state.excluded, state.generation,
      instructionCount whole - ProtocolState.remaining whole state.saved)

/-- Before the last slot, an original commitment path advances one cursor
per instruction while preserving its generation and saved cursor. -/
def IntervalAddresses {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} (state : CommitRecoveryState whole)
    (addresses : List (Option Nat × (Finset Player × Nat × Nat))) : Prop :=
  ∀ index (beforeLast : index + 1 < addresses.length),
    let address := addresses[index]'(by omega)
    address.1 = some (instructionCount whole -
      ProtocolState.remaining whole state.point + index + 1) ∧
      address.2.2.1 = state.generation ∧
      address.2.2.2 = instructionCount whole - ProtocolState.remaining whole state.saved

/-- The numeric invariant composes at the actual unclosed next state. -/
theorem IntervalAddresses.cons {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} (state next : CommitRecoveryState whole)
    (address : Option Nat × (Finset Player × Nat × Nat))
    (addresses : List (Option Nat × (Finset Player × Nat × Nat)))
    (point : instructionCount whole - ProtocolState.remaining whole next.point =
      instructionCount whole - ProtocolState.remaining whole state.point + 1)
    (generation : next.generation = state.generation)
    (saved : ProtocolState.remaining whole next.saved =
      ProtocolState.remaining whole state.saved)
    (head : address.1 = some (instructionCount whole -
        ProtocolState.remaining whole state.point + 1) ∧
      address.2.2.1 = state.generation ∧
      address.2.2.2 = instructionCount whole - ProtocolState.remaining whole state.saved)
    (later : next.IntervalAddresses addresses) :
    state.IntervalAddresses (address :: addresses) := by
  intro index beforeLast
  cases index with
  | zero => simpa only [List.getElem_cons_zero, Nat.add_zero] using head
  | succ index =>
      have bound : index + 1 < addresses.length := by
        simp only [List.length_cons] at beforeLast
        omega
      obtain ⟨rank, gen, kept⟩ := later index bound
      refine ⟨?_, gen.trans generation, ?_⟩
      · rw [point] at rank
        simpa only [List.getElem_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using rank
      · exact kept.trans (congrArg (instructionCount whole - ·) saved)

/-- A realized source path with its original joint instructions retained in
chronological order and one actual post-close public address per instruction.
This refines legal reachability without changing a step or adding a close. -/
inductive InstructionPath {Γ : SourceCtx Player L} {O : Finset VarId}
    (whole : SourceProgram Player L Γ O) (initial : Config Player L Γ) :
    List (Player → Option (CommitRecoveryMove Player L)) →
      List (Option Nat × (Finset Player × Nat × Nat)) →
      CommitRecoveryState whole → CommitRecoveryState whole → Prop where
  | refl (state) : InstructionPath whole initial [] [] state state
  | step {first middle last} {joint rest addresses}
      (legal : (commitRecoveryProtocol whole initial).Legal first joint)
      (supported : middle ∈
        ((commitRecoveryProtocol whole initial).step first ⟨joint, legal⟩).support)
      (later : InstructionPath whole initial rest addresses middle last) :
      InstructionPath whole initial (joint :: rest) (middle.publicAddress :: addresses) first last

/-- Forgetting the retained instruction word gives the existing legal path. -/
theorem InstructionPath.reaches {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} {initial : Config Player L Γ}
    {joints addresses first last}
    (path : InstructionPath whole initial joints addresses first last) :
    (commitRecoveryProtocol whole initial).Reaches first last := by
  induction path with
  | refl => exact .refl _
  | step legal supported later ih => exact Reaches.step ⟨_, legal, supported⟩ ih

/-- Every original instruction has exactly one actual next public signal,
including a retry or exhausted close on its final commitment slot. -/
theorem InstructionPath.addresses_length {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} {initial : Config Player L Γ}
    {joints addresses first last}
    (path : InstructionPath whole initial joints addresses first last) :
    addresses.length = joints.length := by
  induction path with
  | refl => rfl
  | step _ _ _ ih => exact congrArg Nat.succ ih

/-- The final recorded address is the actual endpoint after its real close. -/
theorem InstructionPath.last_address {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L Γ O} {initial : Config Player L Γ}
    {joints addresses first last}
    (path : InstructionPath whole initial joints addresses first last)
    (positive : joints ≠ []) : addresses.getLast? = some last.publicAddress := by
  induction path with
  | refl => exact (positive rfl).elim
  | step _ _ later ih =>
      cases later with
      | refl => rfl
      | step => simpa only [List.getLast?_cons_cons] using ih (List.cons_ne_nil _ _)

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

/-- The exact growing exclusion set after each original slot, before its
possible final close. Accepted failed values do not grow this sequence. -/
def exclusionsAfter : {Γ Δ : SourceCtx Player L} → {O P : Finset VarId} →
    {block : CommitPrefix Γ O Δ P} → {entry : Config Player L Γ} →
    {excluded : Finset Player} → {finished : Config Player L Δ} →
    {after : Finset Player} → block.Attempt entry excluded finished after →
      List (Finset Player)
  | _, _, _, _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, inherited, _, _, .active (owner := owner) _ _ missed _ later =>
      excludeCommit inherited owner missed :: later.exclusionsAfter
  | _, _, _, _, _, _, inherited, _, _, .excluded _ later =>
      inherited :: later.exclusionsAfter

omit [IExpr.ResultTypes L] in
theorem exclusionsAfter_length
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after) :
    attempt.exclusionsAfter.length = block.length := by
  induction attempt with
  | nil => rfl
  | active _ _ _ _ _ ih => exact congrArg Nat.succ ih
  | excluded _ _ ih => exact congrArg Nat.succ ih

omit [IExpr.ResultTypes L] in
/-- A typed prefix which introduces no new excluded owner retains the same
actual exclusion set at every slot, including automatic excluded slots. -/
theorem exclusionsAfter_of_unchanged
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after) :
    after = excluded → attempt.exclusionsAfter = List.replicate block.length excluded := by
  induction attempt with
  | nil => intro _; rfl
  | @active Γ Δ O P name owner payload fresh guard rest entry inherited finished after
      inactive choice missed valid later ih =>
      intro unchanged
      have grows : inherited ⊆ excludeCommit inherited owner missed := by
        cases missed with
        | false => exact Finset.Subset.refl _
        | true => exact Finset.subset_insert _ _
      have same : excludeCommit inherited owner missed = inherited :=
        Finset.Subset.antisymm (unchanged ▸ later.excluded_subset) grows
      have rest := ih (unchanged.trans same.symm)
      simp only [exclusionsAfter, CommitPrefix.length, rest, same, List.replicate_succ]
  | excluded inactive later ih =>
      intro unchanged
      simp only [exclusionsAfter, CommitPrefix.length, ih unchanged, List.replicate_succ]

omit [IExpr.ResultTypes L] in
theorem exclusionsAfter_eq_nil_of_length_zero
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after)
    (zero : block.length = 0) : attempt.exclusionsAfter = [] :=
  List.length_eq_zero_iff.mp (attempt.exclusionsAfter_length.trans zero)

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

omit [IExpr.ResultTypes L] in
/-- A typed commitment attempt retains one original instruction per static slot,
including automatic slots of already excluded owners. -/
theorem joints_length
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId} {block : CommitPrefix Γ O Δ P}
    {entry : Config Player L Γ} {excluded : Finset Player} {finished : Config Player L Δ}
    {after : Finset Player} (attempt : block.Attempt entry excluded finished after) :
    attempt.joints.length = block.length := by
  induction attempt with
  | nil => rfl
  | active _ _ _ _ _ ih =>
      simpa only [joints, List.length_cons, CommitPrefix.length] using congrArg Nat.succ ih
  | excluded _ _ ih =>
      simpa only [joints, List.length_cons, CommitPrefix.length] using congrArg Nat.succ ih

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

/-- The chronological numeric public addresses on the original realized
source trace, using the protocol's existing transition fold. -/
def recoveryAddressWord (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    List (Option Nat × (Finset Player × Nat × Nat)) :=
  letI : Zero (List (Option Nat × (Finset Player × Nat × Nat))) := ⟨[]⟩
  letI : Add (List (Option Nat × (Finset Player × Nat × Nat))) := ⟨List.append⟩
  Trace.valueSum (E := setup.commitRecoveryProtocol)
    (fun event : setup.commitRecoveryProtocol.StepEvent =>
      [event.target.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress]) trace

@[simp] theorem recoveryAddressWord_start (setup : Setup (Player := Player) (L := L)) :
    setup.recoveryAddressWord .start = [] := rfl

@[simp] theorem recoveryAddressWord_extend (setup : Setup (Player := Player) (L := L))
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    setup.recoveryAddressWord (prior.extend joint legal supported) =
      setup.recoveryAddressWord prior ++
        [after.elim (none, (∅, 0, 0)) CommitRecoveryState.publicAddress] := rfl

end Setup
end Vegas.SourceProgram
