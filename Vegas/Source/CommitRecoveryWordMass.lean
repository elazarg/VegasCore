/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryMetadata
import Vegas.Source.CommitRecoveryPublicSuccessorMass
import Vegas.Source.CommitRecoveryNonCommitObservation
import Vegas.Source.CommitRecoveryAttemptExit
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Original Nature weights along a common source public word

Commitment transitions are deterministic, including real phase closure.
At samples the public word identifies the draw under its original law.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId}
  {program : SourceProgram Player L Γ O}

theorem step_noncommit_law (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (notCommit : ProtocolState.atCommit program state.point = false)
    (joint : Player → Option (CommitRecoveryMove Player L)) :
    state.step joint =
      (ProtocolState.recoveryStep program state.point state.excluded joint).map
        (fun result => atPoint result.1 result.2 state.generation) := by
  let raw := ProtocolState.recoveryStep program state.point state.excluded joint
  let keep := fun result (supported : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded joint
      result supported
  have saved : ProtocolState.atCommit program state.saved = false := by
    rw [frontier.saved_eq_point_of_not_atCommit notCommit, notCommit]
  change (pmfToSubtype raw keep).map (fun result => (state.install result.1 result.2).close) = _
  calc
    _ = (pmfToSubtype raw keep).map
        (fun result => atPoint result.1.1 result.1.2 state.generation) := by
      apply map_congr_on_support
      intro result _supported
      simp only [close, Finished, install, saved, Bool.false_eq_true, false_and, ↓reduceIte]
    _ = _ := map_pmfToSubtype raw keep
      (fun result : ProtocolState program × Finset Player =>
        atPoint result.1 result.2 state.generation)

private theorem noncommit_atom (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier)
    (notCommit : ProtocolState.atCommit program state.point = false)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player) :
    state.step joint (atPoint result.1 result.2 state.generation) =
      ProtocolState.recoveryStep program state.point state.excluded joint result := by
  rw [state.step_noncommit_law frontier notCommit joint]
  apply pmf_map_apply_of_injective
  intro first second same
  exact Prod.ext (congrArg (fun state => state.point) same)
    (congrArg (fun state => state.excluded) same)

theorem commit_atom (state : CommitRecoveryState program)
    (committing : ProtocolState.atCommit program state.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (target : CommitRecoveryState program) (supported : target ∈ (state.step joint).support) :
    state.step joint target = 1 := by
  apply (PMF.apply_eq_one_iff _ _).mpr
  ext result
  constructor
  · intro member
    exact Set.mem_singleton_iff.mpr
      (state.step_unique_of_commit committing joint result target member supported)
  · intro equal
    rw [Set.mem_singleton_iff] at equal
    subst result
    exact supported

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- Every actual prefix through one commitment attempt has unit Nature
product, including its final clean, retry or exhausted closing row. -/
theorem commitRecovery_commit_interval_mass
    (distance : Nat) (start : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some start))
    (committing : ProtocolState.atCommit setup.program start.point = true)
    (final : setup.commitRecoveryProtocol.History)
    (retained : TracePrefix prior final.trace)
    (length : final.trace.length = prior.length + distance)
    (within : distance + ProtocolState.commitEnd setup.program start.saved ≤
      ProtocolState.remaining setup.program start.point) :
    final.trace.transitionMass = prior.transitionMass := by
  induction distance generalizing start final with
  | zero =>
      have same := retained.eq_of_length (by omega)
      exact (congrArg (fun history : setup.commitRecoveryProtocol.History =>
        history.trace.transitionMass) same).symm
  | succ distance ih =>
      rcases retained.reachesWithin.eq_or_step with same |
        ⟨joint, legal, reached, realized, restFuel, rest⟩
      · have depths := congrArg (fun history : setup.commitRecoveryProtocol.History =>
          history.trace.length) same
        change prior.length = final.trace.length at depths
        omega
      · obtain ⟨next, supported, rfl⟩ := (PMF.mem_support_map_iff ..).mp realized
        have atom : (setup.commitRecoveryProtocol.step (some start) ⟨joint, legal⟩)
            (some next) = 1 := by
          change ((start.step joint).map some) (some next) = 1
          rw [pmf_map_apply_of_injective _ (Option.some_injective _),
            start.commit_atom committing joint next supported]
        have mass : (prior.extend joint legal realized).transitionMass =
            prior.transitionMass := by
          rw [Trace.transitionMass_extend, atom, ENNReal.toReal_one, mul_one]
        rcases start.step_commit_inside_or_exit (setup.commitRecovery_blockFrontier prior)
          committing joint next supported with
          ⟨saved, _generation, nextCommit, consumed, _beforeEnd⟩ | ⟨_changed, last⟩
        · have nextLength : final.trace.length =
              (prior.extend joint legal realized).length + distance := by
            simp only [Trace.length]
            omega
          have nextWithin : distance + ProtocolState.commitEnd setup.program next.saved ≤
              ProtocolState.remaining setup.program next.point := by
            rw [saved]
            omega
          exact (ih next (prior.extend joint legal realized) nextCommit final rest.tracePrefix
            nextLength nextWithin).trans mass
        · have zero : distance = 0 := by omega
          have same := rest.tracePrefix.eq_of_length (by
            simp only [History.extend, Trace.length]
            omega)
          exact (congrArg (fun history : setup.commitRecoveryProtocol.History =>
            history.trace.transitionMass) same).symm.trans mass


/-- At any later source phase, equal complete public words retain the exact
original Nature atom of the actual supported instruction. Hidden values,
accepted-failure bits and entire retired private words may differ. -/
theorem commitRecovery_step_mass_eq_of_public (who : Player)
    (first second : CommitRecoveryState setup.program)
    (firstTrace : setup.commitRecoveryProtocol.Trace (some first))
    (secondTrace : setup.commitRecoveryProtocol.Trace (some second))
    (past : setup.attemptPublicRecall who firstTrace =
      setup.attemptPublicRecall who secondTrace)
    (leftJoint rightJoint : Player → Option (CommitRecoveryMove Player L))
    (leftNext rightNext : CommitRecoveryState setup.program)
    (leftSupport : leftNext ∈ (first.step leftJoint).support)
    (rightSupport : rightNext ∈ (second.step rightJoint).support)
    (next : setup.attemptPublicSignal who (some leftNext) =
      setup.attemptPublicSignal who (some rightNext)) :
    first.step leftJoint leftNext = second.step rightJoint rightNext := by
  have metadata := setup.commitRecovery_metadata_of_publicRecall who firstTrace secondTrace past
  have control := ProtocolState.MetadataEq.controls setup.program
    first.point second.point metadata.1
  by_cases committing : ProtocolState.atCommit setup.program first.point = true
  · have rightCommitting : ProtocolState.atCommit setup.program second.point = true :=
      control.2.1 ▸ committing
    rw [first.commit_atom committing leftJoint leftNext leftSupport,
      second.commit_atom rightCommitting rightJoint rightNext rightSupport]
  · have notCommit : ProtocolState.atCommit setup.program first.point = false :=
      Bool.eq_false_iff.mpr committing
    have rightNotCommit : ProtocolState.atCommit setup.program second.point = false :=
      control.2.1 ▸ notCommit
    obtain ⟨left, leftRaw, rfl⟩ := first.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier firstTrace) notCommit leftJoint leftNext leftSupport
    obtain ⟨right, rightRaw, rfl⟩ := second.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier secondTrace) rightNotCommit rightJoint
        rightNext rightSupport
    have before : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program first.point) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program second.point) := by
      have signal := congrArg List.head? past
      have current : setup.attemptPublicSignal who (some first) =
          setup.attemptPublicSignal who (some second) := by
        simpa only [attemptPublicSignal, attemptPublicRecall, List.map_cons, List.head?_cons,
          setup.commitRecoverySignals_current, Option.some.injEq] using signal
      exact Option.some.inj (congrArg Prod.fst current)
    have after : ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program left.1) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program right.1) :=
      Option.some.inj (congrArg Prod.fst next)
    rw [first.noncommit_atom (setup.commitRecovery_blockFrontier firstTrace) notCommit,
      second.noncommit_atom (setup.commitRecovery_blockFrontier secondTrace) rightNotCommit]
    have mass := ProtocolState.recoveryStep_noncommit_mass_eq who setup.program
      first.point second.point
      before notCommit first.excluded leftJoint rightJoint left leftRaw right
        (by simpa only [metadata.2.2.1] using rightRaw) after
    simpa only [metadata.2.2.1] using mass

end Setup
end Vegas.SourceProgram
