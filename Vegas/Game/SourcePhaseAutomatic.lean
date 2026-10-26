/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryOwnedStep
import Vegas.Source.CommitRecoveryCursor
import Vegas.Source.CommitRecoveryAutomaticValues

/-! # Arbitrary-profile source laws for automatic excluded instructions -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- An inherited excluded owner contributes its literal NONE instruction to
the original source history under every behavioral profile. The existing real
install and close are retained; the instruction cannot draw Nature. -/
theorem SourceProgram.Setup.commitRecovery_excluded_owned_step_law
    (setup : Setup (Player := Player) (L := L))
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (excluded : owner ∈ current.excluded)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    {target : setup.commitRecoveryProtocol.State}
    (realized : target ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.commitRecoveryModel.runBehavioralFrom profile 1 ⟨some current, trace⟩ =
      PMF.pure ((⟨some current, trace⟩ : setup.commitRecoveryProtocol.History).extend
        legal realized) := by
  have inactive : ∀ who, ¬ setup.commitRecoveryProtocol.active (some current) who := by
    intro who active
    have same : owner = who := Option.some.inj (acting.symm.trans active.1)
    exact active.2 (same ▸ excluded)
  have jointEq : joint = fun _ => none := by
    funext who
    have offered := legal.2 who
    cases chosen : joint who with
    | none => rfl
    | some move =>
        rw [chosen] at offered
        exact (inactive who offered.1).elim
  obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
  have stepPure : setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
      PMF.pure (some next) := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro final supported
    obtain ⟨other, otherReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact congrArg some (setup.commitRecovery_step_unique_of_actor current owner acting
      joint other next otherReached reached)
  rw [setup.commitRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 legal.1,
    setup.commitRecoveryModel.behavioralJoint_eq_pure_of_no_active profile trace legal.1
      inactive, PMF.pure_bind]
  have sameJoint : (⟨fun _ => none,
      ExecutionProtocol.legal_of_legalOption legal.1 inactive⟩ :
        {draw // setup.commitRecoveryProtocol.Legal (some current) draw}) =
          ⟨joint, legal⟩ := Subtype.ext jointEq.symm
  rw [sameJoint]
  apply pmf_eq_pure_of_support_subset_singleton
  intro final supported
  obtain ⟨actual, actualSupport, landed⟩ :=
    (PMF.mem_support_bindOnSupport_iff _ _).mp supported
  have actualEq : actual = some next := by
    rw [stepPure, PMF.mem_support_pure_iff] at actualSupport
    exact actualSupport
  subst actual
  exact (PMF.mem_support_pure_iff _ _).mp landed

omit [Fintype Player] in
theorem SourceProgram.Setup.commitRecovery_path_controls
    (setup : Setup (Player := Player) (L := L))
    {fuel : Nat} {first last : setup.commitRecoveryProtocol.History}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before : CommitRecoveryState setup.program) (start : first.state = some before) :
    ∃ after, last.state = some after ∧ before.generation ≤ after.generation ∧
      before.excluded ⊆ after.excluded := by
  induction path generalizing before with
  | refl => exact ⟨before, start, le_rfl, Finset.Subset.refl _⟩
  | @step fuel first last joint legal next supported rest ih =>
      rcases first with ⟨state, trace⟩
      change state = some before at start
      subst state
      obtain ⟨middle, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨after, ending, generation, excluded⟩ := ih middle equal.symm
      exact ⟨after, ending, (before.step_generation_mono joint middle reached).trans generation,
        (before.step_excluded_monotone joint middle reached).trans excluded⟩

/-- A genuine source interval consisting of already excluded owned instructions has its
exact original source history as a point mass. Padding in the reachability
budget does not add source instructions. This applies to every profile and
therefore to the original source kernel used after physical settlement. -/
theorem SourceProgram.Setup.commitRecovery_excluded_interval_law
    (setup : Setup (Player := Player) (L := L))
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    {fuel : Nat} {first last : setup.commitRecoveryProtocol.History}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before after : CommitRecoveryState setup.program)
    (start : first.state = some before) (ending : last.state = some after)
    (generation : before.generation = after.generation)
    (exclusions : before.excluded = after.excluded)
    (automatic : ∀ point : SourceProgram.ProtocolState setup.program,
      instructionCount setup.program - ProtocolState.remaining setup.program before.point ≤
        instructionCount setup.program - ProtocolState.remaining setup.program point →
      instructionCount setup.program - ProtocolState.remaining setup.program point <
        instructionCount setup.program - ProtocolState.remaining setup.program after.point →
      ∃ owner ∈ before.excluded, ProtocolState.actor setup.program point = some owner) :
    setup.commitRecoveryModel.runBehavioralFrom profile
      (last.trace.length - first.trace.length) first = PMF.pure last ∧
      (before.entryExcluded = before.excluded → ∀ who, who ∉ before.excluded →
        ProtocolState.BindingsHoldValues who setup.program before.point →
          ProtocolState.BindingsHoldValues who setup.program after.point) := by
  induction path generalizing before with
  | refl =>
      refine ⟨?_, ?_⟩
      · simp only [Nat.sub_self]
        rfl
      · intro _clean who _active live
        have same : before = after := Option.some.inj (start.symm.trans ending)
        exact same ▸ live
  | @step budget first last joint legal next supported rest ih =>
      rcases first with ⟨state, trace⟩
      change state = some before at start
      subst state
      obtain ⟨middle, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      subst next
      obtain ⟨final, finalState, laterGeneration, laterExcluded⟩ :=
        setup.commitRecovery_path_controls rest middle rfl
      have finalEq : final = after := Option.some.inj (finalState.symm.trans ending)
      subst final
      have earlierGeneration := before.step_generation_mono joint middle reached
      have earlierExcluded := before.step_excluded_monotone joint middle reached
      have sameGeneration : before.generation = middle.generation := by omega
      have sameExcluded : before.excluded = middle.excluded :=
        Finset.Subset.antisymm (earlierExcluded) (laterExcluded.trans exclusions.ge)
      have rank := before.step_rank joint middle legal.1 reached
      have consumed : ProtocolState.remaining setup.program middle.point + 1 =
          ProtocolState.remaining setup.program before.point := by rcases rank with h | h <;> omega
      have length := setup.commitRecovery_same_generation_length rest middle after rfl ending
        (sameGeneration.symm.trans generation)
      have leftBound := ProtocolState.remaining_le_instructionCount setup.program before.point
      have rightBound := ProtocolState.remaining_le_instructionCount setup.program after.point
      have traceBound := rest.trace_length_le
      change trace.length + 1 ≤ last.trace.length at traceBound
      change ProtocolState.remaining setup.program after.point + last.trace.length =
        ProtocolState.remaining setup.program middle.point + (trace.length + 1) at length
      obtain ⟨owner, excluded, sourceActor⟩ := automatic before.point le_rfl (by omega)
      have single := setup.commitRecovery_excluded_owned_step_law profile before trace
        owner sourceActor excluded joint legal supported
      have following := ih middle rfl ending (sameGeneration.symm.trans generation)
        (sameExcluded.symm.trans exclusions) (by
          intro later low high
          obtain ⟨who, inactive, actor⟩ := automatic later (by omega) high
          exact ⟨who, sameExcluded ▸ inactive, actor⟩)
      have elapsed : last.trace.length - trace.length =
          1 + (last.trace.length - (trace.length + 1)) := by omega
      constructor
      · rw [elapsed, setup.commitRecoveryModel.runBehavioralFrom_add, single, PMF.pure_bind]
        exact following.1
      · intro clean who active live
        obtain ⟨raw, rawSupport, closed⟩ := before.step_raw_result joint middle reached
        have middleRaw : middle.excluded = raw.val.2 := by
          rw [closed, CommitRecoveryState.close_excluded]
          rfl
        have rawExcluded : raw.val.2 = before.excluded :=
          middleRaw.symm.trans sameExcluded.symm
        have rawLive : ProtocolState.BindingsHoldValues who setup.program raw.val.1 := by
          by_cases committing : ProtocolState.atCommit setup.program before.point = true
          · exact ProtocolState.recoveryStep_excluded_commit_bindingsHoldValues
              setup.program before.point before.excluded joint raw.val who owner
                setup.namesNodup committing sourceActor excluded active live rawSupport
          · have notCommit : ProtocolState.atCommit setup.program before.point = false :=
              Bool.eq_false_iff.mpr committing
            exact ProtocolState.recoveryStep_noncommit_bindingsHoldValues
              setup.program before.point before.excluded joint raw.val who notCommit live rawSupport
        let installed := before.install raw.val raw.property
        have installedClean : installed.excluded = installed.entryExcluded :=
          rawExcluded.trans clean.symm
        have closedLive : ProtocolState.BindingsHoldValues who setup.program middle.point := by
          rw [closed]
          exact ((installed.close_success_readout who).mpr ⟨installedClean, rawLive⟩).2
        have middleClean : middle.entryExcluded = middle.excluded := by
          apply Finset.Subset.antisymm middle.entered
          have earlier : before.entryExcluded ⊆ middle.entryExcluded := by
            rw [closed]
            exact installed.entryExcluded_close
          rw [← sameExcluded, ← clean]
          exact earlier
        exact following.2 middleClean who (sameExcluded ▸ active) closedLive

end Vegas
