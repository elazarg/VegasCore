/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalInstalledSourceHistory
import Vegas.Game.PhaseProposalSourceUsability
import Vegas.Game.ProposalRecoveryContinuation
import Vegas.Game.ProposalRecoveryResetContinuation
import Vegas.Game.RecoverySourceTerminal
import Vegas.Pending.ReservedEpochCompletion
import Vegas.Compile.EventGraphStep
import Vegas.Source.CommitRecoveryNonCommitJoint
import Vegas.Pending.PhaseEntryExclusion
import Vegas.Game.PhaseProposalActor
import Vegas.Source.CommitRecoveryCursor
import Vegas.Source.CommitRecoveryWordMass
import Vegas.Source.CommitRecoveryOwnedStep
import Vegas.Game.RecoverySurvivingBindingSource
import Vegas.Game.PhaseProposalReplayScan
import Vegas.Game.RecoveryRevealCheckpoint
import Vegas.Game.CompiledRevealBindingRow
import Vegas.Game.ReservedEpochPublicationBoundary
import Vegas.Game.RecoveryCompletedPhaseWitness
import Vegas.Source.CommitRecoveryAutomaticValues

/-! # Ordinary source kernels at fresh physical continuation boundaries -/

noncomputable section

namespace Vegas

open SourceProgram SourceProgram.Setup EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem nonfailure_disclosure_true (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program)
      (action : OwnAction Player L),
      ProtocolView.atCommit who program view = false →
      action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view →
      ¬ action.IsFailure → OwnAction.disclosure (some action) = true := by
  intro Γ O program
  induction program with
  | ret payoffs => intro view action _notCommit offered; cases offered
  | sample name fresh law next ih =>
      intro view action notCommit offered proper
      cases view with
      | inl _ => cases offered
      | inr later => exact ih later action notCommit offered proper
  | commit name owner fresh guard next ih =>
      intro view action notCommit offered proper
      cases view with
      | inl _ => cases notCommit
      | inr later => exact ih later action notCommit offered proper
  | reveal published owner name fresh selected unresolved next ih =>
      intro view action notCommit offered proper
      cases view with
      | inl _ =>
          obtain ⟨bit, rfl⟩ := offered
          cases bit with
          | false => exact (proper rfl).elim
          | true => rfl
      | inr later => exact ih later action notCommit offered proper

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem nonfailure_proposed_false (move : ProposalRecoveryMove Player L)
    (valid : move.Valid) (proper : ¬ move.semantic.action.IsFailure) : move.proposed = false := by
  cases proposed : move.proposed with
  | false => rfl
  | true =>
      obtain ⟨owner, name, withheld⟩ := valid proposed
      exact (proper (by rw [withheld]; rfl)).elim

omit [Fintype Player] in
private theorem noncommit_joint_unique
    (setup : Setup (Player := Player) (L := L))
    (current : CommitRecoveryState setup.program)
    (notCommit : ProtocolState.atCommit setup.program current.point = false)
    (first second : Player → Option (ProposalRecoveryMove Player L))
    (left : setup.proposalRecoveryProtocol.Legal (some current) first)
    (right : setup.proposalRecoveryProtocol.Legal (some current) second)
    (lf : ∀ who move, first who = some move → ¬ move.semantic.action.IsFailure)
    (rf : ∀ who move, second who = some move → ¬ move.semantic.action.IsFailure) :
    first = second := by
  have semantic := ProtocolState.noncommit_legal_joint_eq_of_disclosure setup.program
    current.point current.excluded (proposalRecoveryJoint first) (proposalRecoveryJoint second)
    notCommit (setup.proposalRecovery_erase_legal first left).2
      (setup.proposalRecovery_erase_legal second right).2 (by
        intro who acting surviving
        have leftLegal := left.2 who
        have rightLegal := right.2 who
        cases firstMove : first who with
        | none =>
            rw [firstMove] at leftLegal
            exact (leftLegal ⟨acting, surviving⟩).elim
        | some firstValue =>
            rw [firstMove] at leftLegal
            cases secondMove : second who with
            | none =>
                rw [secondMove] at rightLegal
                exact (rightLegal ⟨acting, surviving⟩).elim
            | some secondValue =>
                rw [secondMove] at rightLegal
                have f := nonfailure_disclosure_true who setup.program
                  (ProtocolState.observe who setup.program current.point) firstValue.semantic.action
                  ((ProtocolState.atCommit_observe setup.program current.point who).trans
                    notCommit)
                    leftLegal.2.1.1 (lf who firstValue firstMove)
                have s := nonfailure_disclosure_true who setup.program
                  (ProtocolState.observe who setup.program current.point)
                  secondValue.semantic.action
                  ((ProtocolState.atCommit_observe setup.program current.point who).trans
                    notCommit)
                    rightLegal.2.1.1 (rf who secondValue secondMove)
                simpa only [proposalRecoveryJoint, firstMove, secondMove, Option.map_some] using
                  f.trans s.symm)
  funext who
  have leftLegal := left.2 who
  have rightLegal := right.2 who
  cases firstMove : first who with
  | none =>
      rw [firstMove] at leftLegal
      cases secondMove : second who with
      | none => rfl
      | some move =>
          rw [secondMove] at rightLegal
          exact (leftLegal rightLegal.1).elim
  | some firstValue =>
      rw [firstMove] at leftLegal
      cases secondMove : second who with
      | none =>
          rw [secondMove] at rightLegal
          exact (rightLegal leftLegal.1).elim
      | some secondValue =>
          rw [secondMove] at rightLegal
          have same := congrFun semantic who
          simp only [proposalRecoveryJoint, firstMove, secondMove, Option.map_some,
            Option.some.injEq] at same
          have firstFlag := nonfailure_proposed_false firstValue leftLegal.2.2
            (lf who firstValue firstMove)
          have secondFlag := nonfailure_proposed_false secondValue rightLegal.2.2
            (rf who secondValue secondMove)
          apply congrArg some
          cases firstValue
          cases secondValue
          simp only [ProposalRecoveryMove.mk.injEq] at same firstFlag secondFlag ⊢
          exact ⟨same, firstFlag.trans secondFlag.symm⟩

/-- At a noncommitment source instruction, every ordinary coordinate is
the same legal nonfailure joint. At a sample this retains the original Nature
kernel; at a disclosure it retains the original guard evaluator and full
history extension. There is no premise identifying a desired transition law. -/
theorem SourceProgram.Setup.proposalRecovery_ordinary_noncommit_local_law
    (setup : Setup (Player := Player) (L := L))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (notCommit : ProtocolState.atCommit setup.program current.point = false)
    (choices : ∀ who, setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (proper : ∀ who move, (choices who).val = some move →
      ¬ move.semantic.action.IsFailure) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩ =
      setup.proposalRecoveryModel.localStep ⟨some current, trace⟩ choices := by
  classical
  let profile := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  by_cases stopped : setup.proposalRecoveryProtocol.terminal (some current)
  · rw [setup.proposalRecoveryModel.runBehavioralFrom_of_terminal profile 1 stopped]
    simp only [InformationModel.localStep, dite_eq_left stopped]
  have legal : setup.proposalRecoveryProtocol.Legal (some current)
      (fun who => (choices who).val) :=
    ExecutionProtocol.legal_of_legalOption stopped fun who =>
      (setup.proposalRecoveryModel.menu_adequate who trace (choices who).val).mp
        (choices who).property
  rw [setup.proposalRecovery_ordinary_run_succ values 0 ⟨some current, trace⟩]
  have zero : setup.proposalRecoveryModel.runBehavioralFrom profile 0 = PMF.pure := rfl
  rw [zero]
  simp only [PMF.bind_pure]
  change (independentProduct (fun who => values who
    (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)))).bind
      (fun draws => setup.proposalRecoveryModel.localStep ⟨some current, trace⟩
        (fun who => (setup.proposalRecoveryComponentChoice who
          (setup.proposalRecoveryModel.infoOf who trace)).symm
            (setup.proposalRecoveryComponentLabelChoice who
              (setup.proposalRecoveryQuery who
                (setup.proposalRecoveryModel.infoOf who trace)) false (draws who).val))) = _
  calc
    _ = (independentProduct (fun who => values who
        (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)))).bind
          (fun _ => setup.proposalRecoveryModel.localStep ⟨some current, trace⟩ choices) := by
      apply bind_congr_on_support
      intro draws _supported
      let actual := fun who => (setup.proposalRecoveryComponentChoice who
        (setup.proposalRecoveryModel.infoOf who trace)).symm
          (setup.proposalRecoveryComponentLabelChoice who
            (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace))
              false (draws who).val)
      have actualLegal : setup.proposalRecoveryProtocol.Legal (some current)
          (fun who => (actual who).val) :=
        ExecutionProtocol.legal_of_legalOption stopped fun who =>
          (setup.proposalRecoveryModel.menu_adequate who trace (actual who).val).mp
            (actual who).property
      have actualProper : ∀ who move, (actual who).val = some move →
          ¬ move.semantic.action.IsFailure := by
        intro who move selected
        change ((draws who).val.val.map (fun semantic =>
          ProposalRecoveryMove.label semantic false)) = some move at selected
        cases chosen : (draws who).val.val with
        | none => simp only [chosen, Option.map_none, reduceCtorEq] at selected
        | some semantic =>
            have equal : ProposalRecoveryMove.label semantic false = move :=
              Option.some.inj (by simpa only [chosen, Option.map_some] using selected)
            subst move
            simpa only [ProposalRecoveryMove.label_semantic] using
              ((draws who).property semantic chosen).2
      have joint := noncommit_joint_unique setup current notCommit
        (fun who => (actual who).val) (fun who => (choices who).val)
          actualLegal legal actualProper proper
      have same : actual = choices := by
        funext who
        exact Subtype.ext (congrFun joint who)
      exact congrArg (setup.proposalRecoveryModel.localStep ⟨some current, trace⟩) same
    _ = _ := PMF.bind_const _ _

omit [Fintype Player] in
private theorem phase_drain_automatic_path {graph : Vegas.EventGraph Player L}
    (phase : RuntimePhase graph) (state : RecoveryState graph) :
    Relation.ReflTransGen RecoveryState.AutomaticStep state (phase.drain state) := by
  apply Relation.ReflTransGen.lift id (fun first last moved => ?_) _ _
    (phase.drain_trace state)
  obtain ⟨event, eligible, rfl⟩ := moved
  exact ⟨event, eligible.2, rfl⟩

omit [DecidableEq Player] [Fintype Player] in
private theorem automatic_path_exclusions {graph : Vegas.EventGraph Player L}
    {first last : RecoveryState graph}
    (path : Relation.ReflTransGen RecoveryState.AutomaticStep first last) :
    last.excluded = first.excluded := by
  induction path with
  | refl => rfl
  | tail previous moved ih =>
      obtain ⟨event, eligible, rfl⟩ := moved
      exact ih

omit [DecidableEq Player] [Fintype Player] in
private theorem automatic_path_new_completed {graph : Vegas.EventGraph Player L}
    {first last : RecoveryState graph}
    (path : Relation.ReflTransGen RecoveryState.AutomaticStep first last)
    (event : graph.EventId) (completed : event ∈ last.native.config.cut.completed)
    (fresh : event ∉ first.native.config.cut.completed) :
    ∃ owner ∈ first.excluded, graph.actor? event = some owner := by
  classical
  induction path with
  | refl => exact (fresh completed).elim
  | @tail middle last prior moved ih =>
      obtain ⟨chosen, eligible, rfl⟩ := moved
      obtain ⟨action, realized⟩ := middle.completeAutomatic_step chosen eligible
      rw [middle.native.config.step_cut chosen eligible.1 action _ realized,
        EventOrder.Cut.mem_complete] at completed
      rcases completed with equal | earlier
      · subst event
        obtain ⟨owner, acting, excluded⟩ := eligible.owned
        exact ⟨owner, (automatic_path_exclusions prior) ▸ excluded, acting⟩
      · exact ih earlier

omit [Fintype Player] in
private theorem fresh_settle_automatic_path {graph : Vegas.EventGraph Player L}
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    let final := PhaseRuntimeState.settle phases generation entry entry retired
    final.generation = generation ∧ final.retired = retired ∧
      Relation.ReflTransGen RecoveryState.AutomaticStep entry final.current := by
  induction phases generalizing entry with
  | nil => exact ⟨rfl, rfl, .refl⟩
  | cons phase remaining ih =>
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain entry).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
        simp only [RuntimePhase.drain_excluded, Finset.sdiff_self, Finset.empty_inter,
          Finset.not_nonempty_empty, and_false, not_false_eq_true]
      simp only [PhaseRuntimeState.settle, noFailure, ↓reduceIte]
      split
      · obtain ⟨generationEq, retiredEq, path⟩ := ih (phase.drain entry)
        exact ⟨generationEq, retiredEq, (phase_drain_automatic_path phase entry).trans path⟩
      · exact ⟨rfl, rfl, phase_drain_automatic_path phase entry⟩

omit [Fintype Player] in
/-- The real settlement from a fresh semantic image adds only inherited-E
owned completions. It preserves generation and retired attempts, introduces no
Nature draw or callback, and may consume several entire strategic phases. -/
theorem phaseProposal_fresh_settle_completion_origin
    {graph : Vegas.EventGraph Player L}
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry : RecoveryState graph) (retired : List (RetiredCommitAttempt graph)) :
    let final := PhaseRuntimeState.settle phases generation entry entry retired
    final.generation = generation ∧ final.retired = retired ∧
      final.current.excluded = entry.excluded ∧
      KeepsStore entry.native final.current.native ∧
      ∀ event ∈ final.current.native.config.cut.completed,
        event ∉ entry.native.config.cut.completed →
          ∃ owner ∈ entry.excluded, graph.actor? event = some owner := by
  intro final
  obtain ⟨generationEq, retiredEq, path⟩ :=
    fresh_settle_automatic_path phases generation entry retired
  have keeps : ∀ {first last : RecoveryState graph},
      Relation.ReflTransGen RecoveryState.AutomaticStep first last →
        KeepsStore first.native last.native := by
    intro first last steps
    induction steps with
    | refl => exact fun _ _ present => present
    | @tail middle last prior moved ih =>
        obtain ⟨event, eligible, rfl⟩ := moved
        obtain ⟨action, supported⟩ := middle.completeAutomatic_step event eligible
        intro field value present
        exact middle.native.config.step_store_of_some _ event eligible.1 action supported field
          value (ih field value present)
  exact ⟨generationEq, retiredEq, automatic_path_exclusions path,
    keeps path,
    fun event completed fresh => automatic_path_new_completed path event completed fresh⟩

/-- An inherited excluded owner contributes its literal NONE instruction to
the full enriched history under every behavioral profile. The existing real
install and close are retained; the instruction cannot draw Nature. -/
theorem SourceProgram.Setup.proposalRecovery_excluded_owned_step_law
    (setup : Setup (Player := Player) (L := L))
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (excluded : owner ∈ current.excluded)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {target : setup.proposalRecoveryProtocol.State}
    (realized : target ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.proposalRecoveryModel.runBehavioralFrom profile 1 ⟨some current, trace⟩ =
      PMF.pure ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
        legal realized) := by
  have inactive : ∀ who, ¬ setup.proposalRecoveryProtocol.active (some current) who := by
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
  have stepPure : setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩ =
      PMF.pure (some next) := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro final supported
    obtain ⟨other, otherReached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact congrArg some (setup.commitRecovery_step_unique_of_actor current owner acting
      (proposalRecoveryJoint joint) other next otherReached reached)
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 legal.1,
    setup.proposalRecoveryModel.behavioralJoint_eq_pure_of_no_active profile trace legal.1
      inactive, PMF.pure_bind]
  have sameJoint : (⟨fun _ => none,
      ExecutionProtocol.legal_of_legalOption legal.1 inactive⟩ :
        {draw // setup.proposalRecoveryProtocol.Legal (some current) draw}) =
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
private theorem source_path_controls
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

/-- A genuine source interval consisting of inherited-E graph ranks has its
exact full archive-lift history as a point mass. Padding in the reachability
budget does not add source instructions. This applies to every profile and
therefore to the ordinary source kernel used after physical settlement. -/
theorem SourceProgram.Setup.proposalRecovery_excluded_interval_law
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {fuel : Nat} {first last : setup.commitRecoveryProtocol.History}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before after : CommitRecoveryState setup.program)
    (start : first.state = some before) (ending : last.state = some after)
    (generation : before.generation = after.generation)
    (exclusions : before.excluded = after.excluded)
    (automatic : ∀ event : (serviceGraph setup mode).EventId,
      instructionCount setup.program - ProtocolState.remaining setup.program before.point ≤
        event.val →
      event.val < instructionCount setup.program -
        ProtocolState.remaining setup.program after.point →
      ∃ owner ∈ before.excluded, (serviceGraph setup mode).actor? event = some owner) :
    setup.proposalRecoveryModel.runBehavioralFrom profile
      (last.trace.length - first.trace.length)
      ⟨first.state, setup.proposalRecoveryLiftTrace labels first.trace⟩ =
        PMF.pure ⟨last.state, setup.proposalRecoveryLiftTrace labels last.trace⟩ ∧
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
        source_path_controls setup rest middle rfl
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
      let event : (serviceGraph setup mode).EventId :=
        ⟨instructionCount setup.program - ProtocolState.remaining setup.program before.point,
          by change _ < eventCount setup.program; rw [eventCount_eq_instructionCount]; omega⟩
      obtain ⟨owner, excluded, acting⟩ := automatic event le_rfl (by dsimp [event]; omega)
      have sourceActor := (source_actor_at_compiled_rank setup.program mode before.point event
        rfl).trans acting
      let step : setup.commitRecoveryProtocol.StepEvent :=
        ⟨some before, joint, legal, some middle, supported⟩
      have single := setup.proposalRecovery_excluded_owned_step_law profile before
        (setup.proposalRecoveryLiftTrace labels trace) owner sourceActor excluded
        (setup.proposalRecoveryLiftJoint labels step)
        (setup.proposalRecoveryLiftJoint_legal labels step) (target := some middle) (by
          change step.target ∈ (setup.proposalRecoveryProtocol.step step.source
            ⟨setup.proposalRecoveryLiftJoint labels step,
              setup.proposalRecoveryLiftJoint_legal labels step⟩).support
          rw [setup.proposalRecoveryLiftJoint_step]; exact supported)
      have following := ih middle rfl ending (sameGeneration.symm.trans generation)
        (sameExcluded.symm.trans exclusions) (by
          intro later low high
          obtain ⟨who, inactive, actor⟩ := automatic later (by omega) high
          exact ⟨who, sameExcluded ▸ inactive, actor⟩)
      have elapsed : last.trace.length - trace.length =
          1 + (last.trace.length - (trace.length + 1)) := by omega
      constructor
      · rw [elapsed, setup.proposalRecoveryModel.runBehavioralFrom_add, single, PMF.pure_bind]
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

omit [DecidableEq Player] [Fintype Player] in
private theorem frontier_complete_below_attempt {graph : Vegas.EventGraph Player L}
    (state : PhaseRuntimeState graph) (frontier : state.Frontier)
    (event : graph.EventId) (below : event.val < state.attempt.phase) :
    event ∈ state.current.native.config.cut.completed := by
  cases phases : state.phases with
  | nil =>
      have savedPrefix := frontier.positioned
      change PhaseRuntimeState.Positioned state.phases state.entry state.current at savedPrefix
      rw [phases] at savedPrefix
      exact (savedPrefix.2 event).mpr event.isLt
  | cons phase remaining =>
      have within := frontier.positioned
      change PhaseRuntimeState.Positioned state.phases state.entry state.current at within
      rw [phases] at within
      apply within.2.1 event
      simpa only [PhaseRuntimeState.attempt, phases, List.head?_cons, Option.map_some,
        Option.getD_some] using below

omit [DecidableEq Player] [Fintype Player] in
private theorem fresh_frontier_saved_prefix {graph : Vegas.EventGraph Player L}
    (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState graph).Frontier) :
    entry.native.config.cut.IsPrefix
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState graph).attempt.phase := by
  cases phases with
  | nil => exact frontier.positioned
  | cons phase remaining => exact frontier.positioned.1

/-- The SAME checkpoint path produced by actual fresh settlement is exactly
the full source continuation under every profile. Real automatic E drains may
cross several phases; no Nature draw, source recall or archive label is erased. -/
theorem RecoverySourceCheckpoint.fresh_normalization_source_law
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (phases : List (RuntimePhase (serviceGraph setup mode))) (generation : Nat)
    (entry : RecoveryState (serviceGraph setup mode))
    (retired : List (RetiredCommitAttempt (serviceGraph setup mode)))
    (checkpoint : RecoverySourceCheckpoint setup mode
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).Frontier)
    (next : RecoverySourceCheckpoint setup mode
      (PhaseRuntimeState.settle phases generation entry entry retired))
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    setup.proposalRecoveryModel.runBehavioralFrom profile
        (next.trace.length - checkpoint.trace.length)
        ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ =
      PMF.pure ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ ∧
      (∀ who, who ∉ entry.excluded → checkpoint.source.BindingsHoldValues who →
        next.source.BindingsHoldValues who) := by
  let state : PhaseRuntimeState (serviceGraph setup mode) :=
    ⟨phases, generation, entry, entry, retired⟩
  let final := PhaseRuntimeState.settle phases generation entry entry retired
  obtain ⟨generationEq, _retiredEq, excludedEq, _stored, completedOrigin⟩ :=
    phaseProposal_fresh_settle_completion_origin phases generation entry retired
  have entryExcluded : final.entry.excluded = entry.excluded :=
    (PhaseRuntimeState.settle_entry_excluded_of_same phases generation entry entry retired
      rfl).trans excludedEq
  have automatic : ∀ event : (serviceGraph setup mode).EventId,
      instructionCount setup.program - ProtocolState.remaining setup.program
        (checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source)) ≤
          event.val →
      event.val < instructionCount setup.program - ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source)) →
      ∃ owner ∈ entry.excluded, (serviceGraph setup mode).actor? event = some owner := by
    intro event low high
    have oldRank := checkpoint.saved_position
    have nextRank := next.saved_position
    rw [oldRank] at low
    rw [nextRank] at high
    have finalFrontier : final.Frontier :=
      PhaseRuntimeState.settle_frontier phases generation entry entry retired frontier
    have completed := frontier_complete_below_attempt final finalFrontier event high
    have absent : event ∉ entry.native.config.cut.completed := by
      intro present
      have savedPrefix := fresh_frontier_saved_prefix phases generation entry retired frontier
      have below := (savedPrefix.2 event).mp present
      omega
    exact completedOrigin event completed absent
  have interval := setup.proposalRecovery_excluded_interval_law mode profile labels path _ _
    rfl rfl generationEq.symm entryExcluded.symm automatic
  refine ⟨interval.1, ?_⟩
  intro who active live
  have beforeLive := (checkpoint.origin.bindingsHoldValues_lift who _).mpr
    ((ProtocolState.bindingsHoldValues_entry who checkpoint.residual.tail checkpoint.source).mpr
      live)
  have afterLive := interval.2 rfl who active beforeLive
  intro name payload cell
  exact (ProtocolState.bindingsHoldValues_entry who next.residual.tail next.source).mp
    ((next.origin.bindingsHoldValues_lift who _).mp afterLive) cell

theorem RecoverySourceCheckpoint.fresh_normalization_terminal_law
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (phases : List (RuntimePhase (serviceGraph setup mode))) (generation : Nat)
    (entry : RecoveryState (serviceGraph setup mode))
    (retired : List (RetiredCommitAttempt (serviceGraph setup mode)))
    (checkpoint : RecoverySourceCheckpoint setup mode
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (frontier : (⟨phases, generation, entry, entry, retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).Frontier)
    (next : RecoverySourceCheckpoint setup mode
      (PhaseRuntimeState.settle phases generation entry entry retired))
    {fuel : Nat}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
        ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ =
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
        ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ := by
  rw [setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralFrom
    certificate profile (next.trace.length - checkpoint.trace.length),
    (checkpoint.fresh_normalization_source_law mode phases generation entry retired frontier next
      path profile labels).1, PMF.pure_bind]

/-- At an actual ordinary owned disclosure the complete enriched source
history is deterministic, including an arbitrary guard rejection and its real
exclusion update. The legal joint is the one retained by the chosen replay. -/
theorem SourceProgram.Setup.proposalRecovery_ordinary_disclosure_step_law
    (setup : Setup (Player := Player) (L := L))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (notCommit : ProtocolState.atCommit setup.program current.point = false)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (proper : ∀ who move, joint who = some move → ¬ move.semantic.action.IsFailure)
    {target : setup.proposalRecoveryProtocol.State}
    (realized : target ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩ =
      PMF.pure ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
        legal realized) := by
  let choices := fun who => (⟨joint who,
    (setup.proposalRecoveryModel.menu_adequate who trace (joint who)).mpr
      (setup.proposalRecoveryProtocol.legalOption_of_legal legal who)⟩ :
        setup.proposalRecoveryModel.Choice who
          (setup.proposalRecoveryModel.infoOf who trace))
  rw [setup.proposalRecovery_ordinary_noncommit_local_law values current trace notCommit
    choices proper, InformationModel.localStep, dite_eq_right legal.1]
  obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
  apply pmf_eq_pure_of_support_subset_singleton
  intro final supported
  obtain ⟨actual, actualSupport, landed⟩ :=
    (PMF.mem_support_bindOnSupport_iff _ _).mp supported
  obtain ⟨other, otherReached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp actualSupport
  have same := setup.commitRecovery_step_unique_of_actor current owner acting
    (proposalRecoveryJoint joint)
    other next otherReached reached
  subst other
  subst actual
  exact (PMF.mem_support_pure_iff _ _).mp landed

/-- A chosen legal disclosure replay with ordinary active moves has exactly
the ordinary full source-history law. This retains every literal past label
and all guard-induced exclusions, without an intended-play hypothesis. -/
theorem SourceProgram.Setup.proposalRecovery_ordinary_disclosure_path_law
    (setup : Setup (Player := Player) (L := L))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    {first last : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace first)
    (trace : setup.commitRecoveryProtocol.Trace last) (kept : TracePrefix prior trace)
    (ordinary : ∀ event ∈ (proposalSourceSteps setup trace).drop prior.length,
      ∃ current : CommitRecoveryState setup.program, event.source = some current ∧
        ProtocolState.atCommit setup.program current.point = false ∧
        (∃ owner, ProtocolState.actor setup.program current.point = some owner) ∧
        ∀ who move, event.joint who = some move → ¬ move.action.IsFailure) :
    setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        (trace.length - prior.length) ⟨first, setup.proposalRecoveryLiftTrace labels prior⟩ =
      PMF.pure ⟨last, setup.proposalRecoveryLiftTrace labels trace⟩ := by
  induction kept with
  | refl => simp only [Nat.sub_self]; rfl
  | @extend before after earlier kept joint legal realized ih =>
      let event : setup.commitRecoveryProtocol.StepEvent := ⟨before, joint, legal, after, realized⟩
      have bound : prior.length ≤ (proposalSourceSteps setup earlier).length := by
        rw [proposalSourceSteps_length]
        exact kept.length_le
      have suffix : (proposalSourceSteps setup (earlier.extend joint legal realized)).drop
          prior.length = (proposalSourceSteps setup earlier).drop prior.length ++ [event] := by
        rw [proposalSourceSteps_extend, List.drop_append_of_le_length bound]
      have previous := ih (by
        intro row member
        apply ordinary row
        rw [suffix]
        exact List.mem_append_left _ member)
      obtain ⟨current, source, notCommit, ⟨owner, acting⟩, proper⟩ := ordinary event (by
        rw [suffix]
        exact List.mem_append_right _ (List.mem_singleton_self event))
      change before = some current at source
      subst before
      have liftedProper : ∀ who move, setup.proposalRecoveryLiftJoint labels event who =
          some move → ¬ move.semantic.action.IsFailure := by
        intro who move selected
        change ((joint who).map fun move =>
          ProposalRecoveryMove.label move (labels event who)) = some move at selected
        cases chosen : joint who with
        | none => simp only [chosen, Option.map_none, reduceCtorEq] at selected
        | some raw =>
            have same : ProposalRecoveryMove.label raw (labels event who) = move :=
              Option.some.inj (by simpa only [chosen, Option.map_some] using selected)
            subst move
            simpa only [ProposalRecoveryMove.label_semantic] using proper who raw chosen
      have single := setup.proposalRecovery_ordinary_disclosure_step_law values current
        (setup.proposalRecoveryLiftTrace labels earlier) owner acting notCommit
        (setup.proposalRecoveryLiftJoint labels event)
        (setup.proposalRecoveryLiftJoint_legal labels event) liftedProper (target := after) (by
          change event.target ∈ (setup.proposalRecoveryProtocol.step event.source
            ⟨setup.proposalRecoveryLiftJoint labels event,
              setup.proposalRecoveryLiftJoint_legal labels event⟩).support
          rw [setup.proposalRecoveryLiftJoint_step]
          exact realized)
      have elapsed : (earlier.extend joint legal realized).length - prior.length =
          (earlier.length - prior.length) + 1 := by
        have lengths := kept.length_le
        change earlier.length + 1 - prior.length = _
        omega
      rw [elapsed, setup.proposalRecoveryModel.runBehavioralFrom_add, previous, PMF.pure_bind]
      exact single

/-- The actual native sample command and the ordinary enriched source
instruction share the original expression draw at the SAME typed source
cursor. Runtime activation metadata and the source's real close are retained. -/
theorem phaseProposal_ordinary_sample_coupling
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (suffix : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (lift : ProtocolState (.sample name fresh law suffix) → ProtocolState setup.program)
    (origin : ProtocolSuffix setup.program (.sample name fresh law suffix) lift)
    (source : SourceProgram.Config Player L Γ)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (point : current.point = lift (.inl source))
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (agrees : refs.Agrees source.state native.config.store)
    (event : (serviceGraph setup mode).EventId) (ready : native.config.cut.Ready event)
    (output : (serviceGraph setup mode).outputLayout event = .publicData payload)
    (code : cast (congrArg (EventCode (graphLayout setup.program)) output)
      ((serviceGraph setup mode).nodes event) = .sample payload (compilePublicDist refs law))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History ×
        EventGraphRuntime.State (serviceGraph setup mode)),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩ ∧
      joint.map Prod.snd = environmentStep runtime native (.executeSample event) ∧
      ∀ pair ∈ joint.support, ∃ value ∈ (L.evalDist law (sourcePublicEnv source.state)).support,
        pair.1.state = some (CommitRecoveryState.atPoint
          (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
          current.excluded current.generation) ∧
        TracePrefix trace pair.1.trace ∧
        pair.2 = native.complete event ready
          (cast (congrArg EventField.Action output.symm) PUnit.unit)
          (cast (congrArg EventField.Value output.symm) value) := by
  let profile := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  let history : setup.proposalRecoveryProtocol.History := ⟨some current, trace⟩
  let draw := L.evalDist law (sourcePublicEnv source.state)
  let successor := fun value => some (CommitRecoveryState.atPoint
    (lift (.inr (ProtocolState.entry suffix (sampleSuccessor name source value))))
      current.excluded current.generation)
  have actor : ProtocolState.actor setup.program current.point = none := by
    rw [point, origin.actor_lift]
    rfl
  have notCommit : ProtocolState.atCommit setup.program current.point = false := by
    rw [point, origin.atCommit_lift]
    rfl
  have running : ¬ setup.proposalRecoveryProtocol.terminal (some current) := by
    intro stopped
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
      stopped
    rw [point, origin.remaining_lift] at zero
    change instructionCount suffix + 1 = 0 at zero
    omega
  have inactive : ∀ who, ¬ setup.proposalRecoveryProtocol.active (some current) who := by
    intro who active
    change ProtocolState.actor setup.program current.point = some who ∧
      who ∉ current.excluded at active
    rw [actor] at active
    cases active.1
  let legal : setup.proposalRecoveryProtocol.Legal (some current) (fun _ => none) :=
    ExecutionProtocol.legal_of_legalOption running inactive
  have sourceStep : setup.proposalRecoveryProtocol.step (some current)
      ⟨fun _ => none, legal⟩ = draw.map successor := by
    change (current.step (proposalRecoveryJoint (fun _ => none))).map some = _
    rw [current.step_noncommit_law
      (setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace trace)) notCommit,
      point, origin.recoveryStep_lift]
    simp only [ProtocolState.recoveryStep, Sum.elim_inl, PMF.map_comp, Function.comp_def]
    rfl
  let sourceImage : ∀ value ∈ draw.support, setup.proposalRecoveryProtocol.History :=
    fun value supported => history.extend legal (by
      rw [sourceStep]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨value, supported, rfl⟩)
  let nativeImage := fun value => native.complete event ready
    (cast (congrArg EventField.Action output.symm) PUnit.unit)
    (cast (congrArg EventField.Value output.symm) value)
  let joint := draw.bindOnSupport fun value supported =>
    PMF.pure (sourceImage value supported, nativeImage value)
  have sourceLaw : setup.proposalRecoveryModel.runBehavioralFrom profile 1 history =
      draw.bindOnSupport (fun value supported => PMF.pure (sourceImage value supported)) := by
    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 running,
      setup.proposalRecoveryModel.behavioralJoint_eq_pure_of_no_active profile trace running
        inactive, PMF.pure_bind]
    change (setup.proposalRecoveryProtocol.step (some current)
      ⟨fun _ => none, legal⟩).bindOnSupport
        (fun target supported => PMF.pure (history.extend legal supported)) = _
    calc
      _ = (draw.map successor).bindOnSupport (fun target supported => PMF.pure
          (history.extend legal (by rw [sourceStep]; exact supported))) := by
        apply bindOnSupport_congr_measure sourceStep
        intro target first second
        rfl
      _ = _ := by rw [bindOnSupport_map]
  have nativeLaw : environmentStep runtime native (.executeSample event) = draw.map nativeImage :=
    by
      rw [environmentStep_executeSample_eq runtime native event ready payload
        (compilePublicDist refs law) output code (nodeView_eq_sample output code),
        sample_step native.config event ready output refs law code source.state agrees,
        PMF.map_comp]
      rfl
  refine ⟨joint, ?_, ?_, ?_⟩
  · change (draw.bindOnSupport _).map Prod.fst = _
    rw [map_bindOnSupport]
    simpa only [PMF.pure_map] using sourceLaw.symm
  · change (draw.bindOnSupport _).map Prod.snd = _
    rw [map_bindOnSupport, nativeLaw]
    simp only [PMF.pure_map]
    rw [PMF.bindOnSupport_eq_bind]
    exact PMF.bind_pure_comp _ _
  · intro pair supported
    obtain ⟨value, member, landed⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp supported
    cases (PMF.mem_support_pure_iff _ _).mp landed
    exact ⟨value, member, rfl, .extend .refl _ _ _, rfl⟩

/-- Actual normalization of a constructed fresh witness retains its SAME
selected full source history and every archive field needed by continuation. -/
theorem RecoverySourceWitness.fresh_normalized_terminal_law
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phases : List (RuntimePhase (serviceGraph setup mode))) (generation : Nat)
    (entry : RecoveryState (serviceGraph setup mode))
    (retired : List (RetiredCommitAttempt (serviceGraph setup mode)))
    (witness : RecoverySourceWitness setup mode plan
      (⟨phases, generation, entry, entry, retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    (certificate : setup.proposalRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ next : RecoverySourceWitness setup mode plan
        (PhaseRuntimeState.settle phases generation entry entry retired),
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) ∧
      setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
          ⟨_, setup.proposalRecoveryLiftTrace labels witness.checkpoint.trace⟩ =
        setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate profile
          ⟨_, setup.proposalRecoveryLiftTrace labels next.checkpoint.trace⟩ ∧
      witness.checkpoint.ProposalDelta plan next.checkpoint := by
  let state : PhaseRuntimeState (serviceGraph setup mode) :=
    ⟨phases, generation, entry, entry, retired⟩
  obtain ⟨inputs, native⟩ := witness.native
  obtain ⟨checkpoint, aligned, chronology, fuel, path, origins, delta⟩ :=
    witness.checkpoint.normalized_archived state plan witness.suffix witness.chronology
      witness.exclusions witness.failures witness.aligned witness.origins witness.archives native
        witness.binding witness.receipts witness.stored witness.remembered witness.order maximal
  let next : RecoverySourceWitness setup mode plan state.normalize := {
    checkpoint := checkpoint
    aligned := aligned
    chronology := chronology
    origins := origins
    native := ⟨inputs, PhaseRuntimeState.settle_invariant phases generation entry entry retired
      native.saved native.active⟩
    binding := PhaseRuntimeState.settle_bindingRecord phases generation entry entry retired
      witness.binding.saved witness.binding.active witness.binding.fixed
    receipts := PhaseRuntimeState.settle_receiptRecord phases generation entry entry retired
      witness.receipts
    stored := PhaseRuntimeState.settle_storedCheckpoint phases generation entry entry retired
      witness.stored
    remembered := PhaseRuntimeState.settle_historyCheckpoint phases generation entry entry retired
      witness.remembered
    order := PhaseRuntimeState.settle_publicFailureOrder
      (serviceGraph_revealRelaxedOrdered setup mode) phases generation entry entry retired
        witness.order
    suffix := (PhaseRuntimeState.settle_suffix phases generation entry entry retired).trans
      witness.suffix
    archives := PhaseRuntimeState.settle_archivesBefore phases generation entry entry retired
      witness.order.frontier.adjacent witness.archives
    exclusions := PhaseRuntimeState.settle_archivedExclusions phases generation entry entry retired
      witness.exclusions
    failures := PhaseRuntimeState.settle_publicFailureCheckpoint phases generation entry entry
      retired witness.failures }
  refine ⟨next, ⟨fuel, path⟩, ?_, delta⟩
  exact witness.checkpoint.fresh_normalization_terminal_law mode phases generation entry retired
    witness.order.frontier checkpoint path certificate profile labels

/-- Every exact canonical publication replay with TRUE active rows has its
full ordinary source-history law, including arbitrary rejecting guards. -/
theorem RecoverySourceCheckpoint.ordinary_reveal_replay_law
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (exclusion : state.ExclusionRecord) (savedFailures : state.PublicFailureCheckpoint)
    (coverage : state.FailureCoverage)
    (truth : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner → owner ∉ state.entry.excluded →
      owner ∉ (phase.drain state.current).native.failureOwnersBefore event.val →
      ∀ (payload : L.Ty) (publication : (serviceGraph setup mode).outputLayout event =
        .publication payload) (action : ((serviceGraph setup mode).outputLayout event).Action),
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        (phase.drain state.current).native.config.history →
      cast (congrArg EventField.Action publication) action = true)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool)
    (next : RecoverySourceCheckpoint setup mode
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)))
    {fuel : Nat} (path : setup.commitRecoveryProtocol.ReachesWithin fuel
      ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩)
    (replay : NativeSourceReplayExtension setup (phase.drain state.current).native state.generation
      checkpoint.trace next.trace) :
      setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        (phase.high - phase.low) ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ =
          PMF.pure ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ := by
  let image := phase.drain state.current
  classical
  have low : phase.low = state.attempt.phase := by
    simp only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some]
  have nextOffset : (⟨remaining, state.generation, image, image, state.retired⟩ :
      PhaseRuntimeState (serviceGraph setup mode)).attempt.phase = phase.high := by
    have adjacent := exclusion.frontier.adjacent
    have last := exclusion.frontier.last
    rw [installed] at adjacent last
    cases remaining with
    | nil =>
        have endEq := last phase (by simp only [List.getLast?_singleton, Option.mem_some_iff])
        exact endEq.symm
    | cons following rest =>
        exact (adjacent.rel_head? (y := following) (by simp)).symm
  have firstRank := checkpoint.saved_position
  have lastRank := next.saved_position
  rw [← low] at firstRank
  rw [nextOffset] at lastRank
  have counted := setup.commitRecovery_same_generation_length path _ _ rfl rfl rfl
  have firstBound := ProtocolState.remaining_le_instructionCount setup.program
    (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail checkpoint.source))
  have lastBound := ProtocolState.remaining_le_instructionCount setup.program
    (next.residual.lift (ProtocolState.entry next.residual.tail next.source))
  have elapsed : next.trace.length - checkpoint.trace.length = phase.high - phase.low := by
    change ProtocolState.remaining setup.program
        (next.residual.lift (ProtocolState.entry next.residual.tail next.source)) +
        next.trace.length = ProtocolState.remaining setup.program
        (checkpoint.residual.lift (ProtocolState.entry checkpoint.residual.tail
          checkpoint.source)) +
        checkpoint.trace.length at counted
    omega
  rw [← elapsed]
  apply setup.proposalRecovery_ordinary_disclosure_path_law values labels checkpoint.trace
    next.trace path.tracePrefix
  obtain ⟨events, points, chain, head, word, annotated, length, cursors⟩ := replay
  have newSteps : (proposalSourceSteps setup next.trace).drop checkpoint.trace.length =
      events := by
    rw [word, ← proposalSourceSteps_length setup checkpoint.trace, List.drop_left]
  have position := exclusion.frontier.positioned
  rw [installed] at position
  have extension := savedFailures.trans (phase.drain_publicFailureExtension state.current)
  have oldSubset : image.native.failureOwnersBefore phase.low ⊆ state.entry.excluded := by
    intro owner member
    obtain ⟨event, earlier, acting, failed⟩ := (Finset.mem_filter.mp member).2
    exact coverage.saved.covered event owner acting
      ((extension.failures event ((position.1.2 event).mpr earlier)).mp failed)
  cases points with
  | nil => cases head
  | cons start later =>
      have initialEq := Option.some.inj head
      have startPoint := congrArg CommitRecoveryState.point initialEq
      have startExcluded := congrArg CommitRecoveryState.excluded initialEq
      have initialScan : start.2 = state.entry.excluded ∪ image.native.failureOwnersBefore
          (instructionCount setup.program - ProtocolState.remaining setup.program start.1) := by
        change start.1 = checkpoint.residual.lift
          (ProtocolState.entry checkpoint.residual.tail checkpoint.source) at startPoint
        change start.2 = state.entry.excluded at startExcluded
        rw [startPoint, startExcluded, firstRank, Finset.union_eq_left.mpr oldSubset]
      intro event member
      rw [newSteps] at member
      obtain ⟨first, last, source, _target, moved, disclosure, firstMember⟩ :=
        annotated event member
      obtain ⟨index, bound, selected⟩ := List.mem_iff_getElem.mp member
      have cursor := cursors index bound
      rw [selected, source] at cursor
      simp only [Option.map_some, CommitRecoveryState.atPoint] at cursor
      have rank := Option.some.inj cursor
      have lower : phase.low ≤ instructionCount setup.program -
          ProtocolState.remaining setup.program first.1 := by omega
      have upper : instructionCount setup.program -
          ProtocolState.remaining setup.program first.1 < phase.high := by omega
      let nativeEvent : (serviceGraph setup mode).EventId :=
        ⟨instructionCount setup.program - ProtocolState.remaining setup.program first.1,
          upper.trans_le phase.bounded⟩
      have inside : nativeEvent ∈ phase.events :=
        (phase.mem_events nativeEvent).mpr ⟨lower, upper⟩
      have scan := native_public_path_point_scan setup mode image.native state.entry.excluded
        start later chain initialScan first firstMember
      have actorSome : ∃ owner, (serviceGraph setup mode).actor? nativeEvent = some owner := by
        cases acting : (serviceGraph setup mode).actor? nativeEvent with
        | some owner => exact ⟨owner, rfl⟩
        | none =>
            have nonpublication := EventCode.not_publication_of_actor_none
              ((serviceGraph setup mode).nodes nativeEvent) acting
            obtain ⟨payload, publication⟩ := kind ▸ phase.fields nativeEvent lower upper
            rw [publication] at nonpublication
            exact (nonpublication True.intro).elim
      obtain ⟨owner, acting⟩ := actorSome
      refine ⟨CommitRecoveryState.atPoint first.1 first.2 state.generation, source,
        moved.1.2.1, ⟨owner, (source_actor_at_compiled_rank setup.program mode first.1 nativeEvent
          rfl).trans acting⟩, ?_⟩
      intro who move selectedMove
      have legal := event.isLegal
      rw [source] at legal
      have offered := legal.2 who
      rw [selectedMove] at offered
      have sourceActor : ProtocolState.actor setup.program first.1 = some who := offered.1.1
      have sourceActive : who ∉ first.2 := offered.1.2
      have inherited : who ∉ state.entry.excluded := by
        rw [scan] at sourceActive
        exact fun absent => sourceActive (Finset.mem_union_left _ absent)
      have beforeFailure : who ∉ image.native.failureOwnersBefore nativeEvent.val := by
        rw [scan] at sourceActive
        exact fun absent => sourceActive (Finset.mem_union_right _ absent)
      obtain ⟨recordedEvent, payload, publication, action, ranked, recorded, bit⟩ :=
        disclosure who sourceActor sourceActive
      have eventEq : recordedEvent = nativeEvent := Fin.ext (by simpa only [Nat.zero_add] using
        ranked)
      subst recordedEvent
      have graphActor : (serviceGraph setup mode).actor? nativeEvent = some who :=
        (source_actor_at_compiled_rank setup.program mode first.1 nativeEvent rfl).symm.trans
          sourceActor
      have actual := truth nativeEvent inside who graphActor inherited beforeFailure payload
        publication action recorded
      have disclosed := bit.symm.trans actual
      rw [selectedMove] at disclosed
      obtain ⟨name, revealBit, equal⟩ := ProtocolState.recoveryAvailable_reveal_of_not_commit who
        setup.program first.1 sourceActor moved.1.2.1 move offered.2
      subst move
      cases revealBit with
      | false => cases disclosed
      | true => intro failure; cases failure

/-- The actual completed publication image supplies its SAME checkpoint and
the full ordinary source-history law when each active recorded row is TRUE.
Guard failure is retained by the original evaluator and native failure scan. -/
theorem RecoverySourceCheckpoint.ordinary_completed_reveal_law
    {setup : Setup (Player := Player) (L := L)} (mode : ExecutionMode)
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (checkpoint : RecoverySourceCheckpoint setup mode state)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (exclusion : state.ExclusionRecord) (stored : state.StoredCheckpoint)
    (remembered : state.HistoryCheckpoint) (savedFailures : state.PublicFailureCheckpoint)
    (coverage : state.FailureCoverage)
    {inputs : (serviceGraph setup mode).Inputs}
    (reachable : (phase.drain state.current).native.config.Reachable inputs)
    (ordered : (phase.drain state.current).OrderedPublicFailures phase.low state.entry.excluded)
    (finished : phase.Finished (phase.drain state.current))
    (truth : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner → owner ∉ state.entry.excluded →
      owner ∉ (phase.drain state.current).native.failureOwnersBefore event.val →
      ∀ (payload : L.Ty) (publication : (serviceGraph setup mode).outputLayout event =
        .publication payload) (action : ((serviceGraph setup mode).outputLayout event).Action),
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        (phase.drain state.current).native.config.history →
      cast (congrArg EventField.Action publication) action = true)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ next : RecoverySourceCheckpoint setup mode
        (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
          state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)),
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
      setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        (phase.high - phase.low) ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ =
          PMF.pure ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ := by
  obtain ⟨next, ⟨fuel, path⟩, _publicPath, _addresses, _history, _intended, replay⟩ :=
    checkpoint.after_reveal phase remaining installed kind exclusion stored remembered reachable
      ordered finished
  exact ⟨next, ⟨fuel, path⟩, checkpoint.ordinary_reveal_replay_law mode phase remaining installed
    kind exclusion savedFailures coverage truth values labels next path replay⟩

/-- The same chosen publication replay carries the full witness required by
the next phase, rather than an independently selected endpoint checkpoint. -/
theorem RecoverySourceWitness.ordinary_completed_reveal_history
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    {plan : RuntimePhasePlan (serviceGraph setup mode)}
    {state : PhaseRuntimeState (serviceGraph setup mode)}
    (witness : RecoverySourceWitness setup mode plan state)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : state.phases = phase :: remaining) (kind : phase.kind = .reveal)
    (finished : phase.Finished (phase.drain state.current))
    (truth : ∀ event ∈ phase.events, ∀ owner,
      (serviceGraph setup mode).actor? event = some owner → owner ∉ state.entry.excluded →
      owner ∉ (phase.drain state.current).native.failureOwnersBefore event.val →
      ∀ (payload : L.Ty) (publication : (serviceGraph setup mode).outputLayout event =
        .publication payload) (action : ((serviceGraph setup mode).outputLayout event).Action),
      (⟨event, action⟩ : (serviceGraph setup mode).Completion) ∈
        (phase.drain state.current).native.config.history →
      cast (congrArg EventField.Action publication) action = true)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    ∃ next : RecoverySourceWitness setup mode plan
      (⟨remaining, state.generation, phase.drain state.current, phase.drain state.current,
        state.retired⟩ : PhaseRuntimeState (serviceGraph setup mode)),
      (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
        ⟨_, witness.checkpoint.trace⟩ ⟨_, next.checkpoint.trace⟩) ∧
      Relation.ReflTransGen
        (NativePublicSourceStep (phase.drain state.current).native 0 setup.program)
        (witness.checkpoint.residual.lift
          (ProtocolState.entry witness.checkpoint.residual.tail witness.checkpoint.source),
          state.entry.excluded)
        (next.checkpoint.residual.lift
          (ProtocolState.entry next.checkpoint.residual.tail next.checkpoint.source),
          (phase.drain state.current).excluded) ∧
      setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        (phase.high - phase.low)
        ⟨_, setup.proposalRecoveryLiftTrace labels witness.checkpoint.trace⟩ =
          PMF.pure ⟨_, setup.proposalRecoveryLiftTrace labels next.checkpoint.trace⟩ ∧
      witness.checkpoint.ProposalDelta plan next.checkpoint := by
  have member : phase ∈ state.phases.head? := by simp only [installed, List.head?_cons]; rfl
  have planMember : phase ∈ plan.phases := witness.suffix.subset (by
    rw [installed]
    exact List.mem_cons_self)
  obtain ⟨inputs, native⟩ := witness.native
  have imageNative := phase.drain_invariant state.current native.active
  have graphOrder := serviceGraph_revealRelaxedOrdered setup mode
  have imageOrder := phase.orderedPublicFailures_drain phase.low state.entry.excluded state.current
    (witness.order.publicationOrder phase member) witness.order.coverage.active
      witness.order.coverage.inherited graphOrder
  obtain ⟨next, ⟨fuel, path⟩, publicSteps, publicAddresses, word, _intended, replay⟩ :=
    witness.checkpoint.after_reveal phase remaining installed kind witness.receipts.exclusion
      witness.stored witness.remembered imageNative.reachable imageOrder finished
  have law := witness.checkpoint.ordinary_reveal_replay_law mode phase remaining installed kind
    witness.receipts.exclusion witness.failures witness.order.coverage truth values labels next
      path replay
  obtain ⟨aligned, chronology, origins, delta⟩ :=
    witness.checkpoint.public_phase_archive plan maximal phase remaining installed planMember
      (by simp only [kind]; decide) witness.aligned witness.chronology witness.origins
        witness.exclusions witness.failures witness.archives witness.receipts witness.stored
          witness.remembered witness.order ⟨inputs, imageNative⟩ finished next path publicSteps
            publicAddresses word replay
  let nextWitness := witness.completed_phase_checkpoint phase remaining installed finished next
    aligned chronology origins
  exact ⟨nextWitness, ⟨fuel, path⟩, publicSteps, law, delta⟩

section FreshPublication

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" =>
  PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw)

/-- Proper surviving bindings and a genuinely fresh callback namespace force
every source-active recorded publication action to be TRUE. A ready request
at the anchor is allowed; the contradiction uses an actual remembered response. -/
theorem phaseProposalUnflagged_fresh_publication_rows
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor⟩))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.application)
    (stored : anchor.application.StoredCheckpoint)
    (proper : ∀ who, who ∉ anchor.application.current.excluded →
      checkpoint.source.BindingsHoldValues who)
    (fresh : ∀ who, ∀ entry ∈ anchor.recall who,
      entry.beforeView.application.2.attempt ≠ anchor.application.attempt)
    (closing ending : (app).Control)
    (closingTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some closing))
    (joint : Player → Option (app).Action)
    (legal : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some closing) joint)
    (realized : some ending ∈ ((app).transition initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some closing) joint).support)
    (fromStart : TracePrefix trace closingTrace)
    (same : closing.execution.application.attempt = anchor.application.attempt)
    (changed : ending.execution.application.attempt ≠ anchor.application.attempt)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (coverage : (phase.drain raw).FailureCoverage)
    (excludedEq : (phase.drain raw).excluded = ending.execution.application.current.excluded) :
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let model := (menu).information initial horizon scheduler
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (model.runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      final.state = some ending →
      TracePrefix (closingTrace.extend joint legal realized) final.trace →
      ∀ event ∈ phase.events, ∀ owner, (graph).actor? event = some owner →
        owner ∉ anchor.application.current.excluded →
        owner ∉ (phase.drain raw).native.failureOwnersBefore event.val →
      ∀ action : ((graph).outputLayout event).Action,
        (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain raw).native.config.history →
          PhaseProposal.publicationDiscloses ((graph).outputLayout event) action = true := by
  intro horizon scheduler players profile model stopped final supported finalState closedKept
    event inside owner acting active scan action recorded
  obtain ⟨payload, name, selected, checks, output, code, value, locked⟩ :=
    checkpoint.publication_binding_row setup mode phase installed kind stored event inside owner
      acting (proper owner active)
  have noOld : ¬ (anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ ∧
      PhaseCount.ResponseRecorded runtime leaks owner ⟨anchor.application.attempt, event⟩
        (anchor.recall owner)) := by
    rintro ⟨_request, entry, member, requested⟩
    exact fresh owner entry member requested.1.symm
  have actual := phaseProposalUnflagged_fresh_opening_disclosure setup mode runtime leaks bounds
    plan covered maximal (serviceGraph_revealRelaxedOrdered setup mode) values tape activationGap
      processingGap gaps margin remaining anchor trace closing ending closingTrace joint legal
        realized fromStart same changed phase installed kind raw effect coverage excludedEq event
          inside owner acting active payload (checkpoint.refs.get selected) checks output code
            (nodeView_eq_resolve output code) value locked scan action recorded noOld final
              (by
                convert supported using 1
                congr 2
                funext history
                dsimp only [stopped]
                cases history.state <;> rfl) finalState closedKept
  exact (PhaseProposal.publicationDiscloses_cast output action).symm.trans actual

/-- A supported actual fresh publication close has the ordinary full source
phase law at the SAME initialized checkpoint. The ending is the real settle
of its chosen intermediate image, including inherited-E automatic phases. -/
theorem phaseProposalUnflagged_fresh_closing_reveal_law
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some ⟨remaining, none, anchor⟩))
    (checkpoint : RecoverySourceCheckpoint setup mode anchor.application)
    (stored : anchor.application.StoredCheckpoint)
    (proper : ∀ who, who ∉ anchor.application.current.excluded →
      checkpoint.source.BindingsHoldValues who)
    (fresh : ∀ who, ∀ entry ∈ anchor.recall who,
      entry.beforeView.application.2.attempt ≠ anchor.application.attempt)
    (closing ending : (app).Control)
    (closingTrace : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
        (some closing))
    (joint : Player → Option (app).Action)
    (legal : ((menu).protocol initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Legal
        (some closing) joint)
    (realized : some ending ∈ ((app).transition initial (ReservedEpoch.executionHorizon runtime)
      (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)
        (some closing) joint).support)
    (fromStart : TracePrefix trace closingTrace)
    (same : closing.execution.application.attempt = anchor.application.attempt)
    (changed : ending.execution.application.attempt ≠ anchor.application.attempt)
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (kind : phase.kind = .reveal) (raw : RecoveryState graph)
    (effect : PhaseClosingEffect runtime leaks closing.execution ending.execution raw)
    (coverage : (phase.drain raw).FailureCoverage)
    (excludedEq : (phase.drain raw).excluded = ending.execution.application.current.excluded)
    (entryExcluded : anchor.application.entry.excluded = anchor.application.current.excluded)
    (closingInstalled : phase ∈ closing.execution.application.phases.head?)
    (finished : phase.Finished (phase.drain raw))
    (normalized : ending.execution.application =
      ({ closing.execution.application with current := raw } : PhaseRuntimeState graph).normalize)
    (labels : setup.commitRecoveryProtocol.StepEvent → Player → Bool) :
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let model := (menu).information initial horizon scheduler
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some current => current.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (model.runBehavioralUntil
      ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
        ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      final.state = some ending →
      TracePrefix (closingTrace.extend joint legal realized) final.trace →
      ∃ (tail : List (RuntimePhase graph))
        (next : RecoverySourceCheckpoint setup mode
          (⟨tail, closing.execution.application.generation, phase.drain raw, phase.drain raw,
            closing.execution.application.retired⟩ : PhaseRuntimeState graph)),
        closing.execution.application.phases = phase :: tail ∧
        ending.execution.application = PhaseRuntimeState.settle tail
          closing.execution.application.generation (phase.drain raw) (phase.drain raw)
            closing.execution.application.retired ∧
        (∃ fuel, setup.commitRecoveryProtocol.ReachesWithin fuel
          ⟨_, checkpoint.trace⟩ ⟨_, next.trace⟩) ∧
        setup.proposalRecoveryModel.runBehavioralFrom
          (setup.proposalRecoveryNormalizedTrembledProfile
            0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
          (phase.high - phase.low) ⟨_, setup.proposalRecoveryLiftTrace labels checkpoint.trace⟩ =
            PMF.pure ⟨_, setup.proposalRecoveryLiftTrace labels next.trace⟩ := by
  intro horizon scheduler players profile model stopped final supported finalState closedKept
  have rows := phaseProposalUnflagged_fresh_publication_rows setup mode runtime leaks bounds plan
    covered maximal values tape activationGap processingGap gaps margin remaining anchor trace
      checkpoint stored proper fresh closing ending closingTrace joint legal realized fromStart
        same changed phase installed kind raw effect coverage excludedEq final supported finalState
          closedKept
  have initialized : ∀ state ∈ (initial).support, state.Ordered := by
    intro state member
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ member
    exact PhaseRuntimeState.initial_ordered plan draw
  have anchorOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized ((menu).toRawTrace initial horizon scheduler trace)
  have progress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized horizon
    scheduler ⟨remaining, none, anchor⟩ closing trace closingTrace fromStart anchorOrdered
  have sameEntry := (progress.2.2 same.symm).symm
  have sameGeneration : closing.execution.application.generation = anchor.application.generation :=
    congrArg CommitAttemptId.generation same
  have sameOffset := congrArg CommitAttemptId.phase same
  let state : PhaseRuntimeState graph := {closing.execution.application with current := raw}
  let transferred : RecoverySourceCheckpoint setup mode state :=
    checkpoint.transfer sameEntry sameGeneration sameOffset
  have past := checkpoint.transfer_history (other := state) sameEntry sameGeneration sameOffset
  have liftedPast := congrArg (fun history : setup.commitRecoveryProtocol.History =>
    (⟨history.state, setup.proposalRecoveryLiftTrace labels history.trace⟩ :
      setup.proposalRecoveryProtocol.History)) past
  have changedClosing : ending.execution.application.attempt ≠
      closing.execution.application.attempt := fun equal => changed (equal.trans same)
  obtain ⟨⟨draw, native⟩, _binding, receipts, rawStored, remembered, rawCoverage⟩ :=
    phaseClosingEffect_checkpoint_facts setup mode runtime leaks bounds plan horizon scheduler
      closing ending closingTrace raw effect changedClosing
  have failureFrame := phaseClosingEffect_failure_frame setup mode runtime leaks bounds plan
    horizon scheduler closing ending closingTrace raw effect
  have sourceOrder := phaseClosingEffect_publication_order setup mode runtime leaks bounds plan
    horizon scheduler closing ending closingTrace phase (Option.mem_def.mp closingInstalled) raw
      effect changedClosing
  obtain ⟨tail, phases⟩ := List.head?_eq_some_iff.mp (Option.mem_def.mp closingInstalled)
  have truth : ∀ event ∈ phase.events, ∀ owner, (graph).actor? event = some owner →
      owner ∉ state.entry.excluded →
      owner ∉ (phase.drain state.current).native.failureOwnersBefore event.val →
      ∀ (payload : L.Ty) (publication : (graph).outputLayout event = .publication payload)
        (action : ((graph).outputLayout event).Action),
      (⟨event, action⟩ : (graph).Completion) ∈ (phase.drain state.current).native.config.history →
      cast (congrArg EventField.Action publication) action = true := by
    intro event inside owner acting surviving scan payload publication action recorded
    have savedE : state.entry.excluded = anchor.application.current.excluded :=
      (congrArg RecoveryState.excluded sameEntry).trans entryExcluded
    have active : owner ∉ anchor.application.current.excluded := by
      rwa [savedE] at surviving
    exact (PhaseProposal.publicationDiscloses_cast publication action).trans
      (rows event inside owner acting active scan action recorded)
  obtain ⟨next, ⟨fuel, path⟩, law⟩ := transferred.ordinary_completed_reveal_law mode phase tail
    phases kind receipts.exclusion rawStored remembered failureFrame rawCoverage
      (phase.drain_reachable raw native.active.reachable) sourceOrder finished truth values labels
  have noRetry : ¬ (phase.kind = .commitment ∧
      (((phase.drain raw).excluded \ closing.execution.application.entry.excluded) ∩
        phase.owners).Nonempty) := by
    rintro ⟨impossible, _⟩
    cases kind.symm.trans impossible
  have settled : ending.execution.application = PhaseRuntimeState.settle tail
      closing.execution.application.generation (phase.drain raw) (phase.drain raw)
        closing.execution.application.retired := by
    rw [normalized]
    change PhaseRuntimeState.settle closing.execution.application.phases
      closing.execution.application.generation closing.execution.application.entry raw
        closing.execution.application.retired = _
    rw [phases, PhaseRuntimeState.settle_clean phase tail
      closing.execution.application.generation closing.execution.application.entry raw
        closing.execution.application.retired finished noRetry]
  rw [past] at path
  rw [liftedPast] at law
  exact ⟨tail, next, phases, settled, ⟨fuel, path⟩, law⟩

end FreshPublication

end Vegas
