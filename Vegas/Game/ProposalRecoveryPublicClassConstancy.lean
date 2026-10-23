/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPublicClassFactorization
import Vegas.Source.CommitRecoveryFailureCoverage
import Vegas.Source.CommitRecoveryBindingAlternatives
import Vegas.Source.CommitRecoveryPlayerValidity
import Vegas.Game.PhaseProposalSourceFiber
import Vegas.Source.ProposalRecoveryEvolution
import Vegas.Source.ProposalRecoveryDisclosure
import Vegas.Source.ProposalRecoveryPreparationRepairMoves

/-! # Full-information constancy of the foreign source class coefficient -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- Actual completed checks evaluate equally on the same tentative public
proposal and equal public cells. Hidden commitment meanings are never read
through a prediction predicate. -/
private theorem completed_checks_eq_of_public
    {Γ : SourceCtx Player L} {name published : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (metadata : left.MetadataEq right)
    (publicEq : ∀ {x τ} (cell : HasVar Γ x (.publicData τ)),
      left.state.get cell = right.state.get cell)
    (publicationEq : ∀ {x τ} (cell : HasVar Γ x (.publication τ)),
      left.state.get cell = right.state.get cell)
    (value : L.Val payload) :
    (left.registry.completedBy (published := published) left.revelations source).all
        (fun obligation => obligation.accepts
          (Revelations.reveal (published := published) left.revelations source)
            (Env.cons (.success value) left.state)) =
      (right.registry.completedBy (published := published) right.revelations source).all
        (fun obligation => obligation.accepts
          (Revelations.reveal (published := published) right.revelations source)
            (Env.cons (.success value) right.state)) := by
  rcases metadata with ⟨registry, revelations⟩
  rw [← registry, ← revelations]
  apply List.all_congr
  · rfl
  · intro obligation
    apply obligation.accepts_congr
    · intro x ty cell
      cases cell with
      | there cell => exact publicEq cell
    · intro x ty cell
      cases cell with
      | here => rfl
      | there cell => exact publicationEq cell

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem config_failed_impossible_of_values
    {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (config : Config Player L Γ) (proper : config.BindingsHoldValues who)
    (failed : config.FailedBinding who O) : False := by
  obtain ⟨name, payload, source, _pending, bad⟩ := failed.pending
  obtain ⟨value, success⟩ := proper source
  rw [bad] at success
  cases success

omit [Fintype Player] in
/-- A processed failure is covered by actual E; an unresolved failed cell
contradicts its literal typed value. No guard-success condition is used. -/
private theorem failed_impossible_of_surviving_values :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : Vegas.SourceProgram.ProtocolState program)
      (excluded : Finset Player) (who : Player), who ∉ excluded →
      ProtocolState.FailuresCovered program excluded point →
      ProtocolState.BindingsHoldValues who program point →
      ProtocolState.FailedBinding who program point → False
  | _, _, .ret _, config, _, who, _, _, proper, failed =>
      config_failed_impossible_of_values who config proper failed
  | _, _, .sample _ _ _ next, point, excluded, who, survives, covered, proper, failed => by
      cases point with
      | inl config => exact config_failed_impossible_of_values who config proper failed
      | inr point =>
          exact failed_impossible_of_surviving_values next point excluded who
            survives covered proper failed
  | _, _, .commit _ _ _ _ next, point, excluded, who, survives, covered, proper, failed => by
      cases point with
      | inl config => exact config_failed_impossible_of_values who config proper failed
      | inr point =>
          exact failed_impossible_of_surviving_values next point excluded who
            survives covered proper failed
  | _, _, .reveal _ owner _ _ _ _ next, point, excluded, who, survives, covered, proper,
      failed => by
      cases point with
      | inl config => exact config_failed_impossible_of_values who config proper failed
      | inr point =>
          rcases failed with ⟨own, rejected⟩ | pending
          · exact survives (own ▸ covered.1 rejected)
          · exact failed_impossible_of_surviving_values next point excluded who survives
              covered.2 proper pending

omit [Fintype Player] in
private theorem automatic_values_outside_block (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : Vegas.SourceProgram.ProtocolState program),
      ProtocolState.BindingsHoldValues who program point →
      who ∉ ProtocolState.commitOwners program point →
      ProtocolState.BindingsHoldValues who program
        (ProtocolState.automaticCommitBlock program point)
  | _, _, .ret _, _, proper, _ => proper
  | _, _, .sample _ _ _ next, point, proper, outside => by
      cases point with
      | inl _ => exact proper
      | inr point => exact automatic_values_outside_block who next point proper outside
  | _, _, .commit (payload := payload) name owner fresh guard next,
      point, proper, outside => by
      cases point with
      | inr point => exact automatic_values_outside_block who next point proper outside
      | inl config =>
          have absent : who ∉ insert owner (commitPhase next).block.owners := outside
          have headProper : (automaticCommit name owner payload config).BindingsHoldValues who := by
            intro selected ty cell
            cases cell with
            | here => exact (absent (Finset.mem_insert_self _ _)).elim
            | there cell => exact proper cell
          have tailOutside : who ∉ ProtocolState.commitOwners next
              (ProtocolState.entry next (automaticCommit name owner payload config)) := by
            rw [ProtocolState.commitOwners_entry]
            exact fun member => absent (Finset.mem_insert_of_mem member)
          exact automatic_values_outside_block who next _
            ((ProtocolState.bindingsHoldValues_entry who next _).mpr headProper) tailOutside
  | _, _, .reveal _ _ _ _ _ _ next, point, proper, outside => by
      cases point with
      | inl _ => exact proper
      | inr point => exact automatic_values_outside_block who next point proper outside

omit [Fintype Player] in
private theorem close_values_of_surviving
    (current : CommitRecoveryState setup.program) (who : Player)
    (saved : ProtocolState.BindingsHoldValues who setup.program current.saved)
    (live : ProtocolState.BindingsHoldValues who setup.program current.point)
    (survives : who ∉ current.excluded) :
    ProtocolState.BindingsHoldValues who setup.program current.close.saved ∧
      ProtocolState.BindingsHoldValues who setup.program current.close.point := by
  have restored : ProtocolState.BindingsHoldValues who setup.program current.restored :=
    (ProtocolState.bindingsHoldValues_withHistory who setup.program current.saved
      (ProtocolState.history setup.program current.point)).mpr saved
  unfold CommitRecoveryState.close
  split
  · split
    · split
      · exact ⟨restored, restored⟩
      · rename_i _finished _failed noneLeft
        have outside : who ∉ ProtocolState.commitOwners setup.program current.saved := by
          intro member
          exact noneLeft ⟨who, Finset.mem_sdiff.mpr ⟨member, survives⟩⟩
        have outsideRestored : who ∉ ProtocolState.commitOwners setup.program current.restored := by
          simpa only [CommitRecoveryState.restored, ProtocolState.commitOwners_withHistory]
            using outside
        have padded := automatic_values_outside_block who setup.program current.restored
          restored outsideRestored
        exact ⟨padded, padded⟩
    · exact ⟨live, live⟩
  · split
    · exact ⟨saved, live⟩
    · exact ⟨live, live⟩

omit [Fintype Player] in
/-- A single existing recovery instruction preserves a surviving owner's
successful fields unless its actual raw action generated accepted BAD. -/
private theorem recovery_values_of_not_generated :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : Vegas.SourceProgram.ProtocolState program)
      (excluded : Finset Player) (joint : Player → Option (ProposalRecoveryMove Player L))
      (result : Vegas.SourceProgram.ProtocolState program × Finset Player) (who : Player),
      IsLegalJoint (fun owner => ProtocolState.actor program point = some owner ∧ owner ∉ excluded)
        (fun owner => {move : ProposalRecoveryMove Player L |
          move.semantic ∈ ProtocolView.recoveryAvailable owner program
            (ProtocolState.observe owner program point) ∧ move.Valid}) joint →
      who ∉ result.2 → ¬ ProposalRecoveryMove.GeneratedPreparationFailure (joint who) →
      ProtocolState.BindingsHoldValues who program point →
      result ∈ (ProtocolState.recoveryStep program point excluded
        (proposalRecoveryJoint joint)).support →
      ProtocolState.BindingsHoldValues who program result.1 := by
  intro Γ O program
  induction program with
  | ret payoffs =>
      intro point excluded joint result who _legal _survives _notGenerated proper supported
      exact ProtocolState.recoveryStep_noncommit_bindingsHoldValues (.ret payoffs) point
        excluded (proposalRecoveryJoint joint) result who rfl proper supported
  | sample name fresh law next ih =>
      intro point excluded joint result who legal survives notGenerated proper supported
      cases point with
      | inl config =>
          exact ProtocolState.recoveryStep_noncommit_bindingsHoldValues
            (.sample name fresh law next) (.inl config) excluded
              (proposalRecoveryJoint joint) result who rfl proper supported
      | inr point =>
          obtain ⟨after, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih point excluded joint after who legal survives notGenerated proper member
  | @commit Γ O name owner payload fresh guard next ih =>
      intro point excluded joint result who legal survives notGenerated proper supported
      cases point with
      | inr point =>
          obtain ⟨after, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih point excluded joint after who legal survives notGenerated proper member
      | inl config =>
          by_cases absent : owner ∈ excluded
          · simp only [ProtocolState.recoveryStep, Sum.elim_inl, absent, ite_true,
              PMF.mem_support_pure_iff] at supported
            subst result
            apply (ProtocolState.bindingsHoldValues_entry who next _).mpr
            intro selected ty cell
            cases cell with
            | here => exact (survives absent).elim
            | there cell => exact proper cell
          · have offered := legal owner
            obtain ⟨move, chosen⟩ : ∃ move, joint owner = some move := by
              cases chosen : joint owner with
              | none => rw [chosen] at offered; exact (offered ⟨rfl, absent⟩).elim
              | some move => exact ⟨move, rfl⟩
            rw [chosen] at offered
            obtain ⟨choice, _admitted, action⟩ := offered.2.1.1
            have packet : ((proposalRecoveryJoint joint owner).map (·.action)) =
                some (.commit owner name payload choice) := by
              rw [proposalRecoveryJoint, chosen, Option.map_some, Option.map_some, action]
            simp only [ProtocolState.recoveryStep, Sum.elim_inl, absent, ite_false,
              packet, OwnAction.binding_commit, PMF.mem_support_pure_iff] at supported
            subst result
            apply (ProtocolState.bindingsHoldValues_entry who next _).mpr
            intro selected ty cell
            cases cell with
            | there cell => exact proper cell
            | here =>
                cases choice with
                | success value => exact ⟨value, rfl⟩
                | failure =>
                    exfalso
                    cases missing : move.semantic.missing with
                    | true =>
                        apply survives
                        simp only [CommitRecoveryMove.missed, proposalRecoveryJoint, chosen,
                          Option.map_some, Option.elim_some, missing, ite_true]
                        exact Finset.mem_insert_self _ _
                    | false =>
                        apply notGenerated
                        rw [chosen]
                        change move.semantic.missing = false ∧ _
                        rw [missing, action]
                        exact ⟨rfl, trivial⟩
  | reveal published owner name fresh selected unresolved next ih =>
      intro point excluded joint result who legal survives notGenerated proper supported
      cases point with
      | inl config =>
          exact ProtocolState.recoveryStep_noncommit_bindingsHoldValues
            (.reveal published owner name fresh selected unresolved next) (.inl config)
              excluded (proposalRecoveryJoint joint) result who rfl proper supported
      | inr point =>
          obtain ⟨after, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih point excluded joint after who legal survives notGenerated proper member

omit [Fintype Player] in
theorem source_signal_depth (focal : Player) :
    ∀ {state : setup.proposalRecoveryProtocol.State}
      (trace : setup.proposalRecoveryProtocol.Trace state),
      (setup.proposalRecoverySignals.infoOf focal trace).2.length = trace.length
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      rw [InfoSignals.infoOf_extend]
      change ((setup.proposalRecoverySignals.infoOf focal prior).1 ::
        (setup.proposalRecoverySignals.infoOf focal prior).2).length = prior.length + 1
      rw [List.length_cons, source_signal_depth focal prior]

omit [Fintype Player] in
private theorem generated_preparation_before_extend (owner : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (generated : setup.GeneratedPreparationHistory owner ⟨before, prior⟩) :
    setup.GeneratedPreparationHistory owner ⟨after, prior.extend joint legal supported⟩ := by
  obtain ⟨record, member, failed⟩ := generated
  refine ⟨record, ?_, failed⟩
  rw [InfoSignals.ownPlay_extend]
  cases chosen : joint owner with
  | none => exact member
  | some move => exact List.mem_cons_of_mem _ member

omit [Fintype Player] in
private theorem generated_preparation_at_extend (owner : Player)
    {before after : setup.proposalRecoveryProtocol.State}
    (prior : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (generated : ProposalRecoveryMove.GeneratedPreparationFailure (joint owner)) :
    setup.GeneratedPreparationHistory owner ⟨after, prior.extend joint legal supported⟩ := by
  cases selected : joint owner with
  | none =>
      simp only [selected, ProposalRecoveryMove.GeneratedPreparationFailure,
        Option.elim_none] at generated
  | some move =>
      refine ⟨(setup.proposalRecoveryModel.infoOf owner prior, move), ?_, ?_⟩
      · rw [InfoSignals.ownPlay_extend, selected]
        exact List.mem_cons_self
      · simpa only [selected] using generated

omit [Fintype Player] in
/-- A genuine failed source binding is accounted for by permanent exclusion
or an actual generated preparation action. Saved rollback selects its real
old typed fields; canceled actions remain literal in the retained own word. -/
private theorem source_failed_binding_origin
    (wellFormed : setup.WellFormed) {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) (who : Player) :
    ∀ current, state = some current →
      (ProtocolState.FailedBinding who setup.program current.saved →
        who ∈ current.excluded ∨
          setup.GeneratedPreparationHistory who ⟨state, trace⟩) ∧
      (ProtocolState.FailedBinding who setup.program current.point →
        who ∈ current.excluded ∨
          setup.GeneratedPreparationHistory who ⟨state, trace⟩) := by
  classical
  induction trace with
  | start => intro current impossible; cases impossible
  | @extend before after prior joint legal supported ih =>
      intro current equality
      subst after
      cases before with
      | none =>
          obtain ⟨inputs, member, image⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj image
          subst current
          have proper : ProtocolState.BindingsHoldValues who setup.program
              (ProtocolState.entry setup.program (setup.initialConfig inputs)) :=
            (ProtocolState.bindingsHoldValues_entry who setup.program _).mpr
              (fun cell => wellFormed.initialValues inputs member cell)
          have covered := ProtocolState.failuresCovered_entry setup.program ∅
            (setup.initialConfig inputs)
          have impossible := failed_impossible_of_surviving_values setup.program
            (ProtocolState.entry setup.program (setup.initialConfig inputs)) ∅ who
              (Finset.notMem_empty _) covered proper
          exact ⟨fun failed => (impossible failed).elim, fun failed => (impossible failed).elim⟩
      | some previous =>
          obtain ⟨next, nativeMember, image⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          have same := Option.some.inj image
          subst next
          by_cases excluded : who ∈ current.excluded
          · exact ⟨fun _ => Or.inl excluded, fun _ => Or.inl excluded⟩
          · by_cases generated : setup.GeneratedPreparationHistory who
                ⟨some current, prior.extend joint legal supported⟩
            · exact ⟨fun _ => Or.inr generated, fun _ => Or.inr generated⟩
            · have monotone := previous.step_excluded_monotone
                (proposalRecoveryJoint joint) current nativeMember
              have previousSurvives : who ∉ previous.excluded :=
                fun member => excluded (monotone member)
              have previousGood : ¬ setup.GeneratedPreparationHistory who
                  ⟨some previous, prior⟩ := by
                intro earlier
                exact generated (generated_preparation_before_extend setup who prior
                  joint legal supported earlier)
              have previousOrigin := ih previous rfl
              have alternative := setup.commitRecovery_bindingsHoldValues_or_failedBinding
                wellFormed (setup.proposalRecoveryEraseTrace prior) who previous rfl
              have saved : ProtocolState.BindingsHoldValues who setup.program previous.saved := by
                rcases alternative.1 with proper | failed
                · exact proper
                · rcases previousOrigin.1 failed with absent | bad
                  · exact (previousSurvives absent).elim
                  · exact (previousGood bad).elim
              have live : ProtocolState.BindingsHoldValues who setup.program previous.point := by
                rcases alternative.2 with proper | failed
                · exact proper
                · rcases previousOrigin.2 failed with absent | bad
                  · exact (previousSurvives absent).elim
                  · exact (previousGood bad).elim
              have currentGood : ¬ ProposalRecoveryMove.GeneratedPreparationFailure
                  (joint who) := by
                intro bad
                exact generated (generated_preparation_at_extend setup who prior joint legal
                  supported bad)
              obtain ⟨raw, rawMember, closed⟩ := previous.step_raw_result
                (proposalRecoveryJoint joint) current nativeMember
              have rawSurvives : who ∉ raw.val.2 := by
                have sameE : current.excluded = raw.val.2 := by
                  rw [closed, CommitRecoveryState.close_excluded]
                  rfl
                exact sameE ▸ excluded
              have rawValues := recovery_values_of_not_generated setup.program previous.point
                previous.excluded joint raw.val who legal.2 rawSurvives currentGood live rawMember
              have full := close_values_of_surviving setup
                (previous.install raw.val raw.property) who saved rawValues rawSurvives
              have currentValues :
                  ProtocolState.BindingsHoldValues who setup.program current.saved ∧
                    ProtocolState.BindingsHoldValues who setup.program current.point := by
                simpa only [closed] using full
              have coverage := setup.commitRecovery_failuresCovered
                (setup.proposalRecoveryEraseTrace (prior.extend joint legal supported)) current rfl
              exact ⟨fun failed => (failed_impossible_of_surviving_values setup.program
                  current.saved current.excluded who excluded coverage.1
                    currentValues.1 failed).elim,
                fun failed => (failed_impossible_of_surviving_values setup.program current.point
                  current.excluded who excluded coverage.2 currentValues.2 failed).elim⟩

omit [Fintype Player] in
theorem proposalRecovery_bindingsHoldValues_of_surviving_no_generated
    (wellFormed : setup.WellFormed) (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (who : Player)
    (survives : who ∉ current.excluded)
    (good : ¬ setup.GeneratedPreparationHistory who ⟨some current, trace⟩) :
    ProtocolState.BindingsHoldValues who setup.program current.point := by
  have alternative := setup.commitRecovery_bindingsHoldValues_or_failedBinding wellFormed
    (setup.proposalRecoveryEraseTrace trace) who current rfl
  rcases alternative.2 with proper | failed
  · exact proper
  · rcases (source_failed_binding_origin setup wellFormed trace who current rfl).2 failed with
      excluded | generated
    · exact (survives excluded).elim
    · exact (good generated).elim

/-- At an active foreign commitment, its actual next E distinguishes omission
from every proper binding even when this row closes or retries the block.
Accepted BAD is excluded by its actual owned action, not by a stored-value
premise or by a prediction about its guard. -/
private theorem foreign_commit_class_of_next_excluded
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal owner : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (acting : ProtocolState.actor setup.program current.point = some owner)
    (survives : owner ∉ current.excluded) (foreign : owner ≠ focal)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (next : CommitRecoveryState setup.program)
    (supported : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support)
    (good : ¬ setup.GeneratedPreparationHistory owner
      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported)) :
    (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      ⟨some current, trace⟩ joint legal supported).1 =
        if owner ∈ next.excluded then ENNReal.ofReal omission.val else
          ENNReal.ofReal ((1 - omission.val) * (1 - bad.val)) := by
  classical
  obtain ⟨Δ, P, name, actualOwner, payload, fresh, guard, suffix, lift, entry,
    origin, point, _names⟩ := ProtocolState.exists_committing_entry setup.program current.point
      setup.namesNodup committing
  have ownerEq : actualOwner = owner := by
    have original := origin.actor_lift
      (ProtocolState.entry (.commit name actualOwner fresh guard suffix) entry)
    rw [← point] at original
    exact Option.some.inj (original.symm.trans acting)
  subst actualOwner
  obtain ⟨move, selected⟩ : ∃ move, joint owner = some move := by
    have offered := legal.2 owner
    cases chosen : joint owner with
    | none =>
        rw [chosen] at offered
        exact (offered ⟨acting, survives⟩).elim
    | some move => exact ⟨move, rfl⟩
  have offered := legal.2 owner
  rw [selected] at offered
  have available : move.semantic ∈ current.available owner := offered.2.1
  rw [CommitRecoveryState.available, point, origin.recoveryAvailable] at available
  obtain ⟨atom, atomEq⟩ := CommitRecoveryMove.exists_bindingAtom_of_available
    owner name payload fresh guard suffix (entry.view owner) move.semantic available
  have semanticSelected : proposalRecoveryJoint joint owner =
      some (CommitRecoveryMove.bindingAtom owner name payload atom) := by
    rw [proposalRecoveryJoint, selected, Option.map_some, atomEq]
  have nativeSupport : next ∈ (current.step (proposalRecoveryJoint joint)).support := by
    change some next ∈ ((current.step (proposalRecoveryJoint joint)).map some).support at supported
    obtain ⟨target, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    cases Option.some.inj same
    exact member
  obtain ⟨raw, rawSupport, closed⟩ := current.step_raw_result
    (proposalRecoveryJoint joint) next nativeSupport
  rw [point, origin.recoveryStep_lift] at rawSupport
  obtain ⟨localResult, member, image⟩ := (PMF.mem_support_map_iff _ _ _).mp rawSupport
  have result := member
  simp only [ProtocolState.recoveryStep, ProtocolState.entry, Sum.elim_inl,
    survives, ite_false] at result
  have localE := congrArg Prod.snd ((PMF.mem_support_pure_iff _ _).mp result)
  have excluded : next.excluded =
      if CommitRecoveryMove.missed (proposalRecoveryJoint joint owner) then
        insert owner current.excluded else current.excluded := by
    calc
      next.excluded = raw.val.2 := by
        rw [closed, CommitRecoveryState.close_excluded]
        rfl
      _ = localResult.2 := (congrArg Prod.snd image).symm
      _ = _ := localE
  cases atom with
  | inl value =>
      have missing : move.semantic.missing = false := by
        rw [← atomEq]
        rfl
      have action : move.semantic.action = .commit owner name payload (.success value) := by
        rw [← atomEq]
        rfl
      simp only [excluded, semanticSelected, CommitRecoveryMove.missed,
        CommitRecoveryMove.bindingAtom, Option.elim_some, Bool.false_eq_true, ite_false,
        survives, proposalRecoveryForeignRowFactors, acting, foreign, selected, action, missing]
  | inr omitted =>
      cases omitted with
      | true =>
          have missing : move.semantic.missing = true := by rw [← atomEq]; rfl
          have action : move.semantic.action = .commit owner name payload .failure := by
            rw [← atomEq]
            rfl
          simp only [excluded, semanticSelected, CommitRecoveryMove.missed,
            CommitRecoveryMove.bindingAtom, Option.elim_some, ite_true,
            Finset.mem_insert_self, proposalRecoveryForeignRowFactors, acting, foreign,
            ite_false, selected, action, missing]
      | false =>
          exfalso
          apply good
          apply generated_preparation_at_extend setup owner trace joint legal supported
          rw [selected]
          change move.semantic.missing = false ∧ _
          rw [← atomEq]
          exact ⟨rfl, trivial⟩

omit [Fintype Player] in
theorem metadata_restrict_to_suffix
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : Vegas.SourceProgram.ProtocolState program → Vegas.SourceProgram.ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ (first : Vegas.SourceProgram.ProtocolState program)
      (second : Vegas.SourceProgram.ProtocolState whole),
      ProtocolState.MetadataEq whole (lift first) second →
      ∃ localPoint, second = lift localPoint ∧
        ProtocolState.MetadataEq program first localPoint := by
  induction origin with
  | initial => intro first second related; exact ⟨second, rfl, related⟩
  | sampleTail fresh law next previous ih =>
      intro first second related
      obtain ⟨inside, image, paired⟩ := ih (.inr first) second related
      cases inside with
      | inl _ => cases paired
      | inr inside => exact ⟨inside, image, paired⟩
  | commitTail fresh guard next previous ih =>
      intro first second related
      obtain ⟨inside, image, paired⟩ := ih (.inr first) second related
      cases inside with
      | inl _ => cases paired
      | inr inside => exact ⟨inside, image, paired⟩
  | revealTail fresh selected unresolved next previous ih =>
      intro first second related
      obtain ⟨inside, image, paired⟩ := ih (.inr first) second related
      cases inside with
      | inl _ => cases paired
      | inr inside => exact ⟨inside, image, paired⟩

omit [Fintype Player] in
theorem source_reveal_entry :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : Vegas.SourceProgram.ProtocolState program)
      (owner : Player), (Γ.map Prod.fst).Nodup →
      ProtocolState.atCommit program point = false →
      ProtocolState.actor program point = some owner →
      ∃ (Δ : SourceCtx Player L) (P : Finset VarId) (published name : VarId) (payload : L.Ty)
        (fresh : published ∉ Δ.map Prod.fst) (source : HasVar Δ name (.commitment owner payload))
        (unresolved : name ∈ P)
        (next : SourceProgram Player L ((published, .publication payload) :: Δ) (P.erase name))
        (lift : Vegas.SourceProgram.ProtocolState
          (.reveal published owner name fresh source unresolved next) →
            Vegas.SourceProgram.ProtocolState program) (entry : Config Player L Δ),
        ProtocolSuffix program (.reveal published owner name fresh source unresolved next) lift ∧
          point = lift (ProtocolState.entry
            (.reveal published owner name fresh source unresolved next) entry) ∧
              (Δ.map Prod.fst).Nodup
  | _, _, .ret _, _, _, _, _, acting => by cases acting
  | _, _, .sample name fresh law next, point, owner, unique, notCommit, acting => by
      cases point with
      | inl _ => cases acting
      | inr point =>
          obtain ⟨Δ, P, published, subject, payload, selectedFresh, source, unresolved, tail,
            lift, entry, origin, image, names⟩ := source_reveal_entry next point owner
              (List.nodup_cons.mpr ⟨fresh, unique⟩) notCommit acting
          exact ⟨Δ, P, published, subject, payload, selectedFresh, source, unresolved, tail,
            (fun point => .inr (lift point)), entry,
            (ProtocolSuffix.sampleTail fresh law next .initial).compose origin,
            congrArg Sum.inr image, names⟩
  | _, _, .commit name actor fresh guard next, point, owner, unique, notCommit, acting => by
      cases point with
      | inl _ => cases notCommit
      | inr point =>
          obtain ⟨Δ, P, published, subject, payload, selectedFresh, source, unresolved, tail,
            lift, entry, origin, image, names⟩ := source_reveal_entry next point owner
              (List.nodup_cons.mpr ⟨fresh, unique⟩) notCommit acting
          exact ⟨Δ, P, published, subject, payload, selectedFresh, source, unresolved, tail,
            (fun point => .inr (lift point)), entry,
            (ProtocolSuffix.commitTail fresh guard next .initial).compose origin,
            congrArg Sum.inr image, names⟩
  | _, _, .reveal published actor name fresh source unresolved next, point, owner,
      unique, notCommit, acting => by
      cases point with
      | inl config =>
          have own : actor = owner := Option.some.inj acting
          subst actor
          exact ⟨_, _, published, name, _, fresh, source, unresolved, next, id, config,
            .initial, rfl, unique⟩
      | inr point =>
          obtain ⟨Δ, P, selected, subject, payload, selectedFresh, selectedSource,
            selectedUnresolved, tail, lift, entry, origin, image, names⟩ :=
              source_reveal_entry next point owner
              (List.nodup_cons.mpr ⟨fresh, unique⟩) notCommit acting
          exact ⟨Δ, P, selected, subject, payload, selectedFresh, selectedSource,
            selectedUnresolved, tail, (fun point => .inr (lift point)), entry,
            (ProtocolSuffix.revealTail fresh source unresolved next .initial).compose origin,
            congrArg Sum.inr image, names⟩

omit [Fintype Player] in
private theorem source_noncommit_query
    (owner : Player) (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (notCommit : ProtocolState.atCommit setup.program current.point = false) :
    (setup.proposalRecoveryQuery owner
      (setup.proposalRecoveryModel.infoOf owner trace)).1.1.1.1.elim false
        (ProtocolView.atCommit owner setup.program) = false := by
  let original := setup.commitRecoveryModel.infoOf owner (setup.proposalRecoveryEraseTrace trace)
  have atOriginal : original.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = false := by
    rw [setup.commitRecovery_atCommit_info]
    exact notCommit
  have noMiss : setup.commitRecoveryNoMissInformation owner original = original := by
    simp only [commitRecoveryNoMissInformation, atOriginal, Bool.false_eq_true,
      false_and, ite_false]
  change (setup.commitRecoveryErasedInformation owner
    (setup.commitRecoveryNoMissInformation owner
      (setup.proposalRecoveryEraseInfo owner
        (setup.proposalRecoveryModel.infoOf owner trace)))).1.1.1.elim false
          (ProtocolView.atCommit owner setup.program) = false
  rw [setup.proposalRecoveryEraseInfo_observed, noMiss]
  change (original.1.1.1.map (ProtocolView.eraseHistory owner setup.program)).elim false
    (ProtocolView.atCommit owner setup.program) = false
  cases selected : original.1.1.1 with
  | none => rfl
  | some view =>
      simpa only [selected, Option.map_some, Option.elim_some,
        ProtocolView.atCommit_eraseHistory] using atOriginal

omit [Fintype Player] in
/-- At the actual source publication row, arbitrary ordinary value tables
collapse to truthful opening. The two distinct withheld labels retain exactly
the original conditional delivery coin. No binding or guard-success premise
is needed for this choice-law identity. -/
private theorem foreign_publication_choice_law
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded) :
    let information := setup.proposalRecoveryModel.infoOf owner trace
    ∃ truth failed withheld : setup.proposalRecoveryModel.Choice owner information,
      truth.val = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name true, false⟩) ∧
      failed.val = some (ProposalRecoveryMove.failedDisclosure owner name) ∧
      withheld.val = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name false, false⟩) ∧
      setup.proposalRecoveryNormalizedTrembledProfile
          omission.val omission.property.1 omission.property.2
          bad.val bad.property.1 bad.property.2
          delivery.val delivery.property.1 delivery.property.2 values owner information =
        mix omission.val omission.property.1 omission.property.2
          (mix delivery.val delivery.property.1 delivery.property.2
            (PMF.pure failed) (PMF.pure withheld)) (PMF.pure truth) := by
  classical
  intro information
  let key := setup.proposalRecoveryQuery owner information
  have acting : ProtocolState.actor setup.program current.point = some owner := by
    rw [point, origin.actor_lift]
    rfl
  have notCommit : ProtocolState.atCommit setup.program current.point = false := by
    rw [point, origin.atCommit_lift]
    rfl
  have keyNoncommit : key.1.1.1.1.elim false
      (ProtocolView.atCommit owner setup.program) = false :=
    source_noncommit_query setup owner current trace notCommit
  let make (disclosed requested : Bool) : setup.proposalRecoveryModel.Choice owner information := by
    refine ⟨some (ProposalRecoveryMove.label ⟨.reveal owner name disclosed, false⟩ requested), ?_⟩
    apply (setup.proposalRecoveryModel.menu_adequate owner trace _).mpr
    refine ⟨⟨acting, survives⟩, ?_, ProposalRecoveryMove.label_valid _ _⟩
    rw [ProposalRecoveryMove.label_semantic]
    change (⟨.reveal owner name disclosed, false⟩ : CommitRecoveryMove Player L) ∈
      ProtocolView.recoveryAvailable owner setup.program
        (ProtocolState.observe owner setup.program current.point)
    rw [point, origin.recoveryAvailable]
    exact ⟨⟨disclosed, rfl⟩, rfl⟩
  let truth := make true false
  let failed := make false true
  let withheld := make false false
  refine ⟨truth, failed, withheld, rfl, rfl, rfl, ?_⟩
  let equivalence := setup.proposalRecoveryComponentChoice owner information
  let semanticWithheld := setup.proposalRecoveryComponentSemanticChoice owner key
    (equivalence withheld)
  have inverse : setup.commitRecoveryFailureChoice owner key.1 true = semanticWithheld := by
    apply setup.commitRecoveryFailureChoice_eq_of_failure_move owner key.1 true
      semanticWithheld ⟨.reveal owner name false, false⟩ rfl rfl
    rw [keyNoncommit]
    rfl
  have ordinaryRaw (ordinary : setup.CommitRecoveryValueChoice owner key.1) :
      (setup.proposalRecoveryComponentLabelChoice owner key false ordinary.val).val =
        truth.val := by
    let actual := equivalence.symm
      (setup.proposalRecoveryComponentLabelChoice owner key false ordinary.val)
    have offered := (setup.proposalRecoveryModel.menu_adequate owner trace actual.val).mp
      actual.property
    cases selected : ordinary.val.val with
    | none =>
        have absent : actual.val = none := by
          change ordinary.val.val.map (fun move => ProposalRecoveryMove.label move false) = none
          rw [selected]
          rfl
        rw [absent] at offered
        exact (offered ⟨acting, survives⟩).elim
    | some move =>
        have picked : actual.val = some (ProposalRecoveryMove.label move false) := by
          change ordinary.val.val.map (fun move => ProposalRecoveryMove.label move false) = _
          rw [selected]
          rfl
        rw [picked] at offered
        have available := offered.2.1
        rw [ProposalRecoveryMove.label_semantic] at available
        change move ∈ ProtocolView.recoveryAvailable owner setup.program
          (ProtocolState.observe owner setup.program current.point) at available
        rw [point, origin.recoveryAvailable] at available
        obtain ⟨bit, action⟩ := available.1
        have truthful : bit = true := by
          cases bit with
          | true => rfl
          | false =>
              exact ((ordinary.property move selected).2 (by rw [action]; rfl)).elim
        have same : move = (⟨.reveal owner name true, false⟩ : CommitRecoveryMove Player L) :=
          congrArg₂ CommitRecoveryMove.mk (by rw [action, truthful])
            (ordinary.property move selected).1
        change ordinary.val.val.map (fun move => ProposalRecoveryMove.label move false) = _
        rw [selected, same]
        rfl
  have ordinaryMap : ((values owner key).map fun ordinary =>
      (setup.proposalRecoveryComponentLabelChoice owner key false ordinary.val).val) =
        PMF.pure truth.val := by
    calc
      _ = (values owner key).map (fun _ => truth.val) := by
        apply congrArg (PMF.map · (values owner key))
        funext ordinary
        exact ordinaryRaw ordinary
      _ = _ := PMF.map_const _ _
  let coin := mix delivery.val delivery.property.1 delivery.property.2
    (PMF.pure true) (PMF.pure false)
  have failureMap : (coin.map fun requested =>
      (setup.proposalRecoveryComponentLabelChoice owner key requested
        (setup.commitRecoveryFailureChoice owner key.1 true)).val) =
      mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure failed.val) (PMF.pure withheld.val) := by
    rw [inverse]
    simp only [coin, mix_map, PMF.pure_map]
    rfl
  have projected : (setup.proposalRecoveryComponentTrembledLaw owner key
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 (values owner key)).map Subtype.val =
      mix omission.val omission.property.1 omission.property.2
        (mix delivery.val delivery.property.1 delivery.property.2
          (PMF.pure failed.val) (PMF.pure withheld.val)) (PMF.pure truth.val) := by
    rw [setup.proposalRecoveryComponentTrembledLaw_noncommit owner key keyNoncommit,
      mix_map, PMF.map_comp, PMF.map_comp]
    simp only [Function.comp_def]
    rw [failureMap, ordinaryMap]
  apply pmf_map_injective Subtype.val_injective
  change (setup.proposalRecoveryPrescribedProfile
    (fun author coordinate => setup.proposalRecoveryComponentTrembledLaw author coordinate
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 (values author coordinate))
        owner information).map Subtype.val = _
  rw [setup.proposalRecoveryPrescribedProfile_raw, mix_map, mix_map,
    PMF.pure_map, PMF.pure_map, PMF.pure_map]
  exact projected

/-- At a sole owned source instruction, the existing one-step execution
pushes the acting policy through its actual deterministic transition. The
chosen outputs retain their original legal joint and full trace extension. -/
private theorem owned_history_choice_law
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner) :
    ∃ finish : setup.proposalRecoveryModel.Choice owner
        (setup.proposalRecoveryModel.infoOf owner trace) → setup.proposalRecoveryProtocol.History,
      (∀ (choice : setup.proposalRecoveryModel.Choice owner
          (setup.proposalRecoveryModel.infoOf owner trace)),
        ∃ target : setup.proposalRecoveryProtocol.State,
        ∃ legal : setup.proposalRecoveryProtocol.Legal (some current)
          (setup.proposalRecoveryProtocol.singletonJoint owner choice.val),
        ∃ supported : target ∈
            (setup.proposalRecoveryProtocol.step (some current)
              ⟨setup.proposalRecoveryProtocol.singletonJoint owner choice.val, legal⟩).support,
          finish choice = (⟨target,
            trace.extend (setup.proposalRecoveryProtocol.singletonJoint owner choice.val)
              legal supported⟩ : setup.proposalRecoveryProtocol.History)) ∧
      ∀ profile : ∀ author, setup.proposalRecoveryModel.BehavioralPolicy author,
        setup.proposalRecoveryModel.runBehavioralFrom profile 1 ⟨some current, trace⟩ =
          (profile owner (setup.proposalRecoveryModel.infoOf owner trace)).map finish := by
  classical
  have running : ¬ setup.proposalRecoveryProtocol.terminal (some current) := by
    intro stopped
    have absent := ProtocolState.terminal_actor_none owner setup.program current.point stopped
    rw [ProtocolState.actor_observe_eq] at absent
    rw [acting] at absent
    cases absent
  have unique : ∀ author, setup.proposalRecoveryProtocol.active (some current) author →
      author = owner := by
    intro author active
    exact Option.some.inj (active.1.symm.trans acting)
  let embed (choice : setup.proposalRecoveryModel.Choice owner
      (setup.proposalRecoveryModel.infoOf owner trace)) :
      {joint // setup.proposalRecoveryProtocol.Legal (some current) joint} :=
    ⟨setup.proposalRecoveryProtocol.singletonJoint owner choice.val,
      ExecutionProtocol.legal_of_legalOption running fun other => by
        by_cases same : other = owner
        · subst other
          simpa only [ExecutionProtocol.singletonJoint_self] using
            (setup.proposalRecoveryModel.menu_adequate owner trace choice.val).mp choice.property
        · have inactive : ¬ setup.proposalRecoveryProtocol.active (some current) other :=
            fun active => same (unique other active)
          simpa only [ExecutionProtocol.singletonJoint_of_ne _ _ _ same, LegalOption]
            using inactive⟩
  let target (choice : setup.proposalRecoveryModel.Choice owner
      (setup.proposalRecoveryModel.infoOf owner trace)) :
      setup.proposalRecoveryProtocol.State := Classical.choose
    (setup.proposalRecoveryProtocol.step (some current) (embed choice)).support_nonempty
  have reached (choice : setup.proposalRecoveryModel.Choice owner
      (setup.proposalRecoveryModel.infoOf owner trace)) : target choice ∈
      (setup.proposalRecoveryProtocol.step (some current) (embed choice)).support :=
    Classical.choose_spec
      (setup.proposalRecoveryProtocol.step (some current) (embed choice)).support_nonempty
  let finish (choice : setup.proposalRecoveryModel.Choice owner
      (setup.proposalRecoveryModel.infoOf owner trace)) : setup.proposalRecoveryProtocol.History :=
    ⟨target choice, trace.extend (embed choice).val (embed choice).property (reached choice)⟩
  refine ⟨finish,
    (fun choice => ⟨target choice, (embed choice).property, reached choice, rfl⟩), ?_⟩
  intro profile
  rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal profile 0 running,
    setup.proposalRecoveryModel.behavioralJoint_eq_map_of_at_most_one_active
      profile trace running owner unique, PMF.bind_map]
  change (profile owner (setup.proposalRecoveryModel.infoOf owner trace)).bind
    (fun choice => (setup.proposalRecoveryProtocol.step (some current) (embed choice)).bindOnSupport
      (fun next supported => PMF.pure
        ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
          (embed choice).property supported))) = _
  rw [← pmf_bind_pure_eq_map]
  apply bind_congr_on_support
  intro choice _chosen
  apply pmf_eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨actual, actualReached, resultEq⟩ :=
    (PMF.mem_support_bindOnSupport_iff _ _).mp supported
  obtain ⟨selected, selectedReached, selectedEq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp (reached choice)
  obtain ⟨other, otherReached, otherEq⟩ :=
    (PMF.mem_support_map_iff _ _ _).mp actualReached
  have same : other = selected := setup.commitRecovery_step_unique_of_actor current owner
    acting (proposalRecoveryJoint (embed choice).val) other selected otherReached selectedReached
  have endpoint : actual = target choice := by
    rw [← otherEq, ← selectedEq, same]
  have landed := (PMF.mem_support_pure_iff _ _).mp resultEq
  change result = finish choice
  cases endpoint
  exact landed

omit [Fintype Player] in
/-- A genuine active publication uses the original noncommit dispatcher.
Its exact result includes the real guard verdict, exclusion update, saved
point and unchanged generation; no retry is introduced at publication. -/
private theorem publication_step_pure
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded)
    (joint : Player → Option (ProposalRecoveryMove Player L)) :
    let disclose := OwnAction.disclosure ((joint owner).map (fun move => move.semantic.action))
    let result := revealSuccessor published source entry disclose
    current.step (proposalRecoveryJoint joint) =
      PMF.pure (CommitRecoveryState.atPoint
        (lift (.inr (ProtocolState.entry suffix result)))
        (match result.state.get .here with
          | .failure => insert owner current.excluded
          | .success _ => current.excluded) current.generation) := by
  intro disclose result
  have notCommit : ProtocolState.atCommit setup.program current.point = false := by
    rw [point, origin.atCommit_lift]
    rfl
  rw [current.step_noncommit_law
      (setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace trace))
        notCommit, point, origin.recoveryStep_lift]
  simp only [ProtocolState.recoveryStep, Sum.elim_inl, survives, ite_false,
    proposalRecoveryJoint, Option.map_map, PMF.pure_map, Function.comp_def]
  rfl

omit [Fintype Player] in
theorem publication_legal_move_cases
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint) :
    joint owner = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name true, false⟩) ∨
      joint owner = some (ProposalRecoveryMove.failedDisclosure owner name) ∨
      joint owner = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name false, false⟩) := by
  have acting : ProtocolState.actor setup.program current.point = some owner := by
    rw [point, origin.actor_lift]
    rfl
  have offered := setup.proposalRecoveryProtocol.legalOption_of_legal legal owner
  cases selected : joint owner with
  | none =>
      rw [selected] at offered
      exact (offered ⟨acting, survives⟩).elim
  | some move =>
      rw [selected] at offered
      have available := offered.2.1
      change move.semantic ∈ current.available owner at available
      rw [CommitRecoveryState.available, point, origin.recoveryAvailable] at available
      obtain ⟨⟨disclosed, action⟩, noMissing⟩ := available
      have semantic : move.semantic = ⟨.reveal owner name disclosed, false⟩ :=
        congrArg₂ CommitRecoveryMove.mk action noMissing
      cases disclosed with
      | true =>
          have noProposal : move.proposed = false := by
            cases proposed : move.proposed with
            | false => rfl
            | true =>
                obtain ⟨author, subject, failed⟩ := offered.2.2 proposed
                rw [action] at failed
                cases failed
          exact Or.inl (congrArg some
            (congrArg₂ ProposalRecoveryMove.mk semantic noProposal))
      | false =>
          cases proposed : move.proposed with
          | true => exact Or.inr (Or.inl (congrArg some
              (congrArg₂ ProposalRecoveryMove.mk semantic proposed)))
          | false => exact Or.inr (Or.inr (congrArg some
              (congrArg₂ ProposalRecoveryMove.mk semantic proposed)))

/-- The actual publication execution is a three-point mixture of full source
histories. The truthful and failed-disclosure points may have the same focal
observable, but each retains its original semantic cause and labeled joint. -/
private theorem foreign_publication_history_law
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded) :
    ∃ finish : setup.proposalRecoveryModel.Choice owner
        (setup.proposalRecoveryModel.infoOf owner trace) → setup.proposalRecoveryProtocol.History,
      ∃ truth failed withheld : setup.proposalRecoveryModel.Choice owner
          (setup.proposalRecoveryModel.infoOf owner trace),
        truth.val = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name true, false⟩) ∧
        failed.val = some (ProposalRecoveryMove.failedDisclosure owner name) ∧
        withheld.val = some (ProposalRecoveryMove.ordinary ⟨.reveal owner name false, false⟩) ∧
        (∀ (choice : setup.proposalRecoveryModel.Choice owner
            (setup.proposalRecoveryModel.infoOf owner trace)),
          ∃ target : setup.proposalRecoveryProtocol.State,
          ∃ legal : setup.proposalRecoveryProtocol.Legal (some current)
            (setup.proposalRecoveryProtocol.singletonJoint owner choice.val),
          ∃ supported : target ∈
              (setup.proposalRecoveryProtocol.step (some current)
                ⟨setup.proposalRecoveryProtocol.singletonJoint owner choice.val, legal⟩).support,
            finish choice = (⟨target,
              trace.extend (setup.proposalRecoveryProtocol.singletonJoint owner choice.val)
                legal supported⟩ : setup.proposalRecoveryProtocol.History)) ∧
        setup.proposalRecoveryModel.runBehavioralFrom
            (setup.proposalRecoveryNormalizedTrembledProfile
              omission.val omission.property.1 omission.property.2
              bad.val bad.property.1 bad.property.2
              delivery.val delivery.property.1 delivery.property.2 values)
            1 ⟨some current, trace⟩ =
          mix omission.val omission.property.1 omission.property.2
            (mix delivery.val delivery.property.1 delivery.property.2
              (PMF.pure (finish failed)) (PMF.pure (finish withheld)))
            (PMF.pure (finish truth)) := by
  have acting : ProtocolState.actor setup.program current.point = some owner := by
    rw [point, origin.actor_lift]
    rfl
  obtain ⟨finish, selected, law⟩ := owned_history_choice_law setup current trace owner acting
  obtain ⟨truth, failed, withheld, truthEq, failedEq, withheldEq, choices⟩ :=
    foreign_publication_choice_law setup values omission bad delivery origin current trace
      entry point survives
  refine ⟨finish, truth, failed, withheld, truthEq, failedEq, withheldEq, selected, ?_⟩
  rw [law, choices, mix_map, mix_map, PMF.pure_map, PMF.pure_map, PMF.pure_map]

omit [Fintype Player] in
/-- Relative to one literal source prefix, equal foreign cause reads mean
equal new signals and equal instruction classes. Every prior signal and
the complete focal own word are retained on both sides. -/
private theorem foreign_cause_read_extend_eq_iff
    (focal : Player) (before : setup.proposalRecoveryProtocol.History)
    (left right : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal before.state left)
    (rightLegal : setup.proposalRecoveryProtocol.Legal before.state right)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftSupport : leftState ∈
      (setup.proposalRecoveryProtocol.step before.state ⟨left, leftLegal⟩).support)
    (rightSupport : rightState ∈
      (setup.proposalRecoveryProtocol.step before.state ⟨right, rightLegal⟩).support)
    (leftSilent : left focal = none) (rightSilent : right focal = none) :
    setup.proposalRecoveryForeignCauseRead focal (before.extend leftLegal leftSupport) =
        setup.proposalRecoveryForeignCauseRead focal (before.extend rightLegal rightSupport) ↔
      (setup.proposalRecoverySignals.infoOf focal
          (before.trace.extend left leftLegal leftSupport)).1 =
        (setup.proposalRecoverySignals.infoOf focal
          (before.trace.extend right rightLegal rightSupport)).1 ∧
      proposalRecoveryForeignCauseJoint focal left =
        proposalRecoveryForeignCauseJoint focal right := by
  constructor
  · intro same
    refine ⟨congrArg (fun image => image.1.1.1) same, ?_⟩
    exact Option.some.inj (congrArg Prod.snd same)
  · rintro ⟨signal, instruction⟩
    apply Prod.ext
    · change setup.proposalRecoverySignals.withOwnPlayRecall.pushInfo focal
          (setup.proposalRecoveryModel.infoOf focal before.trace) (left focal)
            (setup.commitRecoveryPrivate focal leftState)
            (setup.commitRecoveryPublic leftState,
              setup.proposalRecoveryProposalOf before.state left) =
        setup.proposalRecoverySignals.withOwnPlayRecall.pushInfo focal
          (setup.proposalRecoveryModel.infoOf focal before.trace) (right focal)
            (setup.commitRecoveryPrivate focal rightState)
            (setup.commitRecoveryPublic rightState,
              setup.proposalRecoveryProposalOf before.state right)
      change (setup.commitRecoveryPrivate focal leftState,
          (setup.commitRecoveryPublic leftState,
            setup.proposalRecoveryProposalOf before.state left)) =
        (setup.commitRecoveryPrivate focal rightState,
          (setup.commitRecoveryPublic rightState,
            setup.proposalRecoveryProposalOf before.state right)) at signal
      rw [leftSilent, rightSilent]
      change (((setup.commitRecoveryPrivate focal leftState,
          (setup.commitRecoveryPublic leftState,
            setup.proposalRecoveryProposalOf before.state left)),
          (setup.proposalRecoveryModel.infoOf focal before.trace).1.1 ::
            (setup.proposalRecoveryModel.infoOf focal before.trace).1.2),
          (setup.proposalRecoveryModel.infoOf focal before.trace).2) =
        (((setup.commitRecoveryPrivate focal rightState,
          (setup.commitRecoveryPublic rightState,
            setup.proposalRecoveryProposalOf before.state right)),
          (setup.proposalRecoveryModel.infoOf focal before.trace).1.1 ::
            (setup.proposalRecoveryModel.infoOf focal before.trace).1.2),
          (setup.proposalRecoveryModel.infoOf focal before.trace).2)
      exact congrArg
        (fun current => ((current,
          (setup.proposalRecoveryModel.infoOf focal before.trace).1.1 ::
            (setup.proposalRecoveryModel.infoOf focal before.trace).1.2),
          (setup.proposalRecoveryModel.infoOf focal before.trace).2)) signal
    · exact congrArg some instruction

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- Withheld publication always installs failure, even when a completed
guard rejects it. Truthful publication installs its proper stored value
exactly when the actual completed checks accept that tentative value. -/
private theorem publication_result_of_proper
    {Γ : SourceCtx Player L} {name published : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (entry : Config Player L Γ)
    (value : L.Val payload) (stored : entry.state.get source = .success value) :
    (revealSuccessor published source entry false).state.get .here = .failure ∧
      (revealSuccessor published source entry true).state.get .here =
        if (entry.registry.completedBy (published := published) entry.revelations source).all
            (fun obligation => obligation.accepts
              (Revelations.reveal (published := published) entry.revelations source)
                (Env.cons (.success value) entry.state))
          then .success value else .failure := by
  constructor
  · simp only [revealSuccessor, Bool.false_eq_true, ite_false, Env.cons_get_here]
    split <;> rfl
  · simp only [revealSuccessor, ite_true, stored, Env.cons_get_here]

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- Truthful and failed disclosure have the same complete foreign observer
view precisely on an actually rejecting guard. Hidden stored values are
never compared unless the truthful public proposal has identified them. -/
private theorem publication_views_coalesce_iff
    {Γ : SourceCtx Player L} {name published : VarId} {owner : Player} {payload : L.Ty}
    (focal : Player) (foreign : owner ≠ focal)
    (source : HasVar Γ name (.commitment owner payload)) (entry : Config Player L Γ)
    (value : L.Val payload) (stored : entry.state.get source = .success value) :
    (revealSuccessor published source entry true).view focal =
        (revealSuccessor published source entry false).view focal ↔
      (entry.registry.completedBy (published := published) entry.revelations source).all
        (fun obligation => obligation.accepts
          (Revelations.reveal (published := published) entry.revelations source)
            (Env.cons (.success value) entry.state)) = false := by
  obtain ⟨withheld, truthful⟩ := publication_result_of_proper (published := published)
    source entry value stored
  constructor
  · intro same
    have head := congrArg
      (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
        view.1.cells published (.publication payload) .here) same
    change (revealSuccessor published source entry true).state.get .here =
      (revealSuccessor published source entry false).state.get .here at head
    rw [truthful, withheld] at head
    split at head
    · cases head
    · exact Bool.eq_false_iff.mpr (by assumption)
  · intro rejected
    apply Config.view_reveal_congr focal published source entry entry true false rfl
      (fun same => (foreign same).elim)
    apply congrArg SourceObservation.mk
    funext cellName cell member
    cases member with
    | here =>
        change (revealSuccessor published source entry true).state.get .here =
          (revealSuccessor published source entry false).state.get .here
        rw [truthful, withheld, rejected]
        rfl
    | there member => cases cell <;> rfl

/-- The three source publication weights are evaluated on their actual
observable classes. Distinct no-proposal labels never coalesce with either
proposed cause; the proposed causes coalesce exactly when their public
successors agree. This identity includes coincident truthful/failed points. -/
private theorem publication_class_atoms {α : Type*} [DecidableEq α]
    (omission delivery : Set.Icc (0 : ℝ) 1) (truth failed withheld : α)
    (truthWithheld : truth ≠ withheld) (failedWithheld : failed ≠ withheld) :
    let law := mix omission.val omission.property.1 omission.property.2
      (mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure failed) (PMF.pure withheld)) (PMF.pure truth)
    law withheld = ENNReal.ofReal (omission.val * (1 - delivery.val)) ∧
      law truth = ENNReal.ofReal (1 - omission.val) +
        (if failed = truth then ENNReal.ofReal (omission.val * delivery.val) else 0) ∧
      law failed = ENNReal.ofReal (omission.val * delivery.val) +
        (if truth = failed then ENNReal.ofReal (1 - omission.val) else 0) := by
  classical
  intro law
  constructor
  · simp only [law, mix_apply, PMF.pure_apply,
      Ne.symm failedWithheld, Ne.symm truthWithheld, ite_false, ite_true,
      mul_zero, zero_add, mul_one, add_zero]
    exact (ENNReal.ofReal_mul omission.property.1).symm
  · constructor
    · by_cases same : failed = truth
      · subst failed
        simp only [law, mix_apply, PMF.pure_apply,
          truthWithheld, ite_false, ite_true, mul_zero, mul_one, add_zero]
        rw [← ENNReal.ofReal_mul omission.property.1, add_comm]
      · simp only [law, mix_apply, PMF.pure_apply, same, Ne.symm same,
          truthWithheld, ite_false, ite_true, mul_zero,
          zero_add, mul_one, add_zero]
    · by_cases same : truth = failed
      · subst failed
        simp only [law, mix_apply, PMF.pure_apply,
          truthWithheld, ite_false, ite_true, mul_zero, mul_one, add_zero]
        rw [← ENNReal.ofReal_mul omission.property.1]
      · simp only [law, mix_apply, PMF.pure_apply, same, Ne.symm same,
          failedWithheld, ite_false, ite_true, mul_zero,
          mul_one, add_zero]
        exact (ENNReal.ofReal_mul omission.property.1).symm

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- These are the exact publication normalizers on the actual typed result
and proposal-presence classes. The accepting guard and rejecting guard cases
retain their different truthful/failed-disclosure preimages. -/
private theorem publication_typed_class_atoms
    {Γ : SourceCtx Player L} {name published : VarId} {owner : Player} {payload : L.Ty}
    (omission delivery : Set.Icc (0 : ℝ) 1) (focal : Player) (foreign : owner ≠ focal)
    (source : HasVar Γ name (.commitment owner payload)) (entry : Config Player L Γ)
    (value : L.Val payload) (stored : entry.state.get source = .success value) :
    let truthful := ((revealSuccessor published source entry true).view focal, true)
    let failed := ((revealSuccessor published source entry false).view focal, true)
    let withheld := ((revealSuccessor published source entry false).view focal, false)
    let accepted :=
      (entry.registry.completedBy (published := published) entry.revelations source).all
        (fun obligation => obligation.accepts
          (Revelations.reveal (published := published) entry.revelations source)
            (Env.cons (.success value) entry.state))
    let law := mix omission.val omission.property.1 omission.property.2
      (mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure failed) (PMF.pure withheld)) (PMF.pure truthful)
    law withheld = ENNReal.ofReal (omission.val * (1 - delivery.val)) ∧
      law truthful = ENNReal.ofReal (1 - omission.val) +
        (if accepted = false then ENNReal.ofReal (omission.val * delivery.val) else 0) ∧
      law failed = ENNReal.ofReal (omission.val * delivery.val) +
        (if accepted = false then ENNReal.ofReal (1 - omission.val) else 0) := by
  classical
  intro truthful failed withheld accepted law
  have truthWithheld : truthful ≠ withheld := by
    intro equal
    have impossible : true = false := congrArg Prod.snd equal
    cases impossible
  have failedWithheld : failed ≠ withheld := by
    intro equal
    have impossible : true = false := congrArg Prod.snd equal
    cases impossible
  have coalesce : truthful = failed ↔ accepted = false := by
    constructor
    · intro same
      exact (publication_views_coalesce_iff (published := published) focal foreign
        source entry value stored).mp (congrArg Prod.fst same)
    · intro rejected
      exact Prod.ext ((publication_views_coalesce_iff (published := published) focal foreign
        source entry value stored).mpr rejected) rfl
  have reverseCoalesce : failed = truthful ↔ accepted = false :=
    eq_comm.trans coalesce
  have atoms := publication_class_atoms omission delivery truthful failed withheld
    truthWithheld failedWithheld
  simpa only [coalesce, reverseCoalesce] using atoms

omit [Fintype Player] [IExpr.ResultTypes L] in
/-- The actual public proposal and typed publication result synchronize the
three class normalizers. With no proposal, hidden stored values and guard
verdicts need not agree. With a proposal, the literal public value supplies
the common tentative guard operand. -/
private theorem publication_typed_classes_eq
    {Γ : SourceCtx Player L} {name published : VarId} {owner : Player} {payload : L.Ty}
    (omission delivery : Set.Icc (0 : ℝ) 1) (focal : Player) (foreign : owner ≠ focal)
    (source : HasVar Γ name (.commitment owner payload))
    (left right : Config Player L Γ) (metadata : left.MetadataEq right)
    (before : left.view focal = right.view focal)
    (leftValue rightValue : L.Val payload)
    (leftStored : left.state.get source = .success leftValue)
    (rightStored : right.state.get source = .success rightValue)
    (leftBit leftProposed rightBit rightProposed : Bool)
    (proposal : (if leftBit || leftProposed then some leftValue else none) =
      (if rightBit || rightProposed then some rightValue else none))
    (after : (revealSuccessor published source left leftBit).view focal =
      (revealSuccessor published source right rightBit).view focal) :
    let leftLaw := mix omission.val omission.property.1 omission.property.2
      (mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure ((revealSuccessor published source left false).view focal, true))
        (PMF.pure ((revealSuccessor published source left false).view focal, false)))
      (PMF.pure ((revealSuccessor published source left true).view focal, true))
    let rightLaw := mix omission.val omission.property.1 omission.property.2
      (mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure ((revealSuccessor published source right false).view focal, true))
        (PMF.pure ((revealSuccessor published source right false).view focal, false)))
      (PMF.pure ((revealSuccessor published source right true).view focal, true))
    leftLaw ((revealSuccessor published source left leftBit).view focal,
        leftBit || leftProposed) =
      rightLaw ((revealSuccessor published source right rightBit).view focal,
        rightBit || rightProposed) := by
  classical
  intro leftLaw rightLaw
  have leftAtoms := publication_typed_class_atoms (published := published)
    omission delivery focal foreign
    source left leftValue leftStored
  have rightAtoms := publication_typed_class_atoms (published := published)
    omission delivery focal foreign
    source right rightValue rightStored
  have presence : (leftBit || leftProposed) = (rightBit || rightProposed) := by
    have selected := congrArg Option.isSome proposal
    cases leftBit <;> cases leftProposed <;> cases rightBit <;> cases rightProposed <;>
      simp at selected ⊢
  cases exposed : leftBit || leftProposed with
  | false =>
      have rightExposed : (rightBit || rightProposed) = false := presence.symm.trans exposed
      have leftHidden : leftBit = false := by
        cases leftBit with
        | false => rfl
        | true => simp at exposed
      have rightHidden : rightBit = false := by
        cases rightBit with
        | false => rfl
        | true => simp at rightExposed
      rw [rightExposed, leftHidden, rightHidden]
      exact leftAtoms.1.trans rightAtoms.1.symm
  | true =>
      have rightExposed : (rightBit || rightProposed) = true := presence.symm.trans exposed
      have valueEq : leftValue = rightValue := by
        rw [exposed, rightExposed] at proposal
        exact Option.some.inj proposal
      subst rightValue
      have checks := completed_checks_eq_of_public (published := published)
        source left right metadata
        (fun cell => congrArg
          (fun view : DecisionView focal Γ => view.1.cells _ _ cell) before)
        (fun cell => congrArg
          (fun view : DecisionView focal Γ => view.1.cells _ _ cell) before) leftValue
      have headEq :
          (revealSuccessor published source left leftBit).state.get .here =
            (revealSuccessor published source right rightBit).state.get .here :=
        congrArg (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
          view.1.cells published (.publication payload) .here) after
      obtain ⟨leftWithheld, leftTruth⟩ :=
        publication_result_of_proper (published := published) source left leftValue leftStored
      obtain ⟨rightWithheld, rightTruth⟩ :=
        publication_result_of_proper (published := published) source right leftValue rightStored
      rw [rightExposed]
      cases leftBit with
      | false =>
          cases rightBit with
          | false =>
              rw [leftAtoms.2.2, rightAtoms.2.2, checks]
          | true =>
              have rejected :
                  (right.registry.completedBy (published := published)
                    right.revelations source).all (fun obligation => obligation.accepts
                      (Revelations.reveal (published := published) right.revelations source)
                        (Env.cons (.success leftValue) right.state)) = false := by
                rw [leftWithheld, rightTruth] at headEq
                split at headEq
                · cases headEq
                · exact Bool.eq_false_iff.mpr (by assumption)
              rw [leftAtoms.2.2, rightAtoms.2.1, checks, rejected]
              simp only [ite_true]
              exact add_comm _ _
      | true =>
          cases rightBit with
          | false =>
              have rejected :
                  (left.registry.completedBy (published := published)
                    left.revelations source).all (fun obligation => obligation.accepts
                      (Revelations.reveal (published := published) left.revelations source)
                        (Env.cons (.success leftValue) left.state)) = false := by
                rw [leftTruth, rightWithheld] at headEq
                split at headEq
                · cases headEq
                · exact Bool.eq_false_iff.mpr (by assumption)
              rw [leftAtoms.2.1, rightAtoms.2.2, ← checks, rejected]
              simp only [ite_true]
              exact add_comm _ _
          | true =>
              rw [leftAtoms.2.1, rightAtoms.2.1, checks]

omit [Fintype Player] in
private theorem suffix_observe_congr
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : Vegas.SourceProgram.ProtocolState program → Vegas.SourceProgram.ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (focal : Player) :
    ∀ first second, ProtocolState.observe focal program first =
        ProtocolState.observe focal program second →
      ProtocolState.observe focal whole (lift first) =
        ProtocolState.observe focal whole (lift second) := by
  induction origin with
  | initial => intro first second same; exact same
  | sampleTail fresh law next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | commitTail fresh guard next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)
  | revealTail fresh selected unresolved next previous ih =>
      intro first second same
      exact ih (.inr first) (.inr second) (congrArg Sum.inr same)

omit [Fintype Player] in
/-- A source proposal reads the exposed bit and the current typed store.
The distinction between truthful and failed delivery is not consulted. -/
private theorem recovery_proposal_eq_of_discloses :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : Vegas.SourceProgram.ProtocolState program)
      (left right : Player → Option (ProposalRecoveryMove Player L)),
      (∀ owner, (left owner).map ProposalRecoveryMove.discloses =
        (right owner).map ProposalRecoveryMove.discloses) →
      ProtocolState.recoveryProposal program point left =
        ProtocolState.recoveryProposal program point right
  | _, _, .ret _, _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, left, right, same => by
      cases point with
      | inl _ => rfl
      | inr later =>
          exact congrArg (Option.map fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2))
            (recovery_proposal_eq_of_discloses next later left right same)
  | _, _, .commit _ _ _ _ next, point, left, right, same => by
      cases point with
      | inl _ => rfl
      | inr later =>
          exact congrArg (Option.map fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2))
            (recovery_proposal_eq_of_discloses next later left right same)
  | _, _, .reveal _ owner _ _ _ _ next, point, left, right, same => by
      cases point with
      | inl _ => simp only [ProtocolState.recoveryProposal, Sum.elim_inl, same owner]
      | inr later =>
          exact congrArg (Option.map fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2))
            (recovery_proposal_eq_of_discloses next later left right same)

omit [Fintype Player] in
theorem publication_cause_joint_eq_iff
    (focal owner : Player) (foreign : owner ≠ focal) (name : VarId)
    (leftBit leftProposed rightBit rightProposed : Bool) :
    proposalRecoveryForeignCauseJoint focal
        (setup.proposalRecoveryProtocol.singletonJoint owner
          (some ⟨⟨.reveal owner name leftBit, false⟩, leftProposed⟩)) =
      proposalRecoveryForeignCauseJoint focal
        (setup.proposalRecoveryProtocol.singletonJoint owner
          (some ⟨⟨.reveal owner name rightBit, false⟩, rightProposed⟩)) ↔
      (leftBit || leftProposed) = (rightBit || rightProposed) := by
  constructor
  · intro same
    have selected := congrFun same owner
    simpa only [proposalRecoveryForeignCauseJoint, ExecutionProtocol.singletonJoint_self,
      Option.map_some, foreign, ite_false, ProposalRecoveryMove.discloses,
      OwnAction.disclosure, Option.some.injEq, Sum.inr.injEq, Prod.mk.injEq,
      true_and] using selected
  · intro same
    funext other
    by_cases atOwner : other = owner
    · subst other
      simp only [proposalRecoveryForeignCauseJoint, ExecutionProtocol.singletonJoint_self,
        Option.map_some, foreign, ite_false, ProposalRecoveryMove.discloses,
        OwnAction.disclosure, same]
    · simp only [proposalRecoveryForeignCauseJoint,
        ExecutionProtocol.singletonJoint_of_ne _ _ _ atOwner, Option.map_none]

omit [Fintype Player] in
/-- On one genuine publication row the complete source observable has
exactly the fibers of the new typed focal view and proposal presence. The
proof keeps the original prefix and the actual selected source transitions. -/
theorem publication_history_cause_eq_iff
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded)
    (focal : Player) (foreign : owner ≠ focal)
    (leftBit leftProposed rightBit rightProposed : Bool)
    (leftLegal : setup.proposalRecoveryProtocol.Legal (some current)
      (setup.proposalRecoveryProtocol.singletonJoint owner
        (some ⟨⟨.reveal owner name leftBit, false⟩, leftProposed⟩)))
    (rightLegal : setup.proposalRecoveryProtocol.Legal (some current)
      (setup.proposalRecoveryProtocol.singletonJoint owner
        (some ⟨⟨.reveal owner name rightBit, false⟩, rightProposed⟩)))
    {leftTarget rightTarget : setup.proposalRecoveryProtocol.State}
    (leftSupport : leftTarget ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨_, leftLegal⟩).support)
    (rightSupport : rightTarget ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨_, rightLegal⟩).support) :
    setup.proposalRecoveryForeignCauseRead focal
        ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
          leftLegal leftSupport) =
      setup.proposalRecoveryForeignCauseRead focal
        ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
          rightLegal rightSupport) ↔
      (revealSuccessor published source entry leftBit).view focal =
        (revealSuccessor published source entry rightBit).view focal ∧
      (leftBit || leftProposed) = (rightBit || rightProposed) := by
  classical
  let leftJoint := setup.proposalRecoveryProtocol.singletonJoint owner
    (some (⟨⟨.reveal owner name leftBit, false⟩, leftProposed⟩ : ProposalRecoveryMove Player L))
  let rightJoint := setup.proposalRecoveryProtocol.singletonJoint owner
    (some (⟨⟨.reveal owner name rightBit, false⟩, rightProposed⟩ : ProposalRecoveryMove Player L))
  let leftResult : Config Player L ((published, .publication payload) :: Γ) :=
    revealSuccessor published source entry leftBit
  let rightResult : Config Player L ((published, .publication payload) :: Γ) :=
    revealSuccessor published source entry rightBit
  let leftE : Finset Player := match leftResult.state.get .here with
    | .failure => insert owner current.excluded
    | .success _ => current.excluded
  let rightE : Finset Player := match rightResult.state.get .here with
    | .failure => insert owner current.excluded
    | .success _ => current.excluded
  let leftNext : CommitRecoveryState setup.program := CommitRecoveryState.atPoint
    (lift (.inr (ProtocolState.entry suffix leftResult))) leftE current.generation
  let rightNext : CommitRecoveryState setup.program := CommitRecoveryState.atPoint
    (lift (.inr (ProtocolState.entry suffix rightResult))) rightE current.generation
  have leftPure : current.step (proposalRecoveryJoint leftJoint) = PMF.pure leftNext := by
    simpa only [leftJoint, ExecutionProtocol.singletonJoint_self, Option.map_some,
      OwnAction.disclosure] using publication_step_pure setup origin current trace entry
        point survives leftJoint
  have rightPure : current.step (proposalRecoveryJoint rightJoint) = PMF.pure rightNext := by
    simpa only [rightJoint, ExecutionProtocol.singletonJoint_self, Option.map_some,
      OwnAction.disclosure] using publication_step_pure setup origin current trace entry
        point survives rightJoint
  have leftEndpoint : leftTarget = some leftNext := by
    change leftTarget ∈ ((current.step (proposalRecoveryJoint leftJoint)).map some).support
      at leftSupport
    rw [leftPure, PMF.pure_map, PMF.mem_support_pure_iff] at leftSupport
    exact leftSupport
  have rightEndpoint : rightTarget = some rightNext := by
    change rightTarget ∈ ((current.step (proposalRecoveryJoint rightJoint)).map some).support
      at rightSupport
    rw [rightPure, PMF.pure_map, PMF.mem_support_pure_iff] at rightSupport
    exact rightSupport
  subst leftTarget
  subst rightTarget
  rw [foreign_cause_read_extend_eq_iff setup focal ⟨some current, trace⟩
    leftJoint rightJoint leftLegal rightLegal leftSupport rightSupport
      (ExecutionProtocol.singletonJoint_of_ne _ _ _ (Ne.symm foreign))
      (ExecutionProtocol.singletonJoint_of_ne _ _ _ (Ne.symm foreign)),
    publication_cause_joint_eq_iff setup focal owner foreign name]
  constructor
  · rintro ⟨signal, exposed⟩
    refine ⟨?_, exposed⟩
    have privateView := congrArg Prod.fst signal
    change some (ProtocolState.observe focal setup.program
        (lift (.inr (ProtocolState.entry suffix leftResult)))) =
      some (ProtocolState.observe focal setup.program
        (lift (.inr (ProtocolState.entry suffix rightResult)))) at privateView
    have localView := origin.observe_reflect focal _ _ (Option.some.inj privateView)
    have tailView := Sum.inr.inj localView
    have entryView := congrArg (ProtocolView.entryView focal suffix) tailView
    simpa only [ProtocolView.entryView_observe_entry] using entryView
  · rintro ⟨typed, exposed⟩
    have headEq : leftResult.state.get .here = rightResult.state.get .here :=
      congrArg (fun view : DecisionView focal ((published, .publication payload) :: Γ) =>
        view.1.cells published (.publication payload) .here) typed
    have exclusions : leftE = rightE := by
      unfold leftE rightE
      rw [headEq]
    have privateView : setup.commitRecoveryPrivate focal (some leftNext) =
        setup.commitRecoveryPrivate focal (some rightNext) := by
      apply congrArg some
      exact suffix_observe_congr origin focal _ _
        (congrArg Sum.inr (ProtocolState.observe_entry_congr focal suffix
          leftResult rightResult typed))
    have controls : setup.commitRecoveryPublic (some leftNext) =
        setup.commitRecoveryPublic (some rightNext) := by
      simp only [commitRecoveryPublic, leftNext, rightNext, CommitRecoveryState.atPoint,
        origin.remaining_lift, ProtocolState.remaining, Sum.elim_inr,
        ProtocolState.remaining_entry, exclusions]
    have proposal : setup.proposalRecoveryProposalOf (some current) leftJoint =
        setup.proposalRecoveryProposalOf (some current) rightJoint := by
      unfold proposalRecoveryProposalOf
      simp only [Option.bind_some]
      apply congrArg (Option.map _)
      apply recovery_proposal_eq_of_discloses setup.program current.point
      intro other
      by_cases atOwner : other = owner
      · subst other
        simp only [survives, ite_false, leftJoint, rightJoint,
          ExecutionProtocol.singletonJoint_self, Option.map_some,
          ProposalRecoveryMove.discloses, OwnAction.disclosure, exposed]
      · simp only [leftJoint, rightJoint,
          ExecutionProtocol.singletonJoint_of_ne _ _ _ atOwner]
    refine ⟨?_, exposed⟩
    change (setup.commitRecoveryPrivate focal (some leftNext),
        (setup.commitRecoveryPublic (some leftNext),
          setup.proposalRecoveryProposalOf (some current) leftJoint)) =
      (setup.commitRecoveryPrivate focal (some rightNext),
        (setup.commitRecoveryPublic (some rightNext),
          setup.proposalRecoveryProposalOf (some current) rightJoint))
    rw [privateView, controls, proposal]

/-- The actual full-history one-step observable has the same atom as the
typed publication class mixture. This is a fiber identity at the selected
actual transition, including zero-mass cause coordinates. -/
private theorem publication_typed_class_mass
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
    {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
    {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
    {suffix : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}
    {lift : Vegas.SourceProgram.ProtocolState
      (.reveal published owner name fresh source unresolved suffix) →
        Vegas.SourceProgram.ProtocolState setup.program}
    (origin : ProtocolSuffix setup.program
      (.reveal published owner name fresh source unresolved suffix) lift)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current)) (entry : Config Player L Γ)
    (point : current.point = lift (.inl entry)) (survives : owner ∉ current.excluded)
    (focal : Player) (foreign : owner ≠ focal) (bit proposed : Bool)
    (legal : setup.proposalRecoveryProtocol.Legal (some current)
      (setup.proposalRecoveryProtocol.singletonJoint owner
        (some ⟨⟨.reveal owner name bit, false⟩, proposed⟩)))
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨_, legal⟩).support) :
    let law := setup.proposalRecoveryModel.runBehavioralFrom
      (setup.proposalRecoveryNormalizedTrembledProfile
        omission.val omission.property.1 omission.property.2
        bad.val bad.property.1 bad.property.2
        delivery.val delivery.property.1 delivery.property.2 values) 1 ⟨some current, trace⟩
    let observable := setup.proposalRecoveryForeignCauseRead focal
    let typed := mix omission.val omission.property.1 omission.property.2
      (mix delivery.val delivery.property.1 delivery.property.2
        (PMF.pure ((revealSuccessor published source entry false).view focal, true))
        (PMF.pure ((revealSuccessor published source entry false).view focal, false)))
      (PMF.pure ((revealSuccessor published source entry true).view focal, true))
    (law.map observable)
        (observable ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
          legal supported)) =
      typed ((revealSuccessor published source entry bit).view focal, bit || proposed) := by
  classical
  intro law observable typed
  obtain ⟨finish, truth, failed, withheld, truthEq, failedEq, withheldEq, selected, runLaw⟩ :=
    foreign_publication_history_law setup values omission bad delivery origin current trace
      entry point survives
  have truthPath := selected truth
  have failedPath := selected failed
  have withheldPath := selected withheld
  rw [truthEq] at truthPath
  rw [failedEq] at failedPath
  rw [withheldEq] at withheldPath
  obtain ⟨_truthTarget, truthLegal, truthSupport, truthHistory⟩ := truthPath
  obtain ⟨_failedTarget, failedLegal, failedSupport, failedHistory⟩ := failedPath
  obtain ⟨_withheldTarget, withheldLegal, withheldSupport, withheldHistory⟩ := withheldPath
  let actual : setup.proposalRecoveryProtocol.History :=
    (⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported
  have truthful : observable (finish truth) = observable actual ↔
      ((revealSuccessor published source entry true).view focal, true) =
        ((revealSuccessor published source entry bit).view focal, bit || proposed) := by
    rw [truthHistory]
    simpa only [observable, actual, History.extend, ProposalRecoveryMove.ordinary,
      Prod.mk.injEq, Bool.true_or, Bool.false_or, Bool.or_false] using
      publication_history_cause_eq_iff setup origin current trace entry point survives
        focal foreign true false bit proposed truthLegal legal truthSupport supported
  have failure : observable (finish failed) = observable actual ↔
      ((revealSuccessor published source entry false).view focal, true) =
        ((revealSuccessor published source entry bit).view focal, bit || proposed) := by
    rw [failedHistory]
    simpa only [observable, actual, History.extend, ProposalRecoveryMove.failedDisclosure,
      Prod.mk.injEq, Bool.true_or, Bool.false_or, Bool.or_false] using
      publication_history_cause_eq_iff setup origin current trace entry point survives
        focal foreign false true bit proposed failedLegal legal failedSupport supported
  have hidden : observable (finish withheld) = observable actual ↔
      ((revealSuccessor published source entry false).view focal, false) =
        ((revealSuccessor published source entry bit).view focal, bit || proposed) := by
    rw [withheldHistory]
    simpa only [observable, actual, History.extend, ProposalRecoveryMove.ordinary,
      Prod.mk.injEq, Bool.true_or, Bool.false_or, Bool.or_false] using
      publication_history_cause_eq_iff setup origin current trace entry point survives
        focal foreign false false bit proposed withheldLegal legal withheldSupport supported
  change ((law.map observable) (observable actual)) = _
  rw [show law = _ from runLaw, mix_map, mix_map, PMF.pure_map,
    PMF.pure_map, PMF.pure_map]
  have truthfulReverse : observable actual = observable (finish truth) ↔
      ((revealSuccessor published source entry bit).view focal, bit || proposed) =
        ((revealSuccessor published source entry true).view focal, true) :=
    eq_comm.trans (truthful.trans eq_comm)
  have failureReverse : observable actual = observable (finish failed) ↔
      ((revealSuccessor published source entry bit).view focal, bit || proposed) =
        ((revealSuccessor published source entry false).view focal, true) :=
    eq_comm.trans (failure.trans eq_comm)
  have hiddenReverse : observable actual = observable (finish withheld) ↔
      ((revealSuccessor published source entry bit).view focal, bit || proposed) =
        ((revealSuccessor published source entry false).view focal, false) :=
    eq_comm.trans (hidden.trans eq_comm)
  simp only [typed, mix_apply, PMF.pure_apply,
    truthfulReverse, failureReverse, hiddenReverse]
  split_ifs <;> rfl

omit [Fintype Player] in
/-- Equal proposal reads reflect to one common syntax suffix. The added
absolute source-rank offsets are injective and retain the literal typed
value; no compiler or native source decoder is used. -/
theorem suffix_proposal_eq_iff
    {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : Vegas.SourceProgram.ProtocolState program → Vegas.SourceProgram.ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ first second (left right : Player → Option (ProposalRecoveryMove Player L)),
      ProtocolState.recoveryProposal whole (lift first) left =
          ProtocolState.recoveryProposal whole (lift second) right ↔
        ProtocolState.recoveryProposal program first left =
          ProtocolState.recoveryProposal program second right := by
  have shift : Function.Injective (fun pair : Nat × Sigma L.Val => (pair.1 + 1, pair.2)) := by
    intro first second same
    apply Prod.ext
    · exact Nat.add_right_cancel (congrArg Prod.fst same)
    · have projected := congrArg (fun pair : Nat × Sigma L.Val => pair.2) same
      change first.2 = second.2 at projected
      exact projected
  have mapped (first second : Option (Nat × Sigma L.Val)) :
      first.map (fun pair => (pair.1 + 1, pair.2)) =
        second.map (fun pair => (pair.1 + 1, pair.2)) ↔ first = second := by
    constructor
    · intro same
      cases first with
      | none =>
          cases second with
          | none => rfl
          | some _ => cases same
      | some first =>
          cases second with
          | none => cases same
          | some second => exact congrArg some (shift (Option.some.inj same))
    · exact congrArg (Option.map _)
  induction origin with
  | initial => intro first second left right; rfl
  | sampleTail fresh law next previous ih =>
      intro first second left right
      rw [ih]
      exact mapped _ _
  | commitTail fresh guard next previous ih =>
      intro first second left right
      rw [ih]
      exact mapped _ _
  | revealTail fresh selected unresolved next previous ih =>
      intro first second left right
      rw [ih]
      exact mapped _ _

omit [Fintype Player] in
theorem proposal_read_eq_of_public_proposal
    (left right : CommitRecoveryState setup.program)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (same : setup.proposalRecoveryProposalOf (some left) leftJoint =
      setup.proposalRecoveryProposalOf (some right) rightJoint) :
    ProtocolState.recoveryProposal setup.program left.point
        (fun owner => if owner ∈ left.excluded then none else leftJoint owner) =
      ProtocolState.recoveryProposal setup.program right.point
        (fun owner => if owner ∈ right.excluded then none else rightJoint owner) := by
  have decoded := congrArg (Option.map fun proposal : ProposalRecoveryProposal L =>
    (proposal.address.event, (⟨proposal.payload, proposal.value⟩ : Sigma L.Val))) same
  have eta (pair : Nat × Sigma L.Val) : (pair.1, ⟨pair.2.1, pair.2.2⟩) = pair := by
    cases pair with
    | mk rank value => cases value; rfl
  simp only [proposalRecoveryProposalOf, Option.bind_some, Option.map_map,
    Function.comp_def, eta] at decoded
  change Option.map id _ = Option.map id _ at decoded
  simpa only [Option.map_id, id_eq] using decoded

omit [Fintype Player] in
theorem source_current_of_signals (focal : Player)
    (left right : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoverySignals.infoOf focal left.trace =
      setup.proposalRecoverySignals.infoOf focal right.trace) :
    (setup.commitRecoveryPrivate focal left.state, setup.commitRecoveryPublic left.state) =
      (setup.commitRecoveryPrivate focal right.state, setup.commitRecoveryPublic right.state) := by
  have semantic := congrArg (setup.proposalRecoveryEraseBaseInfo focal) same
  rw [setup.proposalRecoveryEraseBaseInfo_observed,
    setup.proposalRecoveryEraseBaseInfo_observed] at semantic
  have current := congrArg Prod.fst semantic
  rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
  exact current

omit [Fintype Player] in
private theorem source_metadata_of_signals (focal : Player)
    (left right : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoverySignals.infoOf focal left.trace =
      setup.proposalRecoverySignals.infoOf focal right.trace) :
    match left.state, right.state with
    | none, none => True
    | some first, some second => first.MetadataEq second
    | _, _ => False := by
  have semantic := congrArg (setup.proposalRecoveryEraseBaseInfo focal) same
  rw [setup.proposalRecoveryEraseBaseInfo_observed,
    setup.proposalRecoveryEraseBaseInfo_observed] at semantic
  have publicWord := congrArg (fun information : setup.commitRecoverySignals.InfoState focal =>
    (information.1 :: information.2).map fun signal =>
      (signal.1.map (ProtocolView.publicOnly focal setup.program), signal.2)) semantic
  have related := setup.commitRecovery_metadata_of_publicRecall focal
    (setup.proposalRecoveryEraseTrace left.trace) (setup.proposalRecoveryEraseTrace right.trace)
      publicWord
  rcases left with ⟨leftState, leftTrace⟩
  rcases right with ⟨rightState, rightTrace⟩
  cases leftState <;> cases rightState <;> exact related

/-- The paired commitment rows may choose unrelated private values and actual
closure branches. Their common next E determines the same class scalar. -/
private theorem foreign_commit_classes_eq_of_next_excluded
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal owner : Player)
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.proposalRecoveryProtocol.Trace (some left))
    (rightTrace : setup.proposalRecoveryProtocol.Trace (some right))
    (leftCommit : ProtocolState.atCommit setup.program left.point = true)
    (rightCommit : ProtocolState.atCommit setup.program right.point = true)
    (leftActor : ProtocolState.actor setup.program left.point = some owner)
    (rightActor : ProtocolState.actor setup.program right.point = some owner)
    (leftSurvives : owner ∉ left.excluded) (rightSurvives : owner ∉ right.excluded)
    (foreign : owner ≠ focal)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal (some left) leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal (some right) rightJoint)
    (leftNext rightNext : CommitRecoveryState setup.program)
    (leftSupport : some leftNext ∈
      (setup.proposalRecoveryProtocol.step (some left) ⟨leftJoint, leftLegal⟩).support)
    (rightSupport : some rightNext ∈
      (setup.proposalRecoveryProtocol.step (some right) ⟨rightJoint, rightLegal⟩).support)
    (nextE : leftNext.excluded = rightNext.excluded)
    (leftGood : ¬ setup.GeneratedPreparationHistory owner
      ((⟨some left, leftTrace⟩ : setup.proposalRecoveryProtocol.History).extend
        leftLegal leftSupport))
    (rightGood : ¬ setup.GeneratedPreparationHistory owner
      ((⟨some right, rightTrace⟩ : setup.proposalRecoveryProtocol.History).extend
        rightLegal rightSupport)) :
    (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      ⟨some left, leftTrace⟩ leftJoint leftLegal leftSupport).1 =
      (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
        ⟨some right, rightTrace⟩ rightJoint rightLegal rightSupport).1 := by
  rw [foreign_commit_class_of_next_excluded setup values omission bad delivery focal owner
      left leftTrace leftCommit leftActor leftSurvives foreign leftJoint leftLegal leftNext
        leftSupport leftGood,
    foreign_commit_class_of_next_excluded setup values omission bad delivery focal owner
      right rightTrace rightCommit rightActor rightSurvives foreign rightJoint rightLegal rightNext
        rightSupport rightGood, nextE]

private theorem foreign_publication_classes_eq_of_actual_guards
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (_omissionPositive : 0 < omission.val) (_omissionBelow : omission.val < 1)
    (_badBelow : bad.val < 1) (_deliveryPositive : 0 < delivery.val)
    (_deliveryBelow : delivery.val < 1) (focal owner : Player)
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.proposalRecoveryProtocol.Trace (some left))
    (rightTrace : setup.proposalRecoveryProtocol.Trace (some right))
    (leftNoncommit : ProtocolState.atCommit setup.program left.point = false)
    (_rightNoncommit : ProtocolState.atCommit setup.program right.point = false)
    (leftActor : ProtocolState.actor setup.program left.point = some owner)
    (rightActor : ProtocolState.actor setup.program right.point = some owner)
    (leftSurvives : owner ∉ left.excluded) (rightSurvives : owner ∉ right.excluded)
    (foreign : owner ≠ focal)
    (leftJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal (some left) leftJoint)
    {leftTarget : setup.proposalRecoveryProtocol.State}
    (leftSupport : leftTarget ∈
      (setup.proposalRecoveryProtocol.step (some left) ⟨leftJoint, leftLegal⟩).support)
    (rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (rightLegal : setup.proposalRecoveryProtocol.Legal (some right) rightJoint)
    {rightTarget : setup.proposalRecoveryProtocol.State}
    (rightSupport : rightTarget ∈
      (setup.proposalRecoveryProtocol.step (some right) ⟨rightJoint, rightLegal⟩).support)
    (metadata : ProtocolState.MetadataEq setup.program left.point right.point)
    (view : ProtocolState.observe focal setup.program left.point =
      ProtocolState.observe focal setup.program right.point)
    (next : (setup.proposalRecoverySignals.infoOf focal
        (leftTrace.extend leftJoint leftLegal leftSupport)).1 =
      (setup.proposalRecoverySignals.infoOf focal
        (rightTrace.extend rightJoint rightLegal rightSupport)).1)
    (leftValues : ProtocolState.BindingsHoldValues owner setup.program left.point)
    (rightValues : ProtocolState.BindingsHoldValues owner setup.program right.point) :
    (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      ⟨some left, leftTrace⟩ leftJoint leftLegal leftSupport).1 =
      (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
        ⟨some right, rightTrace⟩ rightJoint rightLegal rightSupport).1 := by
  classical
  obtain ⟨Γ, O, published, name, payload, fresh, source, unresolved, suffix,
    lift, leftEntry, origin, leftPoint, _names⟩ := source_reveal_entry setup.program
      left.point owner setup.namesNodup leftNoncommit leftActor
  change left.point = lift (.inl leftEntry) at leftPoint
  obtain ⟨rightLocal, rightPoint, localMetadata⟩ :=
    metadata_restrict_to_suffix origin (.inl leftEntry) right.point
      (by rw [← leftPoint]; exact metadata)
  cases rightLocal with
  | inr _ => cases localMetadata
  | inl rightEntry =>
      have oldGlobal : ProtocolState.observe focal setup.program (lift (.inl leftEntry)) =
          ProtocolState.observe focal setup.program (lift (.inl rightEntry)) := by
        rw [← leftPoint, ← rightPoint]
        exact view
      have oldView : leftEntry.view focal = rightEntry.view focal :=
        Sum.inl.inj (origin.observe_reflect focal (.inl leftEntry) (.inl rightEntry) oldGlobal)
      have leftProper : leftEntry.BindingsHoldValues owner :=
        (origin.bindingsHoldValues_lift owner (.inl leftEntry)).mp
          (leftPoint ▸ leftValues)
      have rightProper : rightEntry.BindingsHoldValues owner :=
        (origin.bindingsHoldValues_lift owner (.inl rightEntry)).mp
          (rightPoint ▸ rightValues)
      obtain ⟨leftValue, leftStored⟩ := leftProper source
      obtain ⟨rightValue, rightStored⟩ := rightProper source
      have leftSingleton : leftJoint =
          setup.proposalRecoveryProtocol.singletonJoint owner (leftJoint owner) := by
        funext other
        by_cases same : other = owner
        · subst other
          exact (ExecutionProtocol.singletonJoint_self setup.proposalRecoveryProtocol
            owner (leftJoint owner)).symm
        · have inactive : ¬ setup.proposalRecoveryProtocol.active (some left) other := by
            intro active
            exact same (Option.some.inj (active.1.symm.trans leftActor))
          rw [ExecutionProtocol.singletonJoint_of_ne _ _ _ same]
          exact LegalOption.eq_none_of_inactive _
            (setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal other) inactive
      have rightSingleton : rightJoint =
          setup.proposalRecoveryProtocol.singletonJoint owner (rightJoint owner) := by
        funext other
        by_cases same : other = owner
        · subst other
          exact (ExecutionProtocol.singletonJoint_self setup.proposalRecoveryProtocol
            owner (rightJoint owner)).symm
        · have inactive : ¬ setup.proposalRecoveryProtocol.active (some right) other := by
            intro active
            exact same (Option.some.inj (active.1.symm.trans rightActor))
          rw [ExecutionProtocol.singletonJoint_of_ne _ _ _ same]
          exact LegalOption.eq_none_of_inactive _
            (setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal other) inactive
      have compare (leftBit leftProposed rightBit rightProposed : Bool)
          (leftSelected : leftJoint owner =
            some ⟨⟨.reveal owner name leftBit, false⟩, leftProposed⟩)
          (rightSelected : rightJoint owner =
            some ⟨⟨.reveal owner name rightBit, false⟩, rightProposed⟩) :
          (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
            ⟨some left, leftTrace⟩ leftJoint leftLegal leftSupport).1 =
            (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
              ⟨some right, rightTrace⟩ rightJoint rightLegal rightSupport).1 := by
        have leftEq := leftSingleton.trans (congrArg
          (setup.proposalRecoveryProtocol.singletonJoint owner) leftSelected)
        have rightEq := rightSingleton.trans (congrArg
          (setup.proposalRecoveryProtocol.singletonJoint owner) rightSelected)
        subst leftJoint
        subst rightJoint
        have leftMass := publication_typed_class_mass setup values omission bad delivery
          origin left leftTrace leftEntry leftPoint leftSurvives focal foreign
            leftBit leftProposed leftLegal leftSupport
        have rightMass := publication_typed_class_mass setup values omission bad delivery
          origin right rightTrace rightEntry rightPoint rightSurvives focal foreign
            rightBit rightProposed rightLegal rightSupport
        have proposal : (if leftBit || leftProposed then some leftValue else none) =
            (if rightBit || rightProposed then some rightValue else none) := by
          have publicProposal := congrArg (fun signal => signal.2.2) next
          have raw := proposal_read_eq_of_public_proposal setup left right _ _ publicProposal
          rw [leftPoint, rightPoint] at raw
          have localProposal := (suffix_proposal_eq_iff origin _ _ _ _).mp raw
          have exposed :
              (if leftBit || leftProposed then some (0, (⟨payload, leftValue⟩ : Sigma L.Val))
                else none) =
              (if rightBit || rightProposed then some (0, (⟨payload, rightValue⟩ : Sigma L.Val))
                else none) := by
            simpa only [ProtocolState.recoveryProposal, Sum.elim_inl,
              leftSurvives, rightSurvives, ite_false,
              ExecutionProtocol.singletonJoint_self, Option.map_some,
              Option.getD_some, ProposalRecoveryMove.discloses,
              OwnAction.disclosure, leftStored, rightStored] using localProposal
          cases leftBit <;> cases leftProposed <;> cases rightBit <;> cases rightProposed <;>
            simp_all
        let leftResult : Config Player L ((published, .publication payload) :: Γ) :=
          revealSuccessor published source leftEntry leftBit
        let rightResult : Config Player L ((published, .publication payload) :: Γ) :=
          revealSuccessor published source rightEntry rightBit
        have leftPure := publication_step_pure setup origin left leftTrace leftEntry
          leftPoint leftSurvives
          (setup.proposalRecoveryProtocol.singletonJoint owner
            (some (⟨⟨.reveal owner name leftBit, false⟩, leftProposed⟩ :
              ProposalRecoveryMove Player L)))
        have rightPure := publication_step_pure setup origin right rightTrace rightEntry
          rightPoint rightSurvives
          (setup.proposalRecoveryProtocol.singletonJoint owner
            (some (⟨⟨.reveal owner name rightBit, false⟩, rightProposed⟩ :
              ProposalRecoveryMove Player L)))
        simp only [ExecutionProtocol.singletonJoint_self, Option.map_some,
          OwnAction.disclosure] at leftPure rightPure
        have actualLeft := leftSupport
        have actualRight := rightSupport
        change leftTarget ∈ ((left.step _).map some).support at actualLeft
        change rightTarget ∈ ((right.step _).map some).support at actualRight
        rw [leftPure, PMF.pure_map, PMF.mem_support_pure_iff] at actualLeft
        rw [rightPure, PMF.pure_map, PMF.mem_support_pure_iff] at actualRight
        have nextPrivate := congrArg Prod.fst next
        change setup.commitRecoveryPrivate focal leftTarget =
          setup.commitRecoveryPrivate focal rightTarget at nextPrivate
        rw [actualLeft, actualRight] at nextPrivate
        have localNext := origin.observe_reflect focal _ _ (Option.some.inj nextPrivate)
        have newView := congrArg (ProtocolView.entryView focal suffix) (Sum.inr.inj localNext)
        have typedNext : leftResult.view focal = rightResult.view focal := by
          simpa only [ProtocolView.entryView_observe_entry] using newView
        have typed := publication_typed_classes_eq (published := published)
          omission delivery focal foreign source
          leftEntry rightEntry localMetadata oldView leftValue rightValue leftStored
            rightStored leftBit leftProposed rightBit rightProposed proposal typedNext
        have mass := leftMass.trans (typed.trans rightMass.symm)
        simpa only [proposalRecoveryForeignRowFactors, leftActor, rightActor, foreign,
          ite_false, ExecutionProtocol.singletonJoint_self] using mass
      rcases publication_legal_move_cases setup origin left leftEntry leftPoint
        leftSurvives leftJoint leftLegal with chosen | chosen | chosen
      · rcases publication_legal_move_cases setup origin right rightEntry rightPoint
          rightSurvives rightJoint rightLegal with other | other | other
        · exact compare true false true false chosen other
        · exact compare true false false true chosen other
        · exact compare true false false false chosen other
      · rcases publication_legal_move_cases setup origin right rightEntry rightPoint
          rightSurvives rightJoint rightLegal with other | other | other
        · exact compare false true true false chosen other
        · exact compare false true false true chosen other
        · exact compare false true false false chosen other
      · rcases publication_legal_move_cases setup origin right rightEntry rightPoint
          rightSurvives rightJoint rightLegal with other | other | other
        · exact compare false false true false chosen other
        · exact compare false false false true chosen other
        · exact compare false false false false chosen other

/-- Actual paired rows have the same foreign class scalar. Current values,
truth/failed-disclosure causes and original initialized draws stay separate. -/
private theorem proposalRecovery_foreign_class_row_eq_of_signals
    (values : ∀ author (key : setup.ProposalRecoveryComponent author),
      PMF (setup.CommitRecoveryValueChoice author key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    (left right : setup.proposalRecoveryProtocol.History)
    (leftJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal left.state leftJoint)
    {leftTarget : setup.proposalRecoveryProtocol.State}
    (leftSupport : leftTarget ∈
      (setup.proposalRecoveryProtocol.step left.state ⟨leftJoint, leftLegal⟩).support)
    (rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (rightLegal : setup.proposalRecoveryProtocol.Legal right.state rightJoint)
    {rightTarget : setup.proposalRecoveryProtocol.State}
    (rightSupport : rightTarget ∈
      (setup.proposalRecoveryProtocol.step right.state ⟨rightJoint, rightLegal⟩).support)
    (same : setup.proposalRecoverySignals.infoOf focal left.trace =
      setup.proposalRecoverySignals.infoOf focal right.trace)
    (next : (setup.proposalRecoverySignals.infoOf focal
        (left.trace.extend leftJoint leftLegal leftSupport)).1 =
      (setup.proposalRecoverySignals.infoOf focal
        (right.trace.extend rightJoint rightLegal rightSupport)).1)
    (leftGood : ∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner
      (left.extend leftLegal leftSupport))
    (rightGood : ∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner
      (right.extend rightLegal rightSupport)) :
    (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      left leftJoint leftLegal leftSupport).1 =
      (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
        right rightJoint rightLegal rightSupport).1 := by
  classical
  have metadata := source_metadata_of_signals setup focal left right same
  have observed := source_current_of_signals setup focal left right same
  rcases left with ⟨leftState, leftTrace⟩
  rcases right with ⟨rightState, rightTrace⟩
  cases leftState with
  | none =>
      cases rightState with
      | none => rfl
      | some right => cases metadata
  | some left =>
      cases rightState with
      | none => cases metadata
      | some right =>
          have privateEq := congrArg Prod.fst observed
          change some (ProtocolState.observe focal setup.program left.point) =
            some (ProtocolState.observe focal setup.program right.point) at privateEq
          have viewEq := Option.some.inj privateEq
          have actorEq : ProtocolState.actor setup.program left.point =
              ProtocolState.actor setup.program right.point := by
            rw [← ProtocolState.actor_observe_eq setup.program left.point focal,
              viewEq, ProtocolState.actor_observe_eq]
          have excludedEq := metadata.2.2.1
          have control := ProtocolState.MetadataEq.controls setup.program left.point right.point
            metadata.1
          cases acting : ProtocolState.actor setup.program left.point with
          | none =>
              have otherActor : ProtocolState.actor setup.program right.point = none :=
                actorEq.symm.trans acting
              simp only [proposalRecoveryForeignRowFactors, acting, otherActor]
          | some owner =>
              have otherActor : ProtocolState.actor setup.program right.point = some owner :=
                actorEq.symm.trans acting
              by_cases focalRow : owner = focal
              · simp only [proposalRecoveryForeignRowFactors, acting, otherActor,
                  focalRow, ite_true]
              · by_cases inherited : owner ∈ left.excluded
                · have otherInherited : owner ∈ right.excluded := excludedEq ▸ inherited
                  have leftNone : leftJoint owner = none := by
                    exact LegalOption.eq_none_of_inactive _
                      (setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal owner)
                      (fun active => active.2 inherited)
                  have rightNone : rightJoint owner = none := by
                    exact LegalOption.eq_none_of_inactive _
                      (setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal owner)
                      (fun active => active.2 otherInherited)
                  simp only [proposalRecoveryForeignRowFactors, acting, otherActor,
                    focalRow, ite_false, leftNone, rightNone]
                · have otherSurvives : owner ∉ right.excluded := excludedEq ▸ inherited
                  cases committing : ProtocolState.atCommit setup.program left.point with
                  | true =>
                      have otherCommit : ProtocolState.atCommit setup.program right.point = true :=
                        control.2.1.symm.trans committing
                      obtain ⟨leftNext, leftTargetEq⟩ : ∃ target, leftTarget = some target := by
                        change leftTarget ∈
                          ((left.step (proposalRecoveryJoint leftJoint)).map some).support
                            at leftSupport
                        obtain ⟨target, _member, image⟩ :=
                          (PMF.mem_support_map_iff _ _ _).mp leftSupport
                        exact ⟨target, image.symm⟩
                      obtain ⟨rightNext, rightTargetEq⟩ : ∃ target, rightTarget = some target := by
                        change rightTarget ∈
                          ((right.step (proposalRecoveryJoint rightJoint)).map some).support
                            at rightSupport
                        obtain ⟨target, _member, image⟩ :=
                          (PMF.mem_support_map_iff _ _ _).mp rightSupport
                        exact ⟨target, image.symm⟩
                      subst leftTarget
                      subst rightTarget
                      have nextE := congrArg (fun signal => signal.2.1.1) next
                      change leftNext.excluded = rightNext.excluded at nextE
                      exact foreign_commit_classes_eq_of_next_excluded setup values omission bad
                        delivery focal owner left right leftTrace rightTrace committing otherCommit
                          acting otherActor inherited otherSurvives focalRow leftJoint rightJoint
                            leftLegal rightLegal leftNext rightNext leftSupport rightSupport nextE
                              (leftGood owner focalRow) (rightGood owner focalRow)
                  | false =>
                      have otherNoncommit :
                          ProtocolState.atCommit setup.program right.point = false :=
                        control.2.1.symm.trans committing
                      have leftBefore : ¬ setup.GeneratedPreparationHistory owner
                          ⟨some left, leftTrace⟩ := by
                        intro generated
                        exact leftGood owner focalRow (generated_preparation_before_extend setup
                          owner leftTrace leftJoint leftLegal leftSupport generated)
                      have rightBefore : ¬ setup.GeneratedPreparationHistory owner
                          ⟨some right, rightTrace⟩ := by
                        intro generated
                        exact rightGood owner focalRow (generated_preparation_before_extend setup
                          owner rightTrace rightJoint rightLegal rightSupport generated)
                      have leftValues :=
                        setup.proposalRecovery_bindingsHoldValues_of_surviving_no_generated
                          wellFormed left leftTrace owner inherited leftBefore
                      have rightValues :=
                        setup.proposalRecovery_bindingsHoldValues_of_surviving_no_generated
                          wellFormed right rightTrace owner otherSurvives rightBefore
                      exact foreign_publication_classes_eq_of_actual_guards setup values
                        omission bad delivery omissionPositive omissionBelow badBelow
                          deliveryPositive deliveryBelow focal owner left right leftTrace rightTrace
                            committing otherNoncommit acting otherActor inherited otherSurvives
                              focalRow leftJoint leftLegal leftSupport rightJoint rightLegal
                                rightSupport metadata.1 viewEq next leftValues rightValues

/-- The foreign class coefficient is determined by the original complete
signal word. This retains the initializer observation and every canceled
attempt; no focal own-action inversion enters the synchronized trace fold. -/
private theorem foreign_class_eq_of_signals
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftTrace : setup.proposalRecoveryProtocol.Trace leftState)
    (rightTrace : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.proposalRecoverySignals.infoOf focal leftTrace =
      setup.proposalRecoverySignals.infoOf focal rightTrace)
    (leftGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨leftState, leftTrace⟩)
    (rightGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨rightState, rightTrace⟩) :
    (setup.proposalRecoveryForeignProducts values omission bad delivery focal leftTrace).1 =
      (setup.proposalRecoveryForeignProducts values omission bad delivery focal rightTrace).1 := by
  classical
  have clock : leftTrace.length = rightTrace.length := by
    have lengths := congrArg (fun information => information.2.length) same
    simpa only [source_signal_depth] using lengths
  induction leftTrace generalizing rightState with
  | start =>
      cases rightTrace with
      | start => rfl
      | extend prior joint legal supported =>
          simp only [Trace.length] at clock
          omega
  | @extend leftSource leftTarget leftEarlier leftJoint leftLegal leftReached ih =>
      cases rightTrace with
      | start => simp only [Trace.length] at clock; omega
      | @extend rightSource rightTarget rightEarlier rightJoint rightLegal rightReached =>
          have previous : setup.proposalRecoverySignals.infoOf focal leftEarlier =
              setup.proposalRecoverySignals.infoOf focal rightEarlier := by
            have past := congrArg Prod.snd same
            change (setup.proposalRecoverySignals.infoOf focal leftEarlier).1 ::
                (setup.proposalRecoverySignals.infoOf focal leftEarlier).2 =
              (setup.proposalRecoverySignals.infoOf focal rightEarlier).1 ::
                (setup.proposalRecoverySignals.infoOf focal rightEarlier).2 at past
            exact Prod.ext (List.cons.inj past).1 (List.cons.inj past).2
          have leftBefore : ∀ owner, owner ≠ focal →
              ¬ setup.GeneratedPreparationHistory owner ⟨leftSource, leftEarlier⟩ := by
            intro owner foreign generated
            exact leftGood owner foreign (generated_preparation_before_extend setup owner
              leftEarlier leftJoint leftLegal leftReached generated)
          have rightBefore : ∀ owner, owner ≠ focal →
              ¬ setup.GeneratedPreparationHistory owner ⟨rightSource, rightEarlier⟩ := by
            intro owner foreign generated
            exact rightGood owner foreign (generated_preparation_before_extend setup owner
              rightEarlier rightJoint rightLegal rightReached generated)
          have prefixFactor := ih rightEarlier previous leftBefore rightBefore (by
            simpa only [Trace.length, Nat.add_left_inj] using clock)
          have row := setup.proposalRecovery_foreign_class_row_eq_of_signals values
            omission bad delivery omissionPositive omissionBelow badBelow deliveryPositive
              deliveryBelow wellFormed focal
                ⟨leftSource, leftEarlier⟩ ⟨rightSource, rightEarlier⟩
                leftJoint leftLegal leftReached rightJoint rightLegal rightReached previous
                (congrArg Prod.fst same) leftGood rightGood
          change (setup.proposalRecoveryForeignProducts values omission bad delivery focal
              leftEarlier).1 * (setup.proposalRecoveryForeignRowFactors values omission bad
                delivery focal ⟨leftSource, leftEarlier⟩ leftJoint leftLegal leftReached).1 =
            (setup.proposalRecoveryForeignProducts values omission bad delivery focal
              rightEarlier).1 * (setup.proposalRecoveryForeignRowFactors values omission bad
                delivery focal ⟨rightSource, rightEarlier⟩ rightJoint rightLegal rightReached).1
          rw [prefixFactor, row]

/-- Full focal information fixes the regular foreign class product even when
foreign disclosure causes and correlated initialized inputs differ. The
complete focal own word remains literal in the separate reach factor. -/
theorem proposalRecovery_foreign_class_eq_of_information
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftTrace : setup.proposalRecoveryProtocol.Trace leftState)
    (rightTrace : setup.proposalRecoveryProtocol.Trace rightState)
    (same : setup.proposalRecoveryModel.infoOf focal leftTrace =
      setup.proposalRecoveryModel.infoOf focal rightTrace)
    (leftGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨leftState, leftTrace⟩)
    (rightGood : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨rightState, rightTrace⟩) :
    (setup.proposalRecoveryForeignProducts values omission bad delivery focal leftTrace).1 =
      (setup.proposalRecoveryForeignProducts values omission bad delivery focal rightTrace).1 := by
  have signals : setup.proposalRecoverySignals.infoOf focal leftTrace =
      setup.proposalRecoverySignals.infoOf focal rightTrace := by
    change setup.proposalRecoverySignals.withOwnPlayRecall.infoOf focal leftTrace =
      setup.proposalRecoverySignals.withOwnPlayRecall.infoOf focal rightTrace at same
    rw [InfoSignals.withOwnPlayRecall_infoOf, InfoSignals.withOwnPlayRecall_infoOf] at same
    exact congrArg Prod.fst same
  exact foreign_class_eq_of_signals setup values omission bad delivery omissionPositive
    omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal leftTrace rightTrace
      signals leftGood rightGood

private theorem proposalRecovery_foreign_class_row_pos_of_good
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (_wellFormed : setup.WellFormed) (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈
      (setup.proposalRecoveryProtocol.step before.state ⟨joint, legal⟩).support)
    (good : ∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner
      (before.extend legal supported)) :
    0 < (setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      before joint legal supported).1 := by
  classical
  rcases before with ⟨state, trace⟩
  cases state with
  | none => exact zero_lt_one
  | some current =>
      change setup.proposalRecoveryProtocol.Legal (some current) joint at legal
      change target ∈
        (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support at supported
      cases acting : ProtocolState.actor setup.program current.point with
      | none => simpa only [proposalRecoveryForeignRowFactors, acting] using zero_lt_one
      | some owner =>
          by_cases foreign : owner = focal
          · simpa only [proposalRecoveryForeignRowFactors, acting, foreign, ite_true]
              using zero_lt_one
          · by_cases survives : owner ∈ current.excluded
            · have absent : joint owner = none :=
                LegalOption.eq_none_of_inactive _
                  (setup.proposalRecoveryProtocol.legalOption_of_legal legal owner)
                  (fun active => active.2 survives)
              simpa only [proposalRecoveryForeignRowFactors, acting, foreign,
                ite_false, absent] using zero_lt_one
            · cases committing : ProtocolState.atCommit setup.program current.point with
              | true =>
                  obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
                  rw [foreign_commit_class_of_next_excluded setup values omission bad
                    delivery focal owner current trace committing acting survives foreign
                      joint legal next supported (good owner foreign)]
                  split
                  · exact ENNReal.ofReal_pos.mpr omissionPositive
                  · exact ENNReal.ofReal_pos.mpr
                      (mul_pos (sub_pos.mpr omissionBelow) (sub_pos.mpr badBelow))
              | false =>
                  obtain ⟨Γ, O, published, name, payload, fresh, source, unresolved,
                    suffix, lift, entry, origin, point, _names⟩ := source_reveal_entry
                      setup.program current.point owner setup.namesNodup committing acting
                  obtain ⟨truth, failed, withheld, truthEq, failedEq, withheldEq, law⟩ :=
                    foreign_publication_choice_law setup values omission bad delivery origin
                      current trace entry point survives
                  let profile := setup.proposalRecoveryNormalizedTrembledProfile
                    omission.val omission.property.1 omission.property.2
                    bad.val bad.property.1 bad.property.2
                    delivery.val delivery.property.1 delivery.property.2 values
                  let choice := setup.proposalRecoveryModel.choicesOfLegal trace
                    ⟨joint, legal⟩ owner
                  have raw : choice.val = joint owner := rfl
                  have choiceSupported : choice ∈
                      (profile owner (setup.proposalRecoveryModel.infoOf owner trace)).support := by
                    dsimp only [profile]
                    rw [law]
                    rcases publication_legal_move_cases setup origin current entry point
                      survives joint legal with selected | selected | selected
                    · have same : choice = truth := Subtype.ext (raw.trans
                        (selected.trans truthEq.symm))
                      rw [same]
                      exact mem_support_mix_right _ _ _ omissionBelow
                        ((PMF.mem_support_pure_iff _ _).mpr rfl)
                    · have same : choice = failed := Subtype.ext (raw.trans
                        (selected.trans failedEq.symm))
                      rw [same]
                      exact mem_support_mix_left _ _ _ omissionPositive
                        (mem_support_mix_left _ _ _ deliveryPositive
                          ((PMF.mem_support_pure_iff _ _).mpr rfl))
                    · have same : choice = withheld := Subtype.ext (raw.trans
                        (selected.trans withheldEq.symm))
                      rw [same]
                      exact mem_support_mix_left _ _ _ omissionPositive
                        (mem_support_mix_right _ _ _ deliveryBelow
                          ((PMF.mem_support_pure_iff _ _).mpr rfl))
                  have jointSupported : (⟨joint, legal⟩ :
                      {draw // setup.proposalRecoveryProtocol.Legal (some current) draw}) ∈
                      (setup.proposalRecoveryModel.behavioralJoint profile trace legal.1).support :=
                      by
                    apply setup.proposalRecoveryModel.mem_support_behavioralJoint
                      profile trace legal.1 joint legal
                    intro other
                    by_cases same : other = owner
                    · subst other
                      exact choiceSupported
                    · have inactive : ¬ setup.proposalRecoveryProtocol.active
                          (some current) other := by
                        intro active
                        exact same (Option.some.inj (active.1.symm.trans acting))
                      let _ := setup.proposalRecoveryModel.subsingleton_choice_of_not_active
                        trace inactive
                      rw [eq_pure_of_subsingleton
                        (profile other (setup.proposalRecoveryModel.infoOf other trace))
                        (setup.proposalRecoveryModel.choicesOfLegal trace ⟨joint, legal⟩ other)]
                      exact (PMF.mem_support_pure_iff _ _).mpr rfl
                  have extendedSupported :
                      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
                        legal supported) ∈
                      (setup.proposalRecoveryModel.runBehavioralFrom profile 1
                        ⟨some current, trace⟩).support := by
                    rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal
                      profile 0 legal.1, PMF.mem_support_bind_iff]
                    refine ⟨⟨joint, legal⟩, jointSupported, ?_⟩
                    apply (PMF.mem_support_bindOnSupport_iff _ _).mpr
                    exact ⟨target, supported, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
                  have observedSupported :
                      setup.proposalRecoveryForeignCauseRead focal
                        ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
                          legal supported) ∈
                      ((setup.proposalRecoveryModel.runBehavioralFrom profile 1
                        ⟨some current, trace⟩).map
                          (setup.proposalRecoveryForeignCauseRead focal)).support :=
                    (PMF.mem_support_map_iff _ _ _).mpr ⟨_, extendedSupported, rfl⟩
                  have observedPositive : 0 <
                      ((setup.proposalRecoveryModel.runBehavioralFrom profile 1
                        ⟨some current, trace⟩).map
                          (setup.proposalRecoveryForeignCauseRead focal))
                        (setup.proposalRecoveryForeignCauseRead focal
                          ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
                            legal supported)) :=
                    pos_iff_ne_zero.mpr ((PMF.mem_support_iff _ _).mp observedSupported)
                  rcases publication_legal_move_cases setup origin current entry point
                    survives joint legal with selected | selected | selected
                  · simpa only [proposalRecoveryForeignRowFactors, acting, foreign,
                      ite_false, selected, ProposalRecoveryMove.ordinary,
                      profile] using observedPositive
                  · simpa only [proposalRecoveryForeignRowFactors, acting, foreign,
                      ite_false, selected, ProposalRecoveryMove.failedDisclosure,
                      profile] using observedPositive
                  · simpa only [proposalRecoveryForeignRowFactors, acting, foreign,
                      ite_false, selected, ProposalRecoveryMove.ordinary,
                      profile] using observedPositive

/-- Regular foreign class mass is positive separately from every ordinary
D atom. Literal zero D coordinates therefore remain valid reach identities. -/
theorem proposalRecovery_foreign_class_pos_of_good
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state)
    (good : ∀ owner, owner ≠ focal →
      ¬ setup.GeneratedPreparationHistory owner ⟨state, trace⟩) :
    0 < (setup.proposalRecoveryForeignProducts values omission bad delivery focal trace).1 := by
  induction trace with
  | start => exact zero_lt_one
  | @extend before after prior joint legal supported ih =>
      have previous : ∀ owner, owner ≠ focal →
          ¬ setup.GeneratedPreparationHistory owner ⟨before, prior⟩ := by
        intro owner foreign generated
        exact good owner foreign (generated_preparation_before_extend setup owner
          prior joint legal supported generated)
      have row := setup.proposalRecovery_foreign_class_row_pos_of_good values omission bad
        delivery omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow
          wellFormed focal ⟨before, prior⟩ joint legal supported good
      exact ENNReal.mul_pos (ih previous).ne' row.ne'

/-- The regular foreign coefficient is an actual positive finite function
of full focal information. Its reach identity retains the original intrinsic
initializer/Nature atom and entire focal own word as separate literal
factors. Every product ends at this source History, before any completion. -/
theorem proposalRecovery_foreign_information_factor
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1)
    (omissionPositive : 0 < omission.val) (omissionBelow : omission.val < 1)
    (badBelow : bad.val < 1) (deliveryPositive : 0 < delivery.val)
    (deliveryBelow : delivery.val < 1) (wellFormed : setup.WellFormed) (focal : Player) :
    ∃ coefficient : setup.proposalRecoveryModel.InfoState focal → ℝ≥0∞,
      (∀ information, 0 < coefficient information ∧ coefficient information ≠ ⊤) ∧
      (∀ history : setup.proposalRecoveryProtocol.History,
        (∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history) →
        coefficient (setup.proposalRecoveryModel.infoOf focal history.trace) =
          (setup.proposalRecoveryForeignProducts values omission bad delivery focal
            history.trace).1) ∧
      ∀ history : setup.proposalRecoveryProtocol.History,
        (∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history) →
        let profile := setup.proposalRecoveryNormalizedTrembledProfile
          omission.val omission.property.1 omission.property.2
          bad.val bad.property.1 bad.property.2
          delivery.val delivery.property.1 delivery.property.2 values
        let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal
          history.trace
        setup.proposalRecoveryModel.historyReachWeight profile history =
          ENNReal.ofReal history.trace.transitionMass *
            ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
              (setup.proposalRecoveryModel.ownPlay focal history.trace)) *
                coefficient (setup.proposalRecoveryModel.infoOf focal history.trace) *
                  factors.2.1 * factors.2.2 := by
  classical
  let represented (information : setup.proposalRecoveryModel.InfoState focal) : Prop :=
    ∃ history : setup.proposalRecoveryProtocol.History,
      setup.proposalRecoveryModel.infoOf focal history.trace = information ∧
      ∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history
  let selected (information : setup.proposalRecoveryModel.InfoState focal)
      (present : represented information) : setup.proposalRecoveryProtocol.History :=
    Classical.choose present
  have selectedInfo (information : setup.proposalRecoveryModel.InfoState focal)
      (present : represented information) :
      setup.proposalRecoveryModel.infoOf focal (selected information present).trace =
        information ∧
      ∀ owner, owner ≠ focal →
        ¬ setup.GeneratedPreparationHistory owner (selected information present) :=
    Classical.choose_spec present
  let coefficient (information : setup.proposalRecoveryModel.InfoState focal) : ℝ≥0∞ :=
    if present : represented information then
      (setup.proposalRecoveryForeignProducts values omission bad delivery focal
        (selected information present).trace).1
    else 1
  have positiveFinite (information : setup.proposalRecoveryModel.InfoState focal) :
      0 < coefficient information ∧ coefficient information ≠ ⊤ := by
    by_cases present : represented information
    · dsimp only [coefficient]
      rw [dite_eq_left present]
      exact ⟨setup.proposalRecovery_foreign_class_pos_of_good values omission bad delivery
        omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal
          (selected information present).trace (selectedInfo information present).2,
        (setup.proposalRecoveryForeignProducts_finite values omission bad delivery focal
          (selected information present).trace).1⟩
    · dsimp only [coefficient]
      rw [dite_eq_right present]
      exact ⟨zero_lt_one, ENNReal.one_ne_top⟩
  have readout (history : setup.proposalRecoveryProtocol.History)
      (good : ∀ owner, owner ≠ focal →
        ¬ setup.GeneratedPreparationHistory owner history) :
      coefficient (setup.proposalRecoveryModel.infoOf focal history.trace) =
        (setup.proposalRecoveryForeignProducts values omission bad delivery focal
          history.trace).1 := by
    have present : represented (setup.proposalRecoveryModel.infoOf focal history.trace) :=
      ⟨history, rfl, good⟩
    dsimp only [coefficient]
    rw [dite_eq_left present]
    exact setup.proposalRecovery_foreign_class_eq_of_information values omission bad delivery
      omissionPositive omissionBelow badBelow deliveryPositive deliveryBelow wellFormed focal
        (selected _ present).trace history.trace (selectedInfo _ present).1
          (selectedInfo _ present).2 good
  refine ⟨coefficient, positiveFinite, readout, ?_⟩
  intro history good
  rw [readout history good]
  exact setup.proposalRecovery_historyReachWeight_foreign_products values omission bad delivery
    focal history

/-- The only changed private label is a foreign truthful disclosure versus
its failed-disclosure copy. Both labels refer to the same owned variable.
All other coordinates, including the observer's, stay literal. -/
def ForeignDisclosureLabels (who : Player)
    (left right : Player → Option (ProposalRecoveryMove Player L)) : Prop :=
  left = right ∨ ∃ owner name, owner ≠ who ∧
    (∀ other, other ≠ owner → left other = right other) ∧
    ((left owner = some (ProposalRecoveryMove.ordinary
          ⟨.reveal owner name true, false⟩) ∧
        right owner = some (ProposalRecoveryMove.failedDisclosure owner name)) ∨
      (right owner = some (ProposalRecoveryMove.ordinary
          ⟨.reveal owner name true, false⟩) ∧
        left owner = some (ProposalRecoveryMove.failedDisclosure owner name)))

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
theorem ForeignDisclosureLabels.own {who : Player}
    {left right : Player → Option (ProposalRecoveryMove Player L)}
    (refines : ForeignDisclosureLabels who left right) : left who = right who := by
  rcases refines with same | ⟨owner, _name, foreign, retained, _labels⟩
  · exact congrFun same who
  · exact retained who (Ne.symm foreign)

/-- A finite pairing of actual supported source steps from the SAME retained
initializer. A changed foreign cause retains its actual public result and
proposal, and permanently excludes its author in both successors. No
probability, information equality or native receipt cause is a field. -/
inductive ProposalRecoveryForeignRefinement (who : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first)) :
    setup.proposalRecoveryProtocol.History → setup.proposalRecoveryProtocol.History → Prop where
  | initial : ProposalRecoveryForeignRefinement who first prior
      ⟨some first, prior⟩ ⟨some first, prior⟩
  | extend {leftState rightState leftAfter rightAfter : setup.proposalRecoveryProtocol.State}
      (left : setup.proposalRecoveryProtocol.Trace leftState)
      (right : setup.proposalRecoveryProtocol.Trace rightState)
      (earlier : ProposalRecoveryForeignRefinement who first prior
        ⟨leftState, left⟩ ⟨rightState, right⟩)
      (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
      (leftLegal : setup.proposalRecoveryProtocol.Legal leftState leftJoint)
      (rightLegal : setup.proposalRecoveryProtocol.Legal rightState rightJoint)
      (leftSupported : leftAfter ∈
        (setup.proposalRecoveryProtocol.step leftState ⟨leftJoint, leftLegal⟩).support)
      (rightSupported : rightAfter ∈
        (setup.proposalRecoveryProtocol.step rightState ⟨rightJoint, rightLegal⟩).support)
      (labels : ForeignDisclosureLabels who leftJoint rightJoint)
      (publicResult : setup.attemptPublicSignal who leftAfter =
        setup.attemptPublicSignal who rightAfter)
      (proposal : setup.proposalRecoveryProposalOf leftState leftJoint =
        setup.proposalRecoveryProposalOf rightState rightJoint)
      (changed : leftJoint ≠ rightJoint →
        ∃ submitted, setup.proposalRecoveryProposalOf leftState leftJoint = some submitted)
      (excluded : ∀ owner, leftJoint owner ≠ rightJoint owner →
        owner ∈ (setup.commitRecoveryPublic leftAfter).1 ∧
          owner ∈ (setup.commitRecoveryPublic rightAfter).1) :
      ProposalRecoveryForeignRefinement who first prior
        ⟨leftAfter, left.extend leftJoint leftLegal leftSupported⟩
        ⟨rightAfter, right.extend rightJoint rightLegal rightSupported⟩

namespace ProposalRecoveryForeignRefinement

variable {setup} {who : Player} {first : CommitRecoveryState setup.program}
  {prior : setup.proposalRecoveryProtocol.Trace (some first)}
  {left right : setup.proposalRecoveryProtocol.History}

omit [Fintype Player] in
theorem retained (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    TracePrefix prior left.trace ∧ TracePrefix prior right.trace := by
  induction refines with
  | initial => exact ⟨.refl, .refl⟩
  | extend _ _ _ leftJoint rightJoint leftLegal rightLegal leftSupported rightSupported
      _ _ _ _ _ ih =>
      exact ⟨.extend ih.1 leftJoint leftLegal leftSupported,
        .extend ih.2 rightJoint rightLegal rightSupported⟩

omit [Fintype Player] in
theorem publicRecall
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    setup.proposalRecoveryPublicRecall who left.trace =
      setup.proposalRecoveryPublicRecall who right.trace := by
  induction refines with
  | initial => rfl
  | extend _ _ _ _ _ _ _ _ _ _ publicResult proposal _ _ ih =>
      simp only [proposalRecoveryPublicRecall, publicResult, proposal, ih]

omit [Fintype Player] in
theorem coordinate
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    (setup.proposalRecoveryJointRecall left.trace).map (fun joint => joint who) =
      (setup.proposalRecoveryJointRecall right.trace).map (fun joint => joint who) := by
  induction refines with
  | initial => rfl
  | extend _ _ _ _ _ _ _ _ _ labels _ _ _ _ ih =>
      simp only [proposalRecoveryJointRecall, List.map_cons, labels.own, ih]

omit [Fintype Player] in
/-- Permitted foreign cause refinements preserve the observer's ENTIRE
labeled source information, including all canceled own binding tags. The
full observer theorem uses the original initializer and supported steps. -/
theorem info_eq
    (refines : setup.ProposalRecoveryForeignRefinement who first prior left right) :
    setup.proposalRecoveryModel.infoOf who left.trace =
      setup.proposalRecoveryModel.infoOf who right.trace := by
  exact setup.proposalRecovery_info_eq_of_observed_prefixes who first first prior prior
    rfl rfl rfl left.trace right.trace refines.retained.1 refines.retained.2
    refines.publicRecall refines.coordinate

end ProposalRecoveryForeignRefinement


/-- No foreign owner has generated an unusable nonmissing preparation anywhere
in this literal source history, including canceled attempts. -/
def proposalRecoveryForeignGood (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) : Prop :=
  ∀ owner, owner ≠ focal → ¬ setup.GeneratedPreparationHistory owner history

/-- Chronological complete focal information and actual foreign source causes. -/
def proposalRecoveryCauseWord (focal : Player) :
    ∀ {state}, setup.proposalRecoveryProtocol.Trace state →
      List (setup.proposalRecoveryModel.InfoState focal ×
        Option (Player → Option (ProposalRecoveryMove Player L ⊕ (Player × VarId × Bool))))
  | _, .start => [setup.proposalRecoveryForeignCauseRead focal ⟨_, .start⟩]
  | _, .extend prior joint legal realized =>
      proposalRecoveryCauseWord focal prior ++
        [setup.proposalRecoveryForeignCauseRead focal
          ⟨_, prior.extend joint legal realized⟩]

open Classical in
/-- The original joint input, complete focal information, chronological source
causes, and whole-history foreign preparation status determine this fiber. -/
def proposalRecoveryClosedKey (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) :=
  (history.state.map (fun state => ProtocolState.base setup.program state.point),
    setup.proposalRecoveryModel.infoOf focal history.trace,
    setup.proposalRecoveryCauseWord focal history.trace,
    decide (setup.proposalRecoveryForeignGood focal history))

/-- Conditional law of the actual source run at the canonical trace's depth. -/
def proposalRecoveryClosedLaw
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (canonical : setup.proposalRecoveryProtocol.History) :=
  fiberPosterior (setup.proposalRecoveryModel.runBehavioral profile canonical.trace.length)
    (setup.proposalRecoveryClosedKey focal) (setup.proposalRecoveryClosedKey focal canonical)

/-- Unnormalized mass of the same actual source fiber. -/
def proposalRecoveryClosedMass
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (canonical : setup.proposalRecoveryProtocol.History) :=
  ((setup.proposalRecoveryModel.runBehavioral profile canonical.trace.length).map
    (setup.proposalRecoveryClosedKey focal)) (setup.proposalRecoveryClosedKey focal canonical)

omit [Fintype Player] in
theorem proposalRecoveryCauseWord_length (focal : Player)
    {state} (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryCauseWord focal trace).length = trace.length + 1 := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [proposalRecoveryCauseWord, List.length_append, List.length_singleton,
        Trace.length, ih]

omit [Fintype Player] in
theorem proposalRecoveryClosedKey_depth (focal : Player)
    (canonical target : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryClosedKey focal target =
      setup.proposalRecoveryClosedKey focal canonical) :
    target.trace.length = canonical.trace.length := by
  have words := congrArg (fun key => key.2.2.1) same
  change setup.proposalRecoveryCauseWord focal target.trace =
    setup.proposalRecoveryCauseWord focal canonical.trace at words
  have lengths := congrArg List.length words
  rw [setup.proposalRecoveryCauseWord_length, setup.proposalRecoveryCauseWord_length] at lengths
  omega

open Classical in
/-- Zero-safe disintegration retains the actual initialized reach atom. -/
theorem proposalRecoveryClosedMass_mul_law
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (canonical target : setup.proposalRecoveryProtocol.History) :
    setup.proposalRecoveryClosedMass profile focal canonical *
        setup.proposalRecoveryClosedLaw profile focal canonical target =
      if setup.proposalRecoveryClosedKey focal target =
          setup.proposalRecoveryClosedKey focal canonical then
        setup.proposalRecoveryModel.historyReachWeight profile target else 0 := by
  classical
  let law := setup.proposalRecoveryModel.runBehavioral profile canonical.trace.length
  let key := setup.proposalRecoveryClosedKey focal
  change (law.map key) (key canonical) * fiberPosterior law key (key canonical) target = _
  by_cases present : key canonical ∈ (law.map key).support
  · rw [fiberPosterior_apply law key (key canonical) present]
    by_cases same : key target = key canonical
    · rw [ite_eq_left same, Set.indicator_of_mem (show target ∈ {h | key h = key canonical}
        from same)]
      have depth := setup.proposalRecoveryClosedKey_depth focal canonical target same
      calc
        _ = law target * ((law.map key) (key canonical) *
            ((law.map key) (key canonical))⁻¹) := by ac_rfl
        _ = law target := by
          rw [ENNReal.mul_inv_cancel ((PMF.mem_support_iff _ _).mp present)
            (PMF.apply_ne_top _ _), mul_one]
        _ = _ := by rw [InformationModel.historyReachWeight, depth]
    · rw [ite_eq_right same, Set.indicator_of_notMem (show target ∉ {h | key h = key canonical}
        from same), zero_mul, mul_zero]
  · rw [(PMF.apply_eq_zero_iff _ _).mpr present, zero_mul]
    split
    · rename_i same
      symm
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro reached
      apply present
      have depth := setup.proposalRecoveryClosedKey_depth focal canonical target same
      apply (PMF.mem_support_map_iff _ _ _).mpr
      refine ⟨target, ?_, same⟩
      simpa only [law, ← depth] using reached
    · rfl

/-- Only a positive conditioning fiber has its usual posterior support. -/
theorem proposalRecoveryClosedLaw_support
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (canonical target : setup.proposalRecoveryProtocol.History)
    (positive : setup.proposalRecoveryClosedMass profile focal canonical ≠ 0) :
    target ∈ (setup.proposalRecoveryClosedLaw profile focal canonical).support ↔
      setup.proposalRecoveryClosedKey focal target =
          setup.proposalRecoveryClosedKey focal canonical ∧
        setup.proposalRecoveryModel.historyReachWeight profile target ≠ 0 := by
  classical
  have present := (PMF.mem_support_iff _ _).mpr positive
  rw [proposalRecoveryClosedLaw, fiberPosterior_support _ _ _ present]
  change (_ = _ ∧ _) ↔ _
  constructor
  · rintro ⟨same, reached⟩
    refine ⟨same, ?_⟩
    have depth := setup.proposalRecoveryClosedKey_depth focal canonical target same
    simpa only [InformationModel.historyReachWeight, depth, PMF.mem_support_iff] using reached
  · rintro ⟨same, reached⟩
    refine ⟨same, ?_⟩
    have depth := setup.proposalRecoveryClosedKey_depth focal canonical target same
    simpa only [InformationModel.historyReachWeight, depth, PMF.mem_support_iff] using reached

variable (who : Player)

omit [Fintype Player] in
theorem proposalRecovery_labels_of_cause_joint
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal leftState leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal rightState rightJoint)
    (same : SourceProgram.Setup.proposalRecoveryForeignCauseJoint who leftJoint =
      SourceProgram.Setup.proposalRecoveryForeignCauseJoint who rightJoint) :
    SourceProgram.Setup.ForeignDisclosureLabels who leftJoint rightJoint := by
  by_cases identical : leftJoint = rightJoint
  · exact Or.inl identical
  obtain ⟨owner, different⟩ := Function.ne_iff.mp identical
  have selected := congrFun same owner
  cases leftCell : leftJoint owner with
  | none =>
      cases rightCell : rightJoint owner with
      | none => exact (different (leftCell.trans rightCell.symm)).elim
      | some rightMove =>
          simp only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell, rightCell,
            Option.map_none, Option.map_some] at selected
          cases selected
  | some leftMove =>
    cases rightCell : rightJoint owner with
    | none =>
        simp only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell, rightCell,
          Option.map_none, Option.map_some] at selected
        cases selected
    | some rightMove =>
      have foreign : owner ≠ who := by
        intro equal
        subst owner
        simp only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell, rightCell,
          Option.map_some, ite_true, Option.some.injEq, Sum.inl.injEq] at selected
        exact different (leftCell.trans ((congrArg some selected).trans rightCell.symm))
      have leftOffered := setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal owner
      have rightOffered := setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal owner
      rw [leftCell] at leftOffered
      rw [rightCell] at rightOffered
      cases leftState with
      | none => exact leftOffered.1.elim
      | some leftCurrent =>
        cases rightState with
        | none => exact rightOffered.1.elim
        | some rightCurrent =>
          have leftActive : ProtocolState.actor setup.program leftCurrent.point = some owner :=
            leftOffered.1.1
          have rightActive : ProtocolState.actor setup.program rightCurrent.point = some owner :=
            rightOffered.1.1
          have others : ∀ other, other ≠ owner → leftJoint other = rightJoint other := by
            intro other notOwner
            have leftNone : leftJoint other = none := by
              apply LegalOption.eq_none_of_inactive _
                (setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal other)
              intro active
              exact notOwner (Option.some.inj (active.1.symm.trans leftActive))
            have rightNone : rightJoint other = none := by
              apply LegalOption.eq_none_of_inactive _
                (setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal other)
              intro active
              exact notOwner (Option.some.inj (active.1.symm.trans rightActive))
            exact leftNone.trans rightNone.symm
          have revealing : ∃ author name bit, leftMove.semantic.action = .reveal author name
            bit := by
            cases action : leftMove.semantic.action with
            | commit author name payload result =>
                cases otherAction : rightMove.semantic.action <;>
                  simp only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell,
                    rightCell,
                    Option.map_some, foreign, ite_false, action, otherAction,
                    Option.some.injEq, Sum.inl.injEq, reduceCtorEq] at selected
                exact (different (leftCell.trans
                  ((congrArg some selected).trans rightCell.symm))).elim
            | reveal author name bit => exact ⟨author, name, bit, rfl⟩
          have leftNoncommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
            setup.program leftCurrent.point leftMove.semantic leftOffered.2.1 revealing
          obtain ⟨name, leftBit, leftSemantic⟩ :=
            ProtocolState.recoveryAvailable_reveal_of_not_commit owner setup.program
              leftCurrent.point leftActive leftNoncommit leftMove.semantic leftOffered.2.1
          have rightRevealing : ∃ author name bit,
              rightMove.semantic.action = .reveal author name bit := by
            cases action : rightMove.semantic.action with
            | commit author name payload result =>
                simp only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell,
                  rightCell,
                  Option.map_some, foreign, ite_false, leftSemantic, action, Option.some.injEq,
                  reduceCtorEq] at selected
            | reveal author name bit => exact ⟨author, name, bit, rfl⟩
          have rightNoncommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
            setup.program rightCurrent.point rightMove.semantic rightOffered.2.1 rightRevealing
          obtain ⟨rightName, rightBit, rightSemantic⟩ :=
            ProtocolState.recoveryAvailable_reveal_of_not_commit owner setup.program
              rightCurrent.point rightActive rightNoncommit rightMove.semantic rightOffered.2.1
          have names : name = rightName := by
            have paired := congrArg (fun value => value.bind fun pair =>
              match pair with | .inl _ => none | .inr coordinate => some coordinate.2.1) selected
            simpa only [SourceProgram.Setup.proposalRecoveryForeignCauseJoint, leftCell, rightCell,
              Option.map_some, foreign, ite_false, leftSemantic, rightSemantic,
              Option.bind_some, Option.some.injEq] using paired
          subst rightName
          have leftValid := leftOffered.2.2
          have rightValid := rightOffered.2.2
          refine Or.inr ⟨owner, name, foreign, others, ?_⟩
          cases leftMove with
          | mk leftMove leftProposed =>
            cases rightMove with
            | mk rightMove rightProposed =>
              dsimp only at leftSemantic rightSemantic
              subst leftMove
              subst rightMove
              cases leftBit <;> cases leftProposed <;> cases rightBit <;> cases rightProposed <;>
                simp_all [ProposalRecoveryMove.Valid, ProposalRecoveryMove.ordinary,
                  ProposalRecoveryMove.failedDisclosure, ProposalRecoveryMove.discloses,
                  OwnAction.disclosure, SourceProgram.Setup.proposalRecoveryForeignCauseJoint]

omit [Fintype Player] in
theorem proposalRecovery_exposed_of_proper (wellFormed : setup.WellFormed)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (owner : Player) (name : VarId) (bit proposed : Bool)
    (chosen : joint owner = some ⟨⟨.reveal owner name bit, false⟩, proposed⟩)
    (exposed : (bit || proposed) = true)
    (good : ¬ setup.GeneratedPreparationHistory owner ⟨some current, trace⟩) :
    ∃ submitted, setup.proposalRecoveryProposalOf (some current) joint = some submitted := by
  have offered := setup.proposalRecoveryProtocol.legalOption_of_legal legal owner
  rw [chosen] at offered
  have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
    setup.program current.point _ offered.2.1 ⟨owner, name, bit, rfl⟩
  obtain ⟨Γ, O, published, subject, payload, fresh, source, unresolved, suffix,
    lift, entry, origin, point, _names⟩ :=
    source_reveal_entry setup.program current.point owner
      setup.namesNodup notCommit offered.1.1
  change current.point = lift (.inl entry) at point
  have proper := setup.proposalRecovery_bindingsHoldValues_of_surviving_no_generated
    wellFormed current trace owner offered.1.2 good
  rw [point, origin.bindingsHoldValues_lift] at proper
  obtain ⟨value, stored⟩ := proper source
  have transport {wholeΓ Γ : SourceCtx Player L} {wholeO O : Finset VarId}
      {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
      {lift : SourceProgram.ProtocolState program → SourceProgram.ProtocolState whole}
      (origin : ProtocolSuffix whole program lift) (point : SourceProgram.ProtocolState program)
      (moves : Player → Option (ProposalRecoveryMove Player L)) :
      (∃ result, ProtocolState.recoveryProposal program point moves = some result) →
        ∃ result, ProtocolState.recoveryProposal whole (lift point) moves = some result := by
    induction origin with
    | initial => exact id
    | sampleTail fresh law next previous ih =>
        rintro ⟨result, read⟩
        apply ih (.inr point)
        exact ⟨(result.1 + 1, result.2), by simp only [ProtocolState.recoveryProposal, read,
          Sum.elim_inr, Option.map_some]⟩
    | commitTail fresh guard next previous ih =>
        rintro ⟨result, read⟩
        apply ih (.inr point)
        exact ⟨(result.1 + 1, result.2), by simp only [ProtocolState.recoveryProposal, read,
          Sum.elim_inr, Option.map_some]⟩
    | revealTail fresh source unresolved next previous ih =>
        rintro ⟨result, read⟩
        apply ih (.inr point)
        exact ⟨(result.1 + 1, result.2), by simp only [ProtocolState.recoveryProposal, read,
          Sum.elim_inr, Option.map_some]⟩
  have localRead := ProtocolState.recoveryProposal_reveal_success fresh source unresolved
    suffix entry (fun author => if author ∈ current.excluded then none else joint author)
      (by simpa only [offered.1.2, ite_false, chosen, Option.map_some, Option.getD_some,
        ProposalRecoveryMove.discloses, OwnAction.disclosure] using exposed) value stored
  obtain ⟨result, read⟩ := transport origin (.inl entry) _ ⟨_, localRead⟩
  refine ⟨⟨⟨setup.program.publicationBlockLow result.1, current.generation, result.1⟩,
    result.2.1, result.2.2⟩, ?_⟩
  simp only [Setup.proposalRecoveryProposalOf, Option.bind_some, point, read, Option.map_some]

omit [Fintype Player] in
theorem proposalRecovery_withheld_excluded {before after : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace before)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
    (owner : Player) (name : VarId)
    (chosen : joint owner = some (ProposalRecoveryMove.failedDisclosure owner name)) :
    owner ∈ (setup.commitRecoveryPublic after).1 := by
  let semantic := proposalRecoveryJoint joint
  have semanticLegal := setup.proposalRecovery_erase_legal joint legal
  let selected : setup.commitRecoveryModel.Choice owner
      (setup.commitRecoveryModel.infoOf owner (setup.proposalRecoveryEraseTrace trace)) :=
    ⟨semantic owner, (setup.commitRecoveryMenu_adequate owner _ _).mpr
      (setup.commitRecoveryProtocol.legalOption_of_legal semanticLegal owner)⟩
  have selectedEq : selected.1 = some ⟨.reveal owner name false, false⟩ := by
    simp only [selected, semantic, Setup.proposalRecoveryJoint, chosen, Option.map_some,
      ProposalRecoveryMove.failedDisclosure]
  apply setup.commitRecovery_voluntaryFailure_step owner
    (setup.proposalRecoveryEraseTrace trace) selected _ semantic semanticLegal rfl after supported
  intro continues
  have kept := continues _ selectedEq
  have offered := setup.commitRecoveryProtocol.legalOption_of_legal semanticLegal owner
  change LegalOption setup.commitRecoveryProtocol before owner selected.1 at offered
  rw [selectedEq] at offered
  cases before with
  | none => exact offered.1.elim
  | some current =>
      have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
        setup.program current.point _ offered.2 ⟨owner, name, false, rfl⟩
      have currentInfo := setup.commitRecovery_atCommit_info owner
        (setup.proposalRecoveryEraseTrace trace)
      apply kept.2
      · simpa only [currentInfo, Option.elim_some] using notCommit
      · trivial

omit [Fintype Player] in
theorem proposalRecovery_refinement_of_cause_word (wellFormed : setup.WellFormed)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    {leftState rightState : setup.proposalRecoveryProtocol.State}
    (left : setup.proposalRecoveryProtocol.Trace leftState)
    (right : setup.proposalRecoveryProtocol.Trace rightState)
    (leftRetained : TracePrefix prior left) (rightRetained : TracePrefix prior right)
    (sameWord : setup.proposalRecoveryCauseWord who left = setup.proposalRecoveryCauseWord who
      right)
    (leftGood : setup.proposalRecoveryForeignGood who ⟨leftState, left⟩)
    (rightGood : setup.proposalRecoveryForeignGood who ⟨rightState, right⟩) :
    setup.ProposalRecoveryForeignRefinement who first prior
      ⟨leftState, left⟩ ⟨rightState, right⟩ := by
  have goodBefore {before after : setup.proposalRecoveryProtocol.State}
      (beforeTrace : setup.proposalRecoveryProtocol.Trace before)
      (joint : Player → Option (ProposalRecoveryMove Player L))
      (legal : setup.proposalRecoveryProtocol.Legal before joint)
      (supported : after ∈ (setup.proposalRecoveryProtocol.step before ⟨joint, legal⟩).support)
      (good : setup.proposalRecoveryForeignGood who ⟨after, beforeTrace.extend joint legal
        supported⟩) :
      setup.proposalRecoveryForeignGood who ⟨before, beforeTrace⟩ := by
    intro owner foreign generated
    obtain ⟨record, member, failed⟩ := generated
    apply good owner foreign
    refine ⟨record, ?_, failed⟩
    rw [InfoSignals.ownPlay_extend]
    cases chosen : joint owner
    · exact member
    · exact List.mem_cons_of_mem _ member
  induction leftRetained generalizing rightState with
  | refl =>
      have lengths := congrArg List.length sameWord
      rw [setup.proposalRecoveryCauseWord_length who, setup.proposalRecoveryCauseWord_length
        who] at lengths
      have same := rightRetained.eq_of_length (by omega)
      cases same
      exact .initial
  | @extend leftBefore leftAfter leftPrior leftRetained leftJoint leftLegal leftSupport ih =>
    cases rightRetained with
    | refl =>
        have lengths := congrArg List.length sameWord
        rw [setup.proposalRecoveryCauseWord_length who, setup.proposalRecoveryCauseWord_length
          who] at lengths
        have bounded := leftRetained.length_le
        simp only [Trace.length] at lengths
        omega
    | @extend rightBefore _ rightPrior rightRetained rightJoint rightLegal rightSupport =>
        change setup.proposalRecoveryCauseWord who leftPrior ++ [_] =
          setup.proposalRecoveryCauseWord who rightPrior ++ [_] at sameWord
        obtain ⟨oldWord, lastWord⟩ := List.append_inj' sameWord rfl
        have sameRead := List.singleton_inj.mp lastWord
        have paired := ih rightPrior rightRetained oldWord
          (goodBefore leftPrior leftJoint leftLegal leftSupport leftGood)
            (goodBefore rightPrior rightJoint rightLegal rightSupport rightGood)
        have signal := congrArg (fun read => read.1.1.1) sameRead
        change (setup.commitRecoveryPrivate who leftAfter,
            (setup.commitRecoveryPublic leftAfter,
              setup.proposalRecoveryProposalOf leftBefore leftJoint)) =
          (setup.commitRecoveryPrivate who rightState,
            (setup.commitRecoveryPublic rightState,
              setup.proposalRecoveryProposalOf rightBefore rightJoint)) at signal
        have publicResult : setup.attemptPublicSignal who leftAfter =
            setup.attemptPublicSignal who rightState := by
          exact congrArg (fun read =>
            (read.1.map (ProtocolView.publicOnly who setup.program), read.2.1)) signal
        have proposal := congrArg (fun read => read.2.2) signal
        have causeJoint : SourceProgram.Setup.proposalRecoveryForeignCauseJoint who leftJoint =
            SourceProgram.Setup.proposalRecoveryForeignCauseJoint who rightJoint := by
          exact Option.some.inj (congrArg Prod.snd sameRead)
        have labels := proposalRecovery_labels_of_cause_joint setup who leftJoint rightJoint
          leftLegal rightLegal causeJoint
        have changedProposal : leftJoint ≠ rightJoint →
            ∃ submitted, setup.proposalRecoveryProposalOf leftBefore leftJoint = some submitted
              := by
          intro different
          rcases labels with identical | ⟨owner, name, foreign, _other, cases⟩
          · exact (different identical).elim
          cases leftBefore with
          | none =>
              have offered := leftLegal.2 owner
              rcases cases with ⟨chosen, _⟩ | ⟨_, chosen⟩ <;>
                simp only [chosen] at offered <;> exact offered.1.elim
          | some current =>
              rcases cases with ⟨chosen, _⟩ | ⟨_, chosen⟩
              · exact proposalRecovery_exposed_of_proper setup wellFormed current leftPrior
                  leftJoint leftLegal owner name
                  true false chosen rfl
                    (goodBefore leftPrior leftJoint leftLegal leftSupport leftGood owner foreign)
              · exact proposalRecovery_exposed_of_proper setup wellFormed current leftPrior
                  leftJoint leftLegal owner name
                  false true chosen rfl
                    (goodBefore leftPrior leftJoint leftLegal leftSupport leftGood owner foreign)
        have changedExcluded : ∀ owner, leftJoint owner ≠ rightJoint owner →
            owner ∈ (setup.commitRecoveryPublic leftAfter).1 ∧
              owner ∈ (setup.commitRecoveryPublic rightState).1 := by
          intro owner different
          rcases labels with identical | ⟨author, name, _foreign, others, cases⟩
          · exact (different (congrFun identical owner)).elim
          have sameOwner : owner = author := by
            by_contra denied
            exact different (others owner denied)
          subst owner
          have excludedEq := congrArg (fun read => read.2.1.1) signal
          rcases cases with ⟨_chosen, rightChosen⟩ | ⟨_chosen, leftChosen⟩
          · have excluded := proposalRecovery_withheld_excluded setup rightPrior rightJoint
              rightLegal rightSupport
              author name rightChosen
            exact ⟨excludedEq.symm ▸ excluded, excluded⟩
          · have excluded := proposalRecovery_withheld_excluded setup leftPrior leftJoint
              leftLegal leftSupport
              author name leftChosen
            exact ⟨excluded, excludedEq ▸ excluded⟩
        exact .extend leftPrior rightPrior paired leftJoint rightJoint leftLegal rightLegal
          leftSupport rightSupport labels publicResult proposal changedProposal changedExcluded


omit [Fintype Player] in
theorem proposalRecovery_initialized_prefix : ∀ {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state),
    (⟨state, trace⟩ : setup.proposalRecoveryProtocol.History) =
        setup.proposalRecoveryProtocol.initHistory ∨
      ∃ (theta : State L setup.context) (_drawn : theta ∈ setup.initialLaw.support)
        (firstTrace : setup.proposalRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
          (ProtocolState.entry setup.program (setup.initialConfig theta)) ∅ 0))),
        firstTrace.length = 1 ∧ TracePrefix firstTrace trace := by
  intro state trace
  induction trace with
  | start => exact Or.inl rfl
  | @extend before after trace joint legal reached ih =>
      rcases ih with initialized | ⟨theta, drawn, firstTrace, depth, retained⟩
      · cases initialized
        obtain ⟨theta, drawn, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        exact Or.inr ⟨theta, drawn, .extend .start joint legal reached, rfl, .refl⟩
      · exact Or.inr ⟨theta, drawn, firstTrace, depth, .extend retained joint legal reached⟩
omit [Fintype Player] in
theorem proposalRecovery_initialized_trace_unique (first : CommitRecoveryState setup.program)
    (left right : setup.proposalRecoveryProtocol.Trace (some first))
    (leftDepth : left.length = 1) (rightDepth : right.length = 1) : left = right := by
  have unique : ∀ (state : setup.proposalRecoveryProtocol.State)
      (left right : setup.proposalRecoveryProtocol.Trace state),
      left.length = 1 → right.length = 1 → left = right := by
    intro state left
    induction left with
    | start => intro right leftDepth; simp only [Trace.length] at leftDepth; omega
    | extend leftPrior leftJoint leftLegal leftReached _ =>
      intro right leftDepth rightDepth
      cases leftPrior with
      | extend => simp only [Trace.length] at leftDepth; omega
      | start =>
        cases right with
        | start => simp only [Trace.length] at rightDepth; omega
        | extend rightPrior rightJoint rightLegal rightReached =>
          cases rightPrior with
          | extend => simp only [Trace.length] at rightDepth; omega
          | start =>
            have sameJoint : leftJoint = rightJoint := by
              funext owner
              have leftNone := LegalOption.eq_none_of_inactive _
                (setup.proposalRecoveryProtocol.legalOption_of_legal leftLegal owner)
                (by change ¬ False; exact not_false)
              have rightNone := LegalOption.eq_none_of_inactive _
                (setup.proposalRecoveryProtocol.legalOption_of_legal rightLegal owner)
                (by change ¬ False; exact not_false)
              exact leftNone.trans rightNone.symm
            cases sameJoint
            rfl
  exact unique _ left right leftDepth rightDepth

omit [Fintype Player] in
theorem proposalRecovery_refinement_of_closed_key (wellFormed : setup.WellFormed)
    (leftCurrent rightCurrent : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some leftCurrent))
    (right : setup.proposalRecoveryProtocol.Trace (some rightCurrent))
    (same : setup.proposalRecoveryClosedKey who ⟨some leftCurrent, left⟩ =
      setup.proposalRecoveryClosedKey who ⟨some rightCurrent, right⟩)
    (leftGood : setup.proposalRecoveryForeignGood who ⟨some leftCurrent, left⟩)
    (rightGood : setup.proposalRecoveryForeignGood who ⟨some rightCurrent, right⟩) :
    ∃ (first : CommitRecoveryState setup.program)
      (prior : setup.proposalRecoveryProtocol.Trace (some first)),
      setup.ProposalRecoveryForeignRefinement who first prior
        ⟨some leftCurrent, left⟩ ⟨some rightCurrent, right⟩ := by
  obtain initialized | ⟨leftTheta, _leftDrawn, leftPrior, leftDepth, leftRetained⟩ :=
    proposalRecovery_initialized_prefix setup left
  · cases initialized
  obtain initialized | ⟨rightTheta, _rightDrawn, rightPrior, rightDepth, rightRetained⟩ :=
    proposalRecovery_initialized_prefix setup right
  · cases initialized
  have leftBase := setup.commitRecovery_base_of_prefix _
    (setup.proposalRecoveryEraseTrace leftPrior) rfl (setup.proposalRecoveryEraseTrace left)
      (setup.proposalRecoveryEraseTrace_prefix leftRetained)
  have rightBase := setup.commitRecovery_base_of_prefix _
    (setup.proposalRecoveryEraseTrace rightPrior) rfl (setup.proposalRecoveryEraseTrace right)
      (setup.proposalRecoveryEraseTrace_prefix rightRetained)
  obtain ⟨leftState, leftStateEq, leftBase, _saved⟩ := leftBase
  obtain ⟨rightState, rightStateEq, rightBase, _saved⟩ := rightBase
  cases Option.some.inj leftStateEq
  cases Option.some.inj rightStateEq
  have thetaEq : leftTheta = rightTheta := by
    have bases := congrArg Prod.fst same
    simpa only [proposalRecoveryClosedKey, Option.map_some, Option.some.injEq,
      leftBase, rightBase, CommitRecoveryState.atPoint,
      ProtocolState.base_entry, Setup.initialConfig] using bases
  subst rightTheta
  have samePrior := proposalRecovery_initialized_trace_unique setup _ leftPrior rightPrior
    leftDepth rightDepth
  rw [← samePrior] at rightRetained
  refine ⟨_, leftPrior, proposalRecovery_refinement_of_cause_word setup who wellFormed _
    leftPrior left right
    leftRetained rightRetained ?_ leftGood rightGood⟩
  exact congrArg (fun key => key.2.2.1) same



omit [Fintype Player] in
/-- Publication cause changes preserve every raw typed field after erasing
private memories. Equal public output identifies the new publication cell. -/
private theorem proposalRecovery_raw_labels_erased (focal : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : SourceProgram.ProtocolState program)
      (excluded : Finset Player)
      (left right : Player → Option (ProposalRecoveryMove Player L)),
      ForeignDisclosureLabels focal left right →
      ∀ l ∈ (ProtocolState.recoveryStep program point excluded
        (proposalRecoveryJoint left)).support,
      ∀ r ∈ (ProtocolState.recoveryStep program point excluded
        (proposalRecoveryJoint right)).support,
      ProtocolView.publicOnly focal program (ProtocolState.observe focal program l.1) =
        ProtocolView.publicOnly focal program (ProtocolState.observe focal program r.1) →
      (ProtocolState.withHistory program l.1 (fun _ => []), l.2) =
        (ProtocolState.withHistory program r.1 (fun _ => []), r.2)
  | _, _, .ret _, _, _, _, _, _, l, lm, r, rm, _ => by
      rw [ProtocolState.recoveryStep, PMF.mem_support_pure_iff] at lm rm
      subst l; subst r; rfl
  | _, _, .sample name fresh law next, point, excluded, left, right, labels,
      l, lm, r, rm, publicEqual => by
      cases point with
      | inl config =>
          obtain ⟨lv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨rv, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          have cells := ProtocolView.publicOnly_entry_cells focal next _ _ (Sum.inr.inj publicEqual)
          have same := congrArg (fun view => view.cells _ _ .here) cells
          change lv = rv at same
          subst rv
          rfl
      | inr point =>
          obtain ⟨lv, ls, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨rv, rs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          exact congrArg (fun result => (Sum.inr result.1, result.2))
            (proposalRecovery_raw_labels_erased focal next point excluded left right labels
              lv ls rv rs (Sum.inr.inj publicEqual))
  | _, _, .commit (payload := payload) name owner fresh guard next, point, excluded, left,
      right, labels,
      l, lm, r, rm, publicEqual => by
      cases point with
      | inl config =>
          have read :
              (OwnAction.binding owner name payload ((proposalRecoveryJoint left owner).map
                  (·.action)),
                CommitRecoveryMove.missed (proposalRecoveryJoint left owner)) =
              (OwnAction.binding owner name payload ((proposalRecoveryJoint right owner).map
                  (·.action)),
                CommitRecoveryMove.missed (proposalRecoveryJoint right owner)) := by
            rcases labels with same | ⟨author, subject, _foreign, others, cases⟩
            · rw [same]
            · by_cases own : owner = author
              · subst author
                rcases cases with ⟨lc, rc⟩ | ⟨rc, lc⟩ <;>
                  simp [proposalRecoveryJoint, lc, rc, ProposalRecoveryMove.ordinary,
                    ProposalRecoveryMove.failedDisclosure, OwnAction.binding,
                    CommitRecoveryMove.missed]
              · simp only [proposalRecoveryJoint, others owner own]
          have laws : ProtocolState.recoveryStep (.commit name owner fresh guard next)
              (.inl config) excluded (proposalRecoveryJoint left) =
            ProtocolState.recoveryStep (.commit name owner fresh guard next)
              (.inl config) excluded (proposalRecoveryJoint right) := by
            simp only [ProtocolState.recoveryStep, Sum.elim_inl, (Prod.mk.inj read).1,
              (Prod.mk.inj read).2]
          rw [laws] at lm
          obtain ⟨result, pure⟩ := ProtocolState.recoveryStep_commit_pure
            (.commit name owner fresh guard next) (.inl config) excluded
            (proposalRecoveryJoint right) rfl
          rw [pure, PMF.mem_support_pure_iff] at lm rm
          subst l; subst r; rfl
      | inr point =>
          obtain ⟨lv, ls, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨rv, rs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          exact congrArg (fun result => (Sum.inr result.1, result.2))
            (proposalRecovery_raw_labels_erased focal next point excluded left right labels
              lv ls rv rs (Sum.inr.inj publicEqual))
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded,
      left, right, labels, l, lm, r, rm, publicEqual => by
      cases point with
      | inl config =>
          by_cases inactive : owner ∈ excluded
          · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ite_true,
              PMF.mem_support_pure_iff] at lm rm
            subst l; subst r; rfl
          · simp only [ProtocolState.recoveryStep, Sum.elim_inl, inactive, ite_false,
                PMF.mem_support_pure_iff] at lm rm
            subst l; subst r
            have cells := ProtocolView.publicOnly_entry_cells focal next _ _ (Sum.inr.inj
                publicEqual)
            have cell := congrArg (fun view => view.cells published _ .here) cells
            let first := revealSuccessor published source config
              (OwnAction.disclosure ((proposalRecoveryJoint left owner).map (·.action)))
            let second := revealSuccessor published source config
              (OwnAction.disclosure ((proposalRecoveryJoint right owner).map (·.action)))
            have value : first.state.get .here = second.state.get .here := by
              simpa only [Config.view, SourceObservation.publicOnly,
                sourceObserve_publication] using cell
            have configs : { first with history := fun _ => [] } =
                { second with history := fun _ => [] } := by
              change Config.mk (Env.cons (first.state.get .here) config.state)
                  (Registry.weaken config.registry) (Revelations.reveal config.revelations source)
                  (fun _ => []) =
                Config.mk (Env.cons (second.state.get .here) config.state)
                  (Registry.weaken config.registry) (Revelations.reveal config.revelations source)
                  (fun _ => [])
              rw [value]
            apply Prod.ext
            · simp only [ProtocolState.withHistory, Sum.elim_inr,
                ProtocolState.withHistory_entry]
              congr 2
            · exact congrArg (fun x => match x with
                  | .failure => insert owner excluded | .success _ => excluded) value
      | inr point =>
          obtain ⟨lv, ls, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
          obtain ⟨rv, rs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
          exact congrArg (fun result => (Sum.inr result.1, result.2))
            (proposalRecovery_raw_labels_erased focal next point excluded left right labels
              lv ls rv rs (Sum.inr.inj publicEqual))

omit [Fintype Player] in
private theorem proposalRecovery_public_erase (focal : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : SourceProgram.ProtocolState program) :
    ProtocolView.publicOnly focal program (ProtocolState.observe focal program
        (ProtocolState.withHistory program point (fun _ => []))) =
      ProtocolView.publicOnly focal program (ProtocolState.observe focal program point) := by
  rw [← ProtocolView.eraseHistory_observe, ProtocolView.publicOnly_eraseHistory]

omit [Fintype Player] in
/-- The erased semantic successor is fixed by the retained source causes and
actual public result, including the original recovery dispatcher. -/
private theorem proposalRecovery_step_labels_erased (focal : Player)
    (first second : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some first))
    (right : setup.proposalRecoveryProtocol.Trace (some second))
    (same : first.eraseHistory = second.eraseHistory)
    (leftJoint rightJoint : Player → Option (ProposalRecoveryMove Player L))
    (leftLegal : setup.proposalRecoveryProtocol.Legal (some first) leftJoint)
    (rightLegal : setup.proposalRecoveryProtocol.Legal (some second) rightJoint)
    (labels : ForeignDisclosureLabels focal leftJoint rightJoint)
    (leftNext rightNext : CommitRecoveryState setup.program)
    (ls : leftNext ∈ (first.step (proposalRecoveryJoint leftJoint)).support)
    (rs : rightNext ∈ (second.step (proposalRecoveryJoint rightJoint)).support)
    (publicEqual : setup.attemptPublicSignal focal (some leftNext) =
      setup.attemptPublicSignal focal (some rightNext)) :
    leftNext.eraseHistory = rightNext.eraseHistory := by
  have point := congrArg CommitRecoveryState.point same
  change ProtocolState.withHistory setup.program first.point (fun _ => []) =
    ProtocolState.withHistory setup.program second.point (fun _ => []) at point
  have excluded : first.excluded = second.excluded := by
    simpa only [CommitRecoveryState.eraseHistory] using
      congrArg CommitRecoveryState.excluded same
  have generation : first.generation = second.generation := by
    simpa only [CommitRecoveryState.eraseHistory] using
      congrArg CommitRecoveryState.generation same
  have control : ProtocolState.atCommit setup.program first.point =
      ProtocolState.atCommit setup.program second.point := by
    simpa only [CommitRecoveryState.eraseHistory,
      (ProtocolState.withHistory_control _ _ _).2.1] using
        congrArg (ProtocolState.atCommit setup.program) point
  by_cases committing : ProtocolState.atCommit setup.program first.point = true
  · have joints : leftJoint = rightJoint := by
      rcases labels with identical | ⟨owner, name, foreign, others, cases⟩
      · exact identical
      · have chosen : ∃ bit proposed,
            leftJoint owner = some ⟨⟨.reveal owner name bit, false⟩, proposed⟩ := by
          rcases cases with ⟨lc, rc⟩ | ⟨rc, lc⟩
          · exact ⟨true, false, lc⟩
          · exact ⟨false, true, lc⟩
        obtain ⟨bit, proposed, chosen⟩ := chosen
        have offered := leftLegal.2 owner
        rw [chosen] at offered
        have notCommit := ProtocolState.not_atCommit_of_recoveryAvailable_reveal owner
          setup.program first.point _ offered.2.1 ⟨owner, name, bit, rfl⟩
        rw [committing] at notCommit
        cases notCommit
    subst rightJoint
    have lm : leftNext.eraseHistory ∈
        ((first.step (proposalRecoveryJoint leftJoint)).map
            CommitRecoveryState.eraseHistory).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨leftNext, ls, rfl⟩
    have rm : rightNext.eraseHistory ∈
        ((second.step (proposalRecoveryJoint leftJoint)).map
            CommitRecoveryState.eraseHistory).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨rightNext, rs, rfl⟩
    rw [← first.step_eraseHistory] at lm
    rw [← second.step_eraseHistory, ← same] at rm
    obtain ⟨l, ls, leq⟩ := (PMF.mem_support_map_iff _ _ _).mp lm
    obtain ⟨r, rs, req⟩ := (PMF.mem_support_map_iff _ _ _).mp rm
    have unique := first.eraseHistory.step_unique_of_commit
      (by simpa only [CommitRecoveryState.eraseHistory,
        (ProtocolState.withHistory_control _ _ _).2.1] using committing)
      (proposalRecoveryJoint leftJoint) l r ls rs
    exact leq.symm.trans ((congrArg CommitRecoveryState.eraseHistory unique).trans req)
  · have notCommit := Bool.eq_false_iff.mpr committing
    obtain ⟨lr, lm, rfl⟩ := first.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace left))
      notCommit _ _ ls
    obtain ⟨rr, rm, rfl⟩ := second.step_noncommit_atPoint
      (setup.commitRecovery_blockFrontier (setup.proposalRecoveryEraseTrace right))
      (control ▸ notCommit) _ _ rs
    let erase := fun result : SourceProgram.ProtocolState setup.program × Finset Player =>
      (ProtocolState.withHistory setup.program result.1 (fun _ => []), result.2)
    have normalized (current : SourceProgram.ProtocolState setup.program) (E : Finset Player)
        (joint : Player → Option (CommitRecoveryMove Player L))
        (result : SourceProgram.ProtocolState setup.program × Finset Player)
        (member : result ∈ (ProtocolState.recoveryStep setup.program current E joint).support) :
        ∃ normalized ∈ (ProtocolState.recoveryStep setup.program
            (ProtocolState.withHistory setup.program current (fun _ => [])) E joint).support,
          erase normalized = erase result := by
      have present := (PMF.mem_support_map_iff erase _ _).mpr ⟨result, member, rfl⟩
      rw [← ProtocolState.recoveryStep_eraseHistory] at present
      exact (PMF.mem_support_map_iff _ _ _).mp present
    obtain ⟨ln, lnSupport, lnEq⟩ := normalized first.point first.excluded _ lr lm
    obtain ⟨rn, rnSupport, rnEq⟩ := normalized second.point second.excluded _ rr rm
    dsimp only [erase] at lnEq rnEq
    have lp := congrArg Prod.fst lnEq
    have rp := congrArg Prod.fst rnEq
    dsimp only at lp rp
    rw [← point, ← excluded] at rnSupport
    have observed : ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program ln.1) =
      ProtocolView.publicOnly focal setup.program
        (ProtocolState.observe focal setup.program rn.1) := by
      rw [← proposalRecovery_public_erase focal _ ln.1,
        ← proposalRecovery_public_erase focal _ rn.1,
        lp, rp,
        proposalRecovery_public_erase, proposalRecovery_public_erase]
      exact Option.some.inj (congrArg Prod.fst publicEqual)
    have raw := proposalRecovery_raw_labels_erased focal setup.program _ _
      leftJoint rightJoint labels ln lnSupport rn rnSupport observed
    have results : erase lr = erase rr := lnEq.symm.trans (raw.trans rnEq)
    have installed := congrArg (fun result =>
      CommitRecoveryState.atPoint result.1 result.2 first.generation) results
    simpa only [erase, CommitRecoveryState.eraseHistory, CommitRecoveryState.atPoint,
      generation] using installed


omit [Fintype Player] in
/-- The actual refinement retains both typed cursors and the complete erased
source history; hidden publication labels only change discarded memories. -/
theorem ProposalRecoveryForeignRefinement.erasedHistory
    {focal : Player} {first : CommitRecoveryState setup.program}
    {prior : setup.proposalRecoveryProtocol.Trace (some first)}
    {left right : setup.proposalRecoveryProtocol.History}
    (refines : setup.ProposalRecoveryForeignRefinement focal first prior left right) :
    setup.proposalRecoveryErasedHistory left = setup.proposalRecoveryErasedHistory right := by
  have strengthened : ∃ lc rc, left.state = some lc ∧ right.state = some rc ∧
      setup.proposalRecoveryErasedHistory left = setup.proposalRecoveryErasedHistory right := by
    induction refines with
    | initial => exact ⟨first, first, rfl, rfl, rfl⟩
    | @extend leftState rightState leftAfter rightAfter left right earlier leftJoint rightJoint
        leftLegal rightLegal leftSupported rightSupported labels publicEqual proposal changed
          excluded ih =>
        obtain ⟨lc, rc, lh, rh, equal⟩ := ih
        dsimp only at lh rh
        subst leftState; subst rightState
        obtain ⟨ln, ls, leq⟩ := (PMF.mem_support_map_iff _ _ _).mp leftSupported
        obtain ⟨rn, rs, req⟩ := (PMF.mem_support_map_iff _ _ _).mp rightSupported
        subst leftAfter; subst rightAfter
        have stateEq : lc.eraseHistory = rc.eraseHistory :=
          Option.some.inj (congrArg Prod.fst (congrArg Prod.fst equal))
        have nextEq := proposalRecovery_step_labels_erased setup focal lc rc left right
          stateEq leftJoint rightJoint leftLegal rightLegal labels ln rn ls rs publicEqual
        refine ⟨ln, rn, rfl, rfl, ?_⟩
        change setup.proposalRecoveryErasedHistory
            ((⟨some lc, left⟩ : setup.proposalRecoveryProtocol.History).extend leftLegal
                leftSupported) =
          setup.proposalRecoveryErasedHistory
            ((⟨some rc, right⟩ : setup.proposalRecoveryProtocol.History).extend rightLegal
                rightSupported)
        rw [setup.proposalRecoveryErasedHistory_extend,
          setup.proposalRecoveryErasedHistory_extend, equal]
        simp only [proposalRecoveryNextErasedHistory, Option.map_some, nextEq, proposal]
  exact strengthened.choose_spec.choose_spec.2.2

omit [Fintype Player] in
private theorem proposalRecovery_good_before (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support)
    (good : setup.proposalRecoveryForeignGood focal (before.extend legal supported)) :
    setup.proposalRecoveryForeignGood focal before := by
  intro owner foreign generated
  exact good owner foreign
    (generated_preparation_before_extend setup owner before.trace joint legal supported generated)

omit [Fintype Player] in
private theorem proposalRecovery_base_extend
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support) :
    after.map (fun state => ProtocolState.base setup.program state.point) =
      some (ProtocolState.base setup.program current.point) := by
  obtain initial | ⟨theta, drawn, first, depth, retained⟩ :=
    proposalRecovery_initialized_prefix setup trace
  · cases initial
  obtain ⟨actual, equality, point, saved⟩ := setup.commitRecovery_base_of_prefix _
    (setup.proposalRecoveryEraseTrace first) rfl (setup.proposalRecoveryEraseTrace trace)
    (setup.proposalRecoveryEraseTrace_prefix retained)
  cases Option.some.inj equality
  obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨nextBase, _⟩ := current.step_base _ point saved
    (proposalRecoveryJoint joint) next reached
  exact congrArg some (nextBase.trans point.symm)

omit [Fintype Player] in
private theorem proposalRecoveryCauseWord_last (focal : Player)
    {state} (trace : setup.proposalRecoveryProtocol.Trace state) :
    (setup.proposalRecoveryCauseWord focal trace).getLast? =
      some (setup.proposalRecoveryForeignCauseRead focal ⟨state, trace⟩) := by
  cases trace <;> simp [proposalRecoveryCauseWord]

omit [Fintype Player] in
/-- Peeling a selected child recovers the exact parent key. This applies to
arbitrary target histories, rather than only the canonical extension. -/
theorem proposalRecoveryClosedKey_prior
    (focal : Player) (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (good : setup.proposalRecoveryForeignGood focal
      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported))
    (target : setup.proposalRecoveryProtocol.History)
    (same : setup.proposalRecoveryClosedKey focal target = setup.proposalRecoveryClosedKey focal
      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported)) :
    setup.proposalRecoveryClosedKey focal target.prior =
      setup.proposalRecoveryClosedKey focal ⟨some current, trace⟩ := by
  classical
  have depth := setup.proposalRecoveryClosedKey_depth focal _ target same
  have targetGood : setup.proposalRecoveryForeignGood focal target := by
    have bit := congrArg (fun key => key.2.2.2) same
    simpa only [proposalRecoveryClosedKey, good, decide_true, decide_eq_true_eq] using bit
  rcases target with ⟨state, target⟩
  cases target with
  | start => simp only [Trace.length, History.extend] at depth; omega
  | @extend before after earlier moves offered reached =>
      have word := congrArg (fun key => key.2.2.1) same
      change setup.proposalRecoveryCauseWord focal earlier ++ [_] =
        setup.proposalRecoveryCauseWord focal trace ++ [_] at word
      have previous := (List.append_inj' word rfl).1
      have read := Option.some.inj (by
        simpa only [proposalRecoveryCauseWord_last] using congrArg List.getLast? previous)
      have beforeSome : ∃ previous, before = some previous := by
        obtain initial | ⟨theta, drawn, first, length, retainedPrefix⟩ :=
          proposalRecovery_initialized_prefix setup earlier
        · have sourceDepth : 0 < trace.length := by
            obtain initial | ⟨_, _, first, length, retained⟩ :=
              proposalRecovery_initialized_prefix setup trace
            · have impossible := congrArg History.state initial
              contradiction
            · have bound := retained.length_le
              omega
          have earlierDepth : earlier.length = 0 := by cases initial; rfl
          simp only [History.extend, Trace.length, earlierDepth] at depth
          omega
        · obtain ⟨actual, equal, _, _⟩ := setup.commitRecovery_base_of_prefix _
            (setup.proposalRecoveryEraseTrace first) rfl
            (setup.proposalRecoveryEraseTrace earlier)
            (setup.proposalRecoveryEraseTrace_prefix retainedPrefix)
          exact ⟨actual, equal⟩
      obtain ⟨previousState, rfl⟩ := beforeSome
      change setup.proposalRecoveryClosedKey focal ⟨some previousState, earlier⟩ =
        setup.proposalRecoveryClosedKey focal ⟨some current, trace⟩
      have bases := congrArg Prod.fst same
      change ((⟨some previousState, earlier⟩ : setup.proposalRecoveryProtocol.History).extend
          offered reached).state.map (fun s => ProtocolState.base setup.program s.point) =
        ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend
          legal supported).state.map (fun s => ProtocolState.base setup.program s.point) at bases
      dsimp only [History.extend] at bases
      rw [
        proposalRecovery_base_extend setup previousState earlier moves offered reached,
        proposalRecovery_base_extend setup current trace joint legal supported] at bases
      have infos : setup.proposalRecoveryModel.infoOf focal earlier =
          setup.proposalRecoveryModel.infoOf focal trace := congrArg Prod.fst read
      apply Prod.ext bases
      apply Prod.ext infos
      apply Prod.ext previous
      have leftGood := proposalRecovery_good_before setup focal
        ⟨some previousState, earlier⟩ moves offered reached targetGood
      have rightGood := proposalRecovery_good_before setup focal
        ⟨some current, trace⟩ joint legal supported good
      exact (decide_eq_true_eq.mpr leftGood).trans (decide_eq_true_eq.mpr rightGood).symm


omit [Fintype Player] in
private theorem proposalRecovery_good_extend_iff (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support) :
    setup.proposalRecoveryForeignGood focal (before.extend legal supported) ↔
      setup.proposalRecoveryForeignGood focal before ∧
        ∀ owner, owner ≠ focal → ¬ ProposalRecoveryMove.GeneratedPreparationFailure (joint
          owner) := by
  constructor
  · intro good
    refine ⟨proposalRecovery_good_before setup focal before joint legal supported good, ?_⟩
    intro owner foreign failed
    cases selected : joint owner with
    | none => simp only [selected, ProposalRecoveryMove.GeneratedPreparationFailure,
        Option.elim_none] at failed
    | some move =>
      apply good owner foreign
      refine ⟨(setup.proposalRecoveryModel.infoOf owner before.trace, move), ?_, ?_⟩
      · change _ ∈ setup.proposalRecoveryModel.ownPlay owner
          (before.trace.extend joint legal supported)
        rw [InfoSignals.ownPlay_extend, selected]
        exact List.mem_cons_self
      · simpa only [selected] using failed
  · rintro ⟨beforeGood, rowGood⟩ owner foreign ⟨record, member, failed⟩
    change record ∈ setup.proposalRecoveryModel.ownPlay owner
      (before.trace.extend joint legal supported) at member
    rw [InfoSignals.ownPlay_extend] at member
    cases selected : joint owner with
    | none =>
      simp only [selected] at member
      exact beforeGood owner foreign ⟨record, member, failed⟩
    | some move =>
      simp only [selected, List.mem_cons] at member
      rcases member with equal | member
      · subst record
        exact rowGood owner foreign (by simpa only [selected] using failed)
      · exact beforeGood owner foreign ⟨record, member, failed⟩

omit [Fintype Player] in
private theorem proposalRecoveryClosedKey_extend_congr (focal : Player)
    (first : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some first))
    (left right : setup.proposalRecoveryProtocol.History)
    (refines : setup.ProposalRecoveryForeignRefinement focal first prior left right)
    (same : setup.proposalRecoveryClosedKey focal left = setup.proposalRecoveryClosedKey focal
      right)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (ll : setup.proposalRecoveryProtocol.Legal left.state joint)
    (rl : setup.proposalRecoveryProtocol.Legal right.state joint)
    {la ra} (ls : la ∈ (setup.proposalRecoveryProtocol.step left.state ⟨joint, ll⟩).support)
    (rs : ra ∈ (setup.proposalRecoveryProtocol.step right.state ⟨joint, rl⟩).support)
    (next : (la.map CommitRecoveryState.eraseHistory,
        setup.proposalRecoveryProposalOf left.state joint) =
      (ra.map CommitRecoveryState.eraseHistory,
        setup.proposalRecoveryProposalOf right.state joint)) :
    setup.proposalRecoveryClosedKey focal (left.extend ll ls) =
      setup.proposalRecoveryClosedKey focal (right.extend rl rs) := by
  classical
  have states := congrArg Prod.fst next
  have proposal := congrArg Prod.snd next
  have publicEqual : setup.attemptPublicSignal focal la = setup.attemptPublicSignal focal ra := by
    have signal (state : setup.proposalRecoveryProtocol.State) :
        setup.attemptPublicSignal focal (state.map CommitRecoveryState.eraseHistory) =
          setup.attemptPublicSignal focal state := by
      cases state with
      | none => rfl
      | some current =>
        simp only [Option.map_some, attemptPublicSignal, commitRecoveryPrivate,
          commitRecoveryPublic, CommitRecoveryState.eraseHistory, proposalRecovery_public_erase,
          ProtocolState.remaining_withHistory]
    exact (signal la).symm.trans
      ((congrArg (setup.attemptPublicSignal focal) states).trans (signal ra))
  have extended := ProposalRecoveryForeignRefinement.extend left.trace right.trace refines
    joint joint ll rl ls rs
    (Or.inl rfl) publicEqual proposal (fun different => (different rfl).elim)
    (fun owner different => (different rfl).elim)
  have base : (left.extend ll ls).state.map (fun s => ProtocolState.base setup.program s.point) =
      (right.extend rl rs).state.map (fun s => ProtocolState.base setup.program s.point) := by
    have erased := congrArg Prod.fst (congrArg Prod.fst extended.erasedHistory)
    have base := congrArg (Option.map fun s => ProtocolState.base setup.program s.point) erased
    simpa only [proposalRecoveryErasedHistory, commitRecoveryErasedHistory,
      History.extend, Option.map_map, Function.comp_def, CommitRecoveryState.eraseHistory,
      ProtocolState.base_withHistory] using base
  have words := congrArg (fun key => key.2.2.1) same
  change setup.proposalRecoveryCauseWord focal left.trace =
    setup.proposalRecoveryCauseWord focal right.trace at words
  have good : setup.proposalRecoveryForeignGood focal left ↔
      setup.proposalRecoveryForeignGood focal right := by
    exact decide_eq_decide.mp (congrArg (fun key => key.2.2.2) same)
  apply Prod.ext base
  apply Prod.ext extended.info_eq
  apply Prod.ext
  · change setup.proposalRecoveryCauseWord focal (left.extend ll ls).trace =
      setup.proposalRecoveryCauseWord focal (right.extend rl rs).trace
    simp only [History.extend, proposalRecoveryCauseWord, words, proposalRecoveryForeignCauseRead,
      proposalRecoveryJointRecall, List.head?_cons, extended.info_eq]
  · apply decide_eq_decide.mpr
    rw [proposalRecovery_good_extend_iff, proposalRecovery_good_extend_iff, good]

/-- The actual prescribed one-step class law is constant on the closed source
fiber. The proof couples original legal joints and original chance results. -/
theorem proposalRecoveryClosedKey_step_law
    (prescription : ∀ owner, setup.ProposalRecoveryPrescription owner)
    (wellFormed : setup.WellFormed) (focal : Player)
    (lc rc : CommitRecoveryState setup.program)
    (left : setup.proposalRecoveryProtocol.Trace (some lc))
    (right : setup.proposalRecoveryProtocol.Trace (some rc))
    (same : setup.proposalRecoveryClosedKey focal ⟨some lc, left⟩ =
      setup.proposalRecoveryClosedKey focal ⟨some rc, right⟩)
    (good : setup.proposalRecoveryForeignGood focal ⟨some lc, left⟩)
    (running : ¬ setup.proposalRecoveryProtocol.terminal (some lc)) :
    (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryPrescribedProfile prescription) 1 ⟨some lc, left⟩).map
        (setup.proposalRecoveryClosedKey focal) =
      (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryPrescribedProfile prescription) 1 ⟨some rc, right⟩).map
        (setup.proposalRecoveryClosedKey focal) := by
  classical
  have rightGood : setup.proposalRecoveryForeignGood focal ⟨some rc, right⟩ := by
    have bit := congrArg (fun key => key.2.2.2) same
    simpa only [proposalRecoveryClosedKey, good, decide_true, true_eq_decide_iff] using bit
  obtain ⟨first, prior, refines⟩ := proposalRecovery_refinement_of_closed_key setup focal
    wellFormed lc rc left right same good rightGood
  have erased := refines.erasedHistory
  have stateEq : (some lc).map CommitRecoveryState.eraseHistory =
      (some rc).map CommitRecoveryState.eraseHistory :=
    congrArg Prod.fst (congrArg Prod.fst erased)
  have rightRunning : ¬ setup.proposalRecoveryProtocol.terminal (some rc) :=
    fun terminal => running ((setup.commitRecovery_terminal_eq_of_erased stateEq).mpr terminal)
  let profile := setup.proposalRecoveryPrescribedProfile prescription
  have joints : (setup.proposalRecoveryModel.behavioralJoint profile left running).map Subtype.val =
      (setup.proposalRecoveryModel.behavioralJoint profile right rightRunning).map Subtype.val := by
    rw [InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
    congr 1
    funext owner
    exact setup.proposalRecoveryPrescribedProfile_normalized prescription owner _ _
      (setup.proposalRecoveryQuery_eq_of_erased_history _ _ erased owner)
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 running,
    InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 rightRunning,
    PMF.map_bind, PMF.map_bind]
  apply bind_eq_of_map_eq _ _ Subtype.val Subtype.val joints
  intro lj _ rj _ equal
  rcases lj with ⟨joint, ll⟩
  rcases rj with ⟨other, rl⟩
  dsimp only at equal
  subst other
  simp only [map_bindOnSupport, InformationModel.runBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_zero, PMF.pure_map]
  let lImage := fun state => if hs : state ∈
      (setup.proposalRecoveryProtocol.step (some lc) ⟨joint, ll⟩).support then
    setup.proposalRecoveryClosedKey focal
      ((⟨some lc, left⟩ : setup.proposalRecoveryProtocol.History).extend ll hs)
    else setup.proposalRecoveryClosedKey focal ⟨some lc, left⟩
  let rImage := fun state => if hs : state ∈
      (setup.proposalRecoveryProtocol.step (some rc) ⟨joint, rl⟩).support then
    setup.proposalRecoveryClosedKey focal
      ((⟨some rc, right⟩ : setup.proposalRecoveryProtocol.History).extend rl hs)
    else setup.proposalRecoveryClosedKey focal ⟨some rc, right⟩
  have leftTotal := bindOnSupport_eq_bind_of_eq_on_support
    (setup.proposalRecoveryProtocol.step (some lc) ⟨joint, ll⟩)
    (f := fun state hs => PMF.pure (setup.proposalRecoveryClosedKey focal
      ((⟨some lc, left⟩ : setup.proposalRecoveryProtocol.History).extend ll hs)))
    (g := fun state => PMF.pure (lImage state)) (fun state hs => by simp only [lImage,
      dite_eq_left hs])
  have rightTotal := bindOnSupport_eq_bind_of_eq_on_support
    (setup.proposalRecoveryProtocol.step (some rc) ⟨joint, rl⟩)
    (f := fun state hs => PMF.pure (setup.proposalRecoveryClosedKey focal
      ((⟨some rc, right⟩ : setup.proposalRecoveryProtocol.History).extend rl hs)))
    (g := fun state => PMF.pure (rImage state)) (fun state hs => by simp only [rImage,
      dite_eq_left hs])
  rw [leftTotal, rightTotal]
  apply bind_eq_of_map_eq _ _ _ _ (setup.proposalRecovery_step_erased_eq stateEq joint ll rl)
  intro la ls ra rs next
  simp only [lImage, rImage, dite_eq_left ls, dite_eq_left rs]
  exact congrArg PMF.pure (proposalRecoveryClosedKey_extend_congr setup focal first prior
    ⟨some lc, left⟩ ⟨some rc, right⟩ refines same joint ll rl ls rs next)

/-- The actual child class mass is the parent mass times its original one-step
class atom. No normalization or positive-mass premise is required. -/
theorem proposalRecoveryClosedMass_extend
    (prescription : ∀ owner, setup.ProposalRecoveryPrescription owner)
    (wellFormed : setup.WellFormed) (focal : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (good : setup.proposalRecoveryForeignGood focal
      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported)) :
    let profile := setup.proposalRecoveryPrescribedProfile prescription
    let parent : setup.proposalRecoveryProtocol.History := ⟨some current, trace⟩
    let child := parent.extend legal supported
    setup.proposalRecoveryClosedMass profile focal child =
      setup.proposalRecoveryClosedMass profile focal parent *
        ((setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent).map
          (setup.proposalRecoveryClosedKey focal)) (setup.proposalRecoveryClosedKey focal
            child) := by
  classical
  intro profile parent child
  let key := setup.proposalRecoveryClosedKey focal
  let initial := setup.proposalRecoveryModel.runBehavioral profile trace.length
  let row := fun h : setup.proposalRecoveryProtocol.History =>
    (setup.proposalRecoveryModel.runBehavioralFrom profile 1 h).map key
  have beforeGood := proposalRecovery_good_before setup focal parent joint legal supported good
  have kernels (h : setup.proposalRecoveryProtocol.History) (present : h ∈ initial.support) :
      row h (key child) = if key h = key parent then row parent (key child) else 0 := by
    by_cases same : key h = key parent
    · rw [ite_eq_left same]
      rcases h with ⟨state, ht⟩
      cases state with
      | none =>
          have base := congrArg Prod.fst same
          simp only [key, proposalRecoveryClosedKey, Option.map_none,
            parent, Option.map_some, reduceCtorEq] at base
      | some actual =>
          have law := setup.proposalRecoveryClosedKey_step_law prescription wellFormed focal
            current actual trace ht same.symm beforeGood legal.1
          exact congrArg (fun distribution => distribution (key child)) law.symm
    · rw [ite_eq_right same]
      apply (PMF.apply_eq_zero_iff _ _).mpr
      intro reached
      obtain ⟨target, ts, selected⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      have oldDepth := (setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin profile
        trace.length setup.proposalRecoveryProtocol.initHistory h present).trace_length_le_add
      have newDepth := setup.proposalRecoveryClosedKey_depth focal child target selected
      have reach := setup.proposalRecoveryModel.runBehavioralFrom_reachesWithin profile 1 h
        target ts
      have previous : target.prior = h := by
        cases reach with
        | refl =>
            simp only [ExecutionProtocol.initHistory, Trace.length, zero_add] at oldDepth
            simp only [child, parent, History.extend, Trace.length] at newDepth
            omega
        | step moves offered realized rest => cases rest; rfl
      apply same
      rw [← previous]
      exact setup.proposalRecoveryClosedKey_prior focal current trace joint legal supported
        good target selected
  change ((setup.proposalRecoveryModel.runBehavioral profile (trace.length + 1)).map key)
    (key child) = _
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom_add,
    PMF.map_bind, PMF.bind_apply]
  change (∑' h, initial h * row h (key child)) = _
  calc
    _ = ∑' h, (if key h = key parent then initial h else 0) * row parent (key child) := by
      apply tsum_congr
      intro h
      by_cases zero : initial h = 0
      · simp only [zero, zero_mul, ite_self]
      · rw [kernels h ((PMF.mem_support_iff _ _).mpr zero)]
        split <;> simp only [mul_zero, zero_mul]
    _ = (∑' h, if key h = key parent then initial h else 0) * row parent (key child) :=
      ENNReal.tsum_mul_right
    _ = _ := by
      congr 1
      change (∑' h, if key h = key parent then initial h else 0) = (initial.map key) (key parent)
      rw [PMF.map_apply]
      apply tsum_congr
      intro h
      by_cases equal : key h = key parent
      · rw [ite_eq_left equal, ite_eq_left equal.symm]
      · rw [ite_eq_right equal, ite_eq_right (Ne.symm equal)]

/-- The PUB mass recurrence uses precisely the actual ForeignCauseRead
marginal. The retained parent prefix adds no further one-step restriction. -/
theorem proposalRecoveryClosedMass_cause
    (prescription : ∀ owner, setup.ProposalRecoveryPrescription owner)
    (wellFormed : setup.WellFormed) (focal : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support)
    (good : setup.proposalRecoveryForeignGood focal
      ((⟨some current, trace⟩ : setup.proposalRecoveryProtocol.History).extend legal supported)) :
    let profile := setup.proposalRecoveryPrescribedProfile prescription
    let parent : setup.proposalRecoveryProtocol.History := ⟨some current, trace⟩
    let child := parent.extend legal supported
    setup.proposalRecoveryClosedMass profile focal child =
      setup.proposalRecoveryClosedMass profile focal parent *
        ((setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent).map
          (setup.proposalRecoveryForeignCauseRead focal))
            (setup.proposalRecoveryForeignCauseRead focal child) := by
  classical
  intro profile parent child
  rw [setup.proposalRecoveryClosedMass_extend prescription wellFormed focal current trace
    joint legal supported good]
  congr 1
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro other
  by_cases zero : setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent other = 0
  · have zero' : (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryPrescribedProfile prescription) 1
        ⟨some current, trace⟩) other = 0 := zero
    simp only [zero', zero, ite_self]
  have present := (PMF.mem_support_iff _ _).mpr zero
  rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 legal.1,
    PMF.mem_support_bind_iff] at present
  obtain ⟨⟨moves, offered⟩, _, present⟩ := present
  obtain ⟨next, reached, landed⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp present
  change other ∈ (PMF.pure (parent.extend offered reached)).support at landed
  cases (PMF.mem_support_pure_iff _ _).mp landed
  have equivalent : setup.proposalRecoveryClosedKey focal (parent.extend offered reached) =
      setup.proposalRecoveryClosedKey focal child ↔
    setup.proposalRecoveryForeignCauseRead focal (parent.extend offered reached) =
      setup.proposalRecoveryForeignCauseRead focal child := by
    constructor
    · intro same
      apply Option.some.inj
      have words := congrArg (fun key => key.2.2.1) same
      change setup.proposalRecoveryCauseWord focal (parent.extend offered reached).trace =
        setup.proposalRecoveryCauseWord focal child.trace at words
      simpa only [proposalRecoveryCauseWord_last] using congrArg List.getLast? words
    · intro observed
      have labels := proposalRecovery_labels_of_cause_joint setup focal moves joint offered legal
        (Option.some.inj (congrArg Prod.snd observed))
      have regular := (proposalRecovery_good_extend_iff setup focal parent joint legal
        supported).mp good
      have otherGood : setup.proposalRecoveryForeignGood focal (parent.extend offered reached) := by
        rw [proposalRecovery_good_extend_iff]
        refine ⟨regular.1, fun owner foreign => ?_⟩
        have row := regular.2 owner foreign
        rcases labels with equal | ⟨author, name, different, others, cases⟩
        · simpa only [equal] using row
        · by_cases own : owner = author
          · subst author
            rcases cases with ⟨lc, rc⟩ | ⟨rc, lc⟩ <;>
              simp [lc, ProposalRecoveryMove.ordinary, ProposalRecoveryMove.failedDisclosure,
                ProposalRecoveryMove.GeneratedPreparationFailure]
          · simpa only [others owner own] using row
      have infos : setup.proposalRecoveryModel.infoOf focal (parent.extend offered reached).trace =
          setup.proposalRecoveryModel.infoOf focal child.trace := congrArg Prod.fst observed
      apply Prod.ext
      · exact (proposalRecovery_base_extend setup current trace moves offered reached).trans
          (proposalRecovery_base_extend setup current trace joint legal supported).symm
      · apply Prod.ext infos
        apply Prod.ext
        · change setup.proposalRecoveryCauseWord focal trace ++ [_] =
            setup.proposalRecoveryCauseWord focal trace ++ [_]
          exact congrArg (fun r => setup.proposalRecoveryCauseWord focal trace ++ [r]) observed
        · change decide (setup.proposalRecoveryForeignGood focal (parent.extend offered reached)) =
            decide (setup.proposalRecoveryForeignGood focal child)
          exact (decide_eq_true_eq.mpr otherGood).trans (decide_eq_true_eq.mpr good).symm
  split_ifs with keySame readSame readSame
  · rfl
  · exact (readSame (equivalent.mp keySame.symm).symm).elim
  · exact (keySame (equivalent.mpr readSame.symm).symm).elim
  · rfl

private theorem proposalRecovery_cause_row_mass
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    {after} (supported : after ∈ (setup.proposalRecoveryProtocol.step (some current)
      ⟨joint, legal⟩).support) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let parent : setup.proposalRecoveryProtocol.History := ⟨some current, trace⟩
    let child := parent.extend legal supported
    let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      parent joint legal supported
    (((setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent).map
      (setup.proposalRecoveryForeignCauseRead focal))
        (setup.proposalRecoveryForeignCauseRead focal child)).toReal =
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩ after).toReal *
        setup.proposalRecoveryModel.playerStepProb profile focal trace ⟨joint, legal⟩ *
          row.1.toReal * row.2.1.toReal := by
  classical
  intro profile parent child row
  by_cases publication : ∃ owner move author name bit,
      ProtocolState.actor setup.program current.point = some owner ∧ owner ≠ focal ∧
        joint owner = some move ∧ move.semantic.action = .reveal author name bit
  · obtain ⟨owner, move, author, name, bit, acting, foreign, chosen, revealing⟩ := publication
    have absent : joint focal = none := by
      apply LegalOption.eq_none_of_inactive _
        (setup.proposalRecoveryProtocol.legalOption_of_legal legal focal)
      intro active
      exact foreign (Option.some.inj (acting.symm.trans active.1))
    have own : setup.proposalRecoveryModel.playerStepProb profile focal trace ⟨joint, legal⟩ =
        1 := by
      have inactive : ¬ setup.proposalRecoveryProtocol.active (some current) focal := by
        have offered := setup.proposalRecoveryProtocol.legalOption_of_legal legal focal
        simpa only [absent, LegalOption] using offered
      let _ := setup.proposalRecoveryModel.subsingleton_choice_of_not_active trace inactive
      unfold InformationModel.playerStepProb
      rw [eq_pure_of_subsingleton (profile focal
        (setup.proposalRecoveryModel.infoOf focal trace))
          (setup.proposalRecoveryModel.choicesOfLegal trace ⟨joint, legal⟩ focal)]
      simp
    have intrinsic : setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩ after =
        1 := by
      obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      change ((current.step (proposalRecoveryJoint joint)).map some) (some next) = 1
      rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
      apply (PMF.apply_eq_one_iff _ _).mpr
      ext other
      constructor
      · intro reached
        exact Set.mem_singleton_iff.mpr
          (setup.commitRecovery_step_unique_of_actor current owner acting _ other next
            reached member)
      · intro same
        exact (Set.mem_singleton_iff.mp same).symm ▸ member
    simp only [row, parent, proposalRecoveryForeignRowFactors, acting, foreign, ite_false,
      chosen, revealing, intrinsic, own, ENNReal.toReal_one, one_mul, mul_one]
    rfl
  · have residual : row.2.2 = 1 := by
      dsimp only [row, parent, proposalRecoveryForeignRowFactors]
      cases acting : ProtocolState.actor setup.program current.point with
      | none => rfl
      | some owner =>
        by_cases same : owner = focal
        · simp only [same, ite_true]
        · simp only [same, ite_false]
          cases chosen : joint owner with
          | none => rfl
          | some move =>
            dsimp only
            cases action : move.semantic.action with
            | commit author name payload binding =>
              dsimp only
              split <;> try rfl
              cases binding <;> rfl
            | reveal author name bit =>
              exact (publication ⟨owner, move, author, name, bit, acting, same, chosen,
                action⟩).elim
    let law := setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent
    have inverse (other : setup.proposalRecoveryProtocol.History) (present : other ∈ law.support)
        (same : setup.proposalRecoveryForeignCauseRead focal other =
          setup.proposalRecoveryForeignCauseRead focal child) : other = child := by
      change other ∈ (setup.proposalRecoveryModel.runBehavioralFrom profile 1 parent).support
        at present
      rw [InformationModel.runBehavioralFrom_succ_of_not_terminal _ _ 0 legal.1,
        PMF.mem_support_bind_iff] at present
      obtain ⟨⟨moves, offered⟩, _, present⟩ := present
      obtain ⟨next, reached, landed⟩ := (PMF.mem_support_bindOnSupport_iff _ _).mp present
      change other ∈ (PMF.pure (parent.extend offered reached)).support at landed
      cases (PMF.mem_support_pure_iff _ _).mp landed
      have labels := proposalRecovery_labels_of_cause_joint setup focal moves joint offered legal
        (Option.some.inj (congrArg Prod.snd same))
      have joints : moves = joint := by
        rcases labels with equal | ⟨owner, name, foreign, _, cases⟩
        · exact equal
        · rcases cases with ⟨_, chosen⟩ | ⟨chosen, _⟩
          all_goals
            have active := legal.2 owner
            rw [chosen] at active
            exact (publication ⟨owner, _, owner, name, _, active.1.1, foreign, chosen,
              rfl⟩).elim
      subst moves
      obtain ⟨ln, ls, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      obtain ⟨rn, rs, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have signal := congrArg (fun read => read.1.1.1) same
      have publicSignal : setup.attemptPublicSignal focal (some ln) =
          setup.attemptPublicSignal focal (some rn) := by
        exact congrArg (fun read =>
          (read.1.map (ProtocolView.publicOnly focal setup.program), read.2.1)) signal
      have equal := setup.commitRecovery_step_eq_of_public focal current
        (setup.proposalRecoveryEraseTrace trace) (proposalRecoveryJoint joint) ln rn ls rs
          publicSignal
      cases equal
      rfl
    have singleton : (law.map (setup.proposalRecoveryForeignCauseRead focal))
        (setup.proposalRecoveryForeignCauseRead focal child) = law child := by
      rw [PMF.map_apply, tsum_eq_single child]
      · simp
      · intro other different
        by_cases zero : law other = 0
        · simp [zero]
        · by_cases same : setup.proposalRecoveryForeignCauseRead focal other =
              setup.proposalRecoveryForeignCauseRead focal child
          · exact (different (inverse other ((PMF.mem_support_iff _ _).mpr zero) same)).elim
          · simp [same, eq_comm]
    rw [singleton, setup.proposalRecoveryModel.runBehavioralFrom_one_prob_extend profile parent
      legal.1 ⟨joint, legal⟩ after supported,
      setup.proposalRecoveryModel.stepProb_eq_player_mul_counterfactual profile focal,
      InformationModel.counterfactualStepProb]
    have opponents := setup.proposalRecovery_foreign_row_opponents values omission bad delivery
      focal parent joint legal supported
    change setup.proposalRecoveryModel.opponentsStepProb profile focal trace ⟨joint, legal⟩ =
      row.1.toReal * row.2.1.toReal * row.2.2.toReal at opponents
    rw [opponents, residual, ENNReal.toReal_one]
    ring

open Classical in
/-- The actual closed source fiber has the intrinsic, focal, class and proper-value
mass. Its zero-safe posterior identity retains exactly the residual PUB factor. -/
theorem proposalRecoveryClosedMass_foreign_products
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (wellFormed : setup.WellFormed)
    (focal : Player) (canonical : setup.proposalRecoveryProtocol.History)
    (good : setup.proposalRecoveryForeignGood focal canonical) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let factors : {state : setup.proposalRecoveryProtocol.State} →
        setup.proposalRecoveryProtocol.Trace state → ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ :=
      setup.proposalRecoveryForeignProducts values omission bad delivery focal
    setup.proposalRecoveryClosedMass profile focal canonical =
      ENNReal.ofReal canonical.trace.transitionMass *
        ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
          (setup.proposalRecoveryModel.ownPlay focal canonical.trace)) *
            (factors canonical.trace).1 * (factors canonical.trace).2.1 ∧
    ∀ target, setup.proposalRecoveryClosedMass profile focal canonical *
        setup.proposalRecoveryClosedLaw profile focal canonical target =
      if setup.proposalRecoveryClosedKey focal target =
          setup.proposalRecoveryClosedKey focal canonical then
        setup.proposalRecoveryClosedMass profile focal canonical * (factors target.trace).2.2
      else 0 := by
  classical
  intro profile factors
  let prescription := fun owner key => setup.proposalRecoveryComponentTrembledLaw owner key
    omission.val omission.property.1 omission.property.2
    bad.val bad.property.1 bad.property.2
    delivery.val delivery.property.1 delivery.property.2 (values owner key)
  have realMass : ∀ (history : setup.proposalRecoveryProtocol.History),
      setup.proposalRecoveryForeignGood focal history →
      (setup.proposalRecoveryClosedMass profile focal history).toReal =
        history.trace.transitionMass *
          setup.proposalRecoveryModel.playerReachProbability profile focal history.trace *
            (factors history.trace).1.toReal * (factors history.trace).2.1.toReal := by
    intro ⟨state, trace⟩
    induction trace with
    | start =>
      intro _good
      simp only [Trace.transitionMass_start, InformationModel.playerReachProbability_start,
        factors, proposalRecoveryForeignProducts, ENNReal.toReal_one, mul_one]
      change (((PMF.pure setup.proposalRecoveryProtocol.initHistory).map
        (setup.proposalRecoveryClosedKey focal))
          (setup.proposalRecoveryClosedKey focal setup.proposalRecoveryProtocol.initHistory)).toReal
        = 1
      rw [PMF.pure_map]
      simp
    | @extend source target prior joint legal supported ih =>
      intro good
      cases source with
      | none =>
        have root : (⟨none, prior⟩ : setup.proposalRecoveryProtocol.History) =
            setup.proposalRecoveryProtocol.initHistory := by
          obtain initial | ⟨theta, _, first, _, retained⟩ :=
            proposalRecovery_initialized_prefix setup prior
          · exact initial
          · obtain ⟨actual, impossible, _, _⟩ := setup.commitRecovery_base_of_prefix _
              (setup.proposalRecoveryEraseTrace first) rfl (setup.proposalRecoveryEraseTrace prior)
              (setup.proposalRecoveryEraseTrace_prefix retained)
            cases impossible
        cases root
        let child : setup.proposalRecoveryProtocol.History := ⟨target, .extend .start joint legal
          supported⟩
        have unique (other : setup.proposalRecoveryProtocol.History)
            (same : setup.proposalRecoveryClosedKey focal other =
              setup.proposalRecoveryClosedKey focal child) : other = child := by
          have depth := setup.proposalRecoveryClosedKey_depth focal child other same
          rcases other with ⟨otherState, otherTrace⟩
          cases otherTrace with
          | start => simp only [child, Trace.length] at depth; omega
          | extend earlier moves offered reached =>
            cases earlier with
            | extend => simp only [child, Trace.length] at depth; omega
            | start =>
              obtain ⟨left, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
              obtain ⟨right, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
              have bases := congrArg Prod.fst same
              have inputs : left = right := by
                simpa only [proposalRecoveryClosedKey, child, Option.map_some,
                  Option.some.injEq, CommitRecoveryState.atPoint, ProtocolState.base_entry,
                  Setup.initialConfig] using bases
              subst right
              exact congrArg (fun tr => (⟨_, tr⟩ : setup.proposalRecoveryProtocol.History))
                (setup.proposalRecovery_initialized_trace_unique _ _ _ rfl rfl)
        have atom : setup.proposalRecoveryClosedMass profile focal child =
            setup.proposalRecoveryModel.historyReachWeight profile child := by
          unfold proposalRecoveryClosedMass
          rw [PMF.map_apply, tsum_eq_single child]
          · simp only [ite_true, InformationModel.historyReachWeight]
          · intro other different
            by_cases same : setup.proposalRecoveryClosedKey focal child =
                setup.proposalRecoveryClosedKey focal other
            · exact (different (unique other same.symm)).elim
            · simp only [same, ite_false]
        change (setup.proposalRecoveryClosedMass profile focal child).toReal = _
        rw [atom, setup.proposalRecovery_historyReach_foreign_products values omission bad delivery
          focal child]
        rw [setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability]
        have initial : setup.proposalRecoveryProtocol.init = none := rfl
        simp only [child, factors, proposalRecoveryForeignProducts,
          proposalRecoveryForeignRowFactors, initial, ENNReal.toReal_one, mul_one]
        rfl
      | some current =>
        have beforeGood := (proposalRecovery_good_extend_iff setup focal ⟨some current, prior⟩
          joint legal supported).mp good
        have mass := setup.proposalRecoveryClosedMass_cause prescription wellFormed focal current
          prior joint legal supported good
        change setup.proposalRecoveryClosedMass profile focal
            ⟨target, prior.extend joint legal supported⟩ =
          setup.proposalRecoveryClosedMass profile focal ⟨some current, prior⟩ *
            ((setup.proposalRecoveryModel.runBehavioralFrom profile 1 ⟨some current, prior⟩).map
              (setup.proposalRecoveryForeignCauseRead focal))
                (setup.proposalRecoveryForeignCauseRead focal
                  ((⟨some current, prior⟩ : setup.proposalRecoveryProtocol.History).extend legal
                    supported)) at mass
        rw [mass, ENNReal.toReal_mul, ih beforeGood.1,
          proposalRecovery_cause_row_mass setup values omission bad delivery focal current prior
            joint legal supported]
        simp only [factors, proposalRecoveryForeignProducts, Trace.transitionMass_extend,
          InformationModel.playerReachProbability, ENNReal.toReal_mul]
        ring
  have mass (history : setup.proposalRecoveryProtocol.History)
      (regular : setup.proposalRecoveryForeignGood focal history) :
      setup.proposalRecoveryClosedMass profile focal history =
        ENNReal.ofReal history.trace.transitionMass *
          ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
            (setup.proposalRecoveryModel.ownPlay focal history.trace)) *
              (factors history.trace).1 * (factors history.trace).2.1 := by
    have finite := setup.proposalRecoveryForeignProducts_finite values omission bad delivery focal
      history.trace
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        finite.1) finite.2.1)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal history.trace.transitionMass_pos.le,
      ENNReal.toReal_ofReal (setup.proposalRecoveryModel.ownPlayReachProbability_nonneg _ _)]
    rw [← setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability]
    exact realMass history regular
  refine ⟨mass canonical good, fun target => ?_⟩
  rw [setup.proposalRecoveryClosedMass_mul_law]
  split_ifs with same
  · have targetGood : setup.proposalRecoveryForeignGood focal target := by
      have bit := congrArg (fun key => key.2.2.2) same
      simpa only [proposalRecoveryClosedKey, good, decide_true, decide_eq_true_eq] using bit
    have masses : setup.proposalRecoveryClosedMass profile focal target =
        setup.proposalRecoveryClosedMass profile focal canonical := by
      unfold proposalRecoveryClosedMass
      rw [setup.proposalRecoveryClosedKey_depth focal canonical target same, same]
    rw [setup.proposalRecovery_historyReachWeight_foreign_products values omission bad delivery
      focal target, ← masses, mass target targetGood]
  · rfl

end Vegas.SourceProgram.Setup
