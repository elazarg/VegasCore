/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryOrdinaryKernel
import Vegas.Game.PhaseProposalCanonicalSourceQuery
import Vegas.Source.ProposalRecoveryEvolution
import Vegas.Source.ProposalRecoveryCommitment
import Vegas.Source.CommitRecoveryCommitUnique

/-! # Ordinary commitment evolution with the complete enriched source image -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- One actual ordinary commitment step retains the entire erased information
vector and proposal word. This also covers an inherited excluded actor: its
ordinary menu is the singleton NONE and the existing recovery step performs
the automatic commitment. No graph history is substituted for the source
history, and no prospective or historical public signal is removed. -/
theorem proposalRecovery_ordinary_commitment_image
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (running : ¬ setup.proposalRecoveryProtocol.terminal (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (who : Player) (actor : ProtocolState.actor setup.program current.point = some who) :
    (setup.proposalRecoveryModel.runBehavioralFrom
        (setup.proposalRecoveryNormalizedTrembledProfile
          0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values)
        1 ⟨some current, trace⟩).map setup.proposalRecoveryErasedHistory =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who trace))).bind (fun choice =>
          (current.step (setup.commitRecoveryProtocol.singletonJoint who choice.val.val)).map
            (fun target => setup.proposalRecoveryNextErasedHistory
              (setup.proposalRecoveryErasedHistory ⟨some current, trace⟩)
              (some target.eraseHistory, none))) := by
  let profile := setup.proposalRecoveryNormalizedTrembledProfile
    0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
  rw [setup.proposalRecovery_oneStep_image profile ⟨some current, trace⟩ running]
  have silent : ∀ joint,
      setup.proposalRecoveryProposalOf (some current) joint = none :=
    setup.proposalRecoveryProposalOf_eq_none_of_atCommit current committing
  simp_rw [silent]
  have joint := setup.proposalRecovery_ordinary_successor_kernel values current trace running
    who actor
  have evolved := congrArg (PMF.map (fun target : setup.proposalRecoveryProtocol.State =>
    setup.proposalRecoveryNextErasedHistory
      (setup.proposalRecoveryErasedHistory ⟨some current, trace⟩)
      (target.map CommitRecoveryState.eraseHistory, none))) joint
  simpa only [profile, PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some]
    using evolved

omit [Fintype Player] in
/-- A support witness for the existing typed commitment successor identifies
the state of every actual local history extension with those same original
choices. Automatic phase closure is included in the existing determinacy
theorem, so the last source slot is not treated as an unclosed state. -/
theorem proposalRecovery_local_commitment_state
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (running : ¬ setup.proposalRecoveryProtocol.terminal (some current))
    (committing : ProtocolState.atCommit setup.program current.point = true)
    (choices : ∀ who, setup.proposalRecoveryModel.Choice who
      (setup.proposalRecoveryModel.infoOf who trace))
    (target : CommitRecoveryState setup.program)
    (supported : target ∈ (current.step
      (proposalRecoveryJoint (fun who => (choices who).val))).support)
    (next : setup.proposalRecoveryProtocol.History)
    (realized : next ∈ (setup.proposalRecoveryModel.localStep ⟨some current, trace⟩
      choices).support) : next.state = some target := by
  rw [InformationModel.localStep, dite_eq_right running,
    PMF.mem_support_bindOnSupport_iff] at realized
  obtain ⟨actual, actualSupport, landed⟩ := realized
  rw [PMF.mem_support_pure_iff] at landed
  subst next
  change actual ∈ ((current.step
    (proposalRecoveryJoint (fun who => (choices who).val))).map some).support at actualSupport
  obtain ⟨result, resultSupport, same⟩ := (PMF.mem_support_map_iff _ _ _).mp actualSupport
  change actual = some target
  rw [← same, current.step_unique_of_commit committing _ result target resultSupport supported]

end Vegas.SourceProgram.Setup

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks

/-- An inherited excluded slot may be completed in source order instead of
eagerly draining the auxiliary graph. Its graph failure action is distinct
from the source's literal automatic NONE instruction. -/
theorem phaseProposalBindingPotentialProfile_excluded_step
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (config : (graph).Config) (event : (graph).EventId) (ready : config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (excluded : who ∈ anchor.application.current.excluded) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase
      values
    let failed : (graph).Action event := cast (congrArg EventField.Action binding.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))
    let stored : ((graph).outputLayout event).Value :=
      cast (congrArg EventField.Value binding.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))
    (graph).normalizedPolicyStep profile config event ready =
        PMF.pure (config.complete event ready failed stored) ∧
      (graph).canonicalContinuation profile (config.complete event ready failed stored) =
        (graph).canonicalContinuation profile config := by
  intro profile failed stored
  have actor : (graph).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding (graph) binding
  have law : (graph).normalizePolicy who (profile who) event actor
      ((graph).playerObserve who config) = PMF.pure failed := by
    rw [phaseProposalBindingPotentialProfile_normalize]
    simp only [phaseProposalBindingPotentialProfile, nodeView_eq_bind binding code]
    rw [dite_eq_left True.intro,
      ite_eq_right (show ¬ (event ∈ phase.events ∧
        who ∉ anchor.application.current.excluded) from fun valid => valid.2 excluded),
      PMF.pure_map]
  have step : (graph).normalizedPolicyStep profile config event ready =
      PMF.pure (config.complete event ready failed stored) := by
    unfold normalizedPolicyStep
    split
    · rename_i owner selected
      have same : owner = who := Option.some.inj (selected.symm.trans actor)
      subst owner
      rw [law, PMF.pure_bind, commit_step config event ready binding code]
    · rename_i absent
      rw [absent] at actor
      cases actor
  refine ⟨step, ?_⟩
  have harmonic := phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
    anchor phase values config event ready
  rw [normalizedThenCanonical, step, PMF.pure_bind] at harmonic
  exact harmonic

/-- At an explicitly identified source cursor the same literal domain draw is
harmonic for the frozen graph potential. The chronological compiler readback
discharges the query equality; no physical callback or new value draw is used
to select a different source history. -/
theorem phaseProposalBindingPotentialProfile_source_draw
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (config : (graph).Config) (event : (graph).EventId) (ready : config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
      (phaseProposalBindingGraphView setup mode runtime leaks anchor who
        ((graph).playerObserve who config)) =
      some (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace))) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase
      values
    (graph).normalizedPolicyStep profile config event ready =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who trace))).bind (fun choice =>
          config.step event ready (cast (congrArg EventField.Action binding.symm)
            (.success (phaseRecoveryDomainValue setup mode event who payload binding
              choice.val.val)))) ∧
    (values who (setup.proposalRecoveryQuery who
      (setup.proposalRecoveryModel.infoOf who trace))).bind (fun choice =>
        (config.step event ready (cast (congrArg EventField.Action binding.symm)
          (.success (phaseRecoveryDomainValue setup mode event who payload binding
            choice.val.val)))).bind ((graph).canonicalContinuation profile)) =
      (graph).canonicalContinuation profile config := by
  intro profile
  have actor : (graph).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding (graph) binding
  have law : (graph).normalizePolicy who (profile who) event actor
      ((graph).playerObserve who config) =
      (values who (setup.proposalRecoveryQuery who
        (setup.proposalRecoveryModel.infoOf who trace))).map (fun choice =>
          cast (congrArg EventField.Action binding.symm)
            (.success (phaseRecoveryDomainValue setup mode event who payload binding
              choice.val.val))) := by
    rw [phaseProposalBindingPotentialProfile_normalize]
    simp only [phaseProposalBindingPotentialProfile, nodeView_eq_bind binding code]
    rw [dite_eq_left True.intro, ite_eq_left ⟨inside, active⟩]
    unfold phaseProposalBindingResults
    rw [queried]
    simp only [PhaseProposalRates.zero, mix_zero, PMF.map_comp, Function.comp_def]
  have harmonic := phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
    anchor phase values config event ready
  have step : (graph).normalizedPolicyStep profile config event ready =
      ((graph).normalizePolicy who (profile who) event actor
        ((graph).playerObserve who config)).bind (config.step event ready) := by
    unfold normalizedPolicyStep
    split
    · rename_i owner selected
      have same : owner = who := Option.some.inj (selected.symm.trans actor)
      subst owner
      rfl
    · rename_i absent
      rw [absent] at actor
      cases actor
  constructor
  · rw [step, law, PMF.bind_map]
    rfl
  · rw [normalizedThenCanonical, step, law, PMF.bind_map, PMF.bind_bind] at harmonic
    exact harmonic

/-- The actual one-step source history and the graph potential can use the
same literal current domain draw. The support certificate retains that draw
and the original source `localStep`; no graph recall is substituted for the
source's remembered original action word. -/
theorem phaseProposalBindingPotentialProfile_source_coupling
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (config : (graph).Config) (event : (graph).EventId) (ready : config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (current : CommitRecoveryState setup.program)
    (trace : setup.proposalRecoveryProtocol.Trace (some current))
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
      (phaseProposalBindingGraphView setup mode runtime leaks anchor who
        ((graph).playerObserve who config)) =
      some (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace))) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase
      values
    let source := setup.proposalRecoveryNormalizedTrembledProfile
      0 le_rfl zero_le_one 0 le_rfl zero_le_one 0 le_rfl zero_le_one values
    let history : setup.proposalRecoveryProtocol.History := ⟨some current, trace⟩
    let domains := fun owner => values owner (setup.proposalRecoveryQuery owner
      (setup.proposalRecoveryModel.infoOf owner trace))
    let choices := fun (draws : ∀ owner, setup.CommitRecoveryValueChoice owner
      (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner trace)).1) owner =>
      (setup.proposalRecoveryComponentChoice owner
        (setup.proposalRecoveryModel.infoOf owner trace)).symm
          (setup.proposalRecoveryComponentLabelChoice owner
            (setup.proposalRecoveryQuery owner (setup.proposalRecoveryModel.infoOf owner trace))
              false (draws owner).val)
    let following := fun (choice : setup.CommitRecoveryValueChoice who
      (setup.proposalRecoveryQuery who (setup.proposalRecoveryModel.infoOf who trace)).1) =>
      config.step event ready (cast (congrArg EventField.Action binding.symm)
        (.success (phaseRecoveryDomainValue setup mode event who payload binding
          choice.val.val)))
    ∃ joint : PMF (setup.proposalRecoveryProtocol.History × (graph).Config),
      joint.map Prod.fst = setup.proposalRecoveryModel.runBehavioralFrom source 1 history ∧
      joint.map Prod.snd = (graph).normalizedPolicyStep profile config event ready ∧
      ∀ pair ∈ joint.support, ∃ draws ∈ (independentProduct domains).support,
        pair.1 ∈ (setup.proposalRecoveryModel.localStep history (choices draws)).support ∧
        pair.2 ∈ (following (draws who)).support := by
  intro profile source history domains choices following
  let joint : PMF (setup.proposalRecoveryProtocol.History × (graph).Config) :=
    (independentProduct domains).bind (fun draws =>
      (setup.proposalRecoveryModel.localStep history (choices draws)).bind (fun next =>
        (following (draws who)).map (fun result => (next, result))))
  refine ⟨joint, ?_, ?_, ?_⟩
  · have expanded := setup.proposalRecovery_ordinary_run_succ values 0 history
    change setup.proposalRecoveryModel.runBehavioralFrom source 1 history =
      (independentProduct domains).bind (fun draws =>
        (setup.proposalRecoveryModel.localStep history (choices draws)).bind PMF.pure)
      at expanded
    simp only [PMF.bind_pure] at expanded
    rw [expanded]
    dsimp only [joint]
    have constant : ∀ choice (next : setup.proposalRecoveryProtocol.History),
        (following choice).map (fun _ => next) = PMF.pure next :=
      fun choice next => PMF.map_const (following choice) next
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, constant, PMF.bind_pure]
  · have coordinate := independentProduct_map_eval domains who
    have identity : ∀ choice, (following choice).map (fun result => result) =
        following choice := fun choice => PMF.map_id (following choice)
    have marginal : joint.map Prod.snd =
        (independentProduct domains).bind (fun draws => following (draws who)) := by
      dsimp only [joint]
      simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, identity, PMF.bind_const]
    rw [marginal]
    change (independentProduct domains).bind (following ∘ fun draws => draws who) = _
    rw [← PMF.bind_map, coordinate]
    exact (phaseProposalBindingPotentialProfile_source_draw setup mode runtime leaks plan
      anchor phase values config event ready who payload binding code inside active current trace
        queried).1.symm
  · intro pair member
    obtain ⟨draws, drawSupport, nextSupport⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp member
    obtain ⟨next, localSupport, resultSupport⟩ :=
      (PMF.mem_support_bind_iff _ _ _).mp nextSupport
    obtain ⟨result, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp resultSupport
    cases same
    exact ⟨draws, drawSupport, localSupport, supported⟩

end Vegas
