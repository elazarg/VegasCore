/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalBindingKernel
import Vegas.Game.PhaseProposalUnflaggedBinding

/-! # Actual first responses advance the same binding continuation potential -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

/-- The graph action determined by the actual typed preparation. No source
value is drawn a second time at inclusion. Missing preparations have a total
failure image, although genuine unflagged first bindings never use it. -/
def phaseProposalPreparedBindingAction (event : (graph).EventId) (who : Player)
    (payload : L.Ty) (binding : (graph).outputLayout event = .binding who payload)
    (response : (app).Action) : (graph).Action event :=
  cast (congrArg EventField.Action binding.symm)
    (((response.transmission.bind PhaseProposal.bindingPreparation).bind
      (fun raw => raw.as? payload)).elim PublicationResult.failure PublicationResult.success)

/-- At a literal fresh callback the actual response PMF, projected to its
prepared graph action, is exactly the current result kernel. The original
initialized joint law is retained in the factual trace hypothesis. -/
theorem phaseProposalUnflagged_binding_action_law
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (execution.recall who) (execution.observe app who)).map
          (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding) =
      (phaseProposalBindingResults setup mode runtime leaks plan values PhaseProposalRates.zero
        who event payload binding (execution.recall who) (execution.observe app who)).map
          (cast (congrArg EventField.Action binding.symm)) := by
  obtain ⟨key, queried, law⟩ := phaseProposalUnflaggedBinding_preparation_law setup mode runtime
    leaks bounds plan complete covered maximal values fullValues horizon scheduler capacity
      remaining who execution trace event payload binding request unsent
  have projected := congrArg (fun draws : PMF (Option (Raw L)) =>
      draws.map (fun raw => cast (congrArg EventField.Action binding.symm)
        ((raw.bind fun value => value.as? payload).elim PublicationResult.failure
          PublicationResult.success))) law
  unfold phaseProposalPreparedBindingAction
  simpa only [PMF.map_comp, Function.comp_def,
    Option.bind_some, Raw.as?_mk, Option.elim_some, phaseProposalBindingResults, queried,
    PhaseProposalRates.zero, mix_zero] using projected

/-- The frozen-entry getter retains all old controls and proposals while its
semantic observation follows the emission frontier. This equality is derived
from concrete getter fields, without an information-neutrality hypothesis. -/
theorem phaseProposalBindingGraphView_query_eq_current
    (anchor execution : (app).Execution) (who : Player) (event : (graph).EventId)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (retired : execution.application.retired = anchor.application.retired)
    (failures : ∀ rank ≤ execution.application.attempt.phase,
      execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
        anchor.application.current.native.publicView.sourceFailureFootprint.1 rank)
    (archive : PhaseProposal.observedSourceArchive runtime leaks (execution.recall who)
        (execution.observe app who) =
      PhaseProposal.observedSourceArchive runtime leaks (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((graph).playerObserve who execution.application.current.native.config))) :
    phaseProposalQuery? setup mode runtime leaks plan who event (execution.recall who)
        (execution.observe app who) =
      phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((graph).playerObserve who execution.application.current.native.config)) := by
  exact phaseProposalQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    (execution.recall who) (anchor.recall who) (execution.observe app who)
    (phaseProposalBindingGraphView setup mode runtime leaks anchor who
      ((graph).playerObserve who execution.application.current.native.config))
    rfl rfl rfl attempt
    (congrArg (List.map (fun prior : RetiredCommitAttempt (graph) =>
      (prior.attempt, prior.state.publicView))) retired) failures archive

/-- One actual fresh SEND is harmonic for the SAME graph frontier. The proof
projects the physical response once, retaining its literal preparation, then
uses the owning graph commutation law. No later admission, source likelihood,
or whole-phase kernel is assumed. -/
theorem phaseProposalUnflagged_binding_emission_harmonic
    (complete : leaks = MessageNetwork.completePendingObservation)
    (covered : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    (horizon : Nat) (scheduler : (app).Scheduler)
    (capacity : horizon ≤ bounds.candidateCount) (remaining : Nat) (who : Player)
    (execution anchor : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : RuntimePhase (graph)) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (code : cast (congrArg (EventCode (graph).layout) binding) ((graph).nodes event) =
      .bind who payload)
    (inside : event ∈ phase.events) (active : who ∉ anchor.application.current.excluded)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (attempt : execution.application.attempt = anchor.application.attempt)
    (retired : execution.application.retired = anchor.application.retired)
    (failures : ∀ rank ≤ execution.application.attempt.phase,
      execution.application.current.native.publicView.sourceFailureFootprint.1 rank =
        anchor.application.current.native.publicView.sourceFailureFootprint.1 rank)
    (archive : PhaseProposal.observedSourceArchive runtime leaks (execution.recall who)
        (execution.observe app who) =
      PhaseProposal.observedSourceArchive runtime leaks (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who
          ((graph).playerObserve who execution.application.current.native.config)))
    (frontier : (graph).Config)
    (agreement : execution.application.current.native.config.CompletedOutputAgreement frontier)
    (inputs : execution.application.current.native.config.inputs = frontier.inputs)
    (hidden : ∀ pending ∈ frontier.cut.completed,
      pending ∉ execution.application.current.native.config.cut.completed →
        ¬ (graph).fieldVisibleTo who (.inr pending)) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor
      phase values
    ∃ ready : frontier.cut.Ready event,
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
        (execution.recall who) (execution.observe app who)).bind (fun response =>
          (frontier.step event ready
            (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding
              response)).bind ((graph).canonicalContinuation profile)) =
        (graph).canonicalContinuation profile frontier := by
  intro profile
  have actor : (graph).actor? event = some who :=
    EventGraph.actor?_of_outputLayout_binding (graph) binding
  obtain ⟨ready, law⟩ := phaseProposalBindingPotentialProfile_hidden_frontier setup mode runtime
    leaks plan anchor phase values execution.application.current.native.config frontier agreement
      inputs who event request.2.2.1 actor hidden
  have queried := phaseProposalBindingGraphView_query_eq_current setup mode runtime leaks plan
    anchor execution who event attempt retired failures archive
  have results := phaseProposalBindingResults_eq_of_query setup mode runtime leaks plan values
    PhaseProposalRates.zero who event payload binding _ _ _ _ queried
  have draws := phaseProposalUnflagged_binding_action_law setup mode runtime leaks bounds plan
    complete covered maximal values fullValues horizon scheduler capacity remaining who execution
      trace event payload binding request unsent
  have current : (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
      (execution.recall who) (execution.observe app who)).map
        (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding) =
      (graph).normalizePolicy who (profile who) event actor
        ((graph).playerObserve who frontier) := by
    rw [draws, results, ← law, phaseProposalBindingPotentialProfile_normalize]
    simp only [phaseProposalBindingPotentialProfile, nodeView_eq_bind binding code]
    rw [dite_eq_left True.intro, ite_eq_left ⟨inside, active⟩]
  refine ⟨ready, ?_⟩
  calc
    _ = PMF.bind ((phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values who
          (execution.recall who) (execution.observe app who)).map
            (phaseProposalPreparedBindingAction setup mode runtime leaks event who payload binding))
        (fun action => (frontier.step event ready action).bind
          ((graph).canonicalContinuation profile)) := by
      rw [PMF.bind_map]
      rfl
    _ = (graph).normalizedThenCanonical profile frontier event ready := by
      have step : (graph).normalizedPolicyStep profile frontier event ready =
          ((graph).normalizePolicy who (profile who) event actor
            ((graph).playerObserve who frontier)).bind (frontier.step event ready) := by
        unfold normalizedPolicyStep
        split
        · rename_i owner selected
          have same : owner = who := Option.some.inj (selected.symm.trans actor)
          subst owner
          rfl
        · rename_i absent
          rw [absent] at actor
          cases actor
      rw [current, normalizedThenCanonical, step, PMF.bind_bind]
    _ = _ := phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
      anchor phase values frontier event ready

end Vegas
