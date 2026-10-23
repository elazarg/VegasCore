/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalCoupledQuery
import Vegas.Game.PhaseProposalUnflagged
import Vegas.EventGraph.RevealRelaxedScheduling
import Vegas.EventGraph.ConfigRestriction

/-! # A frozen-entry graph continuation for one ordinary binding interval

Outside-interval constants complete only the continuation potential. They are
not asserted to be the native future policy or its publication behavior.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

/-- Keep the literal entry's public controls, private catalogue, complete old
traffic and recall. Refresh its pending snapshot deterministically, since the
entry may be idle. Only the graph observation comes from the emission frontier. -/
def phaseProposalBindingGraphView (anchor : (app).Execution) (who : Player)
    (observation : (graph).PlayerObservation who) : (app).PlayerView where
  messages := (anchor.network.learn who (anchor.network.pending.map Message.id).toFinset).observe
    who
  receipts := (anchor.observe (app) who).receipts
  application :=
    ({ who := who
       publicView := anchor.application.current.native.publicView
       observation := observation
       candidates := fun slot => anchor.application.current.native.candidates.lookup (who, slot) },
      anchor.application.publicView)

omit [Fintype Player] in
/-- The auxiliary frozen view contains exactly the entry proposal archive even
when the entry is idle. Its refresh exposes signed packets only. -/
theorem phaseProposalBindingGraphView_archive
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (observation : (graph).PlayerObservation who) :
    PhaseProposal.observedSourceArchive runtime leaks (control.execution.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks control.execution who observation) =
      PhaseProposal.sourceArchive control.execution.network.inputs := by
  have recalled := (app).history_inputRecall initial horizon scheduler trace
  have retained := (app).retained_envelopes_mem_inputs control.execution
    ((app).history_provenance initial horizon scheduler trace) recalled
  have learned := retained.learn who
    (control.execution.network.pending.map Message.id).toFinset
  apply PhaseProposal.sourceArchive_congr
  intro message
  simp only [ReactiveApplication.ResponseMenu.knownPackets, List.mem_append]
  constructor
  · rintro ((own | leaked) | ledger)
    · rw [← recalled who] at own
      exact (List.mem_filter.mp own).1
    · exact learned.leaked who message leaked
    · exact learned.ledger message ledger
  · intro submitted
    by_cases own : message.sender = who
    · left; left
      rw [← recalled who]
      exact List.mem_filter.mpr ⟨submitted, by simp only [own, decide_true]⟩
    · have visible := MessageNetwork.submitted_visible_of_complete_observation
        control.execution.network
        ((app).uniqueIds_history scheduler initial horizon control trace)
        ((app).pendingOrPublished_history scheduler initial horizon trace) who message submitted own
      exact visible.elim (fun leaked => Or.inl (Or.inr leaked)) Or.inr

/-- Neither synthetic future completion order nor synthetic own-action recall
enters the getter. Original own values are still supplied literally in the
masked store; all control/address/archive data remain the actual entry data. -/
theorem phaseProposalBindingGraphView_query_congr
    (anchor : (app).Execution) (who : Player) (event : (graph).EventId)
    (first second : (graph).PlayerObservation who) (stores : first.store = second.store) :
    phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who first) =
      phaseProposalQuery? setup mode runtime leaks plan who event (anchor.recall who)
        (phaseProposalBindingGraphView setup mode runtime leaks anchor who second) := by
  apply phaseProposalQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    (anchor.recall who) (anchor.recall who)
    (phaseProposalBindingGraphView setup mode runtime leaks anchor who first)
    (phaseProposalBindingGraphView setup mode runtime leaks anchor who second)
    rfl rfl stores rfl rfl (fun _ _ => rfl)
  rfl

/-- The current interval uses the literal shared domain table at the frozen
entry getter. Excluded coordinates and all other binding intervals use fixed
failure actions; publications use fixed false. These constants are only a
device for the existing graph canonical-continuation engine. -/
def phaseProposalBindingPotentialProfile
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) : (graph).BehavioralProfile :=
  fun who event _actor observation =>
    match nodeView (graph) event with
    | .bind owner payload outputEq _codeEq =>
        let results : PMF (PublicationResult (L.Val payload)) :=
          if same : owner = who then
            if event ∈ phase.events ∧ who ∉ anchor.application.current.excluded then
              phaseProposalBindingResults setup mode runtime leaks plan values
                PhaseProposalRates.zero who event payload (same ▸ outputEq) (anchor.recall who)
                  (phaseProposalBindingGraphView setup mode runtime leaks anchor who observation)
            else PMF.pure .failure
          else PMF.pure .failure
        results.map (cast (congrArg EventField.Action outputEq.symm))
    | .resolve _owner _payload _binding _checks outputEq _codeEq =>
        PMF.pure (cast (congrArg EventField.Action outputEq.symm) false)
    | .sample _payload _law outputEq _codeEq =>
        PMF.pure (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)

/-- At a binding coordinate the frozen-entry kernel uses only the supplied
visible store. In particular its synthetic completion order and action recall
cannot disclose future source events to the ordinary domain table. -/
theorem phaseProposalBindingPotentialProfile_store_congr
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (event : (graph).EventId) (actor : (graph).actor? event = some who)
    (first second : (graph).PlayerObservation who) (stores : first.store = second.store) :
    phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values
        who event actor first =
      phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values
        who event actor second := by
  cases node : nodeView (graph) event with
  | bind owner payload outputEq codeEq =>
      simp only [phaseProposalBindingPotentialProfile, node]
      split
      · rename_i same
        split
        · apply congrArg (PMF.map _)
          exact phaseProposalBindingResults_eq_of_query setup mode runtime leaks plan values
            PhaseProposalRates.zero who event payload (same ▸ outputEq) _ _ _ _
              (phaseProposalBindingGraphView_query_congr setup mode runtime leaks plan
                anchor who event first second stores)
        · rfl
      · rfl
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [phaseProposalBindingPotentialProfile, node]
  | sample payload law outputEq codeEq =>
      simp only [phaseProposalBindingPotentialProfile, node]

/-- Graph normalization changes only metadata which this current-interval
kernel ignores. This is an identity for the auxiliary potential profile,
not an assertion that arbitrary native policies ignore their observations. -/
theorem phaseProposalBindingPotentialProfile_normalize
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (who : Player) (event : (graph).EventId) (actor : (graph).actor? event = some who)
    (observation : (graph).PlayerObservation who) :
    (graph).normalizePolicy who
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values who)
        event actor observation =
      phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values
        who event actor observation := by
  apply phaseProposalBindingPotentialProfile_store_congr setup mode runtime leaks plan
    anchor phase values who event actor
  rfl

theorem phaseProposalBindingPotentialProfile_oblivious
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    (graph).ObliviousAtPublications
      (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values) := by
  intro who event actor publication first second
  cases node : nodeView (graph) event with
  | bind owner payload outputEq codeEq =>
      rw [outputEq] at publication
      cases publication
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [phaseProposalBindingPotentialProfile, node]
  | sample payload law outputEq codeEq =>
      rw [outputEq] at publication
      cases publication

/-- The owning graph commutation theorem supplies the current-coordinate
harmonic continuation law. It is not a native stopped-run kernel equality. -/
theorem phaseProposalBindingPotentialProfile_harmonic
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (config : (graph).Config) (event : (graph).EventId) (ready : config.cut.Ready event) :
    (graph).normalizedThenCanonical
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        config event ready =
      (graph).canonicalContinuation
        (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values)
        config := by
  exact ((serviceGraph_revealRelaxedOrdered setup mode).readyIndependent
    (phaseProposalBindingPotentialProfile_oblivious setup mode runtime leaks plan anchor phase
      values)).normalizedThenCanonical_eq config event ready

/-- For the actual current drawer, the only ahead-of-settlement fields are
hidden foreign binding emissions. Physical predecessor values are retained
literally. Since the potential getter ignores synthetic recall, these facts
alone identify its ready kernel without reconstructing an auxiliary owner's
native response history. -/
theorem phaseProposalBindingPotentialProfile_hidden_frontier
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (physical frontier : (graph).Config)
    (agreement : physical.CompletedOutputAgreement frontier)
    (inputs : physical.inputs = frontier.inputs)
    (who : Player) (event : (graph).EventId) (ready : physical.cut.Ready event)
    (actor : (graph).actor? event = some who)
    (hidden : ∀ pending ∈ frontier.cut.completed, pending ∉ physical.cut.completed →
      ¬ (graph).fieldVisibleTo who (.inr pending)) :
    frontier.cut.Ready event ∧
      (graph).normalizePolicy who
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values
            who) event actor ((graph).playerObserve who physical) =
        (graph).normalizePolicy who
          (phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor phase values
            who) event actor ((graph).playerObserve who frontier) := by
  have subset := agreement.completed_subset physical frontier
  have frontierReady : frontier.cut.Ready event := by
    constructor
    · intro present
      exact hidden event present ready.1
        (EventCode.output_visible_of_actor ((graph).nodes event) who actor)
    · intro prior predecessor
      exact subset (ready.2 predecessor)
  refine ⟨frontierReady, ?_⟩
  rw [phaseProposalBindingPotentialProfile_normalize,
    phaseProposalBindingPotentialProfile_normalize]
  apply phaseProposalBindingPotentialProfile_store_congr setup mode runtime leaks plan
    anchor phase values who event actor
  apply (graph).playerStore_congr
  intro field visible
  cases field with
  | inl index => exact congrArg (fun values => some (values index)) inputs
  | inr pending =>
      by_cases done : pending ∈ physical.cut.completed
      · exact agreement pending done
      · have absent : pending ∉ frontier.cut.completed := fun completed =>
          hidden pending completed done visible
        have physicalEmpty : physical.outputs pending = none :=
          Option.not_isSome_iff_eq_none.mp (fun present =>
            done ((physical.output_available pending).mp present))
        have frontierEmpty : frontier.outputs pending = none :=
          Option.not_isSome_iff_eq_none.mp (fun present =>
            absent ((frontier.output_available pending).mp present))
        exact physicalEmpty.trans frontierEmpty.symm

end Vegas
