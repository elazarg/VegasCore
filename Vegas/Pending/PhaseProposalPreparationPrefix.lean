/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalLostRecallReplay
import Vegas.Pending.PhaseArchivedBindings
import Vegas.Pending.PhaseProposalBindingSlots
import Vegas.Pending.PhaseResponseNormalization
import Interaction.ReactiveResponseNormalization

/-! # The actual prefix before changing a fresh ordinary preparation

Global physical freshness also holds in the saved checkpoint and every
retired snapshot by the existing immutable-candidate invariants. A value
transposition consequently changes no earlier physical state or foreign
raw decision record.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

local notation "app" => phaseApplication runtime leaks

/-- A preparation-only transposition fixes a native state while its chosen
physical handle is still fresh. Logical values and actions are always fixed. -/
theorem preparationOnly_native_of_fresh
    (candidate : Handle graph) (first second : Raw L) (state : State graph)
    (fresh : state.candidates.lookup candidate = .fresh) :
    state.swap (preparationOnly candidate first second) = state := by
  classical
  let swap := preparationOnly candidate first second
  have configuration : state.config.swap swap.values = state.config := by
    apply Config.ext_fields
    · rfl
    · rfl
    · funext event
      change (state.config.outputs event).map id = state.config.outputs event
      cases state.config.outputs event <;> rfl
    · rw [Config.swap_history]
      apply List.map_id''
      intro completion
      cases completion
      rfl
  have catalogue : swap.candidates state.candidates = state.candidates := by
    cases values : state.candidates with
    | mk table =>
        apply congrArg CommitmentCandidates.mk
        funext owner slot
        change swapCandidate (swap.raw (owner, slot)) (table owner slot) = table owner slot
        by_cases selected : (owner, slot) = candidate
        · have prior : table owner slot = .fresh := by
            have known := fresh
            rw [← selected, values] at known
            exact known
          rw [prior]
          rfl
        · rw [preparationOnly_raw_of_ne candidate (owner, slot) first second selected]
          cases table owner slot <;> rfl
  unfold State.swap
  rw [configuration, catalogue]

/-- Current physical freshness implies the same freshness in all saved and
retired catalogues of this actual counted prefix. -/
theorem preparationOnly_application_of_counted_fresh [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (candidate : Handle graph) (first second : Raw L)
    (fresh : control.execution.application.current.native.candidates.lookup candidate = .fresh) :
    control.execution.application.swap (preparationOnly candidate first second) =
      control.execution.application := by
  let swap := preparationOnly candidate first second
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have record := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have archives := phaseRetiredBindings_history runtime leaks plan inputs horizon scheduler raw
  have priorFresh (state : State graph)
      (kept : KeepsFixedCandidates state control.execution.application.current.native) :
      state.candidates.lookup candidate = .fresh := by
    by_contra fixed
    have prior := kept candidate fixed
    rw [fresh] at prior
    exact fixed prior.symm
  have saved := preparationOnly_native_of_fresh candidate first second
    control.execution.application.entry.native (priorFresh _ record.fixed)
  have current := preparationOnly_native_of_fresh candidate first second
    control.execution.application.current.native fresh
  have retired : control.execution.application.retired.map (RetiredCommitAttempt.swap swap) =
      control.execution.application.retired := by
    conv_rhs => rw [← List.map_id control.execution.application.retired]
    apply List.map_congr_left
    intro archived member
    simp only [id_eq]
    have fixed := preparationOnly_native_of_fresh candidate first second archived.state
      (priorFresh _ (archives archived member).2.2)
    cases archived
    exact congrArg (RetiredCommitAttempt.mk _) fixed
  unfold PhaseRuntimeState.swap
  have savedRecovery : control.execution.application.entry.swap swap =
      control.execution.application.entry := by
    change (⟨control.execution.application.entry.native.swap swap,
      control.execution.application.entry.excluded⟩ : RecoveryState graph) = _
    rw [saved]
  have currentRecovery : control.execution.application.current.swap swap =
      control.execution.application.current := by
    change (⟨control.execution.application.current.native.swap swap,
      control.execution.application.current.excluded⟩ : RecoveryState graph) = _
    rw [current]
  rw [savedRecovery, currentRecovery, retired]
  cases control.execution.application
  rfl

/-- The actual earlier prefix is kept literally. Only the designated sender's
raw aliases may differ under the proof comparison, so they are erased here. -/
theorem preparationOnly_prefix_erased_of_counted_fresh [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player) (slot : CandidateSlot graph) (first second : Raw L)
    (fresh : control.execution.application.current.native.candidates.lookup (owner, slot) =
      .fresh) :
    control.execution.eraseRecall app owner =
      ((preparationOnly (owner, slot) first second).phaseExecution control.execution).eraseRecall
        app owner := by
  classical
  let swap := preparationOnly (owner, slot) first second
  have application := preparationOnly_application_of_counted_fresh bounds plan inputs horizon
    scheduler control trace (owner, slot) first second fresh
  have recalled : ∀ who, who ≠ owner →
      (control.execution.recall who).map swap.phaseEntry = control.execution.recall who := by
    intro who different
    apply swap.phaseRecall_eq_of_fixed bounds (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler control trace who (fun _ _ => rfl) (fun _ _ => rfl)
    intro query
    apply preparationOnly_raw_of_ne
    exact fun same => different (congrArg Prod.fst same)
  change (⟨control.execution.application, control.execution.network, control.execution.receipts,
      fun who => if who = owner then [] else control.execution.recall who,
      control.execution.environmentRecall⟩ : (app).Execution) =
    ⟨control.execution.application.swap swap, control.execution.network, control.execution.receipts,
      fun who => if who = owner then [] else (control.execution.recall who).map swap.phaseEntry,
      control.execution.environmentRecall⟩
  rw [application]
  congr 1
  funext who
  by_cases same : who = owner
  · simp only [same, ↓reduceIte]
  · simp only [same, ↓reduceIte, recalled who same]

private theorem eraseRecall_respond_self (execution : (app).Execution)
    (owner : Player) (response : (app).Action) :
    (execution.respond app owner response).eraseRecall app owner =
      ((execution.eraseRecall app owner).respond app owner response).eraseRecall app owner := by
  classical
  cases response with
  | mk transmission =>
      cases transmission <;>
        simp only [ReactiveApplication.Execution.respond, ReactiveApplication.Execution.eraseRecall]
      all_goals
        congr 1
        funext who
        by_cases same : who = owner <;> simp only [same, ↓reduceIte]

private theorem eraseRecall_of_response_effects
    (left right : (app).Execution) (owner : Player)
    (application : left.application = right.application)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (foreign : ∀ who, who ≠ owner → left.recall who = right.recall who) :
    left.eraseRecall app owner = right.eraseRecall app owner := by
  classical
  cases left
  cases right
  cases application
  cases network
  cases receipts
  cases service
  simp only [ReactiveApplication.Execution.eraseRecall]
  congr 1
  funext who
  by_cases same : who = owner
  · simp only [same, ↓reduceIte]
  · simp only [same, ↓reduceIte]
    exact foreign who same

/-- At the actual fresh slot of any typed counted SEND, replace the typed
value, keep the original earlier trace, and construct its actual counted
response extension. The original private evidence request is retained on the
source side and normalized only for the designated image sender. -/
theorem preparationOnly_changed_response_prefix [Fintype Player]
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (prior : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, execution⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (serial : Nat) (first second : L.Val payload) (evidence : EvidenceRequest graph)
    (offered : (⟨some ⟨⟨.commitment event (owner, .prepared serial),
      some ⟨payload, first⟩⟩, evidence⟩⟩ : (app).Action) ∈
        PhaseCount.onePacketActions runtime leaks bounds owner (execution.recall owner)
          (execution.observe app owner))
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    let original := execution.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩⟩
    let image := execution.respond app owner
      (phaseBindingResponse runtime leaks owner event payload (.success second) serial)
    ∃ imageTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨remaining, none, image⟩),
      TracePrefix prior imageTrace ∧ imageTrace.transitionMass = prior.transitionMass ∧
      image.eraseRecall app owner =
        ((preparationOnly (owner, .prepared serial) ⟨payload, first⟩ ⟨payload,
          second⟩).phaseExecution
          original).eraseRecall app owner ∧
      original.application.entry.native.HandleUnused (owner, .prepared serial) ∧
      ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).ownPlay owner
            imageTrace =
        (some (execution.recall owner, execution.observe app owner),
          phaseBindingResponse runtime leaks owner event payload (.success second) serial) ::
          ((PhaseCount.onePacketMenu runtime leaks bounds).information
            (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).ownPlay owner prior
              := by
  classical
  intro original image
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let source : (app).Action :=
    ⟨some ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩⟩
  let canonical := phaseBindingResponse runtime leaks owner event payload (.success first) serial
  let target := phaseBindingResponse runtime leaks owner event payload (.success second) serial
  let swap : HiddenSwap graph :=
    preparationOnly (owner, .prepared serial) ⟨payload, first⟩ ⟨payload, second⟩
  have slot := PhaseProposal.binding_slot_of_counted_response runtime leaks bounds plan ordered
    inputs horizon scheduler remaining owner execution prior event payload binding request serial
      (some ⟨payload, first⟩) evidence offered values
  have allResults := (Finset.mem_filter.mp slot).2.2
  have targetOffered := allResults (.success second)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    prior
  have recallValid := PhaseCount.countRecall_history runtime leaks raw
  have fresh := (Finset.mem_filter.mp slot).2.1
  have permitted : PhaseCount.permits ((app).outputs (execution.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (execution.recall owner)
        (execution.observe app owner)
          ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩) = true
            := by
    have allowed := (PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ source).mp
      offered
    rcases allowed.2 with impossible | ⟨material, transmitted, permitted⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact permitted
  have normalized : (PhaseCount.normalization runtime leaks).action owner (execution.recall owner)
      (execution.observe app owner) source = canonical := by
    have absent := PhaseCount.normalize_binding_evidence_none runtime leaks owner
      (execution.recall owner) (execution.observe app owner)
      ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩ event
        (owner, .prepared serial) rfl permitted
    have effective : openingEffective owner (execution.observe app owner).application.1
        (.commitment event (owner, .prepared serial)) := ⟨rfl, fresh⟩
    have calls : ((PhaseCount.normalization runtime leaks).normalize owner
        (execution.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (execution.recall owner)
          (execution.observe app owner))
            ⟨⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩, evidence⟩).call =
              ⟨.commitment event (owner, .prepared serial), some ⟨payload, first⟩⟩ :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun material => (⟨some material⟩ : (app).Action))
      (congrArg₂ WitnessedSubmission.mk calls absent)
  have effects := (PhaseCount.normalization runtime leaks).effects execution owner source
    recallValid.1
  rw [normalized] at effects
  have normalizedErased := eraseRecall_of_response_effects
    (execution.respond app owner canonical) original owner effects.1 effects.2.1 effects.2.2.1
      effects.2.2.2.1 effects.2.2.2.2
  have initialRelation := preparationOnly_prefix_erased_of_counted_fresh bounds plan inputs horizon
    scheduler ⟨remaining, some owner, execution⟩ prior owner (.prepared serial) ⟨payload, first⟩
      ⟨payload, second⟩ fresh
  have targetAction : swap.phaseAction canonical = target := by
    simp only [swap, canonical, target, phaseBindingResponse, phaseAction,
      WitnessedSubmission.swap, Submission.swap, preparationOnly, ↓reduceIte,
      Option.map_some, Equiv.swap_apply_left]
  have response := swap.respond_phaseExecution execution owner canonical
    (by
      intro material transmitted
      cases Option.some.inj transmitted
      exact PhaseRuntimeState.emit_swap swap (execution.application.submit owner _)
        owner (execution.network.known owner) _ trivial)
  have paired : image.eraseRecall app owner =
      (swap.phaseExecution original).eraseRecall app owner := by
    change (execution.respond app owner target).eraseRecall app owner = _
    rw [eraseRecall_respond_self, initialRelation, ← eraseRecall_respond_self,
      ← targetAction, response]
    -- Only this sender's private recall is erased on either side.
    have commutes (next : (app).Execution) :
        (swap.phaseExecution next).eraseRecall app owner =
          (swap.phaseExecution (next.eraseRecall app owner)).eraseRecall app owner := by
      simp only [ReactiveApplication.Execution.eraseRecall, phaseExecution]
      congr 1
      funext who
      by_cases same : who = owner <;> simp only [same, ↓reduceIte]
    calc
      _ = (swap.phaseExecution
          ((execution.respond app owner canonical).eraseRecall app owner)).eraseRecall app owner :=
        commutes _
      _ = (swap.phaseExecution (original.eraseRecall app owner)).eraseRecall app owner :=
        congrArg (fun next : (app).Execution =>
          (swap.phaseExecution next).eraseRecall app owner) normalizedErased
      _ = _ := (commutes original).symm
  obtain ⟨imageTrace, retained, mass, word⟩ := phase_respond_trace_prefix bounds initial horizon
    scheduler
    remaining execution owner target prior targetOffered
  have record := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw
  have savedFresh : execution.application.entry.native.candidates.lookup
      (owner, .prepared serial) = .fresh := by
    by_contra fixed
    have persistent := record.fixed (owner, .prepared serial) fixed
    have freshNative : execution.application.current.native.candidates.lookup
        (owner, .prepared serial) = .fresh := fresh
    rw [freshNative] at persistent
    exact fixed persistent.symm
  refine ⟨imageTrace, retained, mass, paired,
    (fun field accepted => record.saved.accepted_fixed field _ accepted savedFresh), ?_⟩
  simpa only [↓reduceIte] using word owner

end Vegas.EventGraphRuntime.HiddenSwap
