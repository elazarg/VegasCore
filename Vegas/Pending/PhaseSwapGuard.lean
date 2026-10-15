/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseClearPhasePersistence
import Vegas.Pending.PhaseSwapMenu

/-! # Backward native replay guards on clear phased histories -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Only completed revelations and ready revelations of the installed phase
may constrain the swap. Future graph-ready revelations remain masked. -/
structure PhaseSwapGuard (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (swap : HiddenSwap graph) (current : (phaseApplication runtime leaks).Execution) : Prop where
  clear : current.application.current.excluded = ∅
  compatible : ∀ event candidate,
    current.application.current.native.accepted (.inr event) = some candidate →
      BindCompatible swap event candidate
  completed : ∀ event, event ∈ current.application.current.native.config.cut.completed →
    RevealFixed swap current.application.current.native event
  active : ∀ phase remaining, current.application.phases = phase :: remaining →
    ∀ event, event ∈ phase.events → current.application.current.native.config.cut.Ready event →
      RevealFixed swap current.application.current.native event
  requests : ∀ who, ∀ entry ∈ current.recall who, ∀ submission,
    entry.action.transmission = some submission → submission.evidence.FixedBy swap

namespace HiddenSwap

omit [DecidableEq Player] in
/-- Revelation compatibility pulls back along the actual accepted table.
Its private field map is state-independent. -/
theorem revealFixed_of_accepted_extension (swap : HiddenSwap graph)
    (before after : State graph)
    (accepted : ∀ field candidate, before.accepted field = some candidate →
      after.accepted field = some candidate) (event : graph.EventId)
    (fixed : RevealFixed swap after event) : RevealFixed swap before event := by
  unfold RevealFixed at fixed ⊢
  cases node : nodeView graph event with
  | bind | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [node] at fixed
      exact ⟨fixed.1, fun candidate present => fixed.2 candidate
        (accepted binding.field candidate present)⟩

end HiddenSwap

/-- The primitive guard is closed under every actual predecessor of a clear
endpoint. No completeness, strategy or observation-fiber hypothesis is used. -/
theorem phaseSwapGuard_of_transition (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (swap : HiddenSwap graph) (initial : PMF (phaseApplication runtime leaks).State)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (joint : Player → Option (phaseApplication runtime leaks).Action)
    (reached : some after ∈ ((phaseApplication runtime leaks).transition initial horizon scheduler
      (some before) joint).support)
    (guarded : PhaseSwapGuard runtime leaks swap after.execution) :
    PhaseSwapGuard runtime leaks swap before.execution := by
  let app := phaseApplication runtime leaks
  obtain ⟨_store, _history, accepted, completed⟩ :=
    (phaseApplication_clear_nativeProgress runtime leaks).transition initial horizon scheduler
      before after joint reached guarded.clear
  have permanent := (phaseApplication_exclusion_monotone runtime leaks).transition initial
    horizon scheduler before after joint reached
  have clear : before.execution.application.current.excluded = ∅ :=
    Finset.subset_empty.mp (guarded.clear ▸ permanent)
  have prefixes := app.transition_recall_prefix initial horizon scheduler before (some after)
    joint reached
  obtain ⟨next, same, recalled⟩ := prefixes
  cases Option.some.inj same
  refine ⟨clear, ?_, ?_, ?_, ?_⟩
  · intro event candidate present
    exact guarded.compatible event candidate (accepted (.inr event) candidate present)
  · intro event done
    exact swap.revealFixed_of_accepted_extension _ _ accepted event
      (guarded.completed event (completed done))
  · intro phase remaining installed event inside ready
    apply swap.revealFixed_of_accepted_extension _ _ accepted event
    by_cases done : event ∈ after.execution.application.current.native.config.cut.completed
    · exact guarded.completed event done
    · have samePhase := (phaseApplication_clear_phasePersistence runtime leaks).transition
        initial horizon scheduler before after joint reached guarded.clear phase remaining
          installed event inside done
      exact guarded.active phase remaining (samePhase.trans installed) event inside
        ⟨done, ready.2.trans completed⟩
  · intro who entry member submission transmitted
    exact guarded.requests who entry ((recalled who).subset member) submission transmitted

end Vegas.EventGraphRuntime
