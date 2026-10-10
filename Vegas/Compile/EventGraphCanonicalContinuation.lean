/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Compile.EventGraphIndependence
import Vegas.EventGraph.SchedulerErasure
import Vegas.EventGraph.ExecutionMode

/-! # Source readout of the compiled canonical semantic continuation

The graph continuation retains its complete semantic key. Its store decoder
recovers the exact original source law, including private initial parameters.
The protected timely source-service theorem composes this readout with actual
initialized reactive execution in modes retaining reveal barriers. Unilateral
deviations, off-path equilibrium completion and native audit payoffs require
separate evidence.
-/

noncomputable section
namespace Vegas
open SourceProgram GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The initial canonical semantic potential of the actual compiled profile
projects to original source execution, without any decoding failure. -/
theorem canonicalContinuation_source_decode
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (initial : State L Γ) :
    ((toEventGraph program).canonicalContinuation (compileEventProfile program profile)
      (EventGraph.Config.initial (encodeInputs initial))).map
        (fun key => decodeState? (terminalRefs program) key.2.1) =
      (SourceProgram.run program profile initial).map some := by
  rw [EventGraph.canonicalContinuation_initial, normalizeProfile_compileEventProfile,
    PMF.map_comp]
  have law := congrArg (fun distribution => distribution.map some)
    (canonical_terminalState_law program profile initial)
  rw [terminalOutcomes_map_decode] at law
  simpa only [PMF.map_comp, Function.comp_def, EventGraph.semanticKey,
    EventGraph.storeRecall] using law

/-- The source readout of the canonical semantic potential preserves the
entire initialized setup law, with its private draw sampled only once. -/
theorem canonicalContinuation_setup_source_decode
    (setup : Setup (Player := Player) (L := L)) (profile : BehavioralProfile setup.program) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.canonicalContinuation (compileEventProfile setup.program profile)
        (EventGraph.Config.initial (setup.eventInputs initial))).map
          (fun key => decodeState? (terminalRefs setup.program) key.2.1)) =
      (setup.run profile).map some := by
  rw [Setup.run, PMF.map_bind]
  apply bind_congr_on_support _
  intro initial _
  exact canonicalContinuation_source_decode setup.program profile initial

/-- Canonical source decoding is exact after transporting the compiled profile
to any dependency mode; operational runtime contracts are separate. -/
theorem canonicalContinuation_mode_source_decode
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (profile : BehavioralProfile program)
    (mode : EventGraph.ExecutionMode) (initial : State L Γ) :
    (((toEventGraph program).withMode mode).canonicalContinuation
      ((toEventGraph program).toModeProfile mode (compileEventProfile program profile))
      (EventGraph.Config.initial (encodeInputs initial))).map
        (fun key => decodeState? (terminalRefs program) key.2.1) =
      (SourceProgram.run program profile initial).map some := by
  rw [EventGraph.canonicalContinuation_initial, PMF.map_comp]
  change ((((toEventGraph program).withMode mode).runPolicies
    ((toEventGraph program).withMode mode).canonicalScheduler
      (((toEventGraph program).withMode mode).normalizeProfile
        ((toEventGraph program).toModeProfile mode (compileEventProfile program profile)))
          (encodeInputs initial)).map
            ((decodeState? (terminalRefs program)) ∘ EventGraph.Config.store)) = _
  rw [← PMF.map_comp]
  rw [EventGraph.runPolicies_withMode_store, EventGraph.fromModeProfile_normalizeProfile,
    EventGraph.fromModeProfile_toModeProfile, normalizeProfile_compileEventProfile]
  have source := canonicalContinuation_source_decode program profile initial
  rw [EventGraph.canonicalContinuation_initial, normalizeProfile_compileEventProfile,
    PMF.map_comp] at source
  simpa only [PMF.map_comp, Function.comp_def, EventGraph.semanticKey,
    EventGraph.storeRecall] using source

end Vegas
