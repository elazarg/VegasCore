/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Compile.EventGraphIndependence
import Vegas.EventGraph.SchedulerErasure

/-! # Source readout of the compiled canonical semantic continuation

The graph continuation retains its complete semantic key. Its store decoder
recovers the exact original source law, including private initial parameters.
The actual runtime/frontier equality is a separate operational obligation.
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

end Vegas
