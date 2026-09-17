/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphCanonical
import Vegas.Compile.EventGraphIndependence
import Vegas.EventGraph.SchedulerErasure

/-! # Source outcome laws under public event scheduling

Graph-level scheduling independence and canonical source correspondence
compose through the terminal store. No source constructor or private initial
value is restricted by the scheduling argument.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]

/-- Every public schedule of the compiled source profile has the same decoded
terminal-state law as source execution. The scheduler may react to the actual
public store and completion order. -/
theorem scheduled_terminalState_law
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames)
    (unique : (Γ.map Prod.fst).Nodup)
    (scheduler : (toEventGraph program unique).PublicScheduler)
    (profile : BehavioralProfile program)
    (state : State L Γ) :
    ((toEventGraph program unique).terminalOutcomes scheduler
        (compileEventProfile program unique profile) (encodeInputs state)).map
      (terminalState program unique) =
    SourceProgram.run program profile state := by
  rw [← canonical_terminalState_law program unique profile state]
  apply FinDist.map_injective (f := some) (Option.some_injective _)
  rw [terminalOutcomes_map_decode, terminalOutcomes_map_decode]
  have storeLaw := (toEventGraph_barrierOrdered program unique).runPolicies_store_eq_canonical
    (compileEventProfile program unique profile) scheduler (encodeInputs state)
  simp only [normalizeProfile_compileEventProfile] at storeLaw
  rw [storeLaw]

/-- One compiled profile serves the entire private initial-state law under
any public scheduler. The setup draw remains inside the game. -/
theorem scheduled_setup_law
    (setup : Setup (Player := Player) (L := L))
    (scheduler : setup.eventGraph.PublicScheduler)
    (profile : BehavioralProfile setup.program) :
    (setup.initialLaw.bind fun initial =>
      (setup.eventGraph.terminalOutcomes scheduler
        (compileEventProfile setup.program setup.namesNodup profile)
        (setup.eventInputs initial)).map
          (terminalState setup.program setup.namesNodup)) =
      setup.run profile := by
  unfold Setup.run
  apply FinDist.bind_congr
  intro initial _
  exact scheduled_terminalState_law setup.program setup.namesNodup scheduler profile initial

end Vegas.SourceProgram.EventLowering
