/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRetainedSlots

/-! # Prescribed policy support on retained service histories

A completed binding miss still supplies its failure-valued output to later
source observations. The compiler therefore decodes every ready source-ranked
decision, including decisions reached after misses. Value-only source admission
then supplies successful binding choices at these abstract views.

This is local policy admissibility. It does not identify a miss-reached source
continuation with a legal history of the original value-only game, and does not
assert that retained histories have zero audit charges.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

variable [Fintype Player]

/-- The retained menu uses only bounded raw responses. -/
theorem canonicalMenu_in_raw (bounds : MessageBounds (serviceGraph setup mode)) :
    (bounds.canonicalMenu (serviceRuntime setup mode deadline) leaks).IncludedIn
      (bounds.rawMenu (serviceRuntime setup mode deadline) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ :=
      ((serviceRuntime setup mode deadline).reactiveNormalization leaks).menu_mem
      (bounds.rawMenu (serviceRuntime setup mode deadline) leaks) who past view response |>.mp
      (bounds.canonicalActions_effective (serviceRuntime setup mode deadline) leaks who past
          view member)
  rw [← normal]
  exact bounds.rawMenu_closed (serviceRuntime setup mode deadline) leaks who past view
      original allowed

omit [Fintype Player] in
/-- A successful resolution packet uses the covered candidate value and an
admitted accepted handle. Failed resolution intentions transmit no packet. -/
theorem sourceService_resolutionPacket_allowed
    (bounds : MessageBounds (serviceGraph setup mode))
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (choice : (serviceGraph setup mode).Action event) (packet : Payload (serviceGraph setup mode))
    (sent : reactiveResolutionPacket who event payload binding checks outputEq
      choice (execution.observe (serviceApplication setup mode deadline leaks) who).application =
          some packet) :
    bounds.AllowsPacket packet := by
  dsimp only [reactiveResolutionPacket] at sent
  split at sent
  · split at sent
    · rename_i value resolved
      split at sent
      · rename_i candidate accepted
        split at sent
        · cases sent
          refine ⟨handles binding.field candidate accepted, ?_⟩
          apply bounds.resolved_value_covered execution.application valid values binding checks
            value
          change EventGraph.EventCode.resolveOutput? binding checks true
            ((serviceGraph setup mode).playerStore who execution.application.config.store) = _
            at resolved
          rwa [EventGraph.EventCode.resolveOutput?_playerStore] at resolved
        · cases sent
      · cases sent
    · cases sent
    · cases sent
  · cases sent

end Vegas
