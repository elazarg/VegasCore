module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Pending.ReactiveCanonicalMenu
public import Vegas.Pending.ReactiveBoundedValues

@[expose] public section

/-! # Prescribed policy support on retained service histories

Canonical responses are bounded raw responses. Authentic opening packets carry
values from successful stored bindings and handles from the native accepted
table. These local bounds do not depend on a publication guard succeeding.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

variable [Fintype Player]

/-- The retained menu uses only bounded raw responses. -/
theorem canonicalMenu_in_raw (bounds : MessageBounds (serviceGraph setup mode)) :
    (bounds.canonicalMenu (serviceTimeouts setup mode duration) leaks).IncludedIn
      (bounds.rawMenu (serviceTimeouts setup mode duration) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ :=
      ((reactiveNormalization (serviceTimeouts setup mode duration)) leaks).menu_mem
      (bounds.rawMenu (serviceTimeouts setup mode duration) leaks) who past view response |>.mp
      (bounds.canonicalActions_effective (serviceTimeouts setup mode duration) leaks who past
          view member)
  rw [← normal]
  exact bounds.rawMenu_closed (serviceTimeouts setup mode duration) leaks who past view
      original allowed

omit [Fintype Player] in
/-- An authentic opening uses the covered binding value and an admitted accepted
handle, regardless of the eventual publication guard result. -/
theorem sourceService_resolutionPacket_allowed
    (bounds : MessageBounds (serviceGraph setup mode))
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (choice : (serviceGraph setup mode).Action event) (packet : Payload (serviceGraph setup mode))
    (sent : reactiveResolutionPacket who event payload binding checks outputEq
      choice (execution.observe (serviceApplication setup mode duration leaks) who).application =
          some packet) :
    bounds.AllowsPacket packet := by
  rcases reactiveResolutionPacket_shape who event payload binding checks outputEq choice
      (execution.observe (serviceApplication setup mode duration leaks) who).application with
    ⟨candidate, raw, opened⟩ | quiet
  · have same : packet = .opening event candidate raw := Option.some.inj (sent.symm.trans opened)
    subst packet
    obtain ⟨_active, _disclose, _named, value, stored, accepted, _owned, rawEq⟩ :=
      reactiveResolutionPacket_opening_spec who event payload binding checks outputEq choice
        (execution.observe (serviceApplication setup mode duration leaks) who).application event
        candidate raw opened
    subst raw
    refine ⟨handles binding.field candidate accepted, ?_⟩
    apply bounds.binding_value_covered execution.application valid values binding value
    change binding.get? ((serviceGraph setup mode).playerStore who
      execution.application.config.store) = some (.success value) at stored
    rwa [binding.get?_playerStore who execution.application.config.store rfl] at stored
  · rw [quiet] at sent
    cases sent

end Vegas
