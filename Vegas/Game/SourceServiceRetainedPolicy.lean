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

variable {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

variable [Fintype Player]

/-- The retained menu uses only bounded raw responses. -/
theorem canonicalMenu_in_raw (bounds : MessageBounds (serviceGraph setup deps)) :
    (bounds.canonicalMenu (serviceTimeouts setup deps duration) leaks).IncludedIn
      (bounds.rawMenu (serviceTimeouts setup deps duration) leaks) := by
  intro who past view response member
  obtain ⟨original, allowed, normal⟩ :=
      ((reactiveNormalization (serviceTimeouts setup deps duration)) leaks).menu_mem
      (bounds.rawMenu (serviceTimeouts setup deps duration) leaks) who past view response |>.mp
      (bounds.canonicalActions_effective (serviceTimeouts setup deps duration) leaks who past
          view member)
  rw [← normal]
  exact bounds.rawMenu_closed (serviceTimeouts setup deps duration) leaks who past view
      original allowed

omit [Fintype Player] in
/-- An authentic opening uses the covered binding value and an admitted accepted
handle, regardless of the eventual publication guard result. -/
theorem sourceService_resolutionPacket_allowed
    (bounds : MessageBounds (serviceGraph setup deps))
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (valid : execution.application.BindingInvariant)
    (values : bounds.CandidateValues execution.application)
    (handles : bounds.AcceptedHandles execution.application)
    (who : Player) (event : (serviceGraph setup deps).EventId) (payload : L.Ty)
    (binding : EventGraph.FieldRef (serviceGraph setup deps).layout (.binding who payload))
    (checks : List (EventGraph.GuardCheck (serviceGraph setup deps).layout payload))
    (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
    (choice : (serviceGraph setup deps).Action event) (packet : Payload (serviceGraph setup deps))
    (sent : reactiveResolutionPacket who event payload binding checks outputEq
      choice (execution.observe (serviceApplication setup deps duration leaks) who).application =
          some packet) :
    bounds.AllowsPacket packet := by
  rcases reactiveResolutionPacket_shape who event payload binding checks outputEq choice
      (execution.observe (serviceApplication setup deps duration leaks) who).application with
    ⟨candidate, raw, opened⟩ | quiet
  · have same : packet = .opening event candidate raw := Option.some.inj (sent.symm.trans opened)
    subst packet
    obtain ⟨_active, _disclose, _named, value, stored, accepted, _owned, rawEq⟩ :=
      reactiveResolutionPacket_opening_spec who event payload binding checks outputEq choice
        (execution.observe (serviceApplication setup deps duration leaks) who).application event
        candidate raw opened
    subst raw
    refine ⟨handles binding.field candidate accepted, ?_⟩
    apply bounds.binding_value_covered execution.application valid values binding value
    change binding.get? ((serviceGraph setup deps).playerStore who
      execution.application.config.store) = some (.success value) at stored
    rwa [binding.get?_playerStore who execution.application.config.store rfl] at stored
  · rw [quiet] at sent
    cases sent

end Vegas
