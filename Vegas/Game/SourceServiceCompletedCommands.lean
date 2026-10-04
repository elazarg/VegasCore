/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskSlots
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Pending.ReactiveBindingCommitmentProvenance
import Vegas.Pending.ReactiveBindingPacketStep
import Interaction.ReactiveRawRoundTrace

/-! # Actual scheduler transitions at a completed repair boundary

The same environment coupling retains completed memory and the actual owner
commitment ledger. Both next controls are real RAW histories, and the focal
actual slot resources remain valid under arbitrary foreign actions.
The exceptional inclusion names an actual signed owner envelope already in
the original traffic. A changed opportunity flag is not called a charge.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Actual initialized traces discharge handler integrity and cache resources.
Every good command preserves the same whole frame, while the permanent ledger
and completed memory also hold on an exceptional inclusion's actual marginals.
No future response-support or deadline protection promise is required. -/
theorem sourceService_completed_environment_coupling
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (original repaired : (application setup leaks).Execution) (who : Player)
    (memory : BindingMemory (runtime setup) leaks)
    (frame : memory.Frame (runtime setup) leaks who original repaired)
    (onlyBindings : memory.shadow.OwnBindings who)
    (past : memory.shadow.CompletedAt original.application.config)
    (ledger : OwnerCommitmentsInertOrMatching who original repaired)
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining + 1, none, original⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining + 1, none, repaired⟩))
    (atTurn : OwnSubmissionsAtTurn setup leaks repaired who)
    (slots : CanonicalSlotsUsed setup leaks repaired who)
    (command : (application setup leaks).Command)
    (selected : command ∈ (scheduler original.environmentRecall
      (original.observeEnvironment (application setup leaks))).support) :
    let app := application setup leaks
    ∃ coupling : PMF (app.Execution × app.Execution),
      coupling.map Prod.fst = original.environmentStep app command ∧
      coupling.map Prod.snd = repaired.environmentStep app command ∧
      ∀ pair ∈ coupling.support,
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨leftRemaining, command.actor? app, pair.1⟩)) ∧
        Nonempty ((app.protocol (initialLaw setup) horizon scheduler).Trace
          (some ⟨rightRemaining, command.actor? app, pair.2⟩)) ∧
        memory.shadow.CompletedAt pair.1.application.config ∧
        OwnerCommitmentsInertOrMatching who pair.1 pair.2 ∧
        OwnSubmissionsAtTurn setup leaks pair.2 who ∧
        CanonicalSlotsUsed setup leaks pair.2 who ∧
        (memory.Frame (runtime setup) leaks who pair.1 pair.2 ∨
          ∃ id packet, command = .include id ∧
            original.network.lookup id = some ⟨id, packet⟩ ∧ id.1 = who ∧
              SignedContentBreach ⟨id, packet⟩) := by
  classical
  let app := application setup leaks
  have leftFacts := legalFacts setup leaks horizon scheduler _ leftTrace
  have rightFacts := legalFacts setup leaks horizon scheduler _ rightTrace
  have traffic := settledFacts_history (initialLaw setup) horizon scheduler leftTrace
  have fixed := (runtime setup).reactiveCommitmentsFixed_history leaks (initialLaw setup)
    horizon scheduler leftTrace
  have ownerCommitment (id event candidate evidence token)
      (found : original.network.lookup id =
        some ⟨id, ⟨.commitment event candidate, evidence, token⟩⟩)
      (authored : id.1 = who) (valid) :=
    ledger _ (traffic.carried.lookup id _ found) authored event candidate rfl valid
  obtain ⟨coupling, left, right, related⟩ := frame.environment_coupling_or_owner_breach
    onlyBindings past leftFacts.evidence leftFacts.binding rightFacts.binding fixed
      leftFacts.remembered rightFacts.remembered ownerCommitment command
  have rightSelected : command ∈ (scheduler repaired.environmentRecall
      (repaired.observeEnvironment app)).support := by
    rwa [← frame.service, ← frame.environment]
  refine ⟨coupling, left, right, ?_⟩
  intro pair supported
  have leftMoved : pair.1 ∈ (original.environmentStep app command).support := by
    rw [← left, PMF.support_map]
    exact ⟨pair, supported, rfl⟩
  have rightMoved : pair.2 ∈ (repaired.environmentStep app command).support := by
    rw [← right, PMF.support_map]
    exact ⟨pair, supported, rfl⟩
  have retained := ((runtime setup).reactiveCompletedInvariant leaks
    original.application.config.cut.completed).environmentStep original pair.1 command
      (Finset.Subset.refl _) leftMoved
  refine ⟨app.raw_trace_environment (initialLaw setup) horizon scheduler leftRemaining original
      pair.1 command leftTrace selected leftMoved,
    app.raw_trace_environment (initialLaw setup) horizon scheduler rightRemaining repaired pair.2
      command rightTrace rightSelected rightMoved,
    past.mono retained, ledger.environment leftFacts.binding pair.1 pair.2 command leftMoved
      rightMoved, ?_, canonicalSlotsUsed_environment rightMoved who slots,
    related pair supported⟩
  unfold OwnSubmissionsAtTurn
  rwa [app.environmentStep_recall repaired pair.2 command rightMoved]

end Vegas
