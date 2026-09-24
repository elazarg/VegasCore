/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactiveAssociationEvidence

/-! # A prior private certificate acquires a public binding association

Alice sends a certified candidate; only Bob observes its opening. A later
packet associates the same candidate with the game, without carrying a new
certificate. Bob can now verify the named binding. Carol sees the association
and the entire ledger but cannot distinguish the two possible binding values.
-/

noncomputable section

namespace VegasTests.ReactiveAssociationEvidence

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev inputs : Fin 0 → EventGraph.EventField (Fin 3) simpleExpr := Fin.elim0
private abbrev outputs : Fin 1 → EventGraph.EventField (Fin 3) simpleExpr :=
  fun _ => .binding 0 .bool

private abbrev graph : EventGraph (Fin 3) simpleExpr where
  inputCount := 0
  order := {
    eventCount := 1
    predecessors _ := ∅
    predecessor_lt := by simp }
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.bind
    (layout := EventGraph.fieldLayout inputs outputs) 0 .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private def leaks : MessageNetwork.ObservationRule (Fin 3) (WitnessedPacket graph) :=
  fun _ _ => FinDist.pure {(0, 0)}

private abbrev app := runtime.reactiveApplication leaks
private abbrev candidate : Handle graph := (0, .prepared 0)
private def opening (bit : Bool) : OpeningFact graph := ⟨candidate, ⟨.bool, bit⟩⟩
private def named (bit : Bool) : EventGraph.CommitmentEvidence graph :=
  ⟨0, .bool, ⟨.inr 0, rfl⟩, bit⟩

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app (State.initial (fun input => nomatch input))

private def first (bit : Bool) : app.Execution :=
  initial.respond app 0 ⟨some (.submit
    ⟨⟨.commitment 0 candidate, some ⟨.bool, bit⟩⟩, .owned (opening bit)⟩)⟩

private def observed (bit : Bool) : app.Execution :=
  { first bit with
    network := (first bit).network.learn 1 {(0, 0)}
    environmentRecall := (first bit).environmentRecall ++
      [⟨(first bit).observeEnvironment app, .activate 1⟩] }

private def offered (bit : Bool) : app.Execution :=
  (observed bit).respond app 0
    ⟨some (.submit ⟨⟨.commitment 0 candidate, none⟩, .none⟩)⟩

private def included (bit : Bool) : app.Execution := (offered bit).includePending app (0, 1)

private theorem ready (bit : Bool) : (offered bit).application.config.cut.Ready 0 := by
  cases bit <;> decide

private def bound (bit : Bool) : State graph :=
  { (offered bit).application.complete 0 (ready bit) (.success bit) (.success bit) with
    accepted := Function.update (offered bit).application.accepted (.inr 0) (some candidate)
    candidates := (offered bit).application.candidates.freeze candidate }

private theorem accepts (bit : Bool) :
    app.handle (offered bit).application ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ =
      some (bound bit) := by
  have unused : (offered bit).application.HandleUnused candidate := by
    intro field
    cases field with
    | inl input => exact Fin.elim0 input
    | inr event =>
        change (none : Option (Handle graph)) ≠ some candidate
        simp
  have result := handle_commitment_eq runtime (offered bit).application (0, 1) 0 candidate
    0 .bool rfl rfl rfl (ready bit) (by change 0 < 2; decide) rfl rfl rfl unused
  change handle runtime (offered bit).application ⟨(0, 1), .commitment 0 candidate⟩ = _
  convert result using 1
  cases bit <;> rfl

private theorem lookup (bit : Bool) : (offered bit).network.lookup (0, 1) =
    some ⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩ := rfl

private theorem included_application (bit : Bool) : (included bit).application = bound bit := by
  unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change (app.handle _ _).getD _ = _
  rw [accepts]
  rfl

theorem activation_leaks_to_bob (bit : Bool) :
    (first bit).environmentStep app (.activate 1) = FinDist.pure (observed bit) := by
  simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
    FinDist.map_pure]
  rfl

theorem proof_before_association (bit : Bool) :
    opening bit ∈ (runtime.packetEvidence leaks).observe ((observed bit).observe app 1) ∧
      (observed bit).application.accepted (.inr 0) = none ∧
      (named bit).binding.get? (observed bit).application.config.store = none := by
  cases bit <;> decide

theorem association_without_new_certificate (bit : Bool) :
    (included bit).network.ledger = [⟨(0, 1), ⟨.commitment 0 candidate, none⟩⟩] ∧
      (included bit).receipts = [((0, 1), true)] ∧
      runtime.bindingEvidenceObserved leaks ((included bit).observe app 1) (named bit) := by
  refine ⟨rfl, ?_, candidate, ?_, ?_⟩
  · unfold included ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [lookup]
    change (offered bit).receipts ++ [((0, 1), (app.handle _ _).isSome)] = _
    rw [accepts]
    rfl
  · change (included bit).application.accepted (.inr 0) = some candidate
    rw [included_application]
    simp [bound]
  · cases bit <;> decide

theorem carol_has_no_certificate (bit : Bool) :
    (runtime.packetEvidence leaks).observe ((included bit).observe app 2) = [] := by
  cases bit <;> rfl

theorem carol_cannot_distinguish :
    (included false).observe app 2 = (included true).observe app 2 := by
  unfold ReactiveApplication.Execution.observe
  rw [included_application, included_application]
  rw [(association_without_new_certificate false).2.1,
    (association_without_new_certificate true).2.1]
  congr 1
  change (⟨2, (bound false).publicView, graph.playerObserve 2 (bound false).config,
      fun slot => (bound false).candidates.lookup (2, slot)⟩ : ReactivePlayerView graph) =
    ⟨2, (bound true).publicView, graph.playerObserve 2 (bound true).config,
      fun slot => (bound true).candidates.lookup (2, slot)⟩
  congr 1
  · unfold State.publicView
    congr 1
    apply EventGraph.PublicObservation.ext
    · rfl
    · apply graph.publicStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event => exact False.elim visible
  · apply EventGraph.PlayerObservation.ext
    · rfl
    · apply graph.playerStore_congr
      intro field visible
      cases field with
      | inl input => exact Fin.elim0 input
      | inr event => exact False.elim (by
          change (0 : Fin 3) = 2 at visible
          cases visible)
    · rfl

end VegasTests.ReactiveAssociationEvidence
