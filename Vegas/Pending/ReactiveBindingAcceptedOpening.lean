/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameOpening
import Vegas.Pending.ReactiveDisclosureStability
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveSignedEvidence

/-! # Actual accepted openings through a private binding repair

An accepted original opening identifies a successful typed binding and the
actual deferred-guard result. These application facts preserve the full repair
frame without a certificate or public guard-success premise. This is an
operational inclusion result, not a continuation payoff comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual opening acceptance supplies its typed successful binding and its
guard result. Accepted publication failure is included. -/
theorem handle_opening_at_resolve_facts (runtime : EventGraphRuntime graph)
    (state next : State graph) (id : MessageId Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (accepted : handle runtime state ⟨id, .opening event candidate raw⟩ = some next) :
    state.config.cut.Ready event ∧ state.WithinDeadline runtime event ∧
      id.1 = actor ∧ candidate.1 = actor ∧
      state.accepted binding.field = some candidate ∧
      ∃ value : L.Val payload, raw = ⟨payload, value⟩ ∧
        state.candidates.lookup candidate = .openable ⟨payload, value⟩ ∧
        binding.get? state.config.store = some (.success value) ∧
        ∃ result : PublicationResult (L.Val payload),
          EventCode.resolveOutput? binding checks true state.config.store = some result := by
  by_cases ready : state.config.cut.Ready event
  swap
  · simp [handle, ready] at accepted
  by_cases timely : state.WithinDeadline runtime event
  swap
  · simp [handle, ready, timely] at accepted
  have facts := accepted
  simp only [handle, dite_eq_left ready, dite_eq_left timely, node] at facts
  split at facts
  swap
  · simp_all only [reduceCtorEq]
  simp only [dite_eq_ite, Option.ite_none_right_eq_some] at facts
  obtain ⟨owned, associated, verified, applied⟩ := facts
  split at applied
  · cases applied
  · rename_i value typed
    by_cases stored : binding.get? state.config.store = some (.success value)
    swap
    · simp [stored] at applied
    have available : ∀ field ∈ insert binding.field (GuardCheck.listReadFields checks),
        (state.config.store field).isSome = true := by
      intro field member
      apply state.config.read_available ready
      rw [resolution_readFields event actor payload binding checks outputEq codeEq]
      exact member
    have defined := EventCode.resolveOutput?_isSome binding checks true
      state.config.store available
    cases resolved : EventCode.resolveOutput? binding checks true state.config.store with
    | none => simp only [resolved, Option.isSome_none, Bool.false_eq_true] at defined
    | some result =>
        have rawEq : raw = ⟨payload, value⟩ := by
          rcases raw with ⟨kind, input⟩
          unfold Raw.as? at typed
          split at typed
          · rename_i same
            change kind = payload at same
            subst kind
            cases Option.some.inj typed
            rfl
          · cases typed
        refine ⟨ready, timely, ?_, owned, associated, value, rawEq, ?_, stored,
          result, rfl⟩
        · assumption
        · have fixed := (CommitmentCandidates.verify_eq_true_iff _ _ _).mp verified
          rwa [rawEq] at fixed

end Vegas.EventGraphRuntime

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Every actual original opening acceptance preserves the repair frame.
Binding provenance derives the shared candidate and value; no evidence or
successful-publication condition is imposed on the packet. -/
theorem accepted_opening_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (evidence : Option (OpeningFact graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩)
    (next : State graph)
    (accepted : handle runtime original.application ⟨id, .opening event candidate raw⟩ =
      some next) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨ready, timely, sender, owned, associated, value, rawEq, leftFixed, stored,
      result, resolved⟩ := runtime.handle_opening_at_resolve_facts original.application next id
        event candidate raw actor payload binding checks outputEq codeEq node accepted
  subst raw
  obtain ⟨rightStored, actual, leftAssociated, _, _, _, rightFixed⟩ :=
    frame.successful_opening leftBinding rightBinding binding value stored
  have same := Option.some.inj (leftAssociated.symm.trans associated)
  subst actual
  exact frame.opening_inclusion onlyBindings id event candidate actor payload binding checks
    outputEq codeEq node ready timely sender owned associated value leftFixed rightFixed stored
      rightStored result resolved evidence found

/-- A matching authentic certificate prevents the repaired side from accepting
an opening that the original application cannot execute. Its typed meaning and
association derive the original successful binding without a private oracle. -/
theorem certified_repaired_opening_inclusion
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, some ⟨candidate, raw⟩, some ⟨event⟩⟩⟩)
    (next : State graph)
    (accepted : handle runtime repaired.application ⟨id, .opening event candidate raw⟩ =
      some next) :
    (handle runtime original.application ⟨id, .opening event candidate raw⟩).isSome = true ∧
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } := by
  obtain ⟨rightReady, rightTimely, sender, owned, rightAssociated, value, rawEq, _,
      rightStored, result, rightResolved⟩ := runtime.handle_opening_at_resolve_facts
        repaired.application next id event candidate raw actor payload binding checks outputEq
          codeEq node accepted
  subst raw
  have leftFixed : original.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩ :=
    sound.lookup id _ found ⟨candidate, ⟨payload, value⟩⟩ (by
      change (⟨candidate, ⟨payload, value⟩⟩ : OpeningFact graph) ∈
        (some ⟨candidate, ⟨payload, value⟩⟩).toList
      exact List.mem_singleton_self _)
  have acceptedEq := congrArg PublicView.accepted frame.publicView
  have associated : original.application.accepted binding.field = some candidate :=
    (congrFun acceptedEq binding.field).trans rightAssociated
  have leftStored := leftBinding.opening_stored binding candidate value associated leftFixed
  obtain ⟨ready, timely, _, resolved⟩ := opening_right_facts runtime repaired.application
    original.application frame.publicView.symm event actor payload binding checks candidate
      rightReady rightTimely rightAssociated value rightStored leftStored result rightResolved
  have leftHandled := handle_opening_eq runtime original.application id event candidate actor
    payload binding checks outputEq codeEq node ready timely sender owned associated value
      leftFixed leftStored result resolved
  refine ⟨by rw [leftHandled]; rfl, ?_⟩
  exact frame.accepted_opening_inclusion onlyBindings leftBinding rightBinding id event candidate
    ⟨payload, value⟩ actor payload binding checks outputEq codeEq node
      (some ⟨candidate, ⟨payload, value⟩⟩) found _ leftHandled

/-- A repaired opening acceptance either preserves the actual inclusion frame
or its persisted signed envelope has no matching certificate. The latter is
the existing breach class, without any additional collection after a charge. -/
theorem repaired_opening_inclusion_or_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (evidence : Option (OpeningFact graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩)
    (next : State graph)
    (accepted : handle runtime repaired.application ⟨id, .opening event candidate raw⟩ =
      some next) :
    let app := runtime.reactiveApplication leaks
    Frame runtime leaks memory owner
      { original.includePending app id with environmentRecall := original.environmentRecall ++
        [⟨original.observeEnvironment app, .include id⟩] }
      { repaired.includePending app id with environmentRecall := repaired.environmentRecall ++
        [⟨repaired.observeEnvironment app, .include id⟩] } ∨
      SignedContentBreach ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩ := by
  by_cases certified : certifiedOpening
      ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩ = true
  · cases evidence with
    | none => simp only [certifiedOpening, Bool.false_eq_true] at certified
    | some fact =>
        simp only [certifiedOpening, decide_eq_true_eq] at certified
        subst fact
        exact Or.inl (frame.certified_repaired_opening_inclusion onlyBindings sound leftBinding
          rightBinding id event candidate raw actor payload binding checks outputEq codeEq node
            found next accepted).2
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨event, candidate, raw, rfl,
      Bool.eq_false_iff.mpr certified⟩)))

/-- An actual repaired-only acceptance is necessarily an uncertified signed
opening. A matching authentic certificate would supply an original acceptance. -/
theorem repaired_only_opening_breach
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (sound : (runtime.packetEvidence leaks).Sound original)
    (leftBinding : original.application.BindingInvariant)
    (rightBinding : repaired.application.BindingInvariant)
    (id : MessageId Player) (event : graph.EventId) (candidate : Handle graph)
    (raw : Raw L) (actor : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding actor payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve actor payload binding checks)
    (node : nodeView graph event = .resolve actor payload binding checks outputEq codeEq)
    (evidence : Option (OpeningFact graph))
    (found : original.network.lookup id =
      some ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩)
    (next : State graph)
    (accepted : handle runtime repaired.application ⟨id, .opening event candidate raw⟩ =
      some next)
    (rejected : handle runtime original.application ⟨id, .opening event candidate raw⟩ = none) :
    SignedContentBreach ⟨id, ⟨.opening event candidate raw, evidence, some ⟨event⟩⟩⟩ := by
  refine Or.inr (Or.inr (Or.inr ⟨event, candidate, raw, rfl, ?_⟩))
  apply Bool.eq_false_iff.mpr
  intro certified
  cases evidence with
  | none => simp only [certifiedOpening, Bool.false_eq_true] at certified
  | some fact =>
      simp only [certifiedOpening, decide_eq_true_eq] at certified
      subst fact
      have possible := (frame.certified_repaired_opening_inclusion onlyBindings sound leftBinding
        rightBinding id event candidate raw actor payload binding checks outputEq codeEq node
          found next accepted).1
      rw [rejected] at possible
      cases possible

end Vegas.EventGraphRuntime.BindingMemory.Frame
