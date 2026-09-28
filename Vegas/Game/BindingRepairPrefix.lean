/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BindingRepairBlock
import Vegas.Pending.ReactiveBindingRepair
import Vegas.Compile.EventGraphInputs

/-! # Repaired compiler prefixes

This is a proof invariant on the existing source configurations and reactive
executions. It preserves the joint public/opponent frame while recording how the
owner's source view is reconstructed. It adds neither runtime state nor player
observations. Static suffix alignment, deadlines and finite menu admission are
proved separately when applying an operational constructor case.
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The source repair and the native frames that must be maintained together.
The private owner's raw response recall is deliberately not equated. -/
structure RepairedPrefix
    {Γ₀ : SourceCtx Player L} {O₀ : Finset VarId}
    (whole : SourceProgram Player L Γ₀ O₀)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    {Γ : SourceCtx Player L} (refs : ContextRefs (toEventGraph whole).layout Γ)
    (owner : Player) (unpatch : ViewMap owner Γ) (patched : PatchMap owner Γ)
    (source : Bool → Config Player L Γ)
    (native : Bool → (runtime.reactiveApplication leaks).Execution) : Prop where
  repair : Patched unpatch patched (source false).state (source true).state
    (source false).history (source true).history
  registry : (source false).registry = (source true).registry
  revelations : @Eq (Revelations Γ) (source false).revelations (source true).revelations
  store : ∀ side, refs.Agrees (source side).state (native side).application.config.store
  history : ∀ side,
    decodeHistory whole (native side).application.config.history = (source side).history
  inputs : (native false).application.config.inputs = (native true).application.config.inputs
  network : (native false).network = (native true).network
  receipts : (native false).receipts = (native true).receipts
  publicView : (native false).application.publicView = (native true).application.publicView
  environmentRecall : (native false).environmentRecall = (native true).environmentRecall
  playerView : ∀ who, who ≠ owner →
    (native false).application.playerView who = (native true).application.playerView who
  recall : ∀ who, who ≠ owner → (native false).recall who = (native true).recall who
  fresh : ∀ query, (native false).application.candidates.lookup (owner, query) = .fresh ↔
    (native true).application.candidates.lookup (owner, query) = .fresh

variable {Γ₀ : SourceCtx Player L} {O₀ : Finset VarId}
  (whole : SourceProgram Player L Γ₀ O₀)
  (runtime : EventGraphRuntime (toEventGraph whole))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))

/-- Initialization carries every persistent private input unchanged, with no
restriction on correlations among owners' inputs or on prior source bindings. -/
theorem RepairedPrefix.initial (state : State L Γ₀) (owner : Player) :
    RepairedPrefix whole runtime leaks (ContextRefs.initial Γ₀ (outputLayout whole))
      owner id (fun _ _ => false)
      (fun _ => ⟨state, [], Revelations.initial Γ₀, fun _ => []⟩)
      (fun _ => ReactiveApplication.Execution.initial (runtime.reactiveApplication leaks)
        (EventGraphRuntime.State.initial (encodeInputs state))) where
  repair := patched_initial state
  registry := rfl
  revelations := rfl
  store := fun _ => initialConfig_agrees whole state
  history := fun _ => rfl
  inputs := rfl
  network := rfl
  receipts := rfl
  publicView := rfl
  environmentRecall := rfl
  playerView := fun _ _ => rfl
  recall := fun _ _ => rfl
  fresh := fun _ => Iff.rfl

variable {whole runtime leaks}
  {Γ : SourceCtx Player L} {refs : ContextRefs (toEventGraph whole).layout Γ}
  {owner : Player} {unpatch : ViewMap owner Γ} {patched : PatchMap owner Γ}
  {source : Bool → Config Player L Γ}
  {native : Bool → (runtime.reactiveApplication leaks).Execution}

/-- The compiler's real masked-store/action decoder recovers the corresponding
source decision view on either side of a repaired invariant. -/
theorem RepairedPrefix.decisionView
    (invariant : RepairedPrefix whole runtime leaks refs owner unpatch patched source native)
    (side : Bool) (who : Player) :
    (decodeObservation? who refs
      ((toEventGraph whole).playerObserve who (native side).application.config).store).map
        (fun observation => (observation, decodeCompletions whole
          ((toEventGraph whole).playerObserve who (native side).application.config).ownActions)) =
      some ((source side).view who) := by
  have observed : decodeObservation? who refs
      ((toEventGraph whole).playerObserve who (native side).application.config).store =
        some (sourceObserve who (source side).state) :=
    decodeObservation?_playerStore_eq_some refs who (source side).state
      (native side).application.config.store (invariant.store side)
  rw [observed]
  change some (sourceObserve who (source side).state,
    decodeHistory whole (native side).application.config.history who) = _
  rw [invariant.history side]
  rfl

/-- One fixed reconstruction function recovers the original owner's source
view from the repaired native prefix; it does not inspect a hidden world. -/
theorem RepairedPrefix.owner_decisionView
    (invariant : RepairedPrefix whole runtime leaks refs owner unpatch patched source native) :
    ((decodeObservation? owner refs
      ((toEventGraph whole).playerObserve owner (native true).application.config).store).map
        (fun observation => (observation, decodeCompletions whole
          ((toEventGraph whole).playerObserve owner
            (native true).application.config).ownActions))).map unpatch =
      some ((source false).view owner) := by
  rw [invariant.decisionView true owner, Option.map_some]
  exact congrArg some invariant.repair.unpatchEq

/-- All other source decision views are unchanged simultaneously, including
their own past actions and their persistent private inputs. -/
theorem RepairedPrefix.foreign_decisionView
    (invariant : RepairedPrefix whole runtime leaks refs owner unpatch patched source native)
    (who : Player) (different : who ≠ owner) :
    (decodeObservation? who refs
      ((toEventGraph whole).playerObserve who (native true).application.config).store).map
        (fun observation => (observation, decodeCompletions whole
          ((toEventGraph whole).playerObserve who (native true).application.config).ownActions)) =
      some ((source false).view who) := by
  rw [invariant.decisionView true who]
  apply congrArg some
  exact Prod.ext
    (sourceObserve_congr who (source true).state (source false).state
      invariant.repair.publicEq invariant.repair.publicationEq invariant.repair.inputEq
      (fun ref => invariant.repair.foreignEq ref different))
    (invariant.repair.historyEq who different)

/-- The existing smallest-fresh allocator remains the same actual function on
both private catalogs. A finite capacity bound is not silently strengthened. -/
theorem RepairedPrefix.freshSlot
    (invariant : RepairedPrefix whole runtime leaks refs owner unpatch patched source native) :
    reactiveFreshSlot ((runtime.reactiveApplication leaks).observePlayer
      (native false).application owner) =
      reactiveFreshSlot ((runtime.reactiveApplication leaks).observePlayer
        (native true).application owner) :=
  reactiveFreshSlot_congr _ _ fun serial => invariant.fresh (.prepared serial)

private theorem pure_eq {A : Type} {first second : A}
    (equal : FinDist.pure first = FinDist.pure second) : first = second := by
  have member : first ∈ (FinDist.pure first).support := FinDist.mem_support_pure.mpr rfl
  rw [equal] at member
  exact FinDist.mem_support_pure.mp member

/-- The actual compiled commitment block extends this invariant. The only
extra premises are its entry service conditions and the static action decoder;
the paired public frame, private repair and source-view reconstruction are
conclusions, not further continuation assumptions. -/
theorem RepairedPrefix.commit
    (invariant : RepairedPrefix whole runtime leaks refs owner unpatch patched source native)
    {payload : L.Ty} (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (event : (toEventGraph whole).EventId)
    (outputEq : (toEventGraph whole).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (toEventGraph whole).layout) outputEq)
      ((toEventGraph whole).nodes event) = .bind owner payload)
    (node : nodeView (toEventGraph whole) event = .bind owner payload outputEq codeEq)
    (before : ∀ {readName cell} (ref : HasVar Γ readName cell),
      FieldBefore event (refs.get ref).field)
    (decoded : ∀ choice : PublicationResult (L.Val payload), decodeEventAction whole event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) choice) =
        some (.commit owner name payload choice))
    (binding repairedBinding : PublicationResult (L.Val payload))
    (repair : repairedBinding = match binding with
      | .failure => .success (L.someValue payload) | .success value => .success value)
    (original : DecisionView owner Γ → Option (PublicationResult (L.Val payload)))
    (chosen : original ((source true).view owner) = some binding)
    (serial : Nat)
    (ready : (native false).application.config.cut.Ready event)
    (timely : (native false).application.WithinDeadline runtime event)
    (fresh : (native false).application.candidates.lookup (owner, .prepared serial) = .fresh)
    (vacant : (native false).application.accepted (.inr event) = none)
    (unused : (native false).application.HandleUnused (owner, .prepared serial))
    (serials : (native false).network.SerialsBeforeNext)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (final : Bool → (runtime.reactiveApplication leaks).Execution)
    (supported : ∀ side, final side ∈
      (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        ((native side).respond (runtime.reactiveApplication leaks) owner
          (runtime.reactiveBinding leaks owner event payload
            (if side then repairedBinding else binding) serial))).support) :
    RepairedPrefix whole runtime leaks
      (refs.cons (name := name) (cell := .commitment owner payload) ⟨.inr event, outputEq⟩)
      owner (unpatch.afterCommit (decide (owner = owner)) name owner payload original)
      (patched.afterCommit (decide (owner = owner)) name owner payload original)
      (fun side => commitSuccessor name guard (source side)
        (if side then repairedBinding else binding)) final := by
  let app := runtime.reactiveApplication leaks
  have readyBoth : ∀ side, (native side).application.config.cut.Ready event := by
    intro side
    cases side with
    | false => exact ready
    | true =>
        rw [← EventGraphRuntime.State.publicView_eventReady, ← invariant.publicView,
          EventGraphRuntime.State.publicView_eventReady]
        exact ready
  have timelyBoth : ∀ side, (native side).application.WithinDeadline runtime event := by
    intro side
    cases side with
    | false => exact timely
    | true =>
        unfold EventGraphRuntime.State.WithinDeadline
        rw [← show (native false).application.clock = (native true).application.clock from
          congrArg PublicView.clock invariant.publicView,
          ← show (native false).application.activatedAt =
              (native true).application.activatedAt from
            congrArg PublicView.activatedAt invariant.publicView]
        exact timely
  have freshBoth : ∀ side,
      (native side).application.candidates.lookup (owner, .prepared serial) = .fresh := by
    intro side
    cases side with
    | false => exact fresh
    | true => exact (invariant.fresh (.prepared serial)).mp fresh
  have accepted : (native false).application.accepted = (native true).application.accepted :=
    congrArg PublicView.accepted invariant.publicView
  have vacantBoth : ∀ side, (native side).application.accepted (.inr event) = none := by
    intro side
    cases side with
    | false => exact vacant
    | true => exact (congrFun accepted (.inr event)).symm.trans vacant
  have unusedBoth : ∀ side,
      (native side).application.HandleUnused (owner, .prepared serial) := by
    intro side
    cases side with
    | false => exact unused
    | true =>
        intro field associated
        exact unused field ((congrFun accepted field).trans associated)
  have serialsBoth : ∀ side, (native side).network.SerialsBeforeNext := by
    intro side
    cases side with
    | false => exact serials
    | true => exact invariant.network ▸ serials
  have repaired := reactive_commit_repair runtime leaks name guard source refs native final
    unpatch patched invariant.repair invariant.registry invariant.revelations invariant.store
    event outputEq codeEq node before binding repairedBinding repair original chosen serial
    readyBoth timelyBoth freshBoth vacantBoth unusedBoth serialsBoth players scheduler supported
  have block (side : Bool) :
      runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        ((native side).respond app owner (runtime.reactiveBinding leaks owner event payload
          (if side then repairedBinding else binding) serial)) = FinDist.pure (final side) := by
    have member := supported side
    rw [runtime.reactiveBinding_reserved_selection leaks (native side) owner event payload _ serial
      (serialsBoth side) players scheduler] at member ⊢
    simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
      FinDist.mem_support_pure] at member ⊢
    exact congrArg FinDist.pure member.symm
  have joint := runtime.reactiveBinding_reserved_hidden_congr leaks (native false) (native true)
    owner invariant.network invariant.receipts invariant.publicView invariant.environmentRecall
    invariant.playerView invariant.recall invariant.fresh event payload outputEq codeEq node
    binding repairedBinding serial ready timely vacant unused serials players scheduler
  dsimp only at joint
  have blockFalse := block false
  have blockTrue := block true
  simp only [Bool.false_eq_true, ↓reduceIte] at blockFalse
  simp only [↓reduceIte] at blockTrue
  rw [blockFalse, blockTrue, FinDist.map_pure, FinDist.map_pure] at joint
  have same :
      ((final false).network, (final false).receipts, (final false).application.publicView,
        (final false).environmentRecall,
        (fun who => if who = owner then none
          else some ((final false).recall who, (final false).application.playerView who)),
        fun query => (final false).application.candidates.lookup (owner, query) = .fresh) =
      ((final true).network, (final true).receipts, (final true).application.publicView,
        (final true).environmentRecall,
        (fun who => if who = owner then none
          else some ((final true).recall who, (final true).application.playerView who)),
        fun query => (final true).application.candidates.lookup (owner, query) = .fresh) := by
    exact pure_eq joint
  refine ⟨repaired.1, repaired.2.1, repaired.2.2.1, repaired.2.2.2, ?_, ?_,
    congrArg Prod.fst same, congrArg (fun frame => frame.2.1) same,
    congrArg (fun frame => frame.2.2.1) same, congrArg (fun frame => frame.2.2.2.1) same,
    ?_, ?_, ?_⟩
  · intro side
    exact reactive_commit_history whole runtime leaks name guard (source side) (native side)
      (final side) (invariant.history side) event outputEq codeEq node _ (decoded _) serial
      (readyBoth side) (timelyBoth side) (freshBoth side) (vacantBoth side) (unusedBoth side)
      (serialsBoth side) players scheduler (supported side)
  · have retained (side : Bool) : (final side).application.config.inputs =
        (native side).application.config.inputs := by
      have law := runtime.reactiveBinding_reserved_config leaks (native side) owner event payload
        outputEq codeEq node (if side then repairedBinding else binding) serial
        (readyBoth side) (timelyBoth side) (freshBoth side) (vacantBoth side) (unusedBoth side)
        (serialsBoth side) players scheduler
      dsimp only at law
      rw [block side, FinDist.map_pure] at law
      have equal := pure_eq law
      exact congrArg (fun result => result.1.inputs) equal
    exact (retained false).trans (invariant.inputs.trans (retained true).symm)
  · intro who different
    have localEq := congrFun (congrArg (fun frame => frame.2.2.2.2.1) same) who
    simp only [different, ↓reduceIte, Option.some.injEq] at localEq
    exact congrArg Prod.snd localEq
  · intro who different
    have localEq := congrFun (congrArg (fun frame => frame.2.2.2.2.1) same) who
    simp only [different, ↓reduceIte, Option.some.injEq] at localEq
    exact congrArg Prod.fst localEq
  · intro query
    exact iff_of_eq (congrFun (congrArg (fun frame => frame.2.2.2.2.2) same) query)

end Vegas
