/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageFocalDeterminism
import Vegas.Graph.MessageBindingSoundness
import Vegas.Graph.MessageInvariant
import Vegas.Graph.MessageStepLaw

/-! # Extracting the first effective action of a native deviation

Native message execution contains private preparation, publication, delivery,
and rejected inclusion steps.  A service block may also contain several graph
phases.  This file identifies the first individual native step that changes the
graph phase, and relates such a step at a player-owned bind or resolve cursor to
the corresponding action of the typed graph semantics.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A supported native path up to, and including, its first graph-phase change.
The output `before` is the last native state at `phase`; `after` is the result of
the first individual action that moves beyond it. -/
inductive FirstPhaseChange (runtime : GraphRuntime Player L Δ) (phase : Nat) :
    runtime.application.State → List runtime.application.Action →
      runtime.application.State → runtime.application.Action →
        runtime.application.State → Prop where
  | here {state next : runtime.application.State}
      {action : runtime.application.Action} {rest : List runtime.application.Action}
      (atPhase : state.application.phase = phase)
      (step : next ∈ (runtime.application.step state action).support)
      (changed : phase < next.application.phase) :
      FirstPhaseChange runtime phase state (action :: rest) state action next
  | later {state middle before after : runtime.application.State}
      {action changedAction : runtime.application.Action}
      {rest : List runtime.application.Action}
      (atPhase : state.application.phase = phase)
      (step : middle ∈ (runtime.application.step state action).support)
      (samePhase : middle.application.phase = phase)
      (tail : FirstPhaseChange runtime phase middle rest before changedAction after) :
      FirstPhaseChange runtime phase state (action :: rest) before changedAction after

namespace FirstPhaseChange

theorem before_phase {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after) :
    before.application.phase = phase := by
  induction first with
  | here atPhase => exact atPhase
  | later _ _ _ tail ih => exact ih

theorem supported {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after) :
    after ∈ (runtime.application.step before action).support := by
  induction first with
  | here _ step => exact step
  | later _ _ _ _ ih => exact ih

theorem changed {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after) :
    phase < after.application.phase := by
  induction first with
  | here _ _ changed => exact changed
  | later _ _ _ _ ih => exact ih

/-- The selected `before` state is genuinely reached by a prefix of the given
native action list.  This is the bridge used to transport run invariants, such
as public agreement and binding soundness, to the extraction point. -/
theorem before_reachable {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after) :
    ∃ pre post,
      actions = pre ++ action :: post ∧
      before ∈ (runtime.application.run pre start).support := by
  induction first with
  | @here state next firstAction rest atPhase step changed =>
      exact ⟨[], rest, rfl, by simp⟩
  | @later state middle prior after firstAction changedAction rest
      atPhase step samePhase tail ih =>
      obtain ⟨pre, post, rest_eq, reachable⟩ := ih
      refine ⟨firstAction :: pre, post, ?_, ?_⟩
      · simp only [List.cons_append, rest_eq]
      · simp only [MessageApplication.run_cons, FinDist.support_bind, Set.mem_iUnion]
        exact ⟨middle, step, reachable⟩

theorem before_publicAgreement {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after)
    (agreement : start.application.PublicAgreement) :
    before.application.PublicAgreement := by
  obtain ⟨pre, _post, _actions, reachable⟩ := first.before_reachable
  exact runtime.run_preserves_publicAgreement start before pre agreement reachable

theorem before_bindingSoundness {runtime : GraphRuntime Player L Δ} {phase : Nat}
    {start before after : runtime.application.State}
    {actions : List runtime.application.Action} {action : runtime.application.Action}
    (first : FirstPhaseChange runtime phase start actions before action after)
    (sound : start.application.BindingSoundness) :
    before.application.BindingSoundness := by
  obtain ⟨pre, _post, _actions, reachable⟩ := first.before_reachable
  exact runtime.run_bindingSoundness pre start before sound reachable

end FirstPhaseChange

/-- Any supported native run that advances the graph has a first individual
phase-changing action, even when the supplied action list crosses several graph
phases. -/
theorem exists_firstPhaseChange_of_run (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action)
    (state final : runtime.application.State)
    (supported : final ∈ (runtime.application.run actions state).support)
    (advanced : state.application.phase < final.application.phase) :
    ∃ before action after,
      FirstPhaseChange runtime state.application.phase state actions before action after := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at supported
      subst final
      exact (Nat.lt_irrefl _ advanced).elim
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨middle, hmiddle, hfinal⟩ := supported
      have monotone := runtime.application_step_phase_mono state middle action hmiddle
      by_cases changed : state.application.phase < middle.application.phase
      · exact ⟨state, action, middle, .here rfl hmiddle changed⟩
      · have same : middle.application.phase = state.application.phase :=
          Nat.le_antisymm (Nat.le_of_not_gt changed) monotone
        have tailAdvanced : middle.application.phase < final.application.phase := by
          simpa [same] using advanced
        obtain ⟨before, changedAction, after, first⟩ :=
          ih middle hfinal tailAdvanced
        rw [same] at first
        exact ⟨before, changedAction, after,
          .later rfl hmiddle same first⟩

/-- The trusted part of a concrete phase change: the immutable ideal state is
extended exactly as one action of the typed graph semantics prescribes.  Pool,
receipt, and policy-local cache state are deliberately absent. -/
inductive State.RealizesOwnAction :
    State Player L Δ → Graph.OwnAction Player L → State Player L Δ → Prop where
  | bind {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
      {fresh : name ∉ Γ.map Prod.fst}
      {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
      {ideal : VEnv L Γ} {values : PublicValues Γ} {bindings : Bindings Player}
      {candidates : CommitmentCandidates Player Slot (Raw L)} {pc clock enteredAt : Nat}
      (choice : PublicationResult (L.Val payload))
      (nextBindings : Bindings Player)
      (nextCandidates : CommitmentCandidates Player Slot (Raw L))
      (nextClock : Nat) :
      State.RealizesOwnAction
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt)
        (.bind owner name payload choice)
        (.running next (VEnv.cons ((R.valueEquiv payload).symm choice) ideal)
          (PublicValues.consSealed values) nextBindings nextCandidates
          (pc + 1) nextClock nextClock)
  | resolveFailure {Γ : VCtx Player L} {outputName bindingName : VarId}
      {owner : Player} {payload : L.Ty} {fresh : outputName ∉ Γ.map Prod.fst}
      {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
      {checks : List (GuardCheck (R := R)
        ((outputName, .pub (R.result payload)) :: Γ))}
      {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
      {ideal : VEnv L Γ} {values : PublicValues Γ} {bindings : Bindings Player}
      {candidates : CommitmentCandidates Player Slot (Raw L)} {pc clock enteredAt : Nat}
      (nextClock : Nat) :
      State.RealizesOwnAction
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt)
        (.resolve owner bindingName false)
        (.running next (VEnv.cons ((R.valueEquiv payload).symm
            (.failure : PublicationResult (L.Val payload))) ideal)
          (PublicValues.consPublic ((R.valueEquiv payload).symm
            (.failure : PublicationResult (L.Val payload))) values)
          bindings candidates (pc + 1) nextClock nextClock)
  | resolveSuccess {Γ : VCtx Player L} {outputName bindingName : VarId}
      {owner : Player} {payload : L.Ty} {fresh : outputName ∉ Γ.map Prod.fst}
      {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
      {checks : List (GuardCheck (R := R)
        ((outputName, .pub (R.result payload)) :: Γ))}
      {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
      {ideal : VEnv L Γ} {values : PublicValues Γ} {bindings : Bindings Player}
      {candidates : CommitmentCandidates Player Slot (Raw L)} {pc clock enteredAt : Nat}
      (value : L.Val payload)
      (accepted : acceptedResult source checks ideal true = .success value)
      (nextClock : Nat) :
      State.RealizesOwnAction
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt)
        (.resolve owner bindingName true)
        (.running next (VEnv.cons ((R.valueEquiv payload).symm (.success value)) ideal)
          (PublicValues.consPublic ((R.valueEquiv payload).symm (.success value)) values)
          bindings candidates (pc + 1) nextClock nextClock)

private theorem advanceBind_realizes
    {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) (handle : Handle Player) :
    ∃ choice : PublicationResult (L.Val payload),
      State.RealizesOwnAction
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt)
        (.bind owner name payload choice)
        (advanceBind next ideal values bindings candidates pc clock handle) := by
  cases candidate : candidates.lookup handle with
  | fresh =>
      refine ⟨.failure, ?_⟩
      simpa [advanceBind, candidate] using
        (State.RealizesOwnAction.bind (Δ := Δ) (.failure : PublicationResult (L.Val payload))
          ((name, handle) :: bindings) (candidates.accept handle) clock)
  | unopenable =>
      refine ⟨.failure, ?_⟩
      simpa [advanceBind, candidate] using
        (State.RealizesOwnAction.bind (Δ := Δ) (.failure : PublicationResult (L.Val payload))
          ((name, handle) :: bindings) (candidates.accept handle) clock)
  | openable raw =>
      cases typed : raw.as? (R.result payload) with
      | none =>
          refine ⟨.failure, ?_⟩
          simpa [advanceBind, candidate, typed] using
            (State.RealizesOwnAction.bind (Δ := Δ)
              (.failure : PublicationResult (L.Val payload))
              ((name, handle) :: bindings) (candidates.accept handle) clock)
      | some encoded =>
          refine ⟨R.valueEquiv payload encoded, ?_⟩
          simpa [advanceBind, candidate, typed] using
            (State.RealizesOwnAction.bind (Δ := Δ) (R.valueEquiv payload encoded)
              ((name, handle) :: bindings) (candidates.accept handle) clock)

private theorem advanceBindFailure_realizes
    {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt nextClock : Nat) :
    State.RealizesOwnAction
      (.running (.bind name owner fresh next) ideal values bindings candidates
        pc clock enteredAt)
      (.bind owner name payload .failure)
      (advanceBindFailure next ideal values bindings candidates pc nextClock) := by
  simpa [advanceBindFailure] using
    (State.RealizesOwnAction.bind (Δ := Δ) (.failure : PublicationResult (L.Val payload))
      bindings candidates nextClock)

/-- At a focal-owned bind cursor, every individual native step that advances
the graph realizes exactly one source-level bind action.  The choice is read
from the immutable value actually appended by the transition; an expired,
fresh, unopenable, or ill-typed candidate therefore extracts as failure. -/
theorem phaseChangingStep_bind_realizes
    (runtime : GraphRuntime Player L Δ)
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (pool : MessagePool Player (Payload Player L))
    (receipts : List (MessageId Player × Bool))
    (action : runtime.application.Action) (after : runtime.application.State)
    (supported : after ∈ (runtime.application.step
      ⟨.running (.bind name owner fresh next) ideal values bindings candidates
        pc clock enteredAt, pool, receipts⟩ action).support)
    (advanced : pc < after.application.phase) :
    ∃ choice : PublicationResult (L.Val payload),
      State.RealizesOwnAction
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt)
        (.bind owner name payload choice) after.application := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      change pc < (runtime.privateStep
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt) who command).phase at advanced
      rw [runtime.privateStep_phase] at advanced
      exact (Nat.lt_irrefl _ advanced).elim
  | submit who wire | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      simp [State.phase] at advanced
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      change application ∈ (runtime.environmentStep
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt) .tick).support at happened
      by_cases expired : runtime.deadline pc ≤ clock + 1 - enteredAt
      · rw [runtime.environmentStep_bind_expired fresh next ideal values bindings candidates
          pc clock enteredAt expired] at happened
        simp only [FinDist.mem_support_pure] at happened
        subst application
        exact ⟨.failure, advanceBindFailure_realizes ideal values bindings candidates
          pc clock enteredAt (clock + 1)⟩
      · simp only [GraphRuntime.environmentStep, GraphRuntime.tick, expired,
          ↓reduceIte, FinDist.mem_support_pure] at happened
        subst application
        simp [State.phase] at advanced
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      cases lookup : pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing
            (state := ⟨.running (.bind name owner fresh next) ideal values bindings candidates
              pc clock enteredAt, pool, receipts⟩) id lookup] at advanced
          simp [State.phase] at advanced
      | some message =>
          cases handled : runtime.handle
              (.running (.bind name owner fresh next) ideal values bindings candidates
                pc clock enteredAt) message with
          | none =>
              rw [runtime.application.includePending_reject
                (state := ⟨.running (.bind name owner fresh next) ideal values bindings candidates
                  pc clock enteredAt, pool, receipts⟩) id message lookup handled] at advanced
              simp [State.phase] at advanced
          | some application =>
              rw [runtime.application.includePending_accept
                (state := ⟨.running (.bind name owner fresh next) ideal values bindings candidates
                  pc clock enteredAt, pool, receipts⟩) id message application lookup handled]
              rcases message with ⟨messageId, wire⟩
              cases wire with
              | commitment site handle =>
                  simp only [GraphRuntime.handle] at handled
                  split_ifs at handled
                  cases handled
                  exact advanceBind_realizes ideal values bindings candidates
                    pc clock enteredAt handle
              | opening | withhold | malformed => simp [GraphRuntime.handle] at handled

private theorem advanceResolveFailure_realizes
    {Γ : VCtx Player L} {outputName bindingName : VarId}
    {owner : Player} {payload : L.Ty} {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt nextClock : Nat) :
    State.RealizesOwnAction
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt)
      (.resolve owner bindingName false)
      (advanceResolve next ideal values bindings candidates pc nextClock .failure) := by
  simpa [advanceResolve, acceptedResult, proposedResult] using
    (State.RealizesOwnAction.resolveFailure (Δ := Δ) (source := source) nextClock)

/-- At a focal-owned resolve cursor, every phase-changing native step realizes
the Boolean selected by the typed graph semantics: an accepted verified opening
is `true`, while authenticated withholding or expiry is `false`.  The opening
case requires public agreement and backward binding soundness; neither an
adversarial policy cache nor `rememberDisclosure` is consulted. -/
theorem phaseChangingStep_resolve_realizes
    (runtime : GraphRuntime Player L Δ)
    {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
    {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (pool : MessagePool Player (Payload Player L))
    (receipts : List (MessageId Player × Bool))
    (agreement : (values : PublicValues Γ) =
      (PublicValues.ofVEnv ideal : PublicValues Γ))
    (bindingSound : State.BindingSoundness
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt))
    (action : runtime.application.Action) (after : runtime.application.State)
    (supported : after ∈ (runtime.application.step
      ⟨.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt, pool, receipts⟩ action).support)
    (advanced : pc < after.application.phase) :
    ∃ disclose : Bool,
      State.RealizesOwnAction
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt)
        (.resolve owner bindingName disclose) after.application := by
  cases action with
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      change pc < (runtime.privateStep
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt) who command).phase at advanced
      rw [runtime.privateStep_phase] at advanced
      exact (Nat.lt_irrefl _ advanced).elim
  | submit who wire | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      simp [State.phase] at advanced
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      change application ∈ (runtime.environmentStep
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt) .tick).support at happened
      by_cases expired : runtime.deadline pc ≤ clock + 1 - enteredAt
      · rw [runtime.environmentStep_resolve_expired fresh source checks next ideal values
          bindings candidates pc clock enteredAt expired] at happened
        simp only [FinDist.mem_support_pure] at happened
        subst application
        exact ⟨false, advanceResolveFailure_realizes ideal values bindings candidates
          pc clock enteredAt (clock + 1)⟩
      · simp only [GraphRuntime.environmentStep, GraphRuntime.tick, expired,
          ↓reduceIte, FinDist.mem_support_pure] at happened
        subst application
        simp [State.phase] at advanced
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst after
      cases lookup : pool.lookup id with
      | none =>
          rw [runtime.application.includePending_missing
            (state := ⟨.running
              (.resolve outputName owner bindingName fresh source checks next)
              ideal values bindings candidates pc clock enteredAt, pool, receipts⟩)
            id lookup] at advanced
          simp [State.phase] at advanced
      | some message =>
          cases handled : runtime.handle
              (.running (.resolve outputName owner bindingName fresh source checks next)
                ideal values bindings candidates pc clock enteredAt) message with
          | none =>
              rw [runtime.application.includePending_reject
                (state := ⟨.running
                  (.resolve outputName owner bindingName fresh source checks next)
                  ideal values bindings candidates pc clock enteredAt, pool, receipts⟩)
                id message lookup handled] at advanced
              simp [State.phase] at advanced
          | some application =>
              rw [runtime.application.includePending_accept
                (state := ⟨.running
                  (.resolve outputName owner bindingName fresh source checks next)
                  ideal values bindings candidates pc clock enteredAt, pool, receipts⟩)
                id message application lookup handled]
              rcases message with ⟨messageId, wire⟩
              cases wire with
              | commitment | malformed => simp [GraphRuntime.handle] at handled
              | withhold site =>
                  simp only [GraphRuntime.handle] at handled
                  split_ifs at handled
                  cases handled
                  exact ⟨false, advanceResolveFailure_realizes ideal values bindings candidates
                    pc clock enteredAt clock⟩
              | opening site handle raw =>
                  simp only [GraphRuntime.handle] at handled
                  split_ifs at handled with valid
                  · cases typed : raw.as? (R.result payload) with
                    | none => rw [typed] at handled; contradiction
                    | some encoded =>
                        rw [typed] at handled
                        cases handled
                        simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
                        have encoded_eq : encoded = ideal.get source :=
                          (State.bound_opening_eq
                            (.resolve outputName owner bindingName fresh source checks next)
                            ideal values bindings candidates pc clock enteredAt source
                            handle raw encoded bindingSound valid.1.2 valid.2 typed).symm
                        have result_eq : acceptedProposal checks values
                            (R.valueEquiv payload encoded) =
                            acceptedResult source checks ideal true := by
                          rw [agreement]
                          have same := acceptedProposal_eq_acceptedResult
                            source checks ideal true
                          simpa only [proposedResult, if_true, ← encoded_eq] using same
                        cases proposal : acceptedProposal checks values
                            (R.valueEquiv payload encoded) with
                        | failure =>
                            rw [proposal] at result_eq
                            exact ⟨false, by
                              simpa [advanceResolve] using
                                (State.RealizesOwnAction.resolveFailure (Δ := Δ)
                                  (source := source) clock)⟩
                        | success value =>
                            rw [proposal] at result_eq
                            exact ⟨true, by
                              simpa [advanceResolve] using
                                (State.RealizesOwnAction.resolveSuccess (Δ := Δ)
                                  (source := source) value result_eq.symm clock)⟩

/-- Applying bind extraction to the step selected by `FirstPhaseChange` makes
the stopping point explicit: later actions in the same service block are not
part of this effective source action. -/
theorem FirstPhaseChange.bind_realizes
    (runtime : GraphRuntime Player L Δ) {phase : Nat}
    {start after : runtime.application.State}
    {actions : List runtime.application.Action}
    {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst}
    {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (pool : MessagePool Player (Payload Player L))
    (receipts : List (MessageId Player × Bool))
    (action : runtime.application.Action)
    (first : FirstPhaseChange runtime phase start actions
      ⟨.running (.bind name owner fresh next) ideal values bindings candidates
        pc clock enteredAt, pool, receipts⟩ action after) :
    ∃ choice : PublicationResult (L.Val payload),
      State.RealizesOwnAction
        (.running (.bind name owner fresh next) ideal values bindings candidates
          pc clock enteredAt)
        (.bind owner name payload choice) after.application := by
  apply runtime.phaseChangingStep_bind_realizes ideal values bindings candidates
    pc clock enteredAt pool receipts action after first.supported
  have atPhase := first.before_phase
  have changed := first.changed
  simp only [State.phase_running] at atPhase
  omega

/-- Resolve extraction at the first actual phase change.  Binding soundness and
public agreement are the only semantic certificates needed at this boundary. -/
theorem FirstPhaseChange.resolve_realizes
    (runtime : GraphRuntime Player L Δ) {phase : Nat}
    {start after : runtime.application.State}
    {actions : List runtime.application.Action}
    {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
    {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat)
    (pool : MessagePool Player (Payload Player L))
    (receipts : List (MessageId Player × Bool))
    (action : runtime.application.Action)
    (agreement : (values : PublicValues Γ) =
      (PublicValues.ofVEnv ideal : PublicValues Γ))
    (bindingSound : State.BindingSoundness
      (.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt))
    (first : FirstPhaseChange runtime phase start actions
      ⟨.running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates pc clock enteredAt, pool, receipts⟩ action after) :
    ∃ disclose : Bool,
      State.RealizesOwnAction
        (.running (.resolve outputName owner bindingName fresh source checks next)
          ideal values bindings candidates pc clock enteredAt)
        (.resolve owner bindingName disclose) after.application := by
  apply runtime.phaseChangingStep_resolve_realizes ideal values bindings candidates
    pc clock enteredAt pool receipts agreement bindingSound action after first.supported
  have atPhase := first.before_phase
  have changed := first.changed
  simp only [State.phase_running] at atPhase
  omega

end Vegas.GraphRuntime

/-- info: 'Vegas.GraphRuntime.FirstPhaseChange.resolve_realizes' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.FirstPhaseChange.resolve_realizes
