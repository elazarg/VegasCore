/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageFocalDeterminism
import Vegas.Graph.MessageBindingSoundness
import Vegas.Graph.MessageInvariant
import Vegas.Graph.MessageStepLaw

/-! # Extracting an effective action of a native deviation

Native message execution contains private preparation, publication, delivery,
and rejected inclusion steps. This file relates an individual native step that
changes the graph phase at a player-owned bind or resolve cursor to the
corresponding action of the typed graph semantics.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

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

end Vegas.GraphRuntime
