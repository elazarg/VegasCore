/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Accounting

/-! # Safety of source publication execution -/

noncomputable section
namespace Vegas.SourceProgram

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem updatePrivate_get_of_name_ne {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} {name other : VarId}
    (state : State L Γ) (source : HasVar Γ name (.privateData owner payload))
    (status : Publication (L.Val payload)) {cell : CellTy Player L}
    (read : HasVar Γ other cell) (different : other ≠ name) :
    (updatePrivate state source status).get read = state.get read := by
  induction Γ generalizing other cell with
  | nil => nomatch source
  | cons entry tail ih =>
      cases source with
      | here =>
          cases read with
          | here => exact False.elim (different rfl)
          | there read => rfl
      | there source =>
          cases read with
          | here => rfl
          | there read => exact ih (fun _ _ h => state.get (.there h)) source read different

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem updatePrivate_get_source {Γ : SourceCtx Player L} {owner : Player}
    {payload : L.Ty} {name : VarId} (state : State L Γ)
    (source : HasVar Γ name (.privateData owner payload))
    (status : Publication (L.Val payload)) :
    (updatePrivate state source status).get source = ((state.get source).1, status) := by
  induction Γ with
  | nil => nomatch source
  | cons entry tail ih =>
      cases source with
      | here => rfl
      | there source => exact ih (fun _ _ h => state.get (.there h)) source

omit [DecidableEq Player] [IExpr.ResultTypes L] in
def _root_.Vegas.SourceGuardRead.References
    {Γ : SourceCtx Player L} {author : Player} {τ : L.Ty}
    (read : SourceGuardRead Γ author τ) (name : VarId) : Prop :=
  match read with
  | .publicData (x := x) _ => x = name
  | .privateData (x := x) _ => x = name
  | .publication (x := x) _ => x = name

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem _root_.Vegas.SourceGuardRead.get_updatePrivate_failed_of_name_eq
    {Γ : SourceCtx Player L} {author owner : Player} {τ payload : L.Ty}
    {name : VarId} (read : SourceGuardRead Γ author τ) (state : State L Γ)
    (source : HasVar Γ name (.privateData owner payload))
    (unique : (Γ.map Prod.fst).Nodup) (same : read.References name) :
    read.get (updatePrivate state source .failed) = .failed := by
  cases read with
  | publicData h =>
      simp only [SourceGuardRead.References] at same
      cases same
      have typeEq := HasVar.type_unique unique h source
      contradiction
  | publication h =>
      simp only [SourceGuardRead.References] at same
      cases same
      have typeEq := HasVar.type_unique unique h source
      contradiction
  | privateData h =>
      simp only [SourceGuardRead.References] at same
      cases same
      have typeEq := HasVar.type_unique unique h source
      cases typeEq
      have proofEq := HasVar.eq_of_nodup unique h source
      cases proofEq
      simp [SourceGuardRead.get]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Obligation.check_updatePrivate_failed_ne_rejected
    {Γ : SourceCtx Player L} (obligation : Obligation (Player := Player) (L := L) Γ)
    (state : State L Γ) {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.privateData owner payload))
    (unique : (Γ.map Prod.fst).Nodup) (before : obligation.check state ≠ .rejected) :
    obligation.check (updatePrivate state source .failed) ≠ .rejected := by
  by_cases subjectSame : obligation.subject = name
  · have failed :
        ((updatePrivate state source .failed).get obligation.source).2 = .failed := by
      have same : (SourceGuardRead.privateData obligation.source).References name := by
        simpa [SourceGuardRead.References] using subjectSame
      have := SourceGuardRead.get_updatePrivate_failed_of_name_eq
        (SourceGuardRead.privateData obligation.source) state source unique same
      simpa [SourceGuardRead.get] using this
    simp [Obligation.check, failed, SourceGuard.check_subject_failed]
  · by_cases affected : (∃ (x : VarId) (τ : L.Ty)
        (h : HasVar obligation.guard.schema x τ),
        x ∈ L.exprDeps obligation.guard.code ∧
          (obligation.guard.reads h).References name)
    · obtain ⟨x, τ, h, supported, same⟩ := affected
      have failed := (obligation.guard.reads h).get_updatePrivate_failed_of_name_eq
        state source unique same
      rw [Obligation.check,
        obligation.guard.check_satisfied_of_failed_read _ _ h supported failed]
      decide
    · rw [Obligation.check, SourceGuard.check_congr obligation.guard _ _ _ _
          (congrArg Prod.snd
            (updatePrivate_get_of_name_ne state source .failed obligation.source subjectSame))]
      · exact before
      · intro x τ h supported
        have different : ¬ (obligation.guard.reads h).References name := by
          intro same
          exact affected ⟨x, τ, h, supported, same⟩
        cases readEq : obligation.guard.reads h with
        | publicData read =>
            simp only [SourceGuardRead.References, readEq] at different
            exact congrArg Publication.value
              (updatePrivate_get_of_name_ne state source .failed read different)
        | privateData read =>
            simp only [SourceGuardRead.References, readEq] at different
            exact congrArg Prod.snd
              (updatePrivate_get_of_name_ne state source .failed read different)
        | publication read =>
            simp only [SourceGuardRead.References, readEq] at different
            rw [SourceGuardRead.get, SourceGuardRead.get]
            congr 1
            exact updatePrivate_get_of_name_ne state source .failed read different

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem Registry.ok_updatePrivate_failed {Γ : SourceCtx Player L}
    (registry : Registry (Player := Player) (L := L) Γ) (state : State L Γ)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar Γ name (.privateData owner payload))
    (unique : (Γ.map Prod.fst).Nodup) (before : registry.ok state = true) :
    registry.ok (updatePrivate state source .failed) = true := by
  induction registry with
  | nil => rfl
  | cons head tail ih =>
      simp only [Registry.ok, List.all_cons, Bool.and_eq_true] at before ⊢
      have beforeHead : head.check state ≠ .rejected := by simpa using before.1
      have afterHead :=
        head.check_updatePrivate_failed_ne_rejected state source unique beforeHead
      exact ⟨by simpa using afterHead, ih before.2⟩

/-- The guard registry obtained after following the remaining source syntax.
It retains every original typed guard and its subject provenance. -/
def finalRegistry : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ →
      Registry (terminalCtx program)
  | _, _, .ret _, registry => registry
  | _, _, .sample _ _ _ next, registry => finalRegistry next registry.weaken
  | _, _, .commit name owner _ guard next, registry =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      finalRegistry next (obligation :: registry.weaken)
  | _, _, .reveal _ _ _ _ _ _ next, registry => finalRegistry next registry.weaken

/-- Every reachable state preserves consistency of every dynamically
registered guard. -/
theorem runWith_registry_ok {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (state : State L Γ)
      (registry : Registry Γ) (history : History Player L),
      (Γ.map Prod.fst).Nodup → registry.ok state = true →
      ∀ outcome ∈ (runWith program profile state registry history).support,
        (finalRegistry program registry).ok outcome = true := by
  induction program with
  | ret payoffs =>
      intro profile state registry history unique consistent outcome supported
      have same := FinDist.mem_support_pure.mp supported
      simpa [same, finalRegistry] using consistent
  | sample name fresh law next ih =>
      intro profile state registry history unique consistent outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      exact ih (afterSample profile) (Env.cons value state) registry.weaken history
        (by simp [fresh, unique]) (by simpa using consistent) outcome supported
  | commit name owner fresh guard next ih =>
      intro profile state registry history unique consistent outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      let nextState := Env.cons (x := name) (τ := CellTy.privateData owner _)
        (value, Publication.pending) state
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      apply ih (afterCommit profile) nextState (obligation :: registry.weaken) _
        (by simp [fresh, unique]) _ outcome supported
      have newOk : (obligation.check nextState != .rejected) = true := by
        apply bne_iff_ne.mpr
        simpa [obligation, nextState, Obligation.check] using
          guard.check_subject_pending_ne_rejected state
      have oldOk : (registry.weaken).ok nextState = true := by
        simpa [nextState] using consistent
      rw [show Registry.ok (obligation :: registry.weaken) nextState =
          ((obligation.check nextState != .rejected) &&
            (registry.weaken).ok nextState) from rfl,
        newOk, oldOk]
      rfl
  | reveal published owner name fresh source unresolved next ih =>
      intro profile state registry history unique consistent outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨disclose, _, supported⟩ := supported
      let proposedResult := boundResult state source disclose
      let proposed := resultPublication proposedResult
      let tentative := updatePrivate state source proposed
      let acceptedResult :=
        if registry.ok tentative then proposedResult else PublicationResult.failure
      let accepted := resultPublication acceptedResult
      let resolved := updatePrivate state source accepted
      apply ih (afterReveal profile) (Env.cons acceptedResult resolved) registry.weaken _
        (by simp [fresh, unique]) _ outcome supported
      rw [Registry.ok_weaken]
      by_cases acceptedTentative : registry.ok tentative = true
      · have resultEq : acceptedResult = proposedResult := by
          simp [acceptedResult, acceptedTentative]
        simpa [resolved, accepted, tentative, resultEq] using acceptedTentative
      · have resultEq : acceptedResult = .failure := by
          simp [acceptedResult, acceptedTentative]
        simpa [resolved, accepted, resultEq, resultPublication] using
          registry.ok_updatePrivate_failed state source unique consistent

/-- At a terminal state no retained guard is rejected. Resolution accounting
strengthens this in `Initial.terminal_guards_hold`. -/
theorem Initial.terminal_registry_consistent
    (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program)
    (outcome : State L initial.program.terminalCtx)
    (supported : outcome ∈ (initial.run profile).support) :
    (finalRegistry initial.program []).ok outcome = true := by
  exact runWith_registry_ok initial.program profile initial.state [] (fun _ => [])
    initial.namesNodup rfl outcome supported

/-- Complete execution decides every retained guard by its code: either the
subject or an input read by the code failed to publish, or all of them were
published and the code holds on the published values. -/
theorem Initial.terminal_guards_hold
    (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program)
    (outcome : State L initial.program.terminalCtx)
    (supported : outcome ∈ (initial.run profile).support)
    (obligation : Obligation initial.program.terminalCtx)
    (member : obligation ∈ finalRegistry initial.program []) :
    ((outcome.get obligation.source).2 = .failed ∨
      ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
        x ∈ L.exprDeps obligation.guard.code ∧
          (obligation.guard.reads h).get outcome = .failed) ∨
    ∃ (subjectValue : L.Val obligation.payload)
      (get : (x : VarId) → (σ : L.Ty) →
        HasVar ((obligation.subject, obligation.payload) :: obligation.guard.schema) x σ →
          x ∈ L.exprDeps obligation.guard.code → L.Val σ),
      (outcome.get obligation.source).2 = .value subjectValue ∧
      (∀ hx, get obligation.subject obligation.payload .here hx = subjectValue) ∧
      (∀ {x τ} (h : HasVar obligation.guard.schema x τ)
        (hx : x ∈ L.exprDeps obligation.guard.code),
          (obligation.guard.reads h).get outcome = .value (get x τ (.there h) hx)) ∧
      L.toBool (L.evalDeps obligation.guard.code get) = true := by
  have consistent := initial.terminal_registry_consistent profile outcome supported
  have notRejected : obligation.check outcome ≠ .rejected := by
    have checked := (List.all_eq_true.mp consistent) obligation member
    simpa [bne_iff_ne] using checked
  have subjectResolved : (outcome.get obligation.source).2 ≠ .pending :=
    initial.terminal_resolved profile outcome supported obligation.source
  have supportResolved : ∀ {x τ} (h : HasVar obligation.guard.schema x τ),
      x ∈ L.exprDeps obligation.guard.code →
        (obligation.guard.reads h).get outcome ≠ .pending := by
    intro x τ h reads
    cases readEq : obligation.guard.reads h with
    | publicData source => simp [SourceGuardRead.get]
    | privateData source =>
        simpa [SourceGuardRead.get] using
          initial.terminal_resolved profile outcome supported source
    | publication source =>
        cases valueEq : outcome.get source <;>
          simp [SourceGuardRead.get, valueEq]
  by_cases supportFailure : ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
      x ∈ L.exprDeps obligation.guard.code ∧ (obligation.guard.reads h).get outcome = .failed
  · exact Or.inl (Or.inr supportFailure)
  cases subjectEq : (outcome.get obligation.source).2 with
  | failed => exact Or.inl (Or.inl rfl)
  | pending => exact absurd subjectEq subjectResolved
  | value subjectValue =>
      obtain ⟨get, getSubject, readsEq⟩ :=
        obligation.guard.toDeferredGuardCode.exists_get subjectValue
          (fun h => (obligation.guard.reads h).get outcome) supportResolved
          (fun h flagged failed => supportFailure ⟨_, _, h, flagged, failed⟩)
      refine Or.inr ⟨subjectValue, get, rfl, getSubject, readsEq, ?_⟩
      have verdict := obligation.guard.check_values subjectValue outcome get getSubject readsEq
      simp only [Obligation.check, subjectEq] at notRejected
      rw [verdict] at notRejected
      by_contra invalid
      exact notRejected (if_neg invalid)

end Vegas.SourceProgram
