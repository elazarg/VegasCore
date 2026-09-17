/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.GuardedPublication
import Vegas.Foundation.ExprInterface

/-! # Retained deferred-guard code

Deferred guards retain ordinary typed expression code and consume typed
publication statuses through an adapter supplied by their execution context.
The subject heads the guard's context and is a required publication of every
guard, including for constant code.

The verdict is characterized case by case: a failed subject or code-read input
satisfies the guard (`DeferredGuardCode.check_subject_failed`,
`DeferredGuardCode.check_satisfied_of_failed_read`); otherwise a pending one
keeps it pending (`DeferredGuardCode.check_pending`); once all of them carry
values, the retained code decides it (`DeferredGuardCode.check_values`).
`DeferredGuardCode.eq_check` shows that these cases determine `check`.
-/

namespace Vegas

open Interaction

/-- Source-independent code for a failure-aware deferred guard. -/
structure DeferredGuardCode (L : IExpr) (subject : VarId) (payload : L.Ty) where
  schema : Ctx L.Ty
  schemaNames : (schema.map Prod.fst).Nodup
  subjectFresh : subject ∉ schema.map Prod.fst
  code : L.Expr ((subject, payload) :: schema) L.bool

namespace DeferredGuardCode

variable {L : IExpr} {subject : VarId} {payload : L.Ty}

private inductive ReadOutcome (L : IExpr) (schema : Ctx L.Ty) (deps : Finset VarId) where
  | failed
  | pending
  | ready (get : ∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)

private def collectReads (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {x τ}, HasVar schema x τ → Publication (L.Val τ)) →
      ReadOutcome L schema deps
  | [], _ => .ready fun h _ => nomatch h
  | (name, τ) :: tail, reads =>
      let rest := collectReads deps tail (fun h => reads (.there h))
      if member : name ∈ deps then
        match reads .here with
        | .failed => .failed
        | .pending => match rest with | .failed => .failed | _ => .pending
        | .value value =>
            match rest with
            | .failed => .failed
            | .pending => .pending
            | .ready tailGet => .ready fun h _ =>
                match h with
                | .here => value
                | .there h => tailGet h (by simpa using ‹_›)
      else
        match rest with
        | .failed => .failed
        | .pending => .pending
        | .ready tailGet => .ready fun h hx =>
            match h with
            | .here => False.elim (member hx)
            | .there h => tailGet h hx

/-- Publication statuses for the guard's whole context: the subject's own
candidate publication in front of the retained schema reads. -/
private def contextReads (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    ∀ {x τ}, HasVar ((subject, payload) :: guard.schema) x τ →
      Publication (L.Val τ) :=
  fun h =>
    match h with
    | .here => candidate
    | .there h => reads h

/-- Evaluate retained guard code from publication statuses. The subject is a
dependency of every guard, including constant code, so it is walked alongside
the schema: failure has precedence over pending, and ordinary code runs only
once every dependency carries a value. -/
def check (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    PublicationGuard.Verdict :=
  match collectReads (insert subject (L.exprDeps guard.code))
      ((subject, payload) :: guard.schema)
      (guard.contextReads candidate reads) with
  | .failed => .satisfied
  | .pending => .pending
  | .ready get =>
      let ordinary := L.evalDeps guard.code fun _ _ h hx =>
        get h (Finset.mem_insert_of_mem hx)
      if L.toBool ordinary then .satisfied else .rejected

/-- A schema variable never names the subject, so the guard's dependency set
flags it exactly when the retained code reads it. -/
private theorem mem_exprDeps_of_schema (guard : DeferredGuardCode L subject payload)
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (flagged : x ∈ insert subject (L.exprDeps guard.code)) :
    x ∈ L.exprDeps guard.code := by
  rcases Finset.mem_insert.mp flagged with rfl | flagged
  · exact absurd h.mem_map_fst guard.subjectFresh
  · exact flagged

private theorem collectReads_congr (deps : Finset VarId) (schema : Ctx L.Ty)
    (left right : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    (agree : ∀ {x τ} (h : HasVar schema x τ), x ∈ deps → left h = right h) :
    collectReads deps schema left = collectReads deps schema right := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailEq := ih (fun h => left (.there h)) (fun h => right (.there h))
        (fun h hx => agree (.there h) hx)
      by_cases member : name ∈ deps
      · have headEq := agree (.here : HasVar ((name, τ) :: tail) name τ) member
        simp only [collectReads, dif_pos member]
        rw [headEq, tailEq]
      · simp only [collectReads, dif_neg member]
        rw [tailEq]

private theorem collectReads_failed_of_failed_read (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    {x : VarId} {τ : L.Ty} (h : HasVar schema x τ) (supported : x ∈ deps)
    (failed : reads h = .failed) : collectReads deps schema reads = .failed := by
  induction schema with
  | nil => exact nomatch h
  | cons entry tail ih =>
      obtain ⟨name, σ⟩ := entry
      cases h with
      | here => simp [collectReads, supported, failed]
      | there h =>
          have tailFailed := ih (fun h => reads (.there h)) h failed
          by_cases member : name ∈ deps
          · cases hhead : reads (.here : HasVar ((name, σ) :: tail) name σ) <;>
              simp [collectReads, member, hhead, tailFailed]
          · simp [collectReads, member, tailFailed]

private theorem collectReads_unready_of_pending_read (deps : Finset VarId)
    (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    {x : VarId} {τ : L.Ty} (h : HasVar schema x τ) (supported : x ∈ deps)
    (pending : reads h = .pending) :
    collectReads deps schema reads = .failed ∨
      collectReads deps schema reads = .pending := by
  induction schema with
  | nil => exact nomatch h
  | cons entry tail ih =>
      obtain ⟨name, σ⟩ := entry
      cases h with
      | here =>
          cases tailOutcome : collectReads deps tail (fun h => reads (.there h)) <;>
            simp [collectReads, supported, pending, tailOutcome]
      | there h =>
          have tailUnready := ih (fun h => reads (.there h)) h pending
          by_cases member : name ∈ deps
          · cases hhead : reads (.here : HasVar ((name, σ) :: tail) name σ) <;>
              rcases tailUnready with hrest | hrest <;>
              simp [collectReads, member, hhead, hrest]
          · rcases tailUnready with hrest | hrest <;>
              simp [collectReads, member, hrest]

private theorem collectReads_ne_failed (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    (noFailure : ∀ {x τ} (h : HasVar schema x τ), x ∈ deps → reads h ≠ .failed) :
    collectReads deps schema reads ≠ .failed := by
  induction schema with
  | nil => simp [collectReads]
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailNotFailed :=
        ih (fun h => reads (.there h)) (fun h hx => noFailure (.there h) hx)
      by_cases member : name ∈ deps
      · have headNotFailed := noFailure (.here : HasVar ((name, τ) :: tail) name τ) member
        cases hhead : reads (.here : HasVar ((name, τ) :: tail) name τ) with
        | failed => exact absurd hhead headNotFailed
        | pending =>
            cases hrest : collectReads deps tail (fun h => reads (.there h)) with
            | failed => exact absurd hrest tailNotFailed
            | pending => simp [collectReads, member, hhead, hrest]
            | ready get => simp [collectReads, member, hhead, hrest]
        | value value =>
            cases hrest : collectReads deps tail (fun h => reads (.there h)) with
            | failed => exact absurd hrest tailNotFailed
            | pending => simp [collectReads, member, hhead, hrest]
            | ready get => simp [collectReads, member, hhead, hrest]
      · cases hrest : collectReads deps tail (fun h => reads (.there h)) with
        | failed => exact absurd hrest tailNotFailed
        | pending => simp [collectReads, member, hrest]
        | ready get => simp [collectReads, member, hrest]

private theorem collectReads_values (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    (values : ∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)
    (readsEq : ∀ {x τ} (h : HasVar schema x τ) (hx : x ∈ deps),
      reads h = .value (values h hx)) :
    collectReads deps schema reads = .ready values := by
  induction schema with
  | nil =>
      simp only [collectReads]
      apply congrArg (ReadOutcome.ready (L := L))
      funext x τ h
      nomatch h
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailReady := ih (fun h => reads (.there h)) (fun h hx => values (.there h) hx)
        (fun h hx => readsEq (.there h) hx)
      by_cases member : name ∈ deps
      · have hhead := readsEq (.here : HasVar ((name, τ) :: tail) name τ) member
        simp only [collectReads, dif_pos member, hhead, tailReady]
        apply congrArg (ReadOutcome.ready (L := L))
        funext x σ h hx
        cases h <;> rfl
      · simp only [collectReads, dif_neg member, tailReady]
        apply congrArg (ReadOutcome.ready (L := L))
        funext x σ h hx
        cases h with
        | here => exact absurd hx member
        | there h => rfl

theorem check_congr (guard : DeferredGuardCode L subject payload)
    (leftCandidate rightCandidate : Publication (L.Val payload))
    (left right : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (candidateEq : leftCandidate = rightCandidate)
    (supportEq : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → left h = right h) :
    guard.check leftCandidate left = guard.check rightCandidate right := by
  subst rightCandidate
  have collected := collectReads_congr (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema)
    (guard.contextReads leftCandidate left) (guard.contextReads leftCandidate right)
    (by
      intro x τ h flagged
      cases h with
      | here => rfl
      | there h => exact supportEq h (guard.mem_exprDeps_of_schema h flagged))
  unfold check
  rw [collected]

/-- A failed input read by the retained code satisfies the guard. -/
theorem check_satisfied_of_failed_read (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (supported : x ∈ L.exprDeps guard.code) (failed : reads h = .failed) :
    guard.check candidate reads = .satisfied := by
  have collected := collectReads_failed_of_failed_read
    (insert subject (L.exprDeps guard.code)) ((subject, payload) :: guard.schema)
    (guard.contextReads candidate reads) (.there h)
    (Finset.mem_insert_of_mem supported) failed
  simp [check, collected]

/-- A failed subject satisfies the guard. -/
@[simp] theorem check_subject_failed (guard : DeferredGuardCode L subject payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    guard.check .failed reads = .satisfied := by
  have collected := collectReads_failed_of_failed_read
    (insert subject (L.exprDeps guard.code)) ((subject, payload) :: guard.schema)
    (guard.contextReads .failed reads) .here
    (Finset.mem_insert_self subject (L.exprDeps guard.code)) rfl
  simp [check, collected]

/-- Without a failure, a pending subject or code-read input keeps the guard
pending. -/
theorem check_pending (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (subjectNotFailed : candidate ≠ .failed)
    (supportNotFailed : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .failed)
    (waiting : candidate = .pending ∨
      ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
        x ∈ L.exprDeps guard.code ∧ reads h = .pending) :
    guard.check candidate reads = .pending := by
  have notFailed := collectReads_ne_failed (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema) (guard.contextReads candidate reads) (by
      intro x τ h flagged
      cases h with
      | here => exact subjectNotFailed
      | there h => exact supportNotFailed h (guard.mem_exprDeps_of_schema h flagged))
  have unready := match waiting with
    | .inl pending =>
        collectReads_unready_of_pending_read (insert subject (L.exprDeps guard.code))
          ((subject, payload) :: guard.schema) (guard.contextReads candidate reads) .here
          (Finset.mem_insert_self subject (L.exprDeps guard.code)) pending
    | .inr ⟨_, _, h, flagged, pending⟩ =>
        collectReads_unready_of_pending_read (insert subject (L.exprDeps guard.code))
          ((subject, payload) :: guard.schema) (guard.contextReads candidate reads) (.there h)
          (Finset.mem_insert_of_mem flagged) pending
  rcases unready with failed | pending
  · exact absurd failed notFailed
  · simp [check, pending]

/-- Once the subject and every code-read input carry values, the retained code
decides the guard. `get` is any valuation of the code's reads agreeing with
those values. -/
theorem check_values (guard : DeferredGuardCode L subject payload)
    (subjectValue : L.Val payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (readsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      reads h = .value (get x τ (.there h) hx)) :
    guard.check (.value subjectValue) reads =
      if L.toBool (L.evalDeps guard.code get) then .satisfied else .rejected := by
  have collected := collectReads_values (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema) (guard.contextReads (.value subjectValue) reads)
    (fun h flagged => match h, flagged with
      | .here, _ => subjectValue
      | .there h, flagged => get _ _ (.there h) (guard.mem_exprDeps_of_schema h flagged))
    (by
      intro x τ h flagged
      cases h with
      | here => rfl
      | there h => exact readsEq h _)
  simp only [check, collected]
  apply congrArg fun ordinary =>
    if L.toBool ordinary then PublicationGuard.Verdict.satisfied else .rejected
  apply congrArg (L.evalDeps guard.code)
  funext x σ h hx
  cases h with
  | here => exact (subjectEq hx).symm
  | there h => rfl

/-- The retained code's value in a full environment decides the guard when the
subject and every code-read input publish that environment's values. -/
theorem check_eval (guard : DeferredGuardCode L subject payload)
    (env : Env L.Val ((subject, payload) :: guard.schema))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (readsEq : ∀ {x τ} (h : HasVar guard.schema x τ), x ∈ L.exprDeps guard.code →
      reads h = .value (env x τ (.there h))) :
    guard.check (.value (env subject payload .here)) reads =
      if L.toBool (L.eval guard.code env) then .satisfied else .rejected := by
  rw [guard.check_values (env subject payload .here) reads (fun x σ h _ => env x σ h)
    (fun _ => rfl) readsEq, L.evalDeps_eq_eval]

/-- Resolved, non-failed code-read inputs and a subject value determine a
valuation of the retained code's reads. -/
theorem exists_get (guard : DeferredGuardCode L subject payload)
    (subjectValue : L.Val payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (supportNotPending : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .pending)
    (supportNotFailed : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .failed) :
    ∃ get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
        x ∈ L.exprDeps guard.code → L.Val σ,
      (∀ hx, get subject payload .here hx = subjectValue) ∧
      ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
        reads h = .value (get x τ (.there h) hx) := by
  have present : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → (reads h).hasValue = true := by
    intro x τ h hx
    cases readEq : reads h with
    | pending => exact absurd readEq (supportNotPending h hx)
    | failed => exact absurd readEq (supportNotFailed h hx)
    | value _ => rfl
  have stored : ∀ {A : Type} (publication : Publication A) (found : publication.hasValue = true),
      publication = .value (publication.get found) := by
    intro A publication found
    cases publication with
    | value data => rfl
    | pending => simp [Publication.hasValue] at found
    | failed => simp [Publication.hasValue] at found
  exact ⟨fun _ _ h hx => match h, hx with
      | .here, _ => subjectValue
      | .there h, hx => (reads h).get (present h hx),
    fun _ => rfl, fun h hx => stored _ (present h hx)⟩

/-- The verdict cases determine `check`: any verdict function obeying them
agrees with it on every input. -/
theorem eq_check (guard : DeferredGuardCode L subject payload)
    (verdict : Publication (L.Val payload) →
      (∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) →
        PublicationGuard.Verdict)
    (subjectFailed : ∀ reads, verdict .failed reads = .satisfied)
    (supportFailed : ∀ candidate reads {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h = .failed → verdict candidate reads = .satisfied)
    (pending : ∀ candidate reads, candidate ≠ .failed →
      (∀ {x τ} (h : HasVar guard.schema x τ),
        x ∈ L.exprDeps guard.code → reads h ≠ .failed) →
      (candidate = .pending ∨
        ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
          x ∈ L.exprDeps guard.code ∧ reads h = .pending) →
      verdict candidate reads = .pending)
    (evaluated : ∀ subjectValue reads
      (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
        x ∈ L.exprDeps guard.code → L.Val σ),
      (∀ hx, get subject payload .here hx = subjectValue) →
      (∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
        reads h = .value (get x τ (.there h) hx)) →
      verdict (.value subjectValue) reads =
        if L.toBool (L.evalDeps guard.code get) then .satisfied else .rejected)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    verdict candidate reads = guard.check candidate reads := by
  by_cases supportFailure : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code ∧ reads h = .failed
  · obtain ⟨x, τ, h, flagged, failed⟩ := supportFailure
    rw [supportFailed candidate reads h flagged failed,
      guard.check_satisfied_of_failed_read candidate reads h flagged failed]
  have supportNotFailed : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .failed :=
    fun h flagged failed => supportFailure ⟨_, _, h, flagged, failed⟩
  cases candidate with
  | failed => rw [subjectFailed, check_subject_failed]
  | pending =>
      rw [pending .pending reads (by simp) supportNotFailed (Or.inl rfl),
        guard.check_pending .pending reads (by simp) supportNotFailed (Or.inl rfl)]
  | value subjectValue =>
      by_cases supportPending : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
          x ∈ L.exprDeps guard.code ∧ reads h = .pending
      · rw [pending _ reads (by simp) supportNotFailed (Or.inr supportPending),
          guard.check_pending _ reads (by simp) supportNotFailed (Or.inr supportPending)]
      · obtain ⟨get, subjectEq, readsEq⟩ := guard.exists_get subjectValue reads
          (fun h flagged waiting => supportPending ⟨_, _, h, flagged, waiting⟩)
          supportNotFailed
        rw [evaluated subjectValue reads get subjectEq readsEq,
          guard.check_values subjectValue reads get subjectEq readsEq]

theorem check_subject_pending_ne_rejected (guard : DeferredGuardCode L subject payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    guard.check .pending reads ≠ .rejected := by
  by_cases supportFailure : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code ∧ reads h = .failed
  · obtain ⟨x, τ, h, flagged, failed⟩ := supportFailure
    rw [guard.check_satisfied_of_failed_read .pending reads h flagged failed]
    decide
  · rw [guard.check_pending .pending reads (by simp)
      (fun h flagged failed => supportFailure ⟨_, _, h, flagged, failed⟩) (Or.inl rfl)]
    decide

theorem check_ne_pending_of_support_resolved (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (subjectResolved : candidate ≠ .pending)
    (supportResolved : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .pending) :
    guard.check candidate reads ≠ .pending := by
  by_cases supportFailure : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code ∧ reads h = .failed
  · obtain ⟨x, τ, h, flagged, failed⟩ := supportFailure
    rw [guard.check_satisfied_of_failed_read candidate reads h flagged failed]
    decide
  cases candidate with
  | pending => exact absurd rfl subjectResolved
  | failed => rw [check_subject_failed]; decide
  | value subjectValue =>
      obtain ⟨get, subjectEq, readsEq⟩ := guard.exists_get subjectValue reads supportResolved
        (fun h flagged failed => supportFailure ⟨_, _, h, flagged, failed⟩)
      rw [guard.check_values subjectValue reads get subjectEq readsEq]
      split <;> decide

/-- A guard cannot reject while every published value of its subject and code-read
inputs agrees with an assignment on which the retained code holds. Pending and
failed inputs are unconstrained. -/
theorem check_compatible (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (subjectValue : L.Val payload)
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (subjectAgrees : ∀ value, candidate = .value value → value = subjectValue)
    (readsAgree : ∀ {x τ} (h : HasVar guard.schema x τ)
      (hx : x ∈ L.exprDeps guard.code) (value : L.Val τ),
        reads h = .value value → value = get x τ (.there h) hx)
    (valid : L.toBool (L.evalDeps guard.code get) = true) :
    guard.check candidate reads ≠ .rejected := by
  by_cases supportFailure : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code ∧ reads h = .failed
  · obtain ⟨x, τ, h, flagged, failed⟩ := supportFailure
    rw [guard.check_satisfied_of_failed_read candidate reads h flagged failed]
    decide
  have supportNotFailed : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .failed :=
    fun h flagged failed => supportFailure ⟨_, _, h, flagged, failed⟩
  cases candidate with
  | failed => rw [check_subject_failed]; decide
  | pending =>
      rw [guard.check_pending .pending reads (by simp) supportNotFailed (Or.inl rfl)]
      decide
  | value published =>
      obtain rfl := subjectAgrees published rfl
      by_cases supportPending : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ),
          x ∈ L.exprDeps guard.code ∧ reads h = .pending
      · rw [guard.check_pending _ reads (by simp) supportNotFailed (Or.inr supportPending)]
        decide
      have readsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
          reads h = .value (get x τ (.there h) hx) := by
        intro x τ h hx
        cases readEq : reads h with
        | pending => exact absurd ⟨_, _, h, hx, readEq⟩ supportPending
        | failed => exact absurd readEq (supportNotFailed h hx)
        | value value => rw [readsAgree h hx value readEq]
      rw [guard.check_values published reads get subjectEq readsEq, if_pos valid]
      decide

end DeferredGuardCode

end Vegas
