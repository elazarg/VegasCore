/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.GuardedPublication
import Vegas.Foundation.ExprInterface

/-! # Retained deferred-guard code

Deferred guards retain ordinary typed expression code and consume typed
publication statuses through an adapter supplied by their execution context.
The subject heads the guard's context and is a required publication of every
guard, including for constant code.
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

@[simp] theorem check_subject_failed (guard : DeferredGuardCode L subject payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    guard.check .failed reads = .satisfied := by
  have collected := collectReads_failed_of_failed_read
    (insert subject (L.exprDeps guard.code)) ((subject, payload) :: guard.schema)
    (guard.contextReads .failed reads) .here
    (Finset.mem_insert_self subject (L.exprDeps guard.code)) rfl
  simp [check, collected]

theorem check_subject_pending_ne_rejected (guard : DeferredGuardCode L subject payload)
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ)) :
    guard.check .pending reads ≠ .rejected := by
  rcases collectReads_unready_of_pending_read
    (insert subject (L.exprDeps guard.code)) ((subject, payload) :: guard.schema)
    (guard.contextReads .pending reads) .here
    (Finset.mem_insert_self subject (L.exprDeps guard.code)) rfl with
    collected | collected <;> simp [check, collected]

private theorem collectReads_terminal (deps : Finset VarId) (schema : Ctx L.Ty)
    (reads : ∀ {x τ}, HasVar schema x τ → Publication (L.Val τ))
    (terminal : ∀ {x τ} (h : HasVar schema x τ), x ∈ deps → reads h ≠ .pending) :
    collectReads deps schema reads = .failed ∨
      ∃ get, collectReads deps schema reads = .ready get := by
  induction schema with
  | nil =>
      let get : ∀ {x τ}, HasVar ([] : Ctx L.Ty) x τ → x ∈ deps → L.Val τ :=
        fun h _ => nomatch h
      exact Or.inr ⟨get, rfl⟩
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailTerminal := fun {x σ} (h : HasVar tail x σ) hx => terminal (.there h) hx
      rcases ih (fun h => reads (.there h)) tailTerminal with tailFailed | ⟨tailGet, tailReady⟩
      · exact Or.inl (by
          by_cases member : name ∈ deps
          · cases hhead : reads (.here : HasVar ((name, τ) :: tail) name τ) <;>
              simp [collectReads, member, hhead, tailFailed]
          · simp [collectReads, member, tailFailed])
      · by_cases member : name ∈ deps
        · have headTerminal := terminal (.here : HasVar ((name, τ) :: tail) name τ) member
          cases hhead : reads (.here : HasVar ((name, τ) :: tail) name τ) with
          | pending => exact False.elim (headTerminal hhead)
          | failed => exact Or.inl (by simp [collectReads, member, hhead])
          | value value =>
              let get : ∀ {x σ}, HasVar ((name, τ) :: tail) x σ → x ∈ deps → L.Val σ :=
                fun h hx => match h with | .here => value | .there h => tailGet h hx
              refine Or.inr ⟨get, ?_⟩
              simp only [collectReads, dif_pos member, hhead, tailReady]
              apply congrArg (ReadOutcome.ready (L := L))
              funext x σ h hx
              cases h <;> rfl
        · let get : ∀ {x σ}, HasVar ((name, τ) :: tail) x σ → x ∈ deps → L.Val σ :=
              fun h hx => match h with
                | .here => False.elim (member hx)
                | .there h => tailGet h hx
          refine Or.inr ⟨get, ?_⟩
          simp only [collectReads, dif_neg member, tailReady]
          apply congrArg (ReadOutcome.ready (L := L))
          funext x σ h hx
          cases h <;> rfl

theorem check_ne_pending_of_support_resolved (guard : DeferredGuardCode L subject payload)
    (candidate : Publication (L.Val payload))
    (reads : ∀ {x τ}, HasVar guard.schema x τ → Publication (L.Val τ))
    (subjectResolved : candidate ≠ .pending)
    (supportResolved : ∀ {x τ} (h : HasVar guard.schema x τ),
      x ∈ L.exprDeps guard.code → reads h ≠ .pending) :
    guard.check candidate reads ≠ .pending := by
  have terminal : ∀ {x : VarId} {τ : L.Ty}
      (h : HasVar ((subject, payload) :: guard.schema) x τ),
      x ∈ insert subject (L.exprDeps guard.code) →
        guard.contextReads candidate reads h ≠ .pending := by
    intro x τ h flagged
    cases h with
    | here => exact subjectResolved
    | there h => exact supportResolved h (guard.mem_exprDeps_of_schema h flagged)
  rcases collectReads_terminal (insert subject (L.exprDeps guard.code))
      ((subject, payload) :: guard.schema) (guard.contextReads candidate reads) terminal with
    failed | ⟨get, ready⟩
  · simp [check, failed]
  · simp only [check, ready]
    split <;> decide

end DeferredGuardCode

end Vegas
