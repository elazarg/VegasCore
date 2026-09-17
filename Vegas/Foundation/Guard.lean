/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Foundation.ExprInterface
import Vegas.Foundation.Result

/-! # Guard code

A guard is typed boolean code over a committed subject and a schema of further
inputs. It is decided once, when the subject and every input the code reads are
published, from their published results alone: a failed subject or code-read
input discharges it (`GuardCode.accepts_subject_failure`,
`GuardCode.accepts_of_failure`); otherwise the code decides it
(`GuardCode.accepts_success`). `GuardCode.eq_accepts` shows that these cases
determine `GuardCode.accepts`.
-/

namespace Vegas

/-- Code for a failure-aware guard on `subject`. The subject heads the code's
context and is an input of every guard, including constant code. -/
structure GuardCode (L : IExpr) (subject : VarId) (payload : L.Ty) where
  schema : Ctx L.Ty
  schemaNames : (schema.map Prod.fst).Nodup
  subjectFresh : subject ∉ schema.map Prod.fst
  code : L.Expr ((subject, payload) :: schema) L.bool

namespace GuardCode

variable {L : IExpr} {subject : VarId} {payload : L.Ty}

/-- Values of the flagged inputs, or `none` if one of them failed. -/
private def values? (deps : Finset VarId) :
    (schema : Ctx L.Ty) →
      (∀ {x τ}, HasVar schema x τ → x ∈ deps → PublicationResult (L.Val τ)) →
      Option (∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)
  | [], _ => some fun h _ => nomatch h
  | (name, _) :: tail, results =>
      match values? deps tail (fun h hx => results (.there h) hx) with
      | none => none
      | some tailGet =>
          if member : name ∈ deps then
            match results .here member with
            | .failure => none
            | .success value => some fun h hx =>
                match h with
                | .here => value
                | .there h => tailGet h hx
          else
            some fun h hx =>
              match h with
              | .here => False.elim (member hx)
              | .there h => tailGet h hx

/-- A schema variable never names the subject, so the guard's dependency set
flags it exactly when the code reads it. -/
private theorem mem_exprDeps_of_schema (guard : GuardCode L subject payload)
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (flagged : x ∈ insert subject (L.exprDeps guard.code)) :
    x ∈ L.exprDeps guard.code := by
  rcases Finset.mem_insert.mp flagged with rfl | flagged
  · exact absurd h.mem_map_fst guard.subjectFresh
  · exact flagged

/-- Results for the guard's flagged context: the subject's result in front of
the code-read schema results. -/
private def contextResults (guard : GuardCode L subject payload)
    (subjectResult : PublicationResult (L.Val payload))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ)) :
    ∀ {x τ}, HasVar ((subject, payload) :: guard.schema) x τ →
      x ∈ insert subject (L.exprDeps guard.code) → PublicationResult (L.Val τ) :=
  fun h flagged =>
    match h, flagged with
    | .here, _ => subjectResult
    | .there h, flagged => results h (guard.mem_exprDeps_of_schema h flagged)

/-- Decide a guard from the published results of its subject and of the inputs
its code reads. A failed subject or code-read input discharges the guard;
otherwise the code is evaluated on the published values. -/
def accepts (guard : GuardCode L subject payload)
    (subjectResult : PublicationResult (L.Val payload))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ)) : Bool :=
  match values? (insert subject (L.exprDeps guard.code)) ((subject, payload) :: guard.schema)
      (guard.contextResults subjectResult results) with
  | none => true
  | some get => L.toBool (L.evalDeps guard.code fun _ _ h hx =>
      get h (Finset.mem_insert_of_mem hx))

private def allFlagged (deps : Finset VarId) :
    (schema : Ctx L.Ty) → (∀ {x τ}, HasVar schema x τ → Bool) → Bool
  | [], _ => true
  | (name, _) :: tail, holds =>
      (decide (name ∉ deps) || holds .here) && allFlagged deps tail (fun h => holds (.there h))

/-- Whether `holds` is true of every schema input the code reads. -/
def allReads (guard : GuardCode L subject payload)
    (holds : ∀ {x τ}, HasVar guard.schema x τ → Bool) : Bool :=
  allFlagged (L.exprDeps guard.code) guard.schema holds

private theorem allFlagged_iff (deps : Finset VarId) (schema : Ctx L.Ty)
    (holds : ∀ {x τ}, HasVar schema x τ → Bool) :
    allFlagged deps schema holds = true ↔
      ∀ {x τ} (h : HasVar schema x τ), x ∈ deps → holds h = true := by
  induction schema with
  | nil => exact ⟨fun _ => fun h _ => (nomatch h), fun _ => rfl⟩
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      simp only [allFlagged, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
        ih (fun h => holds (.there h))]
      constructor
      · rintro ⟨head, rest⟩ x σ h member
        cases h with
        | here => exact head.resolve_left (not_not.mpr member)
        | there h => exact rest h member
      · intro all
        refine ⟨?_, fun h member => all (.there h) member⟩
        by_cases member : name ∈ deps
        · exact Or.inr (all .here member)
        · exact Or.inl member

theorem allReads_iff (guard : GuardCode L subject payload)
    (holds : ∀ {x τ}, HasVar guard.schema x τ → Bool) :
    guard.allReads holds = true ↔
      ∀ {x τ} (h : HasVar guard.schema x τ), x ∈ L.exprDeps guard.code → holds h = true :=
  allFlagged_iff _ _ _

private theorem values?_congr (deps : Finset VarId) (schema : Ctx L.Ty)
    (left right : ∀ {x τ}, HasVar schema x τ → x ∈ deps → PublicationResult (L.Val τ))
    (agree : ∀ {x τ} (h : HasVar schema x τ) (hx : x ∈ deps), left h hx = right h hx) :
    values? deps schema left = values? deps schema right := by
  induction schema with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailEq := ih (fun h hx => left (.there h) hx) (fun h hx => right (.there h) hx)
        (fun h hx => agree (.there h) hx)
      by_cases member : name ∈ deps
      · have headEq := agree (.here : HasVar ((name, τ) :: tail) name τ) member
        simp only [values?, dif_pos member]
        rw [headEq, tailEq]
      · simp only [values?, dif_neg member]
        rw [tailEq]

private theorem values?_of_failure (deps : Finset VarId) (schema : Ctx L.Ty)
    (results : ∀ {x τ}, HasVar schema x τ → x ∈ deps → PublicationResult (L.Val τ))
    {x : VarId} {τ : L.Ty} (h : HasVar schema x τ) (flagged : x ∈ deps)
    (failed : results h flagged = .failure) : values? deps schema results = none := by
  induction schema with
  | nil => exact nomatch h
  | cons entry tail ih =>
      obtain ⟨name, σ⟩ := entry
      cases h with
      | here =>
          cases tailValues : values? deps tail (fun h hx => results (.there h) hx) <;>
            simp [values?, tailValues, flagged, failed]
      | there h =>
          have tailNone := ih (fun h hx => results (.there h) hx) h failed
          simp [values?, tailNone]

private theorem values?_of_success (deps : Finset VarId) (schema : Ctx L.Ty)
    (results : ∀ {x τ}, HasVar schema x τ → x ∈ deps → PublicationResult (L.Val τ))
    (values : ∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)
    (resultsEq : ∀ {x τ} (h : HasVar schema x τ) (hx : x ∈ deps),
      results h hx = .success (values h hx)) :
    values? deps schema results =
      (some values : Option (∀ {x τ}, HasVar schema x τ → x ∈ deps → L.Val τ)) := by
  induction schema with
  | nil =>
      simp only [values?]
      apply congrArg some
      funext x τ h
      nomatch h
  | cons entry tail ih =>
      obtain ⟨name, τ⟩ := entry
      have tailSome := ih (fun h hx => results (.there h) hx)
        (fun h hx => values (.there h) hx) (fun h hx => resultsEq (.there h) hx)
      by_cases member : name ∈ deps
      · have headEq := resultsEq (.here : HasVar ((name, τ) :: tail) name τ) member
        simp only [values?, tailSome, dif_pos member, headEq]
        apply congrArg some
        funext x σ h hx
        cases h <;> rfl
      · simp only [values?, tailSome, dif_neg member]
        apply congrArg some
        funext x σ h hx
        cases h with
        | here => exact absurd hx member
        | there h => rfl

/-- Only the subject and the inputs read by the code matter. -/
theorem accepts_congr (guard : GuardCode L subject payload)
    (subjectResult : PublicationResult (L.Val payload))
    (left right : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    (agree : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      left h hx = right h hx) :
    guard.accepts subjectResult left = guard.accepts subjectResult right := by
  have collected := values?_congr (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema)
    (guard.contextResults subjectResult left) (guard.contextResults subjectResult right)
    (by
      intro x τ h flagged
      cases h with
      | here => rfl
      | there h => exact agree h _)
  unfold accepts
  rw [collected]

/-- A failed subject discharges the guard. -/
@[simp] theorem accepts_subject_failure (guard : GuardCode L subject payload)
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ)) :
    guard.accepts .failure results = true := by
  have collected := values?_of_failure (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema) (guard.contextResults .failure results) .here
    (Finset.mem_insert_self subject (L.exprDeps guard.code)) rfl
  simp [accepts, collected]

/-- A failed input read by the code discharges the guard. -/
theorem accepts_of_failure (guard : GuardCode L subject payload)
    (subjectResult : PublicationResult (L.Val payload))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    {x : VarId} {τ : L.Ty} (h : HasVar guard.schema x τ)
    (read : x ∈ L.exprDeps guard.code) (failed : results h read = .failure) :
    guard.accepts subjectResult results = true := by
  have collected := values?_of_failure (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema) (guard.contextResults subjectResult results)
    (.there h) (Finset.mem_insert_of_mem read) failed
  simp [accepts, collected]

/-- Once the subject and every code-read input succeed, the code decides the
guard. `get` is any valuation of the code's reads agreeing with those values. -/
theorem accepts_success (guard : GuardCode L subject payload)
    (subjectValue : L.Val payload)
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (resultsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      results h hx = .success (get x τ (.there h) hx)) :
    guard.accepts (.success subjectValue) results = L.toBool (L.evalDeps guard.code get) := by
  have collected := values?_of_success (insert subject (L.exprDeps guard.code))
    ((subject, payload) :: guard.schema) (guard.contextResults (.success subjectValue) results)
    (fun h flagged => match h, flagged with
      | .here, _ => subjectValue
      | .there h, flagged => get _ _ (.there h) (guard.mem_exprDeps_of_schema h flagged))
    (by
      intro x τ h flagged
      cases h with
      | here => rfl
      | there h => exact resultsEq h _)
  simp only [accepts, collected]
  apply congrArg L.toBool
  apply congrArg (L.evalDeps guard.code)
  funext x σ h hx
  cases h with
  | here => exact (subjectEq hx).symm
  | there h => rfl

/-- The code's value in a full environment decides the guard when the subject and
every code-read input publish that environment's values. -/
theorem accepts_eval (guard : GuardCode L subject payload)
    (env : Env L.Val ((subject, payload) :: guard.schema))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    (resultsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      results h hx = .success (env x τ (.there h))) :
    guard.accepts (.success (env subject payload .here)) results =
      L.toBool (L.eval guard.code env) := by
  rw [guard.accepts_success (env subject payload .here) results (fun x σ h _ => env x σ h)
    (fun _ => rfl) resultsEq, L.evalDeps_eq_eval]

/-- Successful code-read inputs and a subject value determine a valuation of the
code's reads. -/
theorem exists_get (guard : GuardCode L subject payload)
    (subjectValue : L.Val payload)
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    (succeeded : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      results h hx ≠ .failure) :
    ∃ get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
        x ∈ L.exprDeps guard.code → L.Val σ,
      (∀ hx, get subject payload .here hx = subjectValue) ∧
      ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
        results h hx = .success (get x τ (.there h) hx) := by
  have present : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
      (PublicationResult.equivOption (results h hx)).isSome := by
    intro x τ h hx
    cases resultEq : results h hx with
    | failure => exact absurd resultEq (succeeded h hx)
    | success _ => rfl
  have stored : ∀ {A : Type} (result : PublicationResult A)
      (found : (PublicationResult.equivOption result).isSome),
      result = .success ((PublicationResult.equivOption result).get found) := by
    intro A result found
    cases result with
    | success value => rfl
    | failure => simp [PublicationResult.equivOption] at found
  exact ⟨fun _ _ h hx => match h, hx with
      | .here, _ => subjectValue
      | .there h, hx => (PublicationResult.equivOption (results h hx)).get (present h hx),
    fun _ => rfl, fun h hx => stored _ (present h hx)⟩

/-- The failure and success cases determine `accepts`: any decision procedure
obeying them agrees with it on every input. -/
theorem eq_accepts (guard : GuardCode L subject payload)
    (decision : PublicationResult (L.Val payload) →
      (∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
        PublicationResult (L.Val τ)) → Bool)
    (subjectFailure : ∀ results, decision .failure results = true)
    (inputFailure : ∀ subjectResult results {x τ} (h : HasVar guard.schema x τ)
      (read : x ∈ L.exprDeps guard.code), results h read = .failure →
        decision subjectResult results = true)
    (success : ∀ subjectValue results
      (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
        x ∈ L.exprDeps guard.code → L.Val σ),
      (∀ hx, get subject payload .here hx = subjectValue) →
      (∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
        results h hx = .success (get x τ (.there h) hx)) →
      decision (.success subjectValue) results = L.toBool (L.evalDeps guard.code get))
    (subjectResult : PublicationResult (L.Val payload))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ)) :
    decision subjectResult results = guard.accepts subjectResult results := by
  by_cases failedInput : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ)
      (read : x ∈ L.exprDeps guard.code), results h read = .failure
  · obtain ⟨x, τ, h, read, failed⟩ := failedInput
    rw [inputFailure subjectResult results h read failed,
      guard.accepts_of_failure subjectResult results h read failed]
  cases subjectResult with
  | failure => rw [subjectFailure, accepts_subject_failure]
  | success subjectValue =>
      obtain ⟨get, subjectEq, resultsEq⟩ := guard.exists_get subjectValue results
        (fun h read failed => failedInput ⟨_, _, h, read, failed⟩)
      rw [success subjectValue results get subjectEq resultsEq,
        guard.accepts_success subjectValue results get subjectEq resultsEq]

/-- A guard accepts when every successful result among its subject and code-read
inputs agrees with an assignment on which its code holds. -/
theorem accepts_of_compatible (guard : GuardCode L subject payload)
    (subjectResult : PublicationResult (L.Val payload))
    (results : ∀ {x τ}, HasVar guard.schema x τ → x ∈ L.exprDeps guard.code →
      PublicationResult (L.Val τ))
    (subjectValue : L.Val payload)
    (get : (x : VarId) → (σ : L.Ty) → HasVar ((subject, payload) :: guard.schema) x σ →
      x ∈ L.exprDeps guard.code → L.Val σ)
    (subjectEq : ∀ hx, get subject payload .here hx = subjectValue)
    (subjectAgrees : ∀ value, subjectResult = .success value → value = subjectValue)
    (resultsAgree : ∀ {x τ} (h : HasVar guard.schema x τ)
      (hx : x ∈ L.exprDeps guard.code) (value : L.Val τ),
        results h hx = .success value → value = get x τ (.there h) hx)
    (valid : L.toBool (L.evalDeps guard.code get) = true) :
    guard.accepts subjectResult results = true := by
  by_cases failedInput : ∃ (x : VarId) (τ : L.Ty) (h : HasVar guard.schema x τ)
      (read : x ∈ L.exprDeps guard.code), results h read = .failure
  · obtain ⟨x, τ, h, read, failed⟩ := failedInput
    exact guard.accepts_of_failure subjectResult results h read failed
  cases subjectResult with
  | failure => exact accepts_subject_failure guard results
  | success published =>
      obtain rfl := subjectAgrees published rfl
      have resultsEq : ∀ {x τ} (h : HasVar guard.schema x τ) (hx : x ∈ L.exprDeps guard.code),
          results h hx = .success (get x τ (.there h) hx) := by
        intro x τ h hx
        cases resultEq : results h hx with
        | failure => exact absurd ⟨_, _, h, hx, resultEq⟩ failedInput
        | success value => rw [resultsAgree h hx value resultEq]
      rw [guard.accepts_success published results get subjectEq resultsEq, valid]

end GuardCode

end Vegas
