/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Accounting

/-! # Safety of source publication execution

Every retained obligation whose inputs are all published accepts the published
state: a reveal fails exactly when an obligation it completes rejects, and that
failure then discharges the obligation. At termination every input is published
(`SourceProgram.Initial.revealed`), so every retained guard has a failed input or holds on the
published values (`SourceProgram.Initial.terminal_guards_hold`).
-/

noncomputable section
namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A reveal leaves every already published obligation's decision unchanged. -/
theorem Obligation.accepts_reveal_of_revealed {Γ : SourceCtx Player L} {O : Finset VarId}
    (obligation : Obligation (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.privateData owner payload))
    (accounted : Accounted revelations O) (unresolved : name ∈ O)
    (revealed : obligation.revealed revelations = true)
    (head : PublicationResult (L.Val payload)) (state : State L Γ) :
    (obligation.weaken (x := published)).accepts
        (revelations.reveal (published := published) source)
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload) head state) =
      obligation.accepts revelations state := by
  have unchanged : ∀ {readOwner : Player} {readPayload : L.Ty} {readName : VarId}
      (h : HasVar Γ readName (.privateData readOwner readPayload)),
      (revelations h).isRevealed = true →
        revelations.reveal (published := published) source (.there h) = (revelations h).weaken := by
    intro readOwner readPayload readName h readRevealed
    exact Revelations.reveal_of_ne revelations source h
      (fun same => (accounted h).mp readRevealed (same ▸ unresolved))
  simp only [Obligation.revealed, Bool.and_eq_true, SourceGuard.readsRevealed] at revealed
  obtain ⟨subjectRevealed, readsRevealed⟩ := revealed
  simp only [Obligation.accepts, Obligation.weaken, SourceGuard.accepts, SourceGuard.weaken,
    unchanged obligation.source subjectRevealed, Revelation.result_weaken]
  apply GuardCode.accepts_congr
  intro x τ h read
  have readRevealed := (GuardCode.allReads_iff _ _).mp readsRevealed h read
  cases readEq : obligation.guard.reads h with
  | publicData cell => simp [SourceGuardRead.weaken, SourceGuardRead.result]
  | publication cell => simp [SourceGuardRead.weaken, SourceGuardRead.result]
  | privateData cell =>
      rw [readEq] at readRevealed
      simp [SourceGuardRead.weaken, SourceGuardRead.result, unchanged cell readRevealed]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- An obligation completed by a failed publication accepts it: the failed
publication is one of its inputs. -/
theorem Obligation.accepts_reveal_failure {Γ : SourceCtx Player L}
    (obligation : Obligation (Player := Player) (L := L) Γ) (revelations : Revelations Γ)
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.privateData owner payload)) (unique : (Γ.map Prod.fst).Nodup)
    (before : obligation.revealed revelations = false)
    (after : (obligation.weaken (x := published)).revealed
      (revelations.reveal (published := published) source) = true)
    (state : State L Γ) :
    (obligation.weaken (x := published)).accepts
        (revelations.reveal (published := published) source)
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          PublicationResult.failure state) = true := by
  have changed : ∀ {readOwner : Player} {readPayload : L.Ty} {readName : VarId}
      (h : HasVar Γ readName (.privateData readOwner readPayload)),
      (revelations h).isRevealed = false →
      (revelations.reveal (published := published) source (.there h)).isRevealed = true →
      (revelations.reveal (published := published) source (.there h)).result
        (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
          PublicationResult.failure state) = .failure := by
    intro readOwner readPayload readName h unrevealed revealedAfter
    by_cases same : readName = name
    · subst readName
      have cellEq := HasVar.type_unique unique h source
      cases cellEq
      cases HasVar.eq_of_nodup unique h source
      simp [Revelation.result]
    · simp only [Revelations.reveal_of_ne revelations source h same,
        Revelation.isRevealed_weaken, unrevealed] at revealedAfter
      cases revealedAfter
  simp only [Obligation.revealed, Bool.and_eq_true, Bool.and_eq_false_iff,
    SourceGuard.readsRevealed] at before after
  obtain ⟨subjectAfter, readsAfter⟩ := after
  simp only [Obligation.accepts, Obligation.weaken, SourceGuard.accepts, SourceGuard.weaken]
  by_cases subjectBefore : (revelations obligation.source).isRevealed = true
  · have readsBefore : obligation.guard.allReads
        (fun h => (obligation.guard.reads h).revealed revelations) = false := by
      rcases before with subjectFalse | readsFalse
      · rw [subjectBefore] at subjectFalse; cases subjectFalse
      · exact readsFalse
    have missing : ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
        x ∈ L.exprDeps obligation.guard.code ∧
          (obligation.guard.reads h).revealed revelations = false := by
      by_contra none
      simp only [not_exists, not_and, Bool.not_eq_false] at none
      have all := (GuardCode.allReads_iff _ _).mpr fun h read => none _ _ h read
      rw [readsBefore] at all
      cases all
    obtain ⟨x, τ, h, read, unrevealed⟩ := missing
    have revealedAfter := (GuardCode.allReads_iff _ _).mp readsAfter h read
    apply GuardCode.accepts_of_failure _ _ _ h read
    cases readEq : obligation.guard.reads h with
    | publicData cell => simp [readEq, SourceGuardRead.revealed] at unrevealed
    | publication cell => simp [readEq, SourceGuardRead.revealed] at unrevealed
    | privateData cell =>
        simp only [readEq, SourceGuardRead.revealed] at unrevealed
        have cellAfter : (revelations.reveal (published := published) source
            (.there cell)).isRevealed = true := by
          simpa [Obligation.weaken, SourceGuard.weaken, readEq, SourceGuardRead.weaken,
            SourceGuardRead.revealed] using revealedAfter
        simp only [SourceGuardRead.weaken, SourceGuardRead.result]
        exact changed cell unrevealed cellAfter
  · rw [changed obligation.source (by simpa using subjectBefore) subjectAfter]
    exact GuardCode.accepts_subject_failure _ _

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

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem consistent_weaken {Γ : SourceCtx Player L} {name : VarId}
    {cell : CellTy Player L} (registry : Registry (Player := Player) (L := L) Γ)
    (revelations : Revelations Γ) (head : CellVal L cell) (state : State L Γ)
    (consistent : ∀ obligation ∈ registry, obligation.revealed revelations = true →
      obligation.accepts revelations state = true) :
    ∀ obligation ∈ registry.weaken (x := name) (c := cell),
      obligation.revealed revelations.weaken = true →
        obligation.accepts revelations.weaken (Env.cons head state) = true := by
  intro obligation member revealed
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  rw [Obligation.revealed_weaken] at revealed
  rw [Obligation.accepts_weaken]
  exact consistent original originalMember revealed

/-- Every reachable terminal state keeps every published obligation accepted. -/
theorem runWith_consistent {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (state : State L Γ)
      (registry : Registry Γ) (revelations : Revelations Γ) (history : History Player L),
      (Γ.map Prod.fst).Nodup → Accounted revelations O →
      (∀ obligation ∈ registry, obligation.revealed revelations = true →
        obligation.accepts revelations state = true) →
      ∀ outcome ∈ (runWith program profile state registry revelations history).support,
        ∀ obligation ∈ finalRegistry program registry,
          obligation.revealed (finalRevelations program revelations) = true →
            obligation.accepts (finalRevelations program revelations) outcome = true := by
  induction program with
  | ret payoffs =>
      intro profile state registry revelations history _ _ consistent outcome supported
      have same := FinDist.mem_support_pure.mp supported
      subst outcome
      exact consistent
  | sample name fresh law next ih =>
      intro profile state registry revelations history unique accounted consistent
        outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      exact ih (afterSample profile) (Env.cons value state) registry.weaken revelations.weaken
        history (by simp [fresh, unique])
        (Accounted.weaken_public (by intro _ _ equal; cases equal) accounted)
        (consistent_weaken (cell := .publicData _) registry revelations value state consistent)
        outcome supported
  | commit name owner fresh guard next ih =>
      intro profile state registry revelations history unique accounted consistent
        outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨binding, _, supported⟩ := supported
      apply ih (afterCommit profile) (Env.cons binding state) _ revelations.weaken _
        (by simp [fresh, unique]) (Accounted.commit fresh accounted) _ outcome supported
      intro obligation member revealed
      rcases List.mem_cons.mp member with rfl | member
      · simp [Obligation.revealed, Revelations.weaken, HasVar.tail?,
          Revelation.isRevealed] at revealed
      · exact consistent_weaken (cell := .privateData owner _) registry revelations binding
          state consistent obligation member revealed
  | reveal published owner name fresh source unresolved next ih =>
      intro profile state registry revelations history unique accounted consistent
        outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨disclose, _, supported⟩ := supported
      apply ih (afterReveal profile) _ registry.weaken
        (revelations.reveal (published := published) source) _ (by simp [fresh, unique])
        (Accounted.reveal source unique accounted) _ outcome supported
      intro weakened member revealedAfter
      obtain ⟨obligation, original, rfl⟩ := List.mem_map.mp member
      by_cases revealedBefore : obligation.revealed revelations = true
      · rw [obligation.accepts_reveal_of_revealed revelations source accounted unresolved
          revealedBefore]
        exact consistent obligation original revealedBefore
      · have completed : obligation.weaken ∈ registry.completedBy (published := published)
            revelations source :=
          List.mem_map.mpr ⟨obligation, List.mem_filter.mpr ⟨original, by
            simpa [Obligation.completedBy, revealedBefore] using revealedAfter⟩, rfl⟩
        have failureAccepts := obligation.accepts_reveal_failure revelations source unique
          (by simpa using revealedBefore) revealedAfter state
        cases disclose with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, ite_self]
            exact failureAccepts
        | true =>
            simp only [↓reduceIte]
            split
            · next allAccept => exact (List.all_eq_true.mp allAccept) _ completed
            · exact failureAccepts

/-- Complete execution decides every retained guard by its code: either its
subject or an input its code reads failed to publish, or all of them were
published and the code holds on the published values. -/
theorem Initial.terminal_guards_hold
    (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program)
    (outcome : State L initial.program.terminalCtx)
    (supported : outcome ∈ (initial.run profile).support)
    (obligation : Obligation initial.program.terminalCtx)
    (member : obligation ∈ finalRegistry initial.program []) :
    (((finalRevelations initial.program (Revelations.initial initial.context))
        obligation.source).result outcome = .failure ∨
      ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
        x ∈ L.exprDeps obligation.guard.code ∧
          (obligation.guard.reads h).result
            (finalRevelations initial.program (Revelations.initial initial.context))
            outcome = .failure) ∨
    ∃ (subjectValue : L.Val obligation.payload)
      (get : (x : VarId) → (σ : L.Ty) →
        HasVar ((obligation.subject, obligation.payload) :: obligation.guard.schema) x σ →
          x ∈ L.exprDeps obligation.guard.code → L.Val σ),
      ((finalRevelations initial.program (Revelations.initial initial.context))
        obligation.source).result outcome = .success subjectValue ∧
      (∀ hx, get obligation.subject obligation.payload .here hx = subjectValue) ∧
      (∀ {x τ} (h : HasVar obligation.guard.schema x τ)
        (hx : x ∈ L.exprDeps obligation.guard.code),
          (obligation.guard.reads h).result
            (finalRevelations initial.program (Revelations.initial initial.context))
            outcome = .success (get x τ (.there h) hx)) ∧
      L.toBool (L.evalDeps obligation.guard.code get) = true := by
  have revealed : obligation.revealed
      (finalRevelations initial.program (Revelations.initial initial.context)) = true := by
    simp only [Obligation.revealed, Bool.and_eq_true, SourceGuard.readsRevealed]
    refine ⟨initial.revealed obligation.source, (GuardCode.allReads_iff _ _).mpr ?_⟩
    intro x τ h _
    cases obligation.guard.reads h with
    | publicData cell | publication cell => rfl
    | privateData cell => exact initial.revealed cell
  have accepts := runWith_consistent initial.program profile initial.state []
    (Revelations.initial initial.context) (fun _ => []) initial.namesNodup
    (initial.accounts ▸ Accounted.initial initial.context) (by simp) outcome supported
    obligation member revealed
  simp only [Obligation.accepts, SourceGuard.accepts] at accepts
  by_cases failedInput : ∃ (x : VarId) (τ : L.Ty) (h : HasVar obligation.guard.schema x τ),
      x ∈ L.exprDeps obligation.guard.code ∧
        (obligation.guard.reads h).result
          (finalRevelations initial.program (Revelations.initial initial.context))
          outcome = .failure
  · exact Or.inl (Or.inr failedInput)
  cases subjectEq : ((finalRevelations initial.program (Revelations.initial initial.context))
      obligation.source).result outcome with
  | failure => exact Or.inl (Or.inl rfl)
  | success subjectValue =>
      obtain ⟨get, getSubject, resultsEq⟩ := obligation.guard.exists_get subjectValue _
        (fun h read failed => failedInput ⟨_, _, h, read, failed⟩)
      refine Or.inr ⟨subjectValue, get, rfl, getSubject, resultsEq, ?_⟩
      rw [subjectEq, obligation.guard.accepts_success subjectValue _ get getSubject
        resultsEq] at accepts
      exact accepts

end Vegas.SourceProgram
