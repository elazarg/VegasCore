/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceCommitTail
import Vegas.Source.DisclosureOpening

/-! # The residual after leading disclosures

After `count` leading disclosures of a residual program, the residual program
(`Vegas.revealTail`) carries its own compiled data: the references of its
context (`Vegas.revealTailRefs`), the embedding of its events, its obligation
registry and revelations, and its compiled policy suffix
(`Vegas.CompiledPolicySuffix.revealTailMany`). The prefix decoder of the
program reads through the disclosures into the residual one
(`Vegas.decodeSourcePrefix?_revealTail`).

When every player opens effectively at the leading disclosures
(`Vegas.OpensThrough`), the source run through them is deterministic: each
disclosure publishes exactly what its opening yields (`Vegas.openChain`,
`Vegas.iterate_openChain`).
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The first `count` operations of the program are disclosures. -/
def RevealPrefix : {Γ : SourceCtx Player L} → {names : Finset VarId} →
    SourceProgram Player L Γ names → Nat → Prop
  | _, _, _, 0 => True
  | _, _, .reveal _ _ _ _ _ _ next, count + 1 => RevealPrefix next count
  | _, _, .ret _, _ + 1 => False
  | _, _, .sample _ _ _ _, _ + 1 => False
  | _, _, .commit _ _ _ _ _, _ + 1 => False

/-- The residual program after `count` leading disclosures. -/
def revealTail : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → RevealPrefix program count →
      ResidualProgram program
  | 0, _, _, program, _ => ⟨_, _, program, id⟩
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed =>
      let rest := revealTail count next prefixed
      ⟨rest.context, rest.names, rest.tail, Sum.inr ∘ rest.lift⟩
  | _ + 1, _, _, .ret _, prefixed => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed => prefixed.elim

/-- The residual profile after `count` leading disclosures. -/
def revealTailProfile : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    BehavioralProfile program → BehavioralProfile (revealTail count program prefixed).tail
  | 0, _, _, _, _, profile => profile
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed, profile =>
      revealTailProfile count next prefixed (afterReveal profile)
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The obligation registry after leading disclosures. -/
def revealTailRegistry : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    Registry Γ → Registry (revealTail count program prefixed).context
  | 0, _, _, _, _, registry => registry
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed, registry =>
      revealTailRegistry count next prefixed registry.weaken
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The revelations after leading disclosures. -/
def revealTailRevelations : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    (prefixed : RevealPrefix program count) →
    Revelations Γ → Revelations (revealTail count program prefixed).context
  | 0, _, _, _, _, revelations => revelations
  | count + 1, _, _, .reveal published _ _ _ selected _ next, prefixed, revelations =>
      revealTailRevelations count next prefixed
        (revelations.reveal (published := published) selected)
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The residual states embed injectively. -/
theorem revealTail_lift_injective : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : RevealPrefix program count),
    Function.Injective (revealTail count program prefixed).lift := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed; exact Function.injective_id
  | succ count ih =>
      intro Γ names program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ next => exact Sum.inr_injective.comp (ih next prefixed)

/-- A disclosure's view of its context is that of its residual after the
disclosure, through the leading disclosures. -/
theorem RevealPrefix.le_eventCount : ∀ {count : Nat} {Γ : SourceCtx Player L}
    {names : Finset VarId} {program : SourceProgram Player L Γ names},
    RevealPrefix program count → count ≤ eventCount program
  | 0, _, _, _, _ => Nat.zero_le _
  | _ + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed => by
      have := RevealPrefix.le_eventCount (program := next) prefixed
      simp only [eventCount]
      omega
  | _ + 1, _, _, .ret _, prefixed => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed => prefixed.elim

/-- Leading disclosures are events counted by the program. -/
theorem eventCount_revealTail : ∀ (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : RevealPrefix program count),
    count + eventCount (revealTail count program prefixed).tail = eventCount program := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed; simp [revealTail]
  | succ count ih =>
      intro Γ names program prefixed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal _ _ _ _ _ _ next =>
          have := ih next prefixed
          simp only [revealTail, eventCount] at this ⊢
          omega

section Opening

/-- The policy discloses exactly its effective disclosures at the leading
`count` disclosures. -/
def OpensThrough {who : Player} : (count : Nat) → {Γ : SourceCtx Player L} →
    {names : Finset VarId} → (program : SourceProgram Player L Γ names) →
    RevealPrefix program count → Registry Γ → Revelations Γ → BehavioralPolicy who program →
      Prop
  | 0, _, _, _, _, _, _, _ => True
  | count + 1, _, _, .reveal published _ _ _ selected _ next, prefixed, registry, revelations,
      policy =>
      (∀ own view, policy.1 own view = PMF.pure
        (effectiveDisclosureView published selected registry revelations
          (own.symm ▸ view.1) true)) ∧
      OpensThrough count next prefixed registry.weaken
        (revelations.reveal (published := published) selected) policy.2
  | _ + 1, _, _, .ret _, prefixed, _, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _, _, _ => prefixed.elim

/-- A policy opening effectively opens effectively at every leading prefix of
disclosures, and so does its residual. -/
theorem BehavioralPolicy.OpensEffectively.through {who : Player} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (registry : Registry Γ) (revelations : Revelations Γ) (policy : BehavioralPolicy who program),
      policy.OpensEffectively program registry revelations →
      OpensThrough count program prefixed registry revelations policy ∧
        ∀ profile : BehavioralProfile program, profile who = policy →
          (revealTailProfile count program prefixed profile who).OpensEffectively
            (revealTail count program prefixed).tail
            (revealTailRegistry count program prefixed registry)
            (revealTailRevelations count program prefixed revelations) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed registry revelations policy opens
      exact ⟨trivial, fun profile same => by
        subst same
        exact opens⟩
  | succ count ih =>
      intro Γ names program prefixed registry revelations policy opens
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          obtain ⟨head, rest⟩ := opens
          obtain ⟨through, tail⟩ := ih next prefixed _ _ policy.2 rest
          exact ⟨⟨head, through⟩, fun profile same =>
            tail (afterReveal profile) (by simp only [afterReveal, same])⟩

/-- The configuration after the leading disclosures, each publishing exactly
what its opening yields. -/
def openChain : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    Config Player L Γ → Config Player L (revealTail count program prefixed).context
  | 0, _, _, _, _, config => config
  | count + 1, _, _, .reveal published _ _ _ selected _ next, prefixed, config =>
      openChain count next prefixed (revealSuccessor published selected config
        (effectiveDisclosure published selected config true))
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The registry and revelations the open chain reaches. -/
theorem openChain_eq : ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
    (config : Config Player L Γ),
    openChain count program prefixed config =
      ⟨(openChain count program prefixed config).state,
        revealTailRegistry count program prefixed config.registry,
        revealTailRevelations count program prefixed config.revelations,
        (openChain count program prefixed config).history⟩ := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed config; rfl
  | succ count ih =>
      intro Γ names program prefixed config
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ih next prefixed _

/-- **The source run through leading opened disclosures.** When every player
opens effectively at the leading disclosures, the source run of the program is
the residual source run from the open chain's configuration. -/
theorem iterate_openChain [Fintype Player] :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
      (prefixed : RevealPrefix program count) (more : Nat) (config : Config Player L Γ),
      (∀ who, OpensThrough count program prefixed config.registry config.revelations
        (profile who)) →
      (fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[count + more]
          (PMF.pure (ProtocolState.entry program config)) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep
          (revealTail count program prefixed).tail
          (revealTailProfile count program prefixed profile)))^[more]
          (PMF.pure (ProtocolState.entry _ (openChain count program prefixed config)))).map
            (revealTail count program prefixed).lift := by
  intro count
  induction count with
  | zero =>
      intro Γ names program profile prefixed more config _
      simp only [Nat.zero_add, revealTail, openChain, revealTailProfile, PMF.map_id]
  | succ count ih =>
      intro Γ names program profile prefixed more config opens
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          rw [show count + 1 + more = (count + more) + 1 by omega,
            ProtocolState.behavioralStatePrefix_reveal]
          have kernel : revealKernel profile (config.view owner) =
              PMF.pure (effectiveDisclosure published selected config true) := by
            rw [revealKernel, (opens owner).1 rfl (config.view owner)]
            exact congrArg PMF.pure (effectiveDisclosureView_observe published selected config
              true)
          rw [kernel, PMF.pure_bind]
          have later := ih next (afterReveal profile) prefixed more
            (revealSuccessor published selected config
              (effectiveDisclosure published selected config true))
            (fun who => (opens who).2)
          rw [later, PMF.map_comp]
          rfl

end Opening

variable {setup : Setup (Player := Player) (L := L)}

/-- The head of a disclosure is a publication. -/
theorem reveal_head_layout {Γ : SourceCtx Player L} {names : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : published ∉ Γ.map Prod.fst}
    {selected : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ names}
    {next : SourceProgram Player L ((published, .publication payload) :: Γ) (names.erase name)}
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next)) :
    outputLayout setup.program (embedding.event ⟨0, by simp [eventCount]⟩) =
      .publication payload := by
  simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩

variable (setup) in
/-- The context references after leading disclosures. -/
def revealTailRefs : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    ContextRefs (graphLayout setup.program) Γ →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
      ContextRefs (graphLayout setup.program) (revealTail count program prefixed).context
  | 0, _, _, _, _, refs, _ => refs
  | count + 1, _, _, .reveal published _ _ _ _ _ next, prefixed, refs, embedding =>
      revealTailRefs count next prefixed
        (refs.cons (name := published) ⟨.inr (embedding.event ⟨0, by simp [eventCount]⟩),
          reveal_head_layout embedding⟩)
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
  | _ + 1, _, _, .ret _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _, _ => prefixed.elim

variable (setup) in
/-- The output embedding after leading disclosures. -/
def revealTailEmbedding : (count : Nat) → {Γ : SourceCtx Player L} → {names : Finset VarId} →
    (program : SourceProgram Player L Γ names) → (prefixed : RevealPrefix program count) →
    OutputEmbedding (inputLayout setup.context) (outputLayout setup.program) program →
      OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        (revealTail count program prefixed).tail
  | 0, _, _, _, _, embedding => embedding
  | count + 1, _, _, .reveal _ _ _ _ _ _ next, prefixed, embedding =>
      revealTailEmbedding count next prefixed
        (embedding.tail next (by simp [eventCount]) (fun _ => rfl))
  | _ + 1, _, _, .ret _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .sample _ _ _ _, prefixed, _ => prefixed.elim
  | _ + 1, _, _, .commit _ _ _ _ _, prefixed, _ => prefixed.elim

/-- The residual references precede the residual embedding. -/
theorem revealTailRefsBefore :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program),
      ContextRefsBefore refs embedding →
      ContextRefsBefore (revealTailRefs setup count program prefixed refs embedding)
        (revealTailEmbedding setup count program prefixed embedding) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed refs embedding before; exact before
  | succ count ih =>
      intro Γ names program prefixed refs embedding before
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          apply ih next prefixed
          intro readName cell source remaining
          cases source with
          | here =>
              change (embedding.event ⟨0, by simp [eventCount]⟩).val <
                (embedding.event (Fin.succ remaining)).val
              apply embedding.strictMono
              exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
          | there source => exact before source (Fin.succ remaining)

/-- **The residual compiled policy suffix.** A compiled policy suffix at rank
`offset` gives one for the residual after `count` leading disclosures, at rank
`offset + count`. -/
theorem CompiledPolicySuffix.revealTailMany (wholeProfile : BehavioralProfile setup.program) :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations registry
        embedding refsBefore offset →
      CompiledPolicySuffix setup.program wholeProfile (Vegas.revealTail count program prefixed).tail
        (revealTailProfile count program prefixed profile)
        (revealTailRefs setup count program prefixed refs embedding)
        (revealTailRevelations count program prefixed revelations)
        (revealTailRegistry count program prefixed registry)
        (revealTailEmbedding setup count program prefixed embedding)
        (revealTailRefsBefore count program prefixed refs embedding refsBefore)
        (offset + count) := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed profile refs revelations registry embedding refsBefore
        offset aligned
      exact aligned
  | succ count ih =>
      intro Γ names program prefixed profile refs revelations registry embedding refsBefore
        offset aligned
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          have step := aligned.revealTail setup.program wholeProfile fresh selected unresolved
            next profile refs revelations registry embedding refsBefore offset
          have later := ih next prefixed (afterReveal profile) _ _ _ _ _ (offset + 1) step
          rw [show offset + (count + 1) = offset + 1 + count by omega]
          exact later

/-- The residual profile keeps effective disclosures. -/
theorem effective_revealTail {who : Player} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (profile : BehavioralProfile program) (registry : Registry Γ)
      (revelations : Revelations Γ),
      (profile who).EffectiveDisclosures program registry revelations →
      ((revealTailProfile count program prefixed profile) who).EffectiveDisclosures
        (revealTail count program prefixed).tail
        (revealTailRegistry count program prefixed registry)
        (revealTailRevelations count program prefixed revelations) := by
  intro count
  induction count with
  | zero => intro Γ names program prefixed profile registry revelations effective; exact effective
  | succ count ih =>
      intro Γ names program prefixed profile registry revelations effective
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | reveal published owner name fresh selected unresolved next =>
          exact ih next prefixed (afterReveal profile) _ _ effective.2

/-- **The prefix decoder reads through leading disclosures.** -/
theorem decodeSourcePrefix?_revealTail :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {names : Finset VarId}
      (program : SourceProgram Player L Γ names) (prefixed : RevealPrefix program count)
      (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
      (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (more : Nat) (store : EventGraph.Store (graphLayout setup.program))
      (history : History Player L),
      decodeSourcePrefix? program refs registry revelations embedding.ref (count + more) store
          history =
        (decodeSourcePrefix? (revealTail count program prefixed).tail
          (revealTailRefs setup count program prefixed refs embedding)
          (revealTailRegistry count program prefixed registry)
          (revealTailRevelations count program prefixed revelations)
          (revealTailEmbedding setup count program prefixed embedding).ref more store
          history).map (revealTail count program prefixed).lift := by
  intro count
  induction count with
  | zero =>
      intro Γ names program prefixed refs registry revelations embedding more store history
      simp only [Nat.zero_add, revealTail, revealTailRefs, revealTailRegistry,
        revealTailRevelations, revealTailEmbedding]
      rw [Option.map_id]
      rfl
  | succ count ih =>
      intro Γ names program prefixed refs registry revelations embedding more store history
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ names published owner name payload fresh selected unresolved next =>
          rw [show count + 1 + more = (count + more) + 1 by omega, decodeSourcePrefix?_reveal]
          exact (congrArg (Option.map Sum.inr) (ih next prefixed _ _ _
            (embedding.tail next (by simp [eventCount]) (fun _ => rfl)) more store history)).trans
            (by rw [Option.map_map]; rfl)

/-- The prefix decoder through leading disclosures, at the residual's entry. -/
theorem decodeSourcePrefix?_revealTail_entry (count : Nat) {Γ : SourceCtx Player L}
    {names : Finset VarId} (program : SourceProgram Player L Γ names)
    (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (store : EventGraph.Store (graphLayout setup.program))
    (history : History Player L) :
    decodeSourcePrefix? program refs registry revelations embedding.ref count store history =
      (decodeState? (revealTailRefs setup count program prefixed refs embedding) store).map
        fun state => (revealTail count program prefixed).lift (ProtocolState.entry _
          ⟨state, revealTailRegistry count program prefixed registry,
            revealTailRevelations count program prefixed revelations, history⟩) := by
  have through := decodeSourcePrefix?_revealTail count program prefixed refs registry
    revelations embedding 0 store history
  rw [Nat.add_zero] at through
  rw [through]
  simp only [decodeSourcePrefix?, Option.map_map]
  rfl

end Vegas
