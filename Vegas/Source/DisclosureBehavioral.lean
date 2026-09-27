/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosureNormalization
import GameTheoryExtensions.Math.Probability.FinDist

/-! # Behavioral realization of normalized disclosure intentions

The posterior below contains the original owner's action list, conditioned on
its actual source observation and effective actions. It is part of the policy
construction, not a new state component or source operation. The original
source executor is used on both sides of the realization law.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {who : Player} {Γ : SourceCtx Player L}

/-- The original binding and updated original recall, before observing the
binding emitted by the realized policy. -/
def bindingMemoryLaw (name : VarId) (payload : L.Ty)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist (PublicationResult (L.Val payload)))
    (view : DecisionView who Γ) :
    FinDist (PublicationResult (L.Val payload) × List (OwnAction Player L)) :=
  (remember view).bind fun past =>
    (choose (view.1, past)).map fun binding =>
      (binding, past ++ [.commit who name payload binding])

/-- The effective disclosure and updated original recall. No raw certificate
is emitted by this source policy construction. -/
def disclosureMemoryLaw {name : VarId} {payload : L.Ty} (published : VarId)
    (selected : HasVar Γ name (.commitment who payload))
    (registry : Registry Γ) (revelations : Revelations Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist Bool) (view : DecisionView who Γ) :
    FinDist (Bool × List (OwnAction Player L)) :=
  (remember view).bind fun past =>
    (choose (view.1, past)).map fun disclose =>
      (effectiveDisclosureView published selected registry revelations view.1 disclose,
        past ++ [.reveal who name disclose])

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem bindingMemoryLaw_disintegrate {Result : Type} (name : VarId) (payload : L.Ty)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist (PublicationResult (L.Val payload)))
    (view : DecisionView who Γ)
    (next : PublicationResult (L.Val payload) → List (OwnAction Player L) → FinDist Result) :
    ((remember view).bind fun past => (choose (view.1, past)).bind fun binding =>
      next binding (past ++ [.commit who name payload binding])) =
      ((bindingMemoryLaw name payload remember choose view).map Prod.fst).bind fun binding =>
        (((bindingMemoryLaw name payload remember choose view).condOnFibre Prod.fst binding).map
          Prod.snd).bind (next binding) := by
  have disintegration := congrArg (FinDist.bind · (fun pair => next pair.1 pair.2))
    (bindingMemoryLaw name payload remember choose view).eq_bind_fst_conditional_snd
  simpa only [bindingMemoryLaw, FinDist.bind_bind, FinDist.bind_map] using disintegration

omit [IExpr.ResultTypes L] in
theorem disclosureMemoryLaw_disintegrate {Result : Type} {name : VarId} {payload : L.Ty}
    (published : VarId) (selected : HasVar Γ name (.commitment who payload))
    (registry : Registry Γ) (revelations : Revelations Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (choose : DecisionView who Γ → FinDist Bool) (view : DecisionView who Γ)
    (next : Bool → List (OwnAction Player L) → FinDist Result) :
    ((remember view).bind fun past => (choose (view.1, past)).bind fun disclose =>
      next (effectiveDisclosureView published selected registry revelations view.1 disclose)
        (past ++ [.reveal who name disclose])) =
      ((disclosureMemoryLaw published selected registry revelations remember choose view).map
        Prod.fst).bind fun disclose =>
          (((disclosureMemoryLaw published selected registry revelations remember choose
              view).condOnFibre Prod.fst disclose).map Prod.snd).bind (next disclose) := by
  have disintegration := congrArg (FinDist.bind · (fun pair => next pair.1 pair.2))
    (disclosureMemoryLaw published selected registry revelations remember choose
      view).eq_bind_fst_conditional_snd
  simpa only [disclosureMemoryLaw, FinDist.bind_bind, FinDist.bind_map] using disintegration

/-- A behavioral compiler carries only an observation-local conditional law.
Later policies see their original intentions through that posterior. -/
def BehavioralPolicy.normalizeDisclosureFrom {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    (DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    BehavioralPolicy who program → BehavioralPolicy who program
  | _, _, .ret _, _, _, _, _ => PUnit.unit
  | _, _, .sample _ _ _ next, registry, revelations, remember, policy =>
      normalizeDisclosureFrom next registry.weaken revelations.weaken
        (fun view => remember (view.back false)) policy
  | _, _, .commit (payload := payload) name owner _ guard next,
      registry, revelations, remember, policy =>
      let joint (own : owner = who) (view : DecisionView who _) :=
        bindingMemoryLaw name payload remember (policy.1 own) view
      (fun own view => (joint own view).map Prod.fst,
        normalizeDisclosureFrom next
          (({ owner := owner, subject := name, payload := payload, source := .here,
              guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
          (fun view => if own : owner = who then
            ((joint own (view.back true)).condOnFibre Prod.fst
              ((view.1.cells.get .here).getD .failure)).map Prod.snd
          else remember (view.back false)) policy.2)
  | _, _, .reveal published owner _ _ selected _ next,
      registry, revelations, remember, policy =>
      let joint (own : owner = who) (view : DecisionView who _) :=
        disclosureMemoryLaw published (own ▸ selected) registry revelations remember
          (policy.1 own) view
      (fun own view => (joint own view).map Prod.fst,
        normalizeDisclosureFrom next registry.weaken
          (revelations.reveal (published := published) selected)
          (fun view => if own : owner = who then
            ((joint own (view.back true)).condOnFibre Prod.fst
              (OwnAction.disclosure view.2.getLast?)).map Prod.snd
          else remember (view.back false)) policy.2)

/-- The posterior realization emits only effective representatives at every
reveal, including observations of zero probability under a chosen profile. -/
theorem BehavioralPolicy.normalizeDisclosureFrom_effective {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (policy : BehavioralPolicy who program) →
    (policy.normalizeDisclosureFrom program registry revelations remember).EffectiveDisclosures
      program registry revelations
  | _, _, .ret _, _, _, _, _ => trivial
  | _, _, .sample _ _ _ next, registry, revelations, remember, policy =>
      policy.normalizeDisclosureFrom_effective next _ _ _
  | _, _, .commit _ _ _ _ next, registry, revelations, remember, policy =>
      policy.2.normalizeDisclosureFrom_effective next _ _ _
  | _, _, .reveal published owner _ _ selected _ next,
      registry, revelations, remember, policy => by
      refine ⟨?_, policy.2.normalizeDisclosureFrom_effective next _ _ _⟩
      intro own view response supported
      subst who
      change response ∈ ((disclosureMemoryLaw published selected registry revelations remember
        (policy.1 rfl) view).map Prod.fst).support at supported
      obtain ⟨pair, produced, rfl⟩ := FinDist.support_map .. ▸ supported
      obtain ⟨past, _remembered, produced⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ produced)
      obtain ⟨intended, _chosen, rfl⟩ := FinDist.support_map .. ▸ produced
      exact effectiveDisclosure_idempotent published selected _ intended

private def RealizesDisclosure {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) : Prop :=
  ∀ (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (state : State L Γ) (history : History Player L),
    ((remember (sourceObserve who state, history who)).bind fun past =>
      runWith program (Function.update profile who policy) state registry revelations
        (Function.update history who past)) =
      runWith program (Function.update profile who
        (policy.normalizeDisclosureFrom program registry revelations remember))
        state registry revelations history

private theorem realizesDisclosure_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    {who : Player} (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (ih : RealizesDisclosure (who := who) next) :
    RealizesDisclosure (who := who) (.commit name owner fresh guard next) := by
  intro profile policy registry revelations remember state history
  by_cases owned : owner = who
  · subst who
    let view : DecisionView owner _ := (sourceObserve owner state, history owner)
    let law := bindingMemoryLaw name payload remember (policy.1 rfl) view
    simp only [runWith, commitKernel, Function.update_self, afterCommit_update,
      Function.update_idem, BehavioralPolicy.normalizeDisclosureFrom]
    erw [bindingMemoryLaw_disintegrate name payload remember (policy.1 rfl) view
      (fun binding past => runWith next (Function.update (afterCommit profile) owner policy.2)
        (Env.cons binding state)
        (({ owner := owner, subject := name, payload := payload, source := .here,
            guard := guard.weaken } : Obligation _) :: registry.weaken)
        revelations.weaken (Function.update history owner past))]
    change ((law.map Prod.fst).bind _) = ((law.map Prod.fst).bind _)
    apply FinDist.bind_congr
    intro binding _
    have observed : (sourceObserve owner (Env.cons (x := name) binding state)).cells.get
        (HasVar.here : HasVar ((name, .commitment owner payload) :: _) name
          (.commitment owner payload)) = some binding := by
      simp only [Env.get, sourceObserve, ite_true, Env.cons]
    have step := ih (afterCommit profile) policy.2
      (({ owner := owner, subject := name, payload := payload, source := .here,
          guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
      (fun nextView => if own : owner = owner then
        ((bindingMemoryLaw name payload remember (policy.1 own)
            (nextView.back true)).condOnFibre Prod.fst
          ((nextView.1.cells.get .here).getD .failure)).map Prod.snd
      else remember (nextView.back false))
      (Env.cons binding state)
      (Function.update history owner (history owner ++ [.commit owner name payload binding]))
    simpa only [BehavioralPolicy.normalizeDisclosureFrom,
      dite_true, Function.update_self, back_sourceObserve, ite_true,
      List.dropLast_concat, observed, Option.getD_some,
      Function.update_idem, law, view] using step
  · simp only [runWith, commitKernel, Function.update_of_ne owned, afterCommit_update]
    rw [FinDist.bind_comm]
    apply FinDist.bind_congr
    intro binding _
    have step := ih (afterCommit profile) policy.2
      (({ owner := owner, subject := name, payload := payload, source := .here,
          guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
      (fun nextView => if own : owner = who then
        ((bindingMemoryLaw name payload remember (policy.1 own)
            (nextView.back true)).condOnFibre Prod.fst
          ((nextView.1.cells.get .here).getD .failure)).map Prod.snd
      else remember (nextView.back false))
      (Env.cons binding state)
      (Function.update history owner (history owner ++ [.commit owner name payload binding]))
    simpa only [BehavioralPolicy.normalizeDisclosureFrom,
      dite_eq_right owned, Function.update_of_ne (Ne.symm owned), back_sourceObserve,
      Bool.false_eq_true, ite_false, Function.update_comm (Ne.symm owned)] using step

private theorem runWith_reveal_result {Γ : SourceCtx Player L} {O : Finset VarId}
    (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (profile : BehavioralProfile (.reveal published owner name fresh selected unresolved next))
    (state : State L Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (history : History Player L) :
    runWith (.reveal published owner name fresh selected unresolved next)
        profile state registry revelations history =
      (revealKernel profile (sourceObserve owner state, history owner)).bind fun disclose =>
        runWith next (afterReveal profile)
          (Env.cons (disclosureResult published selected
            ⟨state, registry, revelations, fun _ => []⟩ disclose) state)
          registry.weaken (revelations.reveal (published := published) selected)
          (Function.update history owner (history owner ++ [.reveal owner name disclose])) := rfl

private theorem realizesDisclosure_reveal {Γ : SourceCtx Player L} {O : Finset VarId}
    {who : Player} (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (ih : RealizesDisclosure (who := who) next) :
    RealizesDisclosure (who := who)
      (.reveal published owner name fresh selected unresolved next) := by
  intro profile policy registry revelations remember state history
  by_cases owned : owner = who
  · subst who
    let view : DecisionView owner _ := (sourceObserve owner state, history owner)
    let config : Config Player L _ := ⟨state, registry, revelations, fun _ => []⟩
    let law := disclosureMemoryLaw published selected registry revelations remember
      (policy.1 rfl) view
    let result := fun disclose => disclosureResult published selected config disclose
    have normalizedResult (disclose : Bool) :
        result (effectiveDisclosureView published selected registry revelations
          (sourceObserve owner state) disclose) = result disclose := by
      exact (congrArg result (effectiveDisclosureView_observe published selected config
        disclose)).trans
          (disclosureResult_effectiveDisclosure published selected config disclose)
    simp only [runWith_reveal_result, revealKernel, Function.update_self, afterReveal_update,
      Function.update_idem, BehavioralPolicy.normalizeDisclosureFrom]
    have disintegration := disclosureMemoryLaw_disintegrate published selected registry
      revelations remember (policy.1 rfl) view (fun response past =>
        runWith next (Function.update (afterReveal profile) owner policy.2)
          (Env.cons (result response) state) registry.weaken
          (revelations.reveal (published := published) selected)
          (Function.update history owner past))
    simp only [normalizedResult, view] at disintegration
    erw [disintegration]
    change ((law.map Prod.fst).bind _) = ((law.map Prod.fst).bind _)
    apply FinDist.bind_congr
    intro disclose _
    have step := ih (afterReveal profile) policy.2
      registry.weaken (revelations.reveal (published := published) selected)
      (fun nextView => if own : owner = owner then
        ((disclosureMemoryLaw published (own ▸ selected) registry revelations remember
            (policy.1 own) (nextView.back true)).condOnFibre Prod.fst
          (OwnAction.disclosure nextView.2.getLast?)).map Prod.snd
      else remember (nextView.back false))
      (Env.cons (result disclose) state)
      (Function.update history owner (history owner ++ [.reveal owner name disclose]))
    simpa only [BehavioralPolicy.normalizeDisclosureFrom,
      dite_true, Function.update_self, back_sourceObserve, ite_true,
      List.dropLast_concat, List.getLast?_concat, OwnAction.disclosure,
      Function.update_idem, law, view] using step
  · simp only [runWith_reveal_result, revealKernel, Function.update_of_ne owned,
      afterReveal_update]
    rw [FinDist.bind_comm]
    apply FinDist.bind_congr
    intro disclose _
    have step := ih (afterReveal profile) policy.2
      registry.weaken (revelations.reveal (published := published) selected)
      (fun nextView => if own : owner = who then
        ((disclosureMemoryLaw published (own ▸ selected) registry revelations remember
            (policy.1 own) (nextView.back true)).condOnFibre Prod.fst
          (OwnAction.disclosure nextView.2.getLast?)).map Prod.snd
      else remember (nextView.back false))
      (Env.cons (disclosureResult published selected
        ⟨state, registry, revelations, fun _ => []⟩ disclose) state)
      (Function.update history owner (history owner ++ [.reveal owner name disclose]))
    simpa only [BehavioralPolicy.normalizeDisclosureFrom,
      dite_eq_right owned, Function.update_of_ne (Ne.symm owned), back_sourceObserve,
      Bool.false_eq_true, ite_false, Function.update_comm (Ne.symm owned)] using step

/-- The original source continuation is realized exactly after averaging over
the owner's conditional original recall. Opponents, hidden state, guards and
chance remain arbitrary. This is a multi-step law of the existing executor. -/
theorem normalizeDisclosureFrom_realize {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile program) → (policy : BehavioralPolicy who program) →
    (registry : Registry Γ) → (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (state : State L Γ) → (history : History Player L) →
    ((remember (sourceObserve who state, history who)).bind fun past =>
      runWith program (Function.update profile who policy) state registry revelations
        (Function.update history who past)) =
      runWith program (Function.update profile who
        (policy.normalizeDisclosureFrom program registry revelations remember))
        state registry revelations history
  | _, _, .ret _, _, _, _, _, _, _, _ => by simp only [runWith, FinDist.bind_const]
  | _, _, .sample name fresh law next, profile, policy, registry, revelations,
      remember, state, history => by
      simp only [runWith, afterSample_update]
      rw [FinDist.bind_comm]
      apply FinDist.bind_congr
      intro value _
      have step := normalizeDisclosureFrom_realize next (afterSample profile) policy
        registry.weaken revelations.weaken (fun view => remember (view.back false))
        (Env.cons value state) history
      simpa only [BehavioralPolicy.normalizeDisclosureFrom,
        back_sourceObserve, Bool.false_eq_true, ite_false] using step
  | _, _, .commit name owner fresh guard next, profile, policy,
      registry, revelations, remember, state, history =>
      realizesDisclosure_commit name owner fresh guard next
        (normalizeDisclosureFrom_realize next) profile policy registry revelations remember
          state history
  | _, _, .reveal published owner name fresh selected unresolved next, profile, policy,
      registry, revelations, remember, state, history =>
      realizesDisclosure_reveal published owner name fresh selected unresolved next
        (normalizeDisclosureFrom_realize next) profile policy registry revelations remember
          state history

/-- Normalize a continuation with its existing own recall as the initial
private intention. This construction depends on only this player's policy. -/
def BehavioralPolicy.normalizeDisclosures {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (policy : BehavioralPolicy who program) : BehavioralPolicy who program :=
  policy.normalizeDisclosureFrom program registry revelations (fun view => FinDist.pure view.2)

/-- Every source behavioral policy has a fixed normalized behavioral policy
with the same complete typed terminal law against every opponent profile.
The statement also applies at an arbitrary residual configuration. -/
theorem normalizeDisclosures_runFrom {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (config : Config Player L Γ) :
    runFrom program (Function.update profile who
        (policy.normalizeDisclosures program config.registry config.revelations)) config =
      runFrom program (Function.update profile who policy) config := by
  symm
  simpa only [FinDist.pure_bind, Function.update_eq_self, runFrom,
    BehavioralPolicy.normalizeDisclosures] using
    normalizeDisclosureFrom_realize program profile policy config.registry config.revelations
      (fun view => FinDist.pure view.2) config.state config.history

/-- Simultaneously realize every player's original private intentions. Each
coordinate depends on only that player's policy. -/
def normalizeDisclosureProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ) (revelations : Revelations Γ)
    (profile : BehavioralProfile program) : BehavioralProfile program := fun player =>
  (profile player).normalizeDisclosures program registry revelations

theorem normalizeDisclosureProfile_runFrom [Finite Player] {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (config : Config Player L Γ) :
    runFrom program
        (normalizeDisclosureProfile program config.registry config.revelations profile) config =
      runFrom program profile config := by
  classical
  let _ := Fintype.ofFinite Player
  let translated := normalizeDisclosureProfile program config.registry config.revelations profile
  let selected (players : Finset Player) : BehavioralProfile program := fun who =>
    if who ∈ players then translated who else profile who
  have equality (players : Finset Player) :
      runFrom program (selected players) config = runFrom program profile config := by
    induction players using Finset.induction_on with
    | empty => simp only [selected, Finset.notMem_empty, ite_false]
    | @insert player players absent ih =>
        have more : selected (insert player players) =
            Function.update (selected players) player (translated player) := by
          funext who
          by_cases same : who = player
          · subst who
            simp only [selected, Finset.mem_insert_self, ite_true, Function.update_self]
          · simp only [selected, Finset.mem_insert, same, false_or, Function.update_of_ne same]
        have previous : Function.update (selected players) player (profile player) =
            selected players := by
          funext who
          by_cases same : who = player
          · subst who
            simp only [Function.update_self, selected, absent, ite_false]
          · exact Function.update_of_ne same _ _
        rw [more]
        change runFrom program (Function.update (selected players) player
          ((profile player).normalizeDisclosures program config.registry config.revelations))
          config = _
        rw [normalizeDisclosures_runFrom program (selected players) (profile player) config,
          previous, ih]
  simpa only [selected, Finset.mem_univ, ite_true, translated] using equality Finset.univ

/-- The initial private draw is preserved jointly with the full terminal
state; no independence between different players' initial types is required. -/
theorem normalizeDisclosureProfile_joint_law [Finite Player] {Γ : SourceCtx Player L}
    {O : Finset VarId} {Parameter : Type}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (registry : Registry Γ) (revelations : Revelations Γ) (belief : FinDist (Config Player L Γ))
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (parameter : Config Player L Γ → Parameter) :
    (belief.bind fun config =>
      (runFrom program (normalizeDisclosureProfile program registry revelations profile) config).map
        (fun result => (parameter config, result))) =
      belief.bind fun config => (runFrom program profile config).map
        (fun result => (parameter config, result)) := by
  apply FinDist.bind_congr
  intro config supported
  have same := normalizeDisclosureProfile_runFrom program profile config
  rw [registryEq config supported, revelationsEq config supported] at same
  exact congrArg (FinDist.map fun result => (parameter config, result)) same

end Vegas.SourceProgram
