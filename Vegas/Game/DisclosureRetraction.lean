/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.DisclosurePrefix
import Vegas.Source.DisclosureObservation

/-! # Information-fiber retraction along normalized source prefixes

The original intentions sampled by the posterior always compress back to the
actual normalized state. This property is proved on the support of the existing
source protocol runner, including arbitrarily small positive prefix events.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {who : Player}

omit [Fintype Player] in
theorem ProtocolState.normalizeDisclosureRecall_entry {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (recall : DecisionView who Γ → List (OwnAction Player L))
    (config : Config Player L Γ) :
    normalizeDisclosureRecall program recall (entry program config) =
      entry program (config.withOwnHistory who (recall (config.view who))) := by
  cases program <;> rfl

private def RetractsDisclosure {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : Prop :=
  ∀ (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (recall : DecisionView who Γ → List (OwnAction Player L)) (config : Config Player L Γ),
    (∀ past ∈ (remember (config.view who)).support,
      recall (sourceObserve who config.state, past) = config.history who) →
    ∀ (count : Nat) (state : ProtocolState program),
      state ∈ ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosureFrom program config.registry
          config.revelations remember))))^[count]
        (FinDist.pure (ProtocolState.entry program config))).support →
    ∀ original ∈ (policy.disclosureMemory program config.registry config.revelations
        remember state).support,
      ProtocolState.normalizeDisclosureRecall program recall original = state

omit [Fintype Player] in
private theorem retractsDisclosure_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (policy : BehavioralPolicy who program)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (recall : DecisionView who Γ → List (OwnAction Player L)) (config : Config Player L Γ)
    (coherent : ∀ past ∈ (remember (config.view who)).support,
      recall (sourceObserve who config.state, past) = config.history who)
    (original : ProtocolState program)
    (member : original ∈ (policy.disclosureMemory program config.registry config.revelations
      remember (ProtocolState.entry program config)).support) :
    ProtocolState.normalizeDisclosureRecall program recall original =
      ProtocolState.entry program config := by
  rw [BehavioralPolicy.disclosureMemory_entry, Config.restoreMemory, FinDist.map_comp] at member
  obtain ⟨past, supported, rfl⟩ := FinDist.support_map .. ▸ member
  rw [Function.comp_apply, ProtocolState.normalizeDisclosureRecall_entry,
    Config.withOwnHistory_view, coherent past supported, Config.withOwnHistory_twice]
  simp only [Config.withOwnHistory, Function.update_eq_self]

private theorem retractsDisclosure_sample {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (ih : RetractsDisclosure (who := who) next) :
    RetractsDisclosure (who := who) (.sample name fresh law next) := by
  intro profile policy remember recall config coherent count state reached original member
  cases count with
  | zero =>
      have equal : state = ProtocolState.entry _ config := by
        simpa only [Function.iterate_zero_apply, FinDist.mem_support_pure]
          using reached
      subst state
      exact retractsDisclosure_entry _ policy remember recall config coherent original member
  | succ count =>
      rw [ProtocolState.behavioralStatePrefix_sample
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.sample name fresh law next) config.registry config.revelations remember))
        config count] at reached
      obtain ⟨value, _selected, stepSupported⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨later, laterSupported, rfl⟩ := FinDist.support_map .. ▸ stepSupported
      change original ∈ ((policy.disclosureMemory next config.registry.weaken
        (Revelations.weaken config.revelations)
        (fun view => remember (view.back false)) later).map
          Sum.inr).support at member
      obtain ⟨original, restoredSupported, rfl⟩ := FinDist.support_map .. ▸ member
      apply congrArg Sum.inr
      apply ih (afterSample profile) policy (fun view => remember (view.back false))
        (fun view => recall (view.back false)) (sampleSuccessor name config value) ?_
        count later ?_ original restoredSupported
      · intro past remembered
        rw [back_sample_view] at remembered
        simpa only [Config.view, sampleSuccessor, back_sourceObserve,
          Bool.false_eq_true, ite_false] using coherent past remembered
      · simpa only [afterSample_update, BehavioralPolicy.normalizeDisclosureFrom,
          sampleSuccessor] using laterSupported

private theorem retractsDisclosure_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (ih : RetractsDisclosure (who := who) next) :
    RetractsDisclosure (who := who) (.commit name owner fresh guard next) := by
  intro profile policy remember recall config coherent count state reached original member
  cases count with
  | zero =>
      have equal : state = ProtocolState.entry _ config := by
        simpa only [Function.iterate_zero_apply, FinDist.mem_support_pure] using reached
      subst state
      exact retractsDisclosure_entry _ policy remember recall config coherent original member
  | succ count =>
      rw [ProtocolState.behavioralStatePrefix_commit
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.commit name owner fresh guard next) config.registry config.revelations remember))
        config count] at reached
      obtain ⟨binding, selected, stepSupported⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨later, laterSupported, rfl⟩ := FinDist.support_map .. ▸ stepSupported
      let posterior : DecisionView who ((name, .commitment owner payload) :: Γ) →
          FinDist (List (OwnAction Player L)) := fun view =>
        if own : owner = who then
          ((bindingMemoryLaw name payload remember (policy.1 own)
              (view.back true)).condOnFibre Prod.fst
            ((view.1.cells.get .here).getD .failure)).map Prod.snd
        else remember (view.back false)
      change original ∈ ((policy.2.disclosureMemory next
        ((commitSuccessor name guard config binding).registry)
        ((commitSuccessor name guard config binding).revelations)
        posterior later).map Sum.inr).support at member
      obtain ⟨original, restoredSupported, rfl⟩ := FinDist.support_map .. ▸ member
      apply congrArg Sum.inr
      apply ih (afterCommit profile) policy.2 posterior (bindingRecall name owner payload recall)
        (commitSuccessor name guard config binding) ?_ count later ?_ original restoredSupported
      · intro past remembered
        by_cases own : owner = who
        · subst who
          have observed :
              (sourceObserve owner (Env.cons (x := name) binding config.state)).cells.get
              (HasVar.here : HasVar ((name, .commitment owner payload) :: _) name
                (.commitment owner payload)) = some binding := by
            change (if owner = owner then some binding else none) = some binding
            exact ite_eq_left rfl
          have chosen : binding ∈ ((bindingMemoryLaw name payload remember (policy.1 rfl)
              (config.view owner)).map Prod.fst).support := by
            simpa only [commitKernel, Function.update_self,
              BehavioralPolicy.normalizeDisclosureFrom] using selected
          have remembered' : past ∈ (((bindingMemoryLaw name payload remember (policy.1 rfl)
              (config.view owner)).condOnFibre Prod.fst binding).map Prod.snd).support := by
            simpa only [posterior, dite_true, Config.view, commitSuccessor,
              Function.update_self, back_sourceObserve, ite_true, List.dropLast_concat,
              observed, Option.getD_some] using remembered
          simpa only [Config.withOwnHistory_view] using
            bindingMemoryLaw_recall name guard config remember recall (policy.1 rfl)
              coherent binding chosen past remembered'
        · have remembered' : past ∈ (remember (config.view who)).support := by
            simpa only [posterior, dite_eq_right own, Config.view, commitSuccessor,
              Function.update_of_ne (Ne.symm own), back_sourceObserve, Bool.false_eq_true,
              ite_false] using remembered
          simpa only [bindingRecall, own, decide_false, Bool.false_eq_true, ite_false,
            Config.view, commitSuccessor, Function.update_of_ne (Ne.symm own),
            back_sourceObserve, List.append_nil] using coherent past remembered'
      · simpa only [afterCommit_update, BehavioralPolicy.normalizeDisclosureFrom,
          commitSuccessor, posterior] using laterSupported

private theorem retractsDisclosure_reveal {Γ : SourceCtx Player L} {O : Finset VarId}
    (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (ih : RetractsDisclosure (who := who) next) :
    RetractsDisclosure (who := who)
      (.reveal published owner name fresh selected unresolved next) := by
  intro profile policy remember recall config coherent count state reached original member
  cases count with
  | zero =>
      have equal : state = ProtocolState.entry _ config := by
        simpa only [Function.iterate_zero_apply, FinDist.mem_support_pure] using reached
      subst state
      exact retractsDisclosure_entry _ policy remember recall config coherent original member
  | succ count =>
      rw [ProtocolState.behavioralStatePrefix_reveal
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.reveal published owner name fresh selected unresolved next)
          config.registry config.revelations remember)) config count] at reached
      obtain ⟨disclose, chosen, stepSupported⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨later, laterSupported, rfl⟩ := FinDist.support_map .. ▸ stepSupported
      let posterior : DecisionView who ((published, .publication payload) :: Γ) →
          FinDist (List (OwnAction Player L)) := fun view =>
        if own : owner = who then
          ((disclosureMemoryLaw published (own ▸ selected) config.registry config.revelations
              remember (policy.1 own) (view.back true)).condOnFibre Prod.fst
            (OwnAction.disclosure view.2.getLast?)).map Prod.snd
        else remember (view.back false)
      change original ∈ ((policy.2.disclosureMemory next
        ((revealSuccessor published selected config disclose).registry)
        ((revealSuccessor published selected config disclose).revelations)
        posterior later).map Sum.inr).support at member
      obtain ⟨original, restoredSupported, rfl⟩ := FinDist.support_map .. ▸ member
      apply congrArg Sum.inr
      apply ih (afterReveal profile) policy.2 posterior
        (publicationRecall published name owner payload recall)
        (revealSuccessor published selected config disclose) ?_ count later ?_
        original restoredSupported
      · intro past remembered
        by_cases own : owner = who
        · subst who
          have sampled : disclose ∈ ((disclosureMemoryLaw published selected config.registry
              config.revelations remember (policy.1 rfl) (config.view owner)).map
                Prod.fst).support :=
            by simpa only [revealKernel, Function.update_self,
              BehavioralPolicy.normalizeDisclosureFrom] using chosen
          have remembered' : past ∈ (((disclosureMemoryLaw published selected config.registry
              config.revelations remember (policy.1 rfl) (config.view owner)).condOnFibre
              Prod.fst disclose).map Prod.snd).support := by
            have recalled : OwnAction.disclosure (L := L)
                (some (.reveal owner name disclose)) = disclose := rfl
            simpa only [posterior, dite_true, Config.view, revealSuccessor,
              Function.update_self, back_sourceObserve, ite_true, List.dropLast_concat,
              List.getLast?_concat, recalled] using remembered
          simpa only [Config.withOwnHistory_view] using
            disclosureMemoryLaw_recall published selected config remember recall (policy.1 rfl)
              coherent disclose sampled past remembered'
        · have remembered' : past ∈ (remember (config.view who)).support := by
            simpa only [posterior, dite_eq_right own, Config.view, revealSuccessor,
              Function.update_of_ne (Ne.symm own), back_sourceObserve, Bool.false_eq_true,
              ite_false] using remembered
          unfold publicationRecall
          rw [show decide (owner = who) = false from decide_eq_false own]
          change recall (DecisionView.back false (sourceObserve who
            (revealSuccessor published selected config disclose).state, past)) ++ [] = _
          simpa only [Bool.false_eq_true, ite_false, Config.view, revealSuccessor,
            Function.update_of_ne (Ne.symm own), back_sourceObserve, List.append_nil]
            using coherent past remembered'
      · simpa only [afterReveal_update, BehavioralPolicy.normalizeDisclosureFrom,
          revealSuccessor, posterior] using laterSupported

/-- Every original state in the conditional memory law belongs to exactly
the current normalized information fiber. This follows from actual supported
execution, rather than from an assumed relationship between beliefs. -/
theorem disclosure_prefix_retracts {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile program) → (policy : BehavioralPolicy who program) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (recall : DecisionView who Γ → List (OwnAction Player L)) → (config : Config Player L Γ) →
    (∀ past ∈ (remember (config.view who)).support,
      recall (sourceObserve who config.state, past) = config.history who) →
    ∀ (count : Nat) (state : ProtocolState program),
      state ∈ ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosureFrom program config.registry
          config.revelations remember))))^[count]
        (FinDist.pure (ProtocolState.entry program config))).support →
    ∀ original ∈ (policy.disclosureMemory program config.registry config.revelations
        remember state).support,
      ProtocolState.normalizeDisclosureRecall program recall original = state
  | _, _, .ret result, profile, policy, remember, recall, config, coherent, count,
      state, reached, original, member => by
      have equal : state = config := by
        simpa only [ProtocolState.entry, ProtocolState.behavioralStatePrefix_ret,
          FinDist.mem_support_pure] using reached
      subst state
      exact retractsDisclosure_entry (.ret result) policy remember recall config coherent
        original member
  | _, _, .sample name fresh law next, profile, policy, remember, recall, config, coherent,
      count, state, reached, original, member =>
      retractsDisclosure_sample name fresh law next (disclosure_prefix_retracts next)
        profile policy remember recall config coherent count state reached original member
  | _, _, .commit name owner fresh guard next, profile, policy, remember, recall, config,
      coherent, count, state, reached, original, member =>
      retractsDisclosure_commit name owner fresh guard next (disclosure_prefix_retracts next)
        profile policy remember recall config coherent count state reached original member
  | _, _, .reveal published owner name fresh selected unresolved next,
      profile, policy, remember, recall, config, coherent, count, state,
      reached, original, member =>
      retractsDisclosure_reveal published owner name fresh selected unresolved next
        (disclosure_prefix_retracts next)
        profile policy remember recall config coherent count state reached original member

/-- The behavioral normalization is exactly the deterministic observation
compression of the original source prefix, for every finite prefix length. -/
theorem normalized_disclosure_prefix_map {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program) (config : Config Player L Γ) (count : Nat) :
    ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program config))).map
          (ProtocolState.normalizeDisclosureRecall (who := who) program (fun view => view.2)) =
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who
          (policy.normalizeDisclosures program config.registry config.revelations))))^[count]
        (FinDist.pure (ProtocolState.entry program config)) := by
  rw [normalized_disclosure_prefix program profile policy config count, FinDist.map_bind]
  trans ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
    (Function.update profile who
      (policy.normalizeDisclosures program config.registry config.revelations))))^[count]
    (FinDist.pure (ProtocolState.entry program config))).bind FinDist.pure
  · apply FinDist.bind_congr
    intro state reached
    calc
      _ = (policy.disclosureMemory program config.registry config.revelations
          (fun view => FinDist.pure view.2) state).map (fun _ => state) := by
            apply FinDist.map_congr_of_eq_on_support
            intro original member
            exact disclosure_prefix_retracts program profile policy
              (fun view => FinDist.pure view.2) (fun view => view.2) config
              (fun past supported => FinDist.mem_support_pure.mp supported)
              count state reached original member
      _ = FinDist.pure state := FinDist.map_const _ _
  · exact FinDist.bind_pure _

/-- The prefix projection preserves arbitrary correlated initial parameters
jointly. Static source obligations/publication positions are fixed by the
program point, while the initial cells and memories may be correlated. -/
theorem normalized_disclosure_prefix_joint_law {Γ : SourceCtx Player L} {O : Finset VarId}
    {Parameter : Type} (program : SourceProgram Player L Γ O)
    (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (registry : Registry Γ) (revelations : Revelations Γ) (belief : FinDist (Config Player L Γ))
    (registryEq : ∀ config ∈ belief.support, config.registry = registry)
    (revelationsEq : ∀ config ∈ belief.support, @config.revelations = @revelations)
    (parameter : Config Player L Γ → Parameter) (count : Nat) :
    (belief.bind fun config =>
      ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[count]
          (FinDist.pure (ProtocolState.entry program config))).map
            (fun state => (parameter config,
              ProtocolState.normalizeDisclosureRecall (who := who) program
                (fun view => view.2) state))) =
      belief.bind fun config =>
        ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
          (Function.update profile who
            (policy.normalizeDisclosures program registry revelations))))^[count]
          (FinDist.pure (ProtocolState.entry program config))).map
            (fun state => (parameter config, state)) := by
  apply FinDist.bind_congr
  intro config supported
  have equation := normalized_disclosure_prefix_map program profile policy config count
  rw [registryEq config supported, revelationsEq config supported] at equation
  simpa only [FinDist.map_comp, Function.comp_def] using
    congrArg (FinDist.map (fun state => (parameter config, state))) equation

end Vegas.SourceProgram
