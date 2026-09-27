/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.DisclosurePosterior
import Vegas.Game.SourceStateKernel

/-! # Original private intentions at every source protocol prefix

The restoration kernel below is a conditional law on the existing protocol
states. It changes only one owner's remembered actions. Prefix execution is
the existing source `Vegas.SourceProgram.ProtocolState.behavioralStateStep`.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {who : Player}

/-- Restore the current owner's original intentions using the same local
posterior that defines its normalized behavioral policy. -/
def BehavioralPolicy.disclosureMemory {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Registry Γ → Revelations Γ →
    (DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    BehavioralPolicy who program → ProtocolState program → FinDist (ProtocolState program)
  | _, _, .ret _, _, _, remember, _, config => config.restoreMemory who remember
  | _, _, .sample _ _ _ next, registry, revelations, remember, policy, state =>
      Sum.elim
        (fun config => (config.restoreMemory who remember).map Sum.inl)
        (fun rest => (disclosureMemory next registry.weaken revelations.weaken
          (fun view => remember (view.back false)) policy rest).map Sum.inr) state
  | _, _, .commit (payload := payload) name owner _ guard next,
      registry, revelations, remember, policy, state =>
      Sum.elim
        (fun config => (config.restoreMemory who remember).map Sum.inl)
        (fun rest => (disclosureMemory next
          (({ owner := owner, subject := name, payload := payload, source := .here,
              guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
          (fun view => if own : owner = who then
            ((bindingMemoryLaw name payload remember (policy.1 own)
                (view.back true)).condOnFibre Prod.fst
              ((view.1.cells.get .here).getD .failure)).map Prod.snd
          else remember (view.back false)) policy.2 rest).map Sum.inr) state
  | _, _, .reveal published owner _ _ selected _ next,
      registry, revelations, remember, policy, state =>
      Sum.elim
        (fun config => (config.restoreMemory who remember).map Sum.inl)
        (fun rest => (disclosureMemory next registry.weaken
          (revelations.reveal (published := published) selected)
          (fun view => if own : owner = who then
            ((disclosureMemoryLaw published (own ▸ selected) registry revelations remember
                (policy.1 own) (view.back true)).condOnFibre Prod.fst
              (OwnAction.disclosure view.2.getLast?)).map Prod.snd
          else remember (view.back false)) policy.2 rest).map Sum.inr) state

theorem BehavioralPolicy.disclosureMemory_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (registry : Registry Γ)
    (revelations : Revelations Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (policy : BehavioralPolicy who program) (config : Config Player L Γ) :
    policy.disclosureMemory program registry revelations remember
        (ProtocolState.entry program config) =
      (config.restoreMemory who remember).map (ProtocolState.entry program) := by
  cases program
  · exact (FinDist.map_id _).symm
  all_goals rfl

namespace ProtocolState

variable [Fintype Player] {Γ : SourceCtx Player L} {O : Finset VarId}

theorem behavioralStateStep_sample_entry {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (.sample name fresh law next)) (config : Config Player L Γ) :
    behavioralStateStep (.sample name fresh law next) profile (.inl config) =
      (L.evalDist law (sourcePublicEnv config.state)).map fun value =>
        Sum.inr (entry next (sampleSuccessor name config value)) := by
  classical
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl,
    FinDist.bind_const]

theorem behavioralStateStep_sample_tail {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (.sample name fresh law next)) (state : ProtocolState next) :
    behavioralStateStep (.sample name fresh law next) profile (.inr state) =
      (behavioralStateStep next (afterSample profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterSample, step, FinDist.map_bind]

theorem behavioralStateStep_commit_entry {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inl config) =
      (commitKernel profile (config.view owner)).map fun binding =>
        Sum.inr (entry next (commitSuccessor name guard config binding)) := by
  classical
  let program := SourceProgram.commit name owner fresh guard next
  let laws player := (profile player).protocolAction program
    (observe player program (.inl config))
  let advance (action : Option (OwnAction Player L)) :=
    Sum.inr (α := Config Player L Γ)
      (entry next (commitSuccessor name guard config (OwnAction.binding owner name payload action)))
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl]
  change ((FinDist.pi laws).bind fun joint => FinDist.pure (advance (joint owner))) = _
  rw [← FinDist.map_eq_bind]
  change (FinDist.pi laws).map (advance ∘ fun joint => joint owner) = _
  rw [← FinDist.map_comp, FinDist.map_apply_pi]
  simp only [laws, program, BehavioralPolicy.protocolAction, observe, Sum.elim_inl,
    dite_true, FinDist.map_comp, Function.comp_def, advance, OwnAction.binding_commit, commitKernel]

theorem behavioralStateStep_commit_tail {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (state : ProtocolState next) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inr state) =
      (behavioralStateStep next (afterCommit profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterCommit, step, FinDist.map_bind]

theorem behavioralStatePrefix_ret
    (result : List (Player × L.Expr (SourcePublicCtx L Γ) L.int))
    (profile : BehavioralProfile (.ret result)) (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (behavioralStateStep (.ret result) profile))^[count]
      (FinDist.pure config) = FinDist.pure config := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, FinDist.pure_bind, behavioralStateStep_ret]

theorem behavioralStatePrefix_sample {name : VarId} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
    {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}
    (profile : BehavioralProfile (.sample name fresh law next))
    (config : Config Player L Γ) (count : Nat) :
    (fun distribution => distribution.bind (behavioralStateStep
      (.sample name fresh law next) profile))^[count + 1]
        (FinDist.pure (entry _ config)) =
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        ((fun distribution => distribution.bind (behavioralStateStep next
          (afterSample profile)))^[count]
          (FinDist.pure (entry next (sampleSuccessor name config value)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, FinDist.pure_bind, behavioralStateStep_sample_entry]
      simp only [Function.iterate_zero_apply, FinDist.map_pure, ← FinDist.map_eq_bind]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro value _
      rw [Function.iterate_succ_apply', FinDist.bind_map, FinDist.map_bind]
      exact FinDist.bind_congr fun state _ => behavioralStateStep_sample_tail profile state

theorem behavioralStatePrefix_commit {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh : name ∉ Γ.map Prod.fst} {guard : SourceGuard L Γ owner name payload}
    {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) (count : Nat) :
    (fun distribution => distribution.bind (behavioralStateStep
      (.commit name owner fresh guard next) profile))^[count + 1]
        (FinDist.pure (entry _ config)) =
      (commitKernel profile (config.view owner)).bind fun binding =>
        ((fun distribution => distribution.bind (behavioralStateStep next
          (afterCommit profile)))^[count]
          (FinDist.pure (entry next (commitSuccessor name guard config binding)))).map
            Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, FinDist.pure_bind, behavioralStateStep_commit_entry]
      simp only [Function.iterate_zero_apply, FinDist.map_pure, ← FinDist.map_eq_bind]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro binding _
      rw [Function.iterate_succ_apply', FinDist.bind_map, FinDist.map_bind]
      exact FinDist.bind_congr fun state _ => behavioralStateStep_commit_tail profile state

end ProtocolState

variable [Fintype Player]

private def DisintegratesDisclosure {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : Prop :=
  ∀ (profile : BehavioralProfile program) (policy : BehavioralPolicy who program)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (config : Config Player L Γ) (count : Nat),
    ((config.restoreMemory who remember).bind fun original =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program original))) =
      ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosureFrom program config.registry
          config.revelations remember))))^[count]
        (FinDist.pure (ProtocolState.entry program config))).bind
          (policy.disclosureMemory program config.registry config.revelations remember)

private theorem disintegratesDisclosure_zero {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (config : Config Player L Γ) :
    ((config.restoreMemory who remember).bind fun original =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[0]
        (FinDist.pure (ProtocolState.entry program original))) =
      ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosureFrom program config.registry
          config.revelations remember))))^[0]
        (FinDist.pure (ProtocolState.entry program config))).bind
          (policy.disclosureMemory program config.registry config.revelations remember) := by
  simp only [Function.iterate_zero_apply, FinDist.pure_bind,
    BehavioralPolicy.disclosureMemory_entry, ← FinDist.map_eq_bind]

private theorem disintegratesDisclosure_sample {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (next : SourceProgram Player L ((name, .publicData payload) :: Γ) O)
    (ih : DisintegratesDisclosure (who := who) next) :
    DisintegratesDisclosure (who := who) (.sample name fresh law next) := by
  intro profile policy remember config count
  cases count with
  | zero => exact disintegratesDisclosure_zero _ profile policy remember config
  | succ count =>
      conv_lhs =>
        arg 2
        intro original
        rw [ProtocolState.behavioralStatePrefix_sample
          (Function.update profile who policy) original count]
      rw [ProtocolState.behavioralStatePrefix_sample
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.sample name fresh law next) config.registry config.revelations remember))
        config count]
      simp only [Config.restoreMemory,
        FinDist.bind_map, Config.withOwnHistory, afterSample_update,
        BehavioralPolicy.normalizeDisclosureFrom, FinDist.bind_bind,
        BehavioralPolicy.disclosureMemory, Sum.elim_inr]
      rw [FinDist.bind_comm]
      apply FinDist.bind_congr
      intro value _
      have nextLaw := congrArg (FinDist.map (Sum.inr (α := Config Player L Γ)))
        (ih (afterSample profile) policy (fun view => remember (view.back false))
          (sampleSuccessor name config value) count)
      simpa only [Config.restoreMemory, FinDist.bind_map, Config.withOwnHistory,
        Config.view, sampleSuccessor, back_sourceObserve, Bool.false_eq_true, ite_false,
        FinDist.map_bind] using nextLaw

private theorem disintegratesDisclosure_commit {Γ : SourceCtx Player L} {O : Finset VarId}
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (ih : DisintegratesDisclosure (who := who) next) :
    DisintegratesDisclosure (who := who) (.commit name owner fresh guard next) := by
  intro profile policy remember config count
  cases count with
  | zero => exact disintegratesDisclosure_zero _ profile policy remember config
  | succ count =>
      conv_lhs =>
        arg 2
        intro original
        rw [ProtocolState.behavioralStatePrefix_commit
          (Function.update profile who policy) original count]
      rw [ProtocolState.behavioralStatePrefix_commit
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.commit name owner fresh guard next) config.registry config.revelations remember))
        config count]
      by_cases owned : owner = who
      · subst who
        simp only [Config.restoreMemory, FinDist.bind_map, commitKernel, Function.update_self,
          Config.withOwnHistory_view, afterCommit_update,
          BehavioralPolicy.normalizeDisclosureFrom, FinDist.bind_bind,
          BehavioralPolicy.disclosureMemory, Sum.elim_inr]
        have localLaw := bindingMemoryLaw_disintegrate name payload remember (policy.1 rfl)
          (config.view owner) (fun binding past =>
            ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep next
              (Function.update (afterCommit profile) owner policy.2)))^[count]
              (FinDist.pure (ProtocolState.entry next
                ((commitSuccessor name guard config binding).withOwnHistory owner past)))).map
                  (Sum.inr (α := Config Player L Γ)))
        simp only [Config.view, ← commitSuccessor_withOwnHistory] at localLaw
        erw [localLaw]
        simp only [FinDist.bind_map]
        apply FinDist.bind_congr
        rintro ⟨binding, _⟩ _
        have observed : (sourceObserve owner (Env.cons (x := name) binding config.state)).cells.get
            (HasVar.here : HasVar ((name, .commitment owner payload) :: _) name
              (.commitment owner payload)) = some binding := by
          change (if owner = owner then some binding else none) = some binding
          exact ite_eq_left rfl
        have nextLaw := congrArg (FinDist.map (Sum.inr (α := Config Player L Γ)))
          (ih (afterCommit profile) policy.2
            (fun nextView => if own : owner = owner then
              ((bindingMemoryLaw name payload remember (policy.1 own)
                  (nextView.back true)).condOnFibre Prod.fst
                ((nextView.1.cells.get .here).getD .failure)).map Prod.snd
            else remember (nextView.back false))
            (commitSuccessor name guard config binding) count)
        simpa only [Config.restoreMemory, FinDist.bind_map, Config.view, commitSuccessor,
          Config.withOwnHistory, Function.update_self, Function.update_idem,
          dite_true, back_sourceObserve, ite_true, List.dropLast_concat, observed,
          Option.getD_some, FinDist.map_bind] using nextLaw
      · simp only [Config.restoreMemory, FinDist.bind_map, commitKernel,
          Function.update_of_ne owned, Config.withOwnHistory_foreign_view _ _ owned,
          afterCommit_update, BehavioralPolicy.normalizeDisclosureFrom, FinDist.bind_bind,
          BehavioralPolicy.disclosureMemory, Sum.elim_inr]
        rw [FinDist.bind_comm]
        apply FinDist.bind_congr
        intro binding _
        have nextLaw := congrArg (FinDist.map (Sum.inr (α := Config Player L Γ)))
          (ih (afterCommit profile) policy.2
            (fun nextView => if own : owner = who then
              ((bindingMemoryLaw name payload remember (policy.1 own)
                  (nextView.back true)).condOnFibre Prod.fst
                ((nextView.1.cells.get .here).getD .failure)).map Prod.snd
            else remember (nextView.back false))
            (commitSuccessor name guard config binding) count)
        simpa only [Config.restoreMemory, FinDist.bind_map, Config.withOwnHistory,
          Config.view, commitSuccessor, dite_eq_right owned,
          Function.update_of_ne (Ne.symm owned), Function.update_of_ne owned,
          back_sourceObserve, Bool.false_eq_true,
          ite_false, Function.update_comm (Ne.symm owned), FinDist.map_bind] using nextLaw

private theorem disintegratesDisclosure_reveal {Γ : SourceCtx Player L} {O : Finset VarId}
    (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (ih : DisintegratesDisclosure (who := who) next) :
    DisintegratesDisclosure (who := who)
      (.reveal published owner name fresh selected unresolved next) := by
  intro profile policy remember config count
  cases count with
  | zero => exact disintegratesDisclosure_zero _ profile policy remember config
  | succ count =>
      conv_lhs =>
        arg 2
        intro original
        rw [ProtocolState.behavioralStatePrefix_reveal
          (Function.update profile who policy) original count]
      rw [ProtocolState.behavioralStatePrefix_reveal
        (Function.update profile who (policy.normalizeDisclosureFrom
          (.reveal published owner name fresh selected unresolved next)
          config.registry config.revelations remember)) config count]
      by_cases owned : owner = who
      · subst who
        simp only [Config.restoreMemory, FinDist.bind_map, revealKernel, Function.update_self,
          Config.withOwnHistory_view, afterReveal_update,
          BehavioralPolicy.normalizeDisclosureFrom, FinDist.bind_bind,
          BehavioralPolicy.disclosureMemory, Sum.elim_inr]
        have localLaw := disclosureMemoryLaw_disintegrate published selected config.registry
          config.revelations remember (policy.1 rfl) (config.view owner)
          (fun disclose past =>
            ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep next
              (Function.update (afterReveal profile) owner policy.2)))^[count]
              (FinDist.pure (ProtocolState.entry next
                ((revealSuccessor published selected config disclose).withOwnHistory owner
                  past)))).map (Sum.inr (α := Config Player L Γ)))
        simp only [Config.view, effectiveDisclosureView_observe,
          revealSuccessor_effective_withOwnHistory, ← revealSuccessor_withOwnHistory] at localLaw
        erw [localLaw]
        simp only [FinDist.bind_map]
        apply FinDist.bind_congr
        rintro ⟨disclose, _⟩ _
        have nextLaw := congrArg (FinDist.map (Sum.inr (α := Config Player L Γ)))
          (ih (afterReveal profile) policy.2
            (fun nextView => if own : owner = owner then
              ((disclosureMemoryLaw published (own ▸ selected) config.registry config.revelations
                  remember (policy.1 own) (nextView.back true)).condOnFibre Prod.fst
                (OwnAction.disclosure nextView.2.getLast?)).map Prod.snd
            else remember (nextView.back false))
            (revealSuccessor published selected config disclose) count)
        have recalled : OwnAction.disclosure (L := L)
            (some (.reveal owner name disclose)) = disclose := rfl
        simpa only [Config.restoreMemory, FinDist.bind_map, Config.view, revealSuccessor,
          Config.withOwnHistory, Function.update_self, Function.update_idem,
          dite_true, back_sourceObserve, ite_true, List.dropLast_concat,
          List.getLast?_concat, recalled, FinDist.map_bind] using nextLaw
      · simp only [Config.restoreMemory, FinDist.bind_map, revealKernel,
          Function.update_of_ne owned, Config.withOwnHistory_foreign_view _ _ owned,
          afterReveal_update, BehavioralPolicy.normalizeDisclosureFrom, FinDist.bind_bind,
          BehavioralPolicy.disclosureMemory, Sum.elim_inr]
        rw [FinDist.bind_comm]
        apply FinDist.bind_congr
        intro disclose _
        have nextLaw := congrArg (FinDist.map (Sum.inr (α := Config Player L Γ)))
          (ih (afterReveal profile) policy.2
            (fun nextView => if own : owner = who then
              ((disclosureMemoryLaw published (own ▸ selected) config.registry config.revelations
                  remember (policy.1 own) (nextView.back true)).condOnFibre Prod.fst
                (OwnAction.disclosure nextView.2.getLast?)).map Prod.snd
            else remember (nextView.back false))
            (revealSuccessor published selected config disclose) count)
        simpa only [Config.restoreMemory, FinDist.bind_map, Config.withOwnHistory,
          Config.view, revealSuccessor, dite_eq_right owned,
          Function.update_of_ne (Ne.symm owned), Function.update_of_ne owned,
          back_sourceObserve, Bool.false_eq_true,
          ite_false, Function.update_comm (Ne.symm owned), FinDist.map_bind] using nextLaw

/-- Every finite prefix retains an exact conditional law of the original
owner's intentions. The other players' entire private histories and all game
data are part of this equality, not merely the public outcome. -/
theorem disclosure_prefix_disintegration {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile program) → (policy : BehavioralPolicy who program) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (config : Config Player L Γ) → (count : Nat) →
    ((config.restoreMemory who remember).bind fun original =>
      (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program original))) =
      ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who (policy.normalizeDisclosureFrom program config.registry
          config.revelations remember))))^[count]
        (FinDist.pure (ProtocolState.entry program config))).bind
          (policy.disclosureMemory program config.registry config.revelations remember)
  | _, _, .ret result, profile, policy, remember, config, count => by
      simp only [ProtocolState.entry, ProtocolState.behavioralStatePrefix_ret, FinDist.pure_bind,
        BehavioralPolicy.disclosureMemory, FinDist.bind_pure]
  | _, _, .sample name fresh law next, profile, policy, remember, config, count =>
      disintegratesDisclosure_sample name fresh law next (disclosure_prefix_disintegration next)
        profile policy remember config count
  | _, _, .commit name owner fresh guard next, profile, policy, remember, config, count =>
      disintegratesDisclosure_commit name owner fresh guard next
        (disclosure_prefix_disintegration next) profile policy remember config count
  | _, _, .reveal published owner name fresh selected unresolved next,
      profile, policy, remember, config, count =>
      disintegratesDisclosure_reveal published owner name fresh selected unresolved next
        (disclosure_prefix_disintegration next) profile policy remember config count

/-- With the actual initial recall, restoration begins as the identity. Thus
the original protocol prefix is recovered from the normalized prefix itself. -/
theorem normalized_disclosure_prefix {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (policy : BehavioralPolicy who program) (config : Config Player L Γ) (count : Nat) :
    (fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
      (Function.update profile who policy)))^[count]
        (FinDist.pure (ProtocolState.entry program config)) =
      ((fun distribution => distribution.bind (ProtocolState.behavioralStateStep program
        (Function.update profile who
          (policy.normalizeDisclosures program config.registry config.revelations))))^[count]
        (FinDist.pure (ProtocolState.entry program config))).bind
          (policy.disclosureMemory program config.registry config.revelations
            (fun view => FinDist.pure view.2)) := by
  have equality := disclosure_prefix_disintegration program profile policy
    (fun view => FinDist.pure view.2) config count
  simpa only [Config.restoreMemory, Config.view, FinDist.map_pure, FinDist.pure_bind,
    Config.withOwnHistory, Function.update_eq_self, BehavioralPolicy.normalizeDisclosures]
    using equality

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem restoreMemory_own_view {Γ : SourceCtx Player L}
    (config : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) :
    (config.restoreMemory who remember).map (Config.view who) =
      (remember (config.view who)).map (fun past => ((config.view who).1, past)) := by
  simp only [Config.restoreMemory, FinDist.map_comp, Function.comp_def,
    Config.view, Config.withOwnHistory, Function.update_self]

omit [Fintype Player] [IExpr.ResultTypes L] in
private theorem restoreMemory_own_view_congr {Γ : SourceCtx Player L}
    (left right : Config Player L Γ)
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L)))
    (same : left.view who = right.view who) :
    (left.restoreMemory who remember).map (Config.view who) =
      (right.restoreMemory who remember).map (Config.view who) := by
  rw [restoreMemory_own_view, restoreMemory_own_view, same]

omit [Fintype Player] in
/-- The restoration weights are measurable in this player's own current
observation, even though the full prefix retains arbitrary hidden states. -/
theorem BehavioralPolicy.disclosureMemory_observation_congr {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (registry : Registry Γ) →
    (revelations : Revelations Γ) →
    (remember : DecisionView who Γ → FinDist (List (OwnAction Player L))) →
    (policy : BehavioralPolicy who program) → (left right : ProtocolState program) →
    ProtocolState.observe who program left = ProtocolState.observe who program right →
    (policy.disclosureMemory program registry revelations remember left).map
        (ProtocolState.observe who program) =
      (policy.disclosureMemory program registry revelations remember right).map
        (ProtocolState.observe who program)
  | _, _, .ret _, _, _, remember, _, left, right, same => by
      simp only [disclosureMemory, ProtocolState.observe, restoreMemory_own_view]
      exact congrArg (fun view : DecisionView who _ =>
        (remember view).map (fun past => (view.1, past))) same
  | _, _, .sample _ _ _ next, registry, revelations, remember, policy,
      left, right, same => by
      cases left with
      | inl left =>
          cases right with
          | inl right =>
              have equal := Sum.inl.inj same
              simpa only [disclosureMemory, Sum.elim_inl, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inl (β := ProtocolView who next)))
                  (restoreMemory_own_view_congr left right remember equal)
          | inr _ => cases same
      | inr left =>
          cases right with
          | inl _ => cases same
          | inr right =>
              have equal := Sum.inr.inj same
              have recur := policy.disclosureMemory_observation_congr next registry.weaken
                revelations.weaken (fun view => remember (view.back false)) left right equal
              simpa only [disclosureMemory, Sum.elim_inr, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inr (α := DecisionView who _))) recur
  | _, _, .commit (payload := payload) name owner _ guard next, registry, revelations,
      remember, policy, left, right, same => by
      cases left with
      | inl left =>
          cases right with
          | inl right =>
              have equal := Sum.inl.inj same
              simpa only [disclosureMemory, Sum.elim_inl, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inl (β := ProtocolView who next)))
                  (restoreMemory_own_view_congr left right remember equal)
          | inr _ => cases same
      | inr left =>
          cases right with
          | inl _ => cases same
          | inr right =>
              have equal := Sum.inr.inj same
              have recur := policy.2.disclosureMemory_observation_congr next
                (({ owner := owner, subject := name, payload := payload, source := .here,
                    guard := guard.weaken } : Obligation _) :: registry.weaken) revelations.weaken
                (fun view => if own : owner = who then
                  ((bindingMemoryLaw name payload remember (policy.1 own)
                      (view.back true)).condOnFibre Prod.fst
                    ((view.1.cells.get .here).getD .failure)).map Prod.snd
                else remember (view.back false)) left right equal
              simpa only [disclosureMemory, Sum.elim_inr, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inr (α := DecisionView who _))) recur
  | _, _, .reveal published owner _ _ selected _ next, registry, revelations,
      remember, policy, left, right, same => by
      cases left with
      | inl left =>
          cases right with
          | inl right =>
              have equal := Sum.inl.inj same
              simpa only [disclosureMemory, Sum.elim_inl, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inl (β := ProtocolView who next)))
                  (restoreMemory_own_view_congr left right remember equal)
          | inr _ => cases same
      | inr left =>
          cases right with
          | inl _ => cases same
          | inr right =>
              have equal := Sum.inr.inj same
              have recur := policy.2.disclosureMemory_observation_congr next registry.weaken
                (revelations.reveal (published := published) selected)
                (fun view => if own : owner = who then
                  ((disclosureMemoryLaw published (own ▸ selected) registry revelations remember
                      (policy.1 own) (view.back true)).condOnFibre Prod.fst
                    (OwnAction.disclosure view.2.getLast?)).map Prod.snd
                else remember (view.back false)) left right equal
              simpa only [disclosureMemory, Sum.elim_inr, FinDist.map_comp,
                ProtocolState.observe, Function.comp_def] using
                congrArg (FinDist.map (Sum.inr (α := DecisionView who _))) recur

end Vegas.SourceProgram
