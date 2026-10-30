/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceContinuation

/-! # One-step reductions for the actual source protocol

The syntactic policy supplies the action marginals in the source protocol
step. These equations reduce public sampling, binding and disclosure and
commute with the protocol's residual-state embedding. They introduce no
alternative runner.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

open Classical in
/-- The source protocol step after drawing the encoded syntactic action
marginals, retaining the protocol's ordinary terminal absorption. -/
def behavioralStateStep {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : ProtocolState program) : PMF (ProtocolState program) :=
  if terminal program state then PMF.pure state else
    (independentProduct fun who => (profile who).protocolAction program
      (observe who program state)).bind (step program state)

section Sample

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId} {payload : L.Ty}
  {fresh : name ∉ Γ.map Prod.fst} {law : L.DistExpr (SourcePublicCtx L Γ) payload}
  {next : SourceProgram Player L ((name, .publicData payload) :: Γ) O}

/-- The source chance step draws the original public distribution and does
not depend on the players' simultaneous action marginals. -/
theorem behavioralStateStep_sample_entry
    (profile : BehavioralProfile (.sample name fresh law next))
    (config : Config Player L Γ) :
    behavioralStateStep (.sample name fresh law next) profile (.inl config) =
      (L.evalDist law (sourcePublicEnv config.state)).map (fun value =>
        Sum.inr (entry next (sampleSuccessor name config value))) := by
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl, PMF.bind_const]

theorem behavioralStateStep_sample_tail
    (profile : BehavioralProfile (.sample name fresh law next))
    (state : ProtocolState next) :
    behavioralStateStep (.sample name fresh law next) profile (.inr state) =
      (behavioralStateStep next (afterSample profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped, PMF.pure_map]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterSample, step, PMF.map_bind]

/-- A source prefix samples once and continues in the same residual protocol. -/
theorem behavioralStatePrefix_sample
    (profile : BehavioralProfile (.sample name fresh law next))
    (config : Config Player L Γ) (count : Nat) :
    (fun distribution => distribution.bind (behavioralStateStep
      (.sample name fresh law next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (L.evalDist law (sourcePublicEnv config.state)).bind fun value =>
        ((fun distribution => distribution.bind
          (behavioralStateStep next (afterSample profile)))^[count]
          (PMF.pure (entry next (sampleSuccessor name config value)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_sample_entry]
      simp only [Function.iterate_zero_apply, ← PMF.bind_pure_comp, Function.comp_def,
          PMF.pure_bind]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro value _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_sample_tail profile state

end Sample

section Binding

variable {Γ : SourceCtx Player L} {O : Finset VarId} {name : VarId}
  {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
  {guard : SourceGuard L Γ owner name payload}
  {next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O)}

/-- Only the owner's actual binding marginal affects the source commitment
step; no support conditioning or new commitment interface is introduced. -/
theorem behavioralStateStep_commit_entry
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inl config) =
      (if inactive : owner ∈ (config.view owner).defaulted then PMF.pure none
        else commitKernel profile (config.view owner) inactive).map (fun value =>
        Sum.inr (entry next (commitSuccessor name guard config value))) := by
  classical
  let program := SourceProgram.commit name owner fresh guard next
  let laws who := (profile who).protocolAction program (observe who program (.inl config))
  let advance (action : Option (OwnAction Player L)) :=
    Sum.inr (α := Config Player L Γ)
      (entry next (commitSuccessor name guard config (OwnAction.binding owner name payload action)))
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl]
  change ((independentProduct laws).bind fun joint => PMF.pure (advance (joint owner))) = _
  change (independentProduct laws).map (advance ∘ fun joint => joint owner) = _
  rw [← PMF.map_comp, independentProduct_map_eval]
  change (laws owner).map
    ((fun choice => Sum.inr (entry next (commitSuccessor name guard config choice))) ∘
      OwnAction.binding owner name payload) = _
  rw [← PMF.map_comp]
  exact congrArg
    (PMF.map fun choice => Sum.inr (α := Config Player L Γ)
      (entry next (commitSuccessor name guard config choice)))
    (BehavioralPolicy.protocolAction_commit_binding profile (config.view owner))

theorem behavioralStateStep_commit_tail
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (state : ProtocolState next) :
    behavioralStateStep (.commit name owner fresh guard next) profile (.inr state) =
      (behavioralStateStep next (afterCommit profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped, PMF.pure_map]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterCommit, step, PMF.map_bind]

/-- A finite source prefix draws the original binding policy and then executes
its residual source protocol, retaining the exact private binding choice. -/
theorem behavioralStatePrefix_commit
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (behavioralStateStep
      (.commit name owner fresh guard next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (if inactive : owner ∈ (config.view owner).defaulted then PMF.pure none
        else commitKernel profile (config.view owner) inactive).bind fun value =>
        ((fun law => law.bind (behavioralStateStep next (afterCommit profile)))^[count]
          (PMF.pure (entry next (commitSuccessor name guard config value)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_commit_entry]
      simp only [Function.iterate_zero_apply, ← PMF.bind_pure_comp, Function.comp_def,
          PMF.pure_bind]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro value _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_commit_tail profile state

end Binding

variable {Γ : SourceCtx Player L} {O : Finset VarId} {published name : VarId}
  {owner : Player} {payload : L.Ty} {fresh : published ∉ Γ.map Prod.fst}
  {source : HasVar Γ name (.commitment owner payload)} {unresolved : name ∈ O}
  {next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name)}

theorem behavioralStateStep_reveal_entry
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (config : Config Player L Γ) :
    behavioralStateStep (.reveal published owner name fresh source unresolved next)
        profile (.inl config) =
      (if inactive : owner ∈ (config.view owner).defaulted then PMF.pure false
        else revealKernel profile (config.view owner) inactive).map (fun disclose =>
        Sum.inr (entry next (revealSuccessor published source config disclose))) := by
  classical
  let program := SourceProgram.reveal published owner name fresh source unresolved next
  let laws who := (profile who).protocolAction program (observe who program (.inl config))
  let advance (action : Option (OwnAction Player L)) :=
    Sum.inr (α := Config Player L Γ)
      (entry next (revealSuccessor published source config (OwnAction.disclosure action)))
  simp only [behavioralStateStep, terminal, ite_false, step, Sum.elim_inl]
  change ((independentProduct laws).bind fun joint => PMF.pure (advance (joint owner))) = _
  change (independentProduct laws).map (advance ∘ fun joint => joint owner) = _
  rw [← PMF.map_comp, independentProduct_map_eval]
  change (laws owner).map
    ((fun disclose => Sum.inr (entry next (revealSuccessor published source config disclose))) ∘
      OwnAction.disclosure) = _
  rw [← PMF.map_comp]
  exact congrArg
    (PMF.map fun disclose => Sum.inr (α := Config Player L Γ)
      (entry next (revealSuccessor published source config disclose)))
    (BehavioralPolicy.protocolAction_reveal_disclosure profile (config.view owner))

theorem behavioralStateStep_reveal_tail
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (state : ProtocolState next) :
    behavioralStateStep (.reveal published owner name fresh source unresolved next)
        profile (.inr state) =
      (behavioralStateStep next (afterReveal profile) state).map Sum.inr := by
  classical
  by_cases stopped : terminal next state
  · simp [behavioralStateStep, terminal, stopped, PMF.pure_map]
  · simp only [behavioralStateStep, terminal, stopped, ite_false, observe,
      BehavioralPolicy.protocolAction, Sum.elim_inr, afterReveal, step, PMF.map_bind]

/-- A finite source prefix first draws its actual reveal choice and then
executes the residual source protocol. -/
theorem behavioralStatePrefix_reveal
    (profile : BehavioralProfile (.reveal published owner name fresh source unresolved next))
    (config : Config Player L Γ) (count : Nat) :
    (fun law => law.bind (behavioralStateStep
      (.reveal published owner name fresh source unresolved next) profile))^[count + 1]
        (PMF.pure (entry _ config)) =
      (if inactive : owner ∈ (config.view owner).defaulted then PMF.pure false
        else revealKernel profile (config.view owner) inactive).bind fun disclose =>
        ((fun law => law.bind (behavioralStateStep next (afterReveal profile)))^[count]
          (PMF.pure (entry next
            (revealSuccessor published source config disclose)))).map Sum.inr := by
  induction count with
  | zero =>
      simp only [entry]
      rw [Function.iterate_one, PMF.pure_bind, behavioralStateStep_reveal_entry]
      simp only [Function.iterate_zero_apply, ← PMF.bind_pure_comp, Function.comp_def,
          PMF.pure_bind]
      rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply', ih, PMF.bind_bind]
      apply bind_congr_on_support _
      intro disclose _supported
      rw [Function.iterate_succ_apply', PMF.bind_map, PMF.map_bind]
      exact bind_congr_on_support _ fun state _ => behavioralStateStep_reveal_tail profile state

/-- **The behavioral step at an actor's point** draws the actor's choice and
steps with it. -/
theorem behavioralStateStep_eq_bind_of_actor {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (state : ProtocolState program) (owner : Player)
    (acts : ∀ player, ProtocolView.actor player program (observe player program state) =
      some owner) :
    behavioralStateStep program profile state =
      ((profile owner).protocolAction program (observe owner program state)).bind
        fun choice => step program state (fun _ => choice) := by
  classical
  unfold behavioralStateStep
  rw [ite_eq_right_iff.mpr fun stopped =>
    (not_terminal_of_actor owner owner program state (acts owner) stopped).elim]
  calc (independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).bind (step program state)
      = (independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).bind
          (fun joint => step program state (fun _ => joint owner)) := by
        congr 1
        funext joint
        exact step_eq_of_actor owner owner program state joint (acts owner)
    _ = ((independentProduct fun player => (profile player).protocolAction program
          (observe player program state)).map (fun joint => joint owner)).bind
          (fun choice => step program state (fun _ => choice)) := by
        rw [PMF.bind_map]
        rfl
    _ = _ := by rw [independentProduct_map_eval]

/-- One source step followed by the source continuation is the source
continuation. -/
theorem behavioralStateStep_continuation
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (state : ProtocolState program) :
    (behavioralStateStep program profile state).bind
      (continuationLaw program profile) =
        continuationLaw program profile state := by
  classical
  unfold behavioralStateStep
  split
  · exact PMF.pure_bind _ _
  · rename_i running
    exact continuationLaw_behavioral_step program profile state running
      (independentProduct fun who => (profile who).protocolAction program
        (ProtocolState.observe who program state)) (fun who => independentProduct_map_eval _ who)

/-- A harmonic law is obtained by evaluating its terminal callback under source execution. -/
theorem continuationLaw_bind_terminal {Ω : Type} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    (law : ProtocolState program → PMF Ω) →
    (∀ state, (behavioralStateStep program profile state).bind law = law state) →
    ∀ state, (continuationLaw program profile state).bind
      (fun config => law (terminalState program config)) = law state
  | _, _, .ret _, _, _, _, _ => by simp [continuationLaw, terminalState]
  | _, _, .sample name fresh distribution next, profile, law, harmonic, state => by
      have tail : ∀ state, (behavioralStateStep next (afterSample profile) state).bind
          (fun target => law (.inr target)) = law (.inr state) := by
        intro state
        have original := harmonic (.inr state)
        rw [behavioralStateStep_sample_tail, PMF.bind_map] at original
        exact original
      cases state with
      | inr state =>
          exact continuationLaw_bind_terminal next (afterSample profile)
            (fun target => law (.inr target)) tail state
      | inl config =>
          rw [← harmonic (.inl config), behavioralStateStep_sample_entry, PMF.bind_map]
          simp only [continuationLaw, Sum.elim_inl, runFrom_sample, PMF.bind_bind]
          apply bind_congr_on_support _
          intro value _
          simpa only [continuationLaw_entry, terminalState, Function.comp_apply] using
            continuationLaw_bind_terminal next (afterSample profile)
              (fun target => law (.inr target)) tail
              (entry next (sampleSuccessor name config value))
  | _, _, .commit name owner fresh guard next, profile, law, harmonic, state => by
      have tail : ∀ state, (behavioralStateStep next (afterCommit profile) state).bind
          (fun target => law (.inr target)) = law (.inr state) := by
        intro state
        have original := harmonic (.inr state)
        rw [behavioralStateStep_commit_tail, PMF.bind_map] at original
        exact original
      cases state with
      | inr state =>
          exact continuationLaw_bind_terminal next (afterCommit profile)
            (fun target => law (.inr target)) tail state
      | inl config =>
          rw [← harmonic (.inl config), behavioralStateStep_commit_entry, PMF.bind_map]
          simp only [continuationLaw, Sum.elim_inl, runFrom_commit, PMF.bind_bind]
          apply bind_congr_on_support _
          intro choice _
          simpa only [continuationLaw_entry, terminalState, Function.comp_apply] using
            continuationLaw_bind_terminal next (afterCommit profile)
              (fun target => law (.inr target)) tail
              (entry next (commitSuccessor name guard config choice))
  | _, _, .reveal published owner name fresh selected unresolved next,
      profile, law, harmonic, state => by
      have tail : ∀ state, (behavioralStateStep next (afterReveal profile) state).bind
          (fun target => law (.inr target)) = law (.inr state) := by
        intro state
        have original := harmonic (.inr state)
        rw [behavioralStateStep_reveal_tail, PMF.bind_map] at original
        exact original
      cases state with
      | inr state =>
          exact continuationLaw_bind_terminal next (afterReveal profile)
            (fun target => law (.inr target)) tail state
      | inl config =>
          rw [← harmonic (.inl config), behavioralStateStep_reveal_entry, PMF.bind_map]
          simp only [continuationLaw, Sum.elim_inl, runFrom_reveal, PMF.bind_bind]
          apply bind_congr_on_support _
          intro disclose _
          simpa only [continuationLaw_entry, terminalState, Function.comp_apply] using
            continuationLaw_bind_terminal next (afterReveal profile)
              (fun target => law (.inr target)) tail
              (entry next (revealSuccessor published selected config disclose))
end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))
  (admission : CommitmentInterface setup.program)

/-- The actual initial protocol step samples setup once, irrespective of the
strategic profile. Correlations in the setup law are retained. -/
theorem behavioralStateStep_none
    (profile : Profile (setup.informationModel admission).behavioralSignature) :
    setup.behavioralStateStep admission profile none =
      setup.initialLaw.map (fun initial =>
        some (ProtocolState.entry setup.program (Config.initial initial))) := by
  simp [behavioralStateStep, protocolStep, PMF.bind_const]

/-- Encoding the syntactic policies gives exactly their action-marginal
kernel after setup, with only the existing `some` state embedding. -/
theorem behavioralStateStep_encoded_some
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program admission)
    (state : SourceProgram.ProtocolState setup.program) :
    setup.behavioralStateStep admission
        (fun who => setup.toProtocolBehavioralPolicy admission who (profile who) (permitted who))
        (some state) =
      (ProtocolState.behavioralStateStep setup.program profile state).map some := by
  classical
  by_cases stopped : ProtocolState.terminal setup.program state
  · simp [behavioralStateStep, ProtocolState.behavioralStateStep, stopped, PMF.pure_map]
  · simp only [behavioralStateStep, Option.elim_some, stopped, ite_false, protocolStep,
      ProtocolState.behavioralStateStep, PMF.map_bind]
    let choices who := setup.toProtocolBehavioralPolicy admission who
      (profile who) (permitted who) (setup.protocolObserve who (some state))
    have factors :
        independentProduct (fun who => (profile who).protocolAction setup.program
          (ProtocolState.observe who setup.program state)) =
        (independentProduct choices).map (fun selected who => (selected who).1) := by
      rw [independentProduct_map]
      congr 1
      funext who
      exact (setup.toProtocolBehavioralPolicy_map_val admission who (profile who)
        (permitted who) (some (ProtocolState.observe who setup.program state))).symm
    rw [factors, PMF.bind_map]
    rfl

end Setup

end Vegas.SourceProgram
