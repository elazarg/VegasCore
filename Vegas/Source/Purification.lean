/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.Setup
import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheoryExtensions.Math.Probability.SiteDraw

/-! # Every policy is a mixture of pure ones

A deviation certificate may answer a behavioral policy with a *mixture* of
policies, but the mixture is drawn once, before the private setup law and before
any chance step, so a component has to serve every branch at once. That is what
stops the naive induction: a mixture chosen per branch is not a mixture chosen
in advance.

The construction here draws the actions of the whole program up front. A source
program is a straight line — every decision point of a player occurs exactly
once in every run — so a draw at a decision point may be coupled arbitrarily
across the views reachable there, and only independence *between* decision
points is needed. The draws at one point are independent draws at the finitely
many reachable views, whose marginal at the view actually read is the law there
(`GameTheory.Math.Probability.drawAtSites_bind_apply`).

The induction runs over a list of configurations rather than one, so that a
single mixture serves every branch created before the point reached. That list
stays finite because every step branches finitely: chance laws are exact finite
tables, commitment kernels have finite support at every view, disclosures are
Boolean, and a setup's initial law is assumed finitely supported. Binding payload
types may be infinite. Finite binding types imply the kernel condition, but
infinite-support action kernels are outside this finite-mixture construction.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-! ## Every policy is a mixture of pure ones -/

/-- The finitely many values of a finitely supported law, listed. -/
private def supportList {α : Type*} (law : PMF α) (finite : law.support.Finite) : List α :=
  finite.toFinset.toList

private theorem mem_supportList {α : Type*} {law : PMF α} (finite : law.support.Finite)
    {value : α} (supported : value ∈ law.support) : value ∈ supportList law finite :=
  Finset.mem_toList.mpr (finite.mem_toFinset.mpr supported)

/-- Each commitment kernel has finite support at every view. Payload types may
be infinite; Boolean disclosure kernels are automatically finitely supported. -/
def BehavioralPolicy.HasFiniteSupport {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → BehavioralPolicy who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, policy => HasFiniteSupport next policy
  | _, _, .commit _ _ _ _ next, policy =>
      (∀ own view active, (policy.1 own view active).support.Finite) ∧
        HasFiniteSupport next policy.2
  | _, _, .reveal _ _ _ _ _ _ next, policy => HasFiniteSupport next policy.2

/-- Finite binding alphabets supply the policy-level support condition. -/
theorem BehavioralPolicy.hasFiniteSupport_of_finiteBindingTypes {who : Player} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O), program.FiniteBindingTypes →
      ∀ policy : BehavioralPolicy who program, policy.HasFiniteSupport program
  | _, _, .ret _, _, _ => trivial
  | _, _, .sample _ _ _ next, finite, policy =>
      hasFiniteSupport_of_finiteBindingTypes next finite policy
  | _, _, .commit _ _ _ _ next, finite, policy => by
      have := finite.1
      exact ⟨fun _ _ _ => Set.toFinite _,
        hasFiniteSupport_of_finiteBindingTypes next finite.2 policy.2⟩
  | _, _, .reveal _ _ _ _ _ _ next, finite, policy =>
      hasFiniteSupport_of_finiteBindingTypes next finite policy.2

private def RealizesPureMixtures {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) : Prop :=
  ∀ (profile : BehavioralProfile program) (policy : BehavioralPolicy who program),
    (∀ player, (profile player).HasFiniteSupport program) → policy.HasFiniteSupport program →
    ∀ configs : List (Config Player L Γ),
      ∃ mixture : PMF (PurePolicy who program), mixture.support.Finite ∧ ∀ config ∈ configs,
        runFrom program (Function.update profile who policy) config =
          mixture.bind fun choice => runFrom program
            (Function.update profile who (PurePolicy.toBehavioral program choice)) config

private theorem realizesPureMixtures_commit {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (name : VarId) (owner : Player) {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (ih : RealizesPureMixtures (who := who) next) :
    RealizesPureMixtures (who := who) (.commit name owner fresh guard next) := by
  intro profile policy profileFinite policyFinite configs
  classical
  by_cases hown : owner = who
  · subst who
    let choose (view : DecisionView owner Γ) :
        PMF (Option (PublicationResult (L.Val payload))) :=
      if inactive : owner ∈ view.defaulted then PMF.pure none
      else policy.1 rfl view inactive
    have chooseFinite : ∀ view : DecisionView owner Γ, (choose view).support.Finite := by
      intro view
      by_cases inactive : owner ∈ view.defaulted
      · simpa only [choose, dite_eq_left inactive, PMF.support_pure] using
          Set.finite_singleton (none : Option (PublicationResult (L.Val payload)))
      · simpa only [choose, dite_eq_right inactive] using policyFinite.1 rfl view inactive
    let successors : List (Config Player L ((name, .commitment owner payload) :: Γ)) :=
      configs.flatMap fun (config : Config Player L Γ) =>
        (supportList (α := Option (PublicationResult (L.Val payload)))
          (choose (Config.view (Γ := Γ) owner config))
          (chooseFinite (Config.view (Γ := Γ) owner config))).map
          (commitSuccessor name guard config)
    have tailExists := ih (afterCommit (k := next) profile) policy.2
      (fun player => (profileFinite player).2) policyFinite.2 successors
    obtain ⟨tail, tailFinite, htail⟩ := tailExists
    refine ⟨(drawAtSites choose (configs.map (Config.view owner)).toFinset
        (fun _ => none)).bind fun assigned =>
      tail.bind fun rest => PMF.pure (fun _ view _ => assigned view, rest),
      bind_support_finite (drawAtSites_support_finite _ _ _ fun view _ => chooseFinite view)
        fun _ _ => bind_support_finite tailFinite fun _ _ => by simp,
      fun config hconfig => ?_⟩
    have hview : config.view owner ∈ configs.map (Config.view owner) :=
      List.mem_map.mpr ⟨config, hconfig, rfl⟩
    have hmember : ∀ choice ∈ (choose (config.view owner)).support,
        commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
          (supportList (choose (other.view owner)) (chooseFinite _)).map
            (commitSuccessor name guard other) := fun choice hchoice =>
      List.mem_flatMap.mpr ⟨config, hconfig,
        List.mem_map.mpr ⟨choice, mem_supportList _ hchoice, rfl⟩⟩
    have hkernel : commitKernel (Function.update profile owner policy) = policy.1 rfl := by
      simp [commitKernel]
    have hpure : ∀ choice : PurePolicy owner (.commit name owner fresh guard next),
        commitKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
          fun view active => PMF.pure (choice.1 rfl view active) := by
      intro choice
      simp [commitKernel, PurePolicy.toBehavioral, Function.update_self]
    have hsnd : ∀ choice : PurePolicy owner (.commit name owner fresh guard next),
        (PurePolicy.toBehavioral (.commit name owner fresh guard next) choice).2 =
          PurePolicy.toBehavioral next choice.2 := fun _ => rfl
    by_cases inactive : owner ∈ config.defaulted
    · simp only [runFrom_commit, hkernel, hpure, hsnd, afterCommit_update, inactive,
        dite_true, PMF.bind_bind, PMF.pure_bind]
      rw [htail _ (hmember none (by simp [choose, inactive]))]
      exact (PMF.bind_const _ _).symm
    · simp only [runFrom_commit, hkernel, hpure, hsnd, afterCommit_update, inactive,
        dite_false, PMF.bind_bind, PMF.pure_bind]
      rw [drawAtSites_bind_apply choose (configs.map (Config.view owner)).toFinset
        (fun _ => none) (List.mem_toFinset.mpr hview)
        (fun choice => tail.bind fun rest =>
          runFrom next (Function.update (afterCommit (k := next) profile) owner
            (PurePolicy.toBehavioral next rest)) (commitSuccessor name guard config choice))]
      simp only [choose, Config.view_defaulted, inactive, dite_false]
      exact bind_congr_on_support _ fun choice hchoice =>
        htail _ (hmember choice (by simpa [choose, inactive] using hchoice))
  · let choose (config : Config Player L Γ) :
        PMF (Option (PublicationResult (L.Val payload))) :=
      if inactive : owner ∈ config.defaulted then PMF.pure none
      else commitKernel profile (config.view owner) inactive
    have chooseFinite (config : Config Player L Γ) : (choose config).support.Finite := by
      unfold choose
      split
      · rw [PMF.support_pure]
        exact Set.finite_singleton _
      · exact (profileFinite owner).1 rfl (config.view owner) _
    obtain ⟨tail, tailFinite, htail⟩ :=
      ih (afterCommit (k := next) profile) policy.2
        (fun player => (profileFinite player).2) policyFinite.2
        (configs.flatMap fun config => (supportList (choose config) (chooseFinite _)).map
          (commitSuccessor name guard config))
    refine ⟨tail.bind fun rest => PMF.pure (fun own => absurd own hown, rest),
      bind_support_finite tailFinite fun _ _ => by simp, fun config hconfig => ?_⟩
    have hmember : ∀ choice ∈ (choose config).support,
        commitSuccessor name guard config choice ∈ configs.flatMap fun other =>
          (supportList (choose other) (chooseFinite _)).map
            (commitSuccessor name guard other) := fun choice hchoice =>
      List.mem_flatMap.mpr ⟨config, hconfig,
        List.mem_map.mpr ⟨choice, mem_supportList _ hchoice, rfl⟩⟩
    have hkernel : ∀ replacement : BehavioralPolicy who (.commit name owner fresh guard next),
        commitKernel (Function.update profile who replacement) = commitKernel profile := by
      intro replacement
      simp [commitKernel, Function.update_of_ne hown]
    have hsnd : ∀ choice : PurePolicy who (.commit name owner fresh guard next),
        (PurePolicy.toBehavioral (.commit name owner fresh guard next) choice).2 =
          PurePolicy.toBehavioral next choice.2 := fun _ => rfl
    simp only [runFrom_commit, hkernel, hsnd, afterCommit_update, PMF.bind_bind,
      PMF.pure_bind]
    change (choose config).bind _ = tail.bind _
    rw [bind_congr_on_support _ fun choice hchoice => htail _ (hmember choice hchoice),
      PMF.bind_comm]

private theorem realizesPureMixtures_reveal {who : Player} {Γ : SourceCtx Player L}
    {O : Finset VarId} (published : VarId) (owner : Player) (name : VarId) {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (source : HasVar Γ name (.commitment owner payload)) (unresolved : name ∈ O)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ) (O.erase name))
    (ih : RealizesPureMixtures (who := who) next) :
    RealizesPureMixtures (who := who)
      (.reveal published owner name fresh source unresolved next) := by
  intro profile policy profileFinite policyFinite configs
  classical
  by_cases hown : owner = who
  · subst who
    let choose (view : DecisionView owner Γ) :=
      if inactive : owner ∈ view.defaulted then PMF.pure false
      else policy.1 rfl view inactive
    obtain ⟨tail, tailFinite, htail⟩ :=
      ih (afterReveal profile) policy.2 profileFinite policyFinite
        (configs.flatMap fun config =>
          (supportList (choose (config.view owner)) (Set.toFinite _)).map
            (revealSuccessor published source config))
    refine ⟨(drawAtSites choose (configs.map (Config.view owner)).toFinset
        (fun _ => false)).bind fun assigned =>
      tail.bind fun rest => PMF.pure (fun _ view _ => assigned view, rest),
      bind_support_finite (drawAtSites_support_finite _ _ _ fun _ _ => Set.toFinite _)
        fun _ _ => bind_support_finite tailFinite fun _ _ => by simp,
      fun config hconfig => ?_⟩
    have hview : config.view owner ∈ configs.map (Config.view owner) :=
      List.mem_map.mpr ⟨config, hconfig, rfl⟩
    have hmember : ∀ disclose ∈ (choose (config.view owner)).support,
        revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
          (supportList (choose (other.view owner)) (Set.toFinite _)).map
            (revealSuccessor published source other) := fun disclose hdisclose =>
      List.mem_flatMap.mpr ⟨config, hconfig,
        List.mem_map.mpr ⟨disclose, mem_supportList _ hdisclose, rfl⟩⟩
    have hkernel : revealKernel (Function.update profile owner policy) = policy.1 rfl := by
      simp [revealKernel]
    have hpure : ∀ choice :
        PurePolicy owner (.reveal published owner name fresh source unresolved next),
        revealKernel (Function.update profile owner (PurePolicy.toBehavioral _ choice)) =
          fun view active => PMF.pure (choice.1 rfl view active) := by
      intro choice
      simp [revealKernel, PurePolicy.toBehavioral, Function.update_self]
    have hsnd : ∀ choice :
        PurePolicy owner (.reveal published owner name fresh source unresolved next),
        (PurePolicy.toBehavioral
          (.reveal published owner name fresh source unresolved next) choice).2 =
          PurePolicy.toBehavioral next choice.2 := fun _ => rfl
    by_cases inactive : owner ∈ config.defaulted
    · simp only [runFrom_reveal, hkernel, hpure, hsnd, afterReveal_update, inactive,
        dite_true, PMF.bind_bind, PMF.pure_bind]
      rw [htail _ (hmember false (by simp [choose, inactive]))]
      exact (PMF.bind_const _ _).symm
    · simp only [runFrom_reveal, hkernel, hpure, hsnd, afterReveal_update, inactive,
        dite_false, PMF.bind_bind, PMF.pure_bind]
      rw [drawAtSites_bind_apply choose (configs.map (Config.view owner)).toFinset
        (fun _ => false) (List.mem_toFinset.mpr hview)
        (fun disclose => tail.bind fun rest =>
          runFrom next (Function.update (afterReveal profile) owner
            (PurePolicy.toBehavioral next rest))
            (revealSuccessor published source config disclose))]
      simp only [choose, Config.view_defaulted, inactive, dite_false]
      exact bind_congr_on_support _ fun disclose hdisclose =>
        htail _ (hmember disclose (by simpa [choose, inactive] using hdisclose))
  · let choose (config : Config Player L Γ) :=
      if inactive : owner ∈ config.defaulted then PMF.pure false
      else revealKernel profile (config.view owner) inactive
    obtain ⟨tail, tailFinite, htail⟩ :=
      ih (afterReveal profile) policy.2 profileFinite policyFinite
        (configs.flatMap fun config => (supportList (choose config) (Set.toFinite _)).map
          (revealSuccessor published source config))
    refine ⟨tail.bind fun rest => PMF.pure (fun own => absurd own hown, rest),
      bind_support_finite tailFinite fun _ _ => by simp, fun config hconfig => ?_⟩
    have hmember : ∀ disclose ∈ (choose config).support,
        revealSuccessor published source config disclose ∈ configs.flatMap fun other =>
          (supportList (choose other) (Set.toFinite _)).map
            (revealSuccessor published source other) := fun disclose hdisclose =>
      List.mem_flatMap.mpr ⟨config, hconfig,
        List.mem_map.mpr ⟨disclose, mem_supportList _ hdisclose, rfl⟩⟩
    have hkernel : ∀ replacement : BehavioralPolicy who
          (.reveal published owner name fresh source unresolved next),
        revealKernel (Function.update profile who replacement) = revealKernel profile := by
      intro replacement
      simp [revealKernel, Function.update_of_ne hown]
    have hsnd : ∀ choice :
        PurePolicy who (.reveal published owner name fresh source unresolved next),
        (PurePolicy.toBehavioral
          (.reveal published owner name fresh source unresolved next) choice).2 =
          PurePolicy.toBehavioral next choice.2 := fun _ => rfl
    simp only [runFrom_reveal, hkernel, hsnd, afterReveal_update, PMF.bind_bind,
      PMF.pure_bind]
    change (choose config).bind _ = tail.bind _
    rw [bind_congr_on_support _ fun disclose hdisclose => htail _ (hmember disclose hdisclose),
      PMF.bind_comm]


/-- One mixture of pure policies reproduces a behavioral policy's law from every
configuration in a list, against unchanged opponents. The list is what lets a
single mixture serve every branch: the successors of a chance step, or of
another player's action, go into the list for the rest of the program. -/
theorem exists_pureMixture {who : Player} :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (p : SourceProgram Player L Γ O) →
    (profile : BehavioralProfile p) → (policy : BehavioralPolicy who p) →
    (∀ player, (profile player).HasFiniteSupport p) → policy.HasFiniteSupport p →
    (configs : List (Config Player L Γ)) →
    ∃ mixture : PMF (PurePolicy who p), mixture.support.Finite ∧ ∀ config ∈ configs,
      runFrom p (Function.update profile who policy) config =
        mixture.bind fun choice =>
          runFrom p (Function.update profile who (PurePolicy.toBehavioral p choice)) config
  | _, _, .ret _, _, _, _, _, _ =>
      ⟨PMF.pure PUnit.unit, by simp, fun config _ => by simp [runFrom]⟩
  | Γ, _, .sample name (payload := payload) fresh law k, profile, policy,
      profileFinite, policyFinite, configs => by
      obtain ⟨mixture, mixtureFinite, hmixture⟩ :=
        exists_pureMixture k (afterSample profile) policy profileFinite policyFinite
        (configs.flatMap fun config =>
          (supportList (L.evalDist law (sourcePublicEnv config.state))
            (L.evalDist_support_finite _ _)).map (sampleSuccessor name config))
      refine ⟨mixture, mixtureFinite, fun config hconfig => ?_⟩
      have member : ∀ value ∈ (L.evalDist law (sourcePublicEnv config.state)).support,
          sampleSuccessor name config value ∈ configs.flatMap fun other =>
            (supportList (L.evalDist law (sourcePublicEnv other.state))
              (L.evalDist_support_finite _ _)).map (sampleSuccessor name other) :=
        fun value hvalue => List.mem_flatMap.mpr ⟨config, hconfig,
          List.mem_map.mpr ⟨value, mem_supportList _ hvalue, rfl⟩⟩
      simp only [runFrom_sample, afterSample_update]
      rw [bind_congr_on_support _ fun value hvalue => hmixture _ (member value hvalue),
        PMF.bind_comm]
      rfl
  | _, _, .commit name owner fresh guard next, profile, policy,
      profileFinite, policyFinite, configs =>
      realizesPureMixtures_commit name owner fresh guard next (exists_pureMixture next)
        profile policy profileFinite policyFinite configs
  | _, _, .reveal published owner name fresh source unresolved next, profile, policy,
      profileFinite, policyFinite, configs =>
      realizesPureMixtures_reveal published owner name fresh source unresolved next
        (exists_pureMixture next) profile policy profileFinite policyFinite configs

/-- One mixture of pure policies reproduces a behavioral policy's terminal state
law across a whole setup, against unchanged opponents. The draw precedes the
private initial law, which is what a deviation certificate needs. -/
theorem exists_pureMixture_run {who : Player} (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw]
    (profile : BehavioralProfile setup.program) (policy : BehavioralPolicy who setup.program)
    (profileFinite : ∀ player, (profile player).HasFiniteSupport setup.program)
    (policyFinite : policy.HasFiniteSupport setup.program) :
    ∃ mixture : PMF (PurePolicy who setup.program), mixture.support.Finite ∧
      setup.run (Function.update profile who policy) =
        mixture.bind fun choice =>
          setup.run (Function.update profile who
            (PurePolicy.toBehavioral setup.program choice)) := by
  obtain ⟨mixture, mixtureFinite, hmixture⟩ :=
    exists_pureMixture setup.program profile policy profileFinite policyFinite
    ((supportList setup.initialLaw setup.initialLaw_support_finite).map fun initial =>
      Config.initial initial)
  refine ⟨mixture, mixtureFinite, ?_⟩
  have hrun : ∀ initial ∈ setup.initialLaw.support,
      SourceProgram.run setup.program (Function.update profile who policy) initial =
        mixture.bind fun choice =>
          SourceProgram.run setup.program
            (Function.update profile who (PurePolicy.toBehavioral setup.program choice))
            initial := fun initial hinitial =>
    hmixture _ (List.mem_map.mpr ⟨initial, mem_supportList _ hinitial, rfl⟩)
  simp only [Setup.run]
  rw [bind_congr_on_support _ hrun, PMF.bind_comm]

/-! ## The pure-strategy game

The game a source program presents when a policy may not randomize. Only the
strategies change, so the two games are compared by the identity on outcomes. -/

/-- The behavioral policies underlying a pure profile. -/
def pureProfile {Γ : SourceCtx Player L} {O : Finset VarId}
    {p : SourceProgram Player L Γ O} (profile : ∀ who, PurePolicy who p) :
    BehavioralProfile p := fun who => PurePolicy.toBehavioral p (profile who)

namespace Setup

/-- The pure-strategy game of a setup. Reducible for the same reason as
`Setup.valueBindingGame`: `sig.Strategy` has to reduce to `PurePolicy`. -/
@[reducible] def pureGame (setup : Setup (Player := Player) (L := L)) :
    GameForm Player where
  sig :=
    { Strategy := fun who => PurePolicy who setup.program
      Outcome := SourceProgram.PublicOutcome setup.program }
  play profile := setup.publicRun (pureProfile profile)

@[simp] theorem pureGame_play (setup : Setup (Player := Player) (L := L))
    (profile : Profile setup.pureGame.sig) :
    setup.pureGame.play profile = setup.publicRun (pureProfile profile) := rfl

end Setup

end Vegas.SourceProgram
