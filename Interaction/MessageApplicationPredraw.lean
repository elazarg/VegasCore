/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyTrace
import GameTheory.Protocol.Strategic

/-! # Finite predrawing of a native policy

A fixed message-application schedule is presented as a singleton execution
protocol. The selected policy can be a principal's policy or the environment's
policy; all other invocations retain their original stochastic kernels. Local
history grows at every selected invocation, allowing finite predrawing through
the generic protocol theorem. The complete native trace law is preserved.

The singleton is an analysis device. In particular, selecting the environment
does not make it a game player or restrict its view of pending messages.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- Command carrier at the selected native invocation. -/
def InvocationCommand (app : MessageApplication Principal) :
    @Invocation Principal → Type _
  | .player _ => app.PlayerCommand
  | .environment => app.EnvironmentPolicyCommand

/-- Recorded local information at a native invocation. -/
def InvocationSite (app : MessageApplication Principal) :
    @Invocation Principal → Type _
  | .player _ => List app.PlayerEntry × app.View
  | .environment => List app.EnvironmentEntry × app.EnvironmentObservation

def invocationSite (app : MessageApplication Principal) (who : @Invocation Principal)
    (execution : app.PolicyExecution) : app.InvocationSite who :=
  match who with
  | .player owner => (execution.principalHistory owner,
      State.observe app execution.native owner)
  | .environment => (execution.environmentHistory,
      State.environmentView app execution.native)

def invocationCount (app : MessageApplication Principal) (who : @Invocation Principal)
    (site : app.InvocationSite who) : Nat :=
  match who with
  | .player _ => site.1.length
  | .environment => site.1.length

def invocationWait (app : MessageApplication Principal) (who : @Invocation Principal) :
    app.InvocationCommand who :=
  match who with
  | .player _ => .wait
  | .environment => .wait

def invocationStep (app : MessageApplication Principal) (who : @Invocation Principal)
    (execution : app.PolicyExecution) :
    app.InvocationCommand who → FinDist app.PolicyExecution :=
  match who with
  | .player owner => app.playerStep owner execution
  | .environment => app.environmentPolicyStep execution

def playersReplacing (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (who : @Invocation Principal)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    Principal → app.PlayerPolicy :=
  match who with
  | .player owner => Profile.update (sig := policySignature Principal app) players owner
      (fun history view => replacement (history, view))
  | .environment => players

def environmentReplacing (app : MessageApplication Principal)
    (environment : app.EnvironmentPolicy) (who : @Invocation Principal)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    app.EnvironmentPolicy :=
  match who with
  | .player _ => environment
  | .environment => fun history view => replacement (history, view)

theorem invoke_replacing_self (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (execution : app.PolicyExecution) :
    app.invoke (app.playersReplacing players who replacement)
      (app.environmentReplacing environment who replacement) execution who =
      (replacement (app.invocationSite who execution)).bind
        (app.invocationStep who execution) := by
  cases who <;> simp [playersReplacing, environmentReplacing, invoke, invocationSite,
    invocationStep]

theorem invoke_replacing_other (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who next : @Invocation Principal) (hnext : next ≠ who)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (execution : app.PolicyExecution) :
    app.invoke (app.playersReplacing players who replacement)
      (app.environmentReplacing environment who replacement) execution next =
      app.invoke players environment execution next := by
  cases who with
  | player owner =>
      cases next with
      | player other =>
          have hother : other ≠ owner := fun h => hnext (congrArg Invocation.player h)
          simp [playersReplacing, invoke,
            Profile.update_of_ne _ _ hother]
      | environment => rfl
  | environment =>
      cases next with
      | player other => rfl
      | environment => exact False.elim (hnext rfl)

theorem invocationStep_count (app : MessageApplication Principal)
    (who : @Invocation Principal) (execution next : app.PolicyExecution)
    (command : app.InvocationCommand who)
    (hnext : next ∈ (app.invocationStep who execution command).support) :
    app.invocationCount who (app.invocationSite who next) =
      app.invocationCount who (app.invocationSite who execution) + 1 := by
  cases who with
  | player owner =>
      change (next.principalHistory owner).length = _
      rw [app.playerStep_history_self owner execution command next hnext]
      simp [invocationCount, invocationSite]
  | environment => exact app.environmentStep_history_length execution command next hnext

theorem invoke_other_count (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who other : @Invocation Principal) (hother : other ≠ who)
    (execution next : app.PolicyExecution)
    (hnext : next ∈ (app.invoke players environment execution other).support) :
    app.invocationCount who (app.invocationSite who next) =
      app.invocationCount who (app.invocationSite who execution) := by
  cases other with
  | player owner =>
      simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      cases who with
      | player focal =>
          have hne : focal ≠ owner :=
            fun h => hother (congrArg Invocation.player h.symm)
          change (next.principalHistory focal).length = _
          rw [app.playerStep_other_history owner focal hne execution command next hstep]
          rfl
      | environment =>
          change next.environmentHistory.length = _
          rw [app.playerStep_environmentHistory owner execution command next hstep]
          rfl
  | environment =>
      cases who with
      | environment => exact False.elim (hother rfl)
      | player focal =>
          simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨command, _, hstep⟩ := hnext
          change (next.principalHistory focal).length = _
          rw [app.environmentStep_principalHistory execution command next hstep]
          rfl

/-- State of the singleton presentation of a remaining fixed schedule. -/
structure FocalState (app : MessageApplication Principal) where
  remaining : List (@Invocation Principal)
  execution : app.PolicyExecution

def focalSite? (app : MessageApplication Principal) (who : @Invocation Principal)
    (state : app.FocalState) : Option (app.InvocationSite who) :=
  match state.remaining with
  | next :: _ => if next = who then some (app.invocationSite who state.execution) else none
  | [] => none

def focalTransition (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (state : app.FocalState)
    (choice : Option (app.InvocationCommand who)) : FinDist app.FocalState :=
  match state.remaining with
  | [] => FinDist.pure state
  | next :: rest =>
      if next = who then
        match choice with
        | some command => (app.invocationStep who state.execution command).map
            (fun execution => ⟨rest, execution⟩)
        | none => FinDist.pure state
      else (app.invoke players environment state.execution next).map
        (fun execution => ⟨rest, execution⟩)

@[simp] theorem focalTransition_focal (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (state : app.FocalState) (rest : List (@Invocation Principal))
    (command : app.InvocationCommand who) (hremaining : state.remaining = who :: rest) :
    app.focalTransition players environment who state (some command) =
      (app.invocationStep who state.execution command).map
        (fun execution => ⟨rest, execution⟩) := by
  simp [focalTransition, hremaining]

@[simp] theorem focalTransition_other (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who next : @Invocation Principal) (state : app.FocalState)
    (rest : List (@Invocation Principal))
    (hremaining : state.remaining = next :: rest) (hnext : next ≠ who) :
    app.focalTransition players environment who state none =
      (app.invoke players environment state.execution next).map
        (fun execution => ⟨rest, execution⟩) := by
  simp [focalTransition, hremaining, hnext]

theorem focalTransition_focal_remaining (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (state next : app.FocalState)
    (rest : List (@Invocation Principal))
    (command : app.InvocationCommand who) (hremaining : state.remaining = who :: rest)
    (hnext : next ∈ (app.focalTransition players environment who state (some command)).support) :
    next.remaining = rest := by
  rw [app.focalTransition_focal players environment who state rest command hremaining,
    FinDist.support_map] at hnext
  obtain ⟨execution, _, rfl⟩ := hnext
  rfl

theorem focalTransition_other_remaining (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who owner : @Invocation Principal) (state next : app.FocalState)
    (rest : List (@Invocation Principal))
    (hremaining : state.remaining = owner :: rest) (howner : owner ≠ who)
    (hnext : next ∈ (app.focalTransition players environment who state none).support) :
    next.remaining = rest := by
  rw [app.focalTransition_other players environment who owner state rest hremaining howner,
    FinDist.support_map] at hnext
  obtain ⟨execution, _, rfl⟩ := hnext
  rfl

/-- A selected native policy as the sole decision maker of an analysis protocol.
Other invocations retain their actual kernels. Selecting the environment here
does not add a game player or change any native observation. -/
abbrev focalProtocol (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) : ExecutionProtocol Unit where
  State := app.FocalState
  Action _ := app.InvocationCommand who
  init := ⟨schedule, initial⟩
  active state _ := match state.remaining with
    | next :: _ => next = who
    | [] => False
  available _ _ := Set.univ
  terminal state := state.remaining = []
  step state legal := app.focalTransition players environment who state (legal.1 ())
  progress state hterm := by
    cases hremaining : state.remaining with
    | nil => exact False.elim (hterm hremaining)
    | cons next rest =>
        by_cases hnext : next = who
        · exact ⟨fun _ => some (app.invocationWait who), fun _ => by simp [hnext]⟩
        · exact ⟨fun _ => none, fun _ => by simp [hnext]⟩

/-- Signals whose only nontrivial information states are actual selected polls.
This is an analysis-only singleton adapter: its public signal does not publish
the selected policy's local history to any native runtime player.
All other runtime policies remain fixed transition kernels. -/
abbrev focalSignals (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    InfoSignals (app.focalProtocol players environment who schedule initial) where
  PublicSignal := Option (app.InvocationSite who)
  PrivateSignal _ := Unit
  initialPublic := app.focalSite? who ⟨schedule, initial⟩
  initialPrivate _ := ()
  publicSignal event := app.focalSite? who event.target
  privateSignal _ _ := ()
  InfoState _ := Option (app.InvocationSite who)
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

@[simp] theorem focalSignals_infoOf (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    {state : (app.focalProtocol players environment who schedule initial).State}
    (trace : (app.focalProtocol players environment who schedule initial).Trace state) :
    (app.focalSignals players environment who schedule initial).infoOf () trace =
      app.focalSite? who state := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih => rfl

/-- Information model whose nontrivial states are actual selected polling sites. -/
abbrev focalInformation (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    InformationModel (app.focalProtocol players environment who schedule initial) where
  toInfoSignals := app.focalSignals players environment who schedule initial
  menu _ info := match info with
    | none => {choice | choice = none}
    | some _ => {choice | choice.isSome}
  menu_adequate := by
    intro _ state trace choice
    rw [focalSignals_infoOf]
    cases hremaining : state.remaining with
    | nil =>
        simp only [focalSite?, hremaining]
        change (choice = none ↔ _)
        cases choice <;> simp [hremaining, LegalOption, focalProtocol]
    | cons next rest =>
        by_cases hnext : next = who
        · subst next
          simp only [focalSite?, hremaining, ↓reduceIte]
          change (choice.isSome = true ↔ _)
          cases choice with
          | none => simp [LegalOption, focalProtocol, hremaining]
          | some command =>
              exact ⟨fun _ => ⟨by simp [hremaining], Set.mem_univ command⟩,
                fun _ => rfl⟩
        · simp only [focalSite?, hremaining, if_neg hnext]
          change (choice = none ↔ _)
          cases choice <;> simp [hremaining, hnext, LegalOption, focalProtocol]

/-- The original focal policy, typed as the behavioral policy of the scheduled
one-player presentation. -/
def focalBehavioral (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    (app.focalInformation players environment who schedule initial).BehavioralPolicy () :=
  fun info => match info with
  | none => FinDist.pure ⟨none, by simp⟩
  | some site => (replacement site).map fun command =>
      ⟨some command, by simp⟩

theorem focalBehavioral_eq_of_eq_some (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (info : Option (app.InvocationSite who)) (site : app.InvocationSite who)
    (hinfo : info = some site) :
    app.focalBehavioral players environment who schedule initial replacement info =
      (replacement site).map fun command =>
        ⟨some command, by simp [hinfo]⟩ := by
  subst info
  rfl

/-- Read a deterministic adapter policy back as the selected native
policy.  At an active information state its certified option is necessarily a
command; `wait` is only the total fallback outside that certified case. -/
def focalPolicyOfPure (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (purePolicy : (app.focalInformation players environment who schedule initial).Policy ()) :
    app.InvocationSite who → FinDist (app.InvocationCommand who) := fun site =>
  FinDist.pure ((purePolicy (some site)).1.getD (app.invocationWait who))

theorem focalBehavioral_focalPolicyOfPure (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (purePolicy : (app.focalInformation players environment who schedule initial).Policy ()) :
    app.focalBehavioral players environment who schedule initial
        (app.focalPolicyOfPure players environment who schedule initial purePolicy) =
      purePolicy.toBehavioral := by
  funext info
  cases info with
  | none =>
      apply congrArg FinDist.pure
      apply Subtype.ext
      exact (purePolicy none).2.symm
  | some site =>
      let choice := purePolicy (some site)
      cases hchoice : choice.1 with
      | none =>
          have hmenu := choice.2
          simp [choice, hchoice] at hmenu
      | some command =>
          simp only [focalBehavioral, focalPolicyOfPure, FinDist.map_pure]
          rw [show purePolicy (some site) = choice from rfl, hchoice]
          apply congrArg FinDist.pure
          apply Subtype.ext
          simpa [choice] using hchoice.symm

theorem focal_step_history_length (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (state : (app.focalProtocol players environment who schedule initial).State)
    (joint : Unit → Option (app.InvocationCommand who))
    (legal : (app.focalProtocol players environment who schedule initial).Legal state joint)
    (next : app.FocalState)
    (hnext : next ∈ ((app.focalProtocol players environment who schedule initial).step
      state ⟨joint, legal⟩).support) :
    app.invocationCount who (app.invocationSite who next.execution) =
      app.invocationCount who (app.invocationSite who state.execution) +
        if (joint ()).isSome then 1 else 0 := by
  change next ∈ (app.focalTransition players environment who state (joint ())).support at hnext
  cases hremaining : state.remaining with
  | nil => exact False.elim (legal.1 hremaining)
  | cons owner rest =>
      by_cases howner : owner = who
      · subst owner
        cases hchoice : joint () with
        | none =>
            have hi := legal.2 ()
            simp only [hchoice] at hi
            exact False.elim (hi (by simp [hremaining]))
        | some command =>
            rw [hchoice, app.focalTransition_focal players environment who state rest command
              hremaining, FinDist.support_map] at hnext
            obtain ⟨execution, hexecution, rfl⟩ := hnext
            simpa using app.invocationStep_count who state.execution execution command hexecution
      · cases hchoice : joint () with
        | some command =>
            have hi := legal.2 ()
            simp only [hchoice] at hi
            have ha := hi.1
            simp [hremaining, howner] at ha
        | none =>
            rw [hchoice, app.focalTransition_other players environment who owner state rest
              hremaining howner, FinDist.support_map] at hnext
            obtain ⟨execution, hexecution, rfl⟩ := hnext
            simpa using app.invoke_other_count players environment who owner howner
              state.execution execution hexecution

theorem focal_actedAt_history_length_lt (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    {state : (app.focalProtocol players environment who schedule initial).State}
    (trace : (app.focalProtocol players environment who schedule initial).Trace state) :
    ∀ info ∈ (app.focalSignals players environment who schedule initial).actedAt () trace,
      ∃ site, info = some site ∧
        app.invocationCount who site <
          app.invocationCount who (app.invocationSite who state.execution) := by
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      intro info hmem
      rw [InfoSignals.actedAt] at hmem
      have hlength := app.focal_step_history_length players environment who schedule initial
        source joint legal target realized
      cases hchoice : joint () with
      | none =>
          rw [hchoice] at hmem
          obtain ⟨site, hsite, hlt⟩ := ih info hmem
          refine ⟨site, hsite, ?_⟩
          simp [hchoice] at hlength
          omega
      | some command =>
          rw [hchoice] at hmem
          simp only [List.mem_cons] at hmem
          have hi := legal.2 ()
          simp only [hchoice] at hi
          have hactive := hi.1
          cases hremaining : source.remaining with
          | nil => simp [hremaining] at hactive
          | cons owner rest =>
              have howner : owner = who := by
                simpa [focalProtocol, hremaining] using hactive
              subst owner
              have hsourceInfo :
                  (app.focalSignals players environment who schedule initial).infoOf () prior =
                    some (app.invocationSite who source.execution) := by
                rw [focalSignals_infoOf]
                simp [focalSite?, hremaining]
              simp [hchoice] at hlength
              rcases hmem with hnow | hold
              · exact ⟨app.invocationSite who source.execution,
                  hnow.trans hsourceInfo, by omega⟩
              · obtain ⟨site, hsite, hlt⟩ := ih info hold
                exact ⟨site, hsite, by omega⟩

theorem focal_actsOnceAtEachInfoState (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.focalInformation players environment who schedule initial).ActsOnceAtEachInfoState := by
  intro i
  cases i
  intro state trace
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      rw [InfoSignals.actedAt]
      cases hchoice : joint () with
      | none => simpa [hchoice] using ih
      | some command =>
          simp only [List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hmem
          obtain ⟨site, hsite, hlt⟩ :=
            app.focal_actedAt_history_length_lt players environment who schedule initial prior
              _ hmem
          have hi := legal.2 ()
          simp only [hchoice] at hi
          have hactive := hi.1
          cases hremaining : source.remaining with
          | nil => simp [hremaining] at hactive
          | cons owner rest =>
              have howner : owner = who := by
                simpa [focalProtocol, hremaining] using hactive
              subst owner
              rw [focalSignals_infoOf] at hsite
              simp only [focalSite?, hremaining, ↓reduceIte, Option.some.injEq] at hsite
              rw [← hsite] at hlt
              exact (Nat.lt_irrefl _) hlt

theorem focal_actsOnceWhereItMatters (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.focalInformation players environment who schedule initial).ActsOnceWhereItMatters :=
  InformationModel.actsOnceWhereItMatters_of_actsOnce
    (M := app.focalInformation players environment who schedule initial)
    (app.focal_actsOnceAtEachInfoState players environment who schedule initial)

/-- Prior native snapshots in reverse chronological order. Folding this list
around a suffix trace restores the already-recorded execution prefix. -/
def focalPriorSnapshots (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    {state : app.FocalState} →
      (app.focalProtocol players environment who schedule initial).Trace state →
        List app.PolicyExecution
  | _, .start => []
  | _, .extend (source := source) prior _ _ _ => source.execution ::
      app.focalPriorSnapshots players environment who schedule initial prior

/-- Attach the protocol history's already-recorded snapshots to a native trace
starting at the history's current execution. -/
def focalRecordedTrace (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (history : (app.focalProtocol players environment who schedule initial).History)
    (suffix : app.PolicyTrace) : app.PolicyTrace :=
  (app.focalPriorSnapshots players environment who schedule initial history.trace).foldl
    (fun trace snapshot => .step snapshot trace) suffix

@[simp] theorem focalRecordedTrace_init (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (suffix : app.PolicyTrace) :
    app.focalRecordedTrace players environment who schedule initial
      (app.focalProtocol players environment who schedule initial).initHistory suffix =
        suffix := rfl

@[simp] theorem focalRecordedTrace_extend (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (history : (app.focalProtocol players environment who schedule initial).History)
    (joint : Unit → Option (app.InvocationCommand who))
    (legal : (app.focalProtocol players environment who schedule initial).Legal history.state joint)
    (next : app.FocalState)
    (realized : next ∈ ((app.focalProtocol players environment who schedule initial).step
      history.state ⟨joint, legal⟩).support)
    (suffix : app.PolicyTrace) :
    app.focalRecordedTrace players environment who schedule initial
        (history.extend legal realized) suffix =
      app.focalRecordedTrace players environment who schedule initial history
        (.step history.state.execution suffix) := rfl


/-- Behavioral execution of the scheduled presentation is exactly the shared
policy runner with only the selected policy replaced. The statement starts
at an arbitrary history of the fixed adapter, which keeps the dependent trace
type fixed while induction consumes the remaining schedule. -/
theorem focal_runBehavioralFrom (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who))
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ((app.focalInformation players environment who schedule initial).runBehavioralFrom
      (fun _ => app.focalBehavioral players environment who schedule initial replacement)
      history.state.remaining.length history).map
        (fun result => app.focalRecordedTrace players environment who schedule initial result
          (.finish result.state.execution)) =
      (app.tracePolicies (app.playersReplacing players who replacement)
        (app.environmentReplacing environment who replacement)
        history.state.remaining history.state.execution).map
          (app.focalRecordedTrace players environment who schedule initial history) := by
  induction hremaining : history.state.remaining generalizing history with
  | nil =>
      simp [hremaining, InformationModel.runBehavioralFrom, tracePolicies, focalRecordedTrace]
  | cons next rest ih =>
      have hterm : ¬(app.focalProtocol players environment who schedule initial).terminal
          history.state := by simp [focalProtocol, hremaining]
      simp only [List.length_cons]
      rw [InformationModel.runBehavioralFrom_succ_of_not_terminal
        (M := app.focalInformation players environment who schedule initial)
        _ rest.length hterm]
      by_cases hnext : next = who
      · subst next
        have hinfo :
            (app.focalSignals players environment who schedule initial).infoOf
                () history.trace =
              some (app.invocationSite who history.state.execution) := by
          rw [focalSignals_infoOf]
          simp [focalSite?, hremaining]
        let site : app.InvocationSite who := app.invocationSite who history.state.execution
        let chosen (command : app.InvocationCommand who) :
            (app.focalInformation players environment who schedule initial).Choice ()
              ((app.focalInformation players environment who schedule initial).infoOf
                () history.trace) := ⟨some command, by
          change some command ∈
            (app.focalInformation players environment who schedule initial).menu () _
          rw [hinfo]
          simp⟩
        have hpolicy :
            app.focalBehavioral players environment who schedule initial replacement
                ((app.focalInformation players environment who schedule initial).infoOf
                  () history.trace) =
              (replacement site).map chosen := by
          simpa [site, chosen] using
            app.focalBehavioral_eq_of_eq_some players environment who schedule initial
              replacement _ site hinfo
        rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
          (M := app.focalInformation players environment who schedule initial)
          _ history.trace hterm () (fun _ _ => rfl), hpolicy]
        simp only [Set.ofPred_eq_eq_singleton, FinDist.map_comp, FinDist.bind_map,
          Function.comp_apply, FinDist.map_bind, FinDist.map_bindOnSupport]
        simp only [tracePolicies]
        rw [app.invoke_replacing_self, FinDist.bind_bind, FinDist.map_bind]
        apply FinDist.bind_congr
        intro command hcommand
        calc
          _ = (app.focalTransition players environment who history.state
                (some command)).bindOnSupport fun state _ =>
                (app.tracePolicies (app.playersReplacing players who replacement)
                  (app.environmentReplacing environment who replacement)
                  rest state.execution).map fun suffix =>
                    app.focalRecordedTrace players environment who schedule initial history
                      (.step history.state.execution suffix) := by
              apply FinDist.bindOnSupport_congr
              intro nextState hnextState
              rw [ih (history.extend _ hnextState)
                (app.focalTransition_focal_remaining players environment who history.state
                  nextState rest command hremaining hnextState)]
              rfl
          _ = (app.focalTransition players environment who history.state
                (some command)).bind fun state =>
                (app.tracePolicies (app.playersReplacing players who replacement)
                  (app.environmentReplacing environment who replacement)
                  rest state.execution).map fun suffix =>
                    app.focalRecordedTrace players environment who schedule initial history
                      (.step history.state.execution suffix) :=
              FinDist.bindOnSupport_eq_bind _ _
          _ = _ := by
              rw [app.focalTransition_focal players environment who history.state rest
                command hremaining, FinDist.bind_map, FinDist.map_bind]
              apply FinDist.bind_congr
              intro nextExecution _
              rw [FinDist.map_comp]
              rfl
      · rw [InformationModel.behavioralJoint_eq_pure_of_no_active
          (M := app.focalInformation players environment who schedule initial)
          _ history.trace hterm (fun _ => by simp [focalProtocol, hremaining, hnext])]
        simp only [FinDist.pure_bind]
        rw [FinDist.map_bindOnSupport]
        simp only [tracePolicies]
        rw [FinDist.map_bind]
        calc
          _ = (app.focalTransition players environment who history.state none).bindOnSupport
                fun state _ => (app.tracePolicies (app.playersReplacing players who replacement)
                  (app.environmentReplacing environment who replacement)
                  rest state.execution).map fun suffix =>
                    app.focalRecordedTrace players environment who schedule initial history
                      (.step history.state.execution suffix) := by
              apply FinDist.bindOnSupport_congr
              intro nextState hnextState
              rw [ih (history.extend _ hnextState)
                (app.focalTransition_other_remaining players environment who next history.state
                  nextState rest hremaining hnext hnextState)]
              rfl
          _ = (app.focalTransition players environment who history.state none).bind
                fun state => (app.tracePolicies (app.playersReplacing players who replacement)
                  (app.environmentReplacing environment who replacement)
                  rest state.execution).map fun suffix =>
                    app.focalRecordedTrace players environment who schedule initial history
                      (.step history.state.execution suffix) :=
              FinDist.bindOnSupport_eq_bind _ _
          _ = _ := by
              rw [app.focalTransition_other players environment who next history.state rest
                hremaining hnext, FinDist.bind_map, app.invoke_replacing_other _ _ _ _ hnext]
              apply FinDist.bind_congr
              intro nextExecution _
              rw [FinDist.map_comp]
              rfl

theorem focal_runPureFrom (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (pureProfile : (i : Unit) →
      (app.focalInformation players environment who schedule initial).Policy i)
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ((app.focalInformation players environment who schedule initial).runFrom pureProfile
      history.state.remaining.length history).map
        (fun result => app.focalRecordedTrace players environment who schedule initial result
          (.finish result.state.execution)) =
      (app.tracePolicies
        (app.playersReplacing players who
          (app.focalPolicyOfPure players environment who schedule initial (pureProfile ())))
        (app.environmentReplacing environment who
          (app.focalPolicyOfPure players environment who schedule initial (pureProfile ())))
        history.state.remaining history.state.execution).map
          (app.focalRecordedTrace players environment who schedule initial history) := by
  rw [← InformationModel.runBehavioralFrom_toBehavioral]
  have hprofile :
      (fun i => (pureProfile i).toBehavioral) =
        (fun _ => app.focalBehavioral players environment who schedule initial
          (app.focalPolicyOfPure players environment who schedule initial (pureProfile ()))) := by
    funext i
    cases i
    exact (app.focalBehavioral_focalPolicyOfPure players environment who schedule initial
      (pureProfile ())).symm
  rw [hprofile]
  exact app.focal_runBehavioralFrom players environment who schedule initial _ history

/-- Predraw the selected native policy while preserving the entire trace law.
The finite mixture may depend on the fixed other policies and initial state;
no finite carrier of all command functions is required. -/
theorem exists_invocation_response_mixture_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : @Invocation Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (replacement : app.InvocationSite who → FinDist (app.InvocationCommand who)) :
    ∃ mixture : FinDist (app.InvocationSite who → app.InvocationCommand who),
      mixture.bind (fun response => app.tracePolicies
        (app.playersReplacing players who (fun site => FinDist.pure (response site)))
        (app.environmentReplacing environment who (fun site => FinDist.pure (response site)))
        schedule initial) =
      app.tracePolicies (app.playersReplacing players who replacement)
        (app.environmentReplacing environment who replacement) schedule initial := by
  let M := app.focalInformation players environment who schedule initial
  let history := (app.focalProtocol players environment who schedule initial).initHistory
  let behavioral : (i : Unit) → M.BehavioralPolicy i :=
    fun _ => app.focalBehavioral players environment who schedule initial replacement
  obtain ⟨mixed, hmixed⟩ :=
    InformationModel.exists_mixed_runMixedFrom_eq_runBehavioralFrom
      (M := M) (app.focal_actsOnceWhereItMatters players environment who schedule initial)
      behavioral schedule.length history
  let response (pureProfile : (i : Unit) → M.Policy i)
      (site : app.InvocationSite who) : app.InvocationCommand who :=
    ((pureProfile () (some site)).1).getD (app.invocationWait who)
  refine ⟨(FinDist.pi mixed).map response, ?_⟩
  rw [FinDist.bind_map]
  have hprefix :
      app.focalRecordedTrace players environment who schedule initial history = id := rfl
  calc
    _ = (M.runMixedFrom mixed schedule.length history).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) := by
        rw [InformationModel.runMixedFrom, FinDist.map_bind]
        apply FinDist.bind_congr
        intro pureProfile _
        have hresponse : (fun site => FinDist.pure (response pureProfile site)) =
            app.focalPolicyOfPure players environment who schedule initial (pureProfile ()) := rfl
        rw [hresponse]
        simpa only [hprefix, FinDist.map_id, history, ExecutionProtocol.initHistory_state] using
          (app.focal_runPureFrom players environment who schedule initial pureProfile history).symm
    _ = (M.runBehavioralFrom behavioral schedule.length history).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) := by rw [hmixed]
    _ = _ := by
        simpa only [hprefix, FinDist.map_id, history, ExecutionProtocol.initHistory_state] using
          app.focal_runBehavioralFrom players environment who schedule initial replacement history

/-- Every randomized unilateral policy on a fixed finite schedule is a finite
mixture of total deterministic command functions, with the complete native
trace law and every other policy and the environment unchanged. -/
theorem exists_native_response_mixture_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist (List app.PlayerEntry → app.View → app.PlayerCommand),
      mixture.bind (fun response => app.tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal app)
          players who (fun history view => FinDist.pure (response history view)))
        environment schedule initial) =
      app.tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal app)
          players who replacement) environment schedule initial := by
  obtain ⟨mixture, hlaw⟩ := app.exists_invocation_response_mixture_tracePolicies
    players environment (.player who) schedule initial (fun site => replacement site.1 site.2)
  refine ⟨mixture.map (fun response history view => response (history, view)), ?_⟩
  rw [FinDist.bind_map]
  exact hlaw

/-- Randomized environment responses can be predrawn without changing any
player policy, environment observation, or the law of the complete native
trace. This is a probability decomposition, not a strategic-player assumption. -/
theorem exists_environment_response_mixture_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@Invocation Principal)) (initial : app.PolicyExecution) :
    ∃ mixture : FinDist
        (List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand),
      mixture.bind (fun response => app.tracePolicies players
        (fun history view => FinDist.pure (response history view)) schedule initial) =
      app.tracePolicies players environment schedule initial := by
  obtain ⟨mixture, hlaw⟩ := app.exists_invocation_response_mixture_tracePolicies
    players environment .environment schedule initial (fun site => environment site.1 site.2)
  refine ⟨mixture.map (fun response history view => response (history, view)), ?_⟩
  rw [FinDist.bind_map]
  exact hlaw

/-- Predraw a focal policy and the environment jointly, preserving the full
trace law and all opponent kernels. The finite response-pair mixture need not
factor into independent mixtures; neither response gains new observations. -/
theorem exists_joint_response_mixture_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist
        ((List app.PlayerEntry → app.View → app.PlayerCommand) ×
          (List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand)),
      mixture.bind (fun responses => app.tracePolicies
        (Profile.update (sig := policySignature Principal app)
          players who (fun history view => FinDist.pure (responses.1 history view)))
        (fun history view => FinDist.pure (responses.2 history view)) schedule initial) =
      app.tracePolicies (Profile.update (sig := policySignature Principal app)
        players who replacement) environment schedule initial := by
  obtain ⟨playerResponses, hplayerResponses⟩ := app.exists_native_response_mixture_tracePolicies
    players environment who schedule initial replacement
  let PlayerResponse := List app.PlayerEntry → app.View → app.PlayerCommand
  let EnvironmentResponse :=
    List app.EnvironmentEntry → app.EnvironmentObservation → app.EnvironmentPolicyCommand
  have environmentExists (response : PlayerResponse) :
      ∃ mixture : FinDist EnvironmentResponse,
        mixture.bind (fun environmentResponse => app.tracePolicies
          (Profile.update (sig := policySignature Principal app)
            players who (fun history view => FinDist.pure (response history view)))
          (fun history view => FinDist.pure (environmentResponse history view)) schedule initial) =
        app.tracePolicies (Profile.update (sig := policySignature Principal app)
          players who (fun history view => FinDist.pure (response history view)))
          environment schedule initial :=
    app.exists_environment_response_mixture_tracePolicies
      (Profile.update (sig := policySignature Principal app)
        players who (fun history view => FinDist.pure (response history view)))
      environment schedule initial
  let environmentResponses (response : PlayerResponse) :=
    Classical.choose (environmentExists response)
  refine ⟨playerResponses.bind (fun response =>
    (environmentResponses response).map fun environmentResponse =>
      (response, environmentResponse)), ?_⟩
  rw [FinDist.bind_bind]
  calc
    _ = playerResponses.bind (fun response => app.tracePolicies
        (Profile.update (sig := policySignature Principal app)
          players who (fun history view => FinDist.pure (response history view)))
        environment schedule initial) := by
      apply FinDist.bind_congr
      intro response _
      rw [FinDist.bind_map]
      exact Classical.choose_spec (environmentExists response)
    _ = _ := hplayerResponses

end Interaction.MessageApplication
