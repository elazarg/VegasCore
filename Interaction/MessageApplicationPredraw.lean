/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyTrace
import GameTheory.Protocol.Strategic

/-! # Finite predrawing of one message-application policy

This module presents a fixed message-application schedule as a one-player
execution protocol.  Invocations of the selected principal are the player's
decisions.  Every other principal invocation and every environment invocation
is retained as the original stochastic kernel.  The wrapper introduces no new
interpreter: its transition is `MessageApplication.playerStep` or
`MessageApplication.invoke` from the shared runner.
-/

noncomputable section

namespace Interaction.MessageApplication

open GameTheory GameTheory.Protocol GameTheory.Math.Probability

universe uPrincipal

variable {Principal : Type uPrincipal} [DecidableEq Principal]

/-- State of the one-player presentation of a remaining fixed schedule. -/
structure FocalState (app : MessageApplication Principal) where
  remaining : List (@Invocation Principal)
  execution : app.PolicyExecution

/-- The polling information supplied to the selected player's original policy. -/
abbrev FocalSite (app : MessageApplication Principal) :=
  List app.PlayerEntry × app.View

def focalSite? (app : MessageApplication Principal) (who : Principal)
    (state : app.FocalState) : Option app.FocalSite :=
  match state.remaining with
  | .player next :: _ =>
      if next = who then some (state.execution.principalHistory who,
        State.observe app state.execution.native who) else none
  | .environment :: _ | [] => none

def focalTransition (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (state : app.FocalState) (choice : Option app.PlayerCommand) :
    FinDist app.FocalState :=
  match state.remaining with
  | [] => FinDist.pure state
  | .player next :: rest =>
      if next = who then
        match choice with
        | some command => (app.playerStep who state.execution command).map
            (fun execution => ⟨rest, execution⟩)
        | none => FinDist.pure state
      else (app.invoke players environment state.execution (.player next)).map
        (fun execution => ⟨rest, execution⟩)
  | .environment :: rest =>
      (app.invoke players environment state.execution .environment).map
        (fun execution => ⟨rest, execution⟩)

@[simp] theorem focalTransition_focal (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (state : app.FocalState) (rest : List (@Invocation Principal))
    (command : app.PlayerCommand) (hremaining : state.remaining = .player who :: rest) :
    app.focalTransition players environment who state (some command) =
      (app.playerStep who state.execution command).map
        (fun execution => ⟨rest, execution⟩) := by
  simp [focalTransition, hremaining]

@[simp] theorem focalTransition_other (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who next : Principal) (state : app.FocalState) (rest : List (@Invocation Principal))
    (hremaining : state.remaining = .player next :: rest) (hnext : next ≠ who) :
    app.focalTransition players environment who state none =
      (app.invoke players environment state.execution (.player next)).map
        (fun execution => ⟨rest, execution⟩) := by
  simp [focalTransition, hremaining, hnext]

@[simp] theorem focalTransition_environment (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (state : app.FocalState) (rest : List (@Invocation Principal))
    (hremaining : state.remaining = .environment :: rest) :
    app.focalTransition players environment who state none =
      (app.invoke players environment state.execution .environment).map
        (fun execution => ⟨rest, execution⟩) := by
  simp [focalTransition, hremaining]

theorem focalTransition_focal_remaining (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (state next : app.FocalState) (rest : List (@Invocation Principal))
    (command : app.PlayerCommand) (hremaining : state.remaining = .player who :: rest)
    (hnext : next ∈ (app.focalTransition players environment who state (some command)).support) :
    next.remaining = rest := by
  rw [app.focalTransition_focal players environment who state rest command hremaining,
    FinDist.support_map] at hnext
  obtain ⟨execution, _, rfl⟩ := hnext
  rfl

theorem focalTransition_other_remaining (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who owner : Principal) (state next : app.FocalState) (rest : List (@Invocation Principal))
    (hremaining : state.remaining = .player owner :: rest) (howner : owner ≠ who)
    (hnext : next ∈ (app.focalTransition players environment who state none).support) :
    next.remaining = rest := by
  rw [app.focalTransition_other players environment who owner state rest hremaining howner,
    FinDist.support_map] at hnext
  obtain ⟨execution, _, rfl⟩ := hnext
  rfl

theorem focalTransition_environment_remaining (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (state next : app.FocalState) (rest : List (@Invocation Principal))
    (hremaining : state.remaining = .environment :: rest)
    (hnext : next ∈ (app.focalTransition players environment who state none).support) :
    next.remaining = rest := by
  rw [app.focalTransition_environment players environment who state rest hremaining,
    FinDist.support_map] at hnext
  obtain ⟨execution, _, rfl⟩ := hnext
  rfl

/-- A fixed schedule with fixed nonfocal policies, exposed as a one-player
protocol.  `Unit` is the selected principal; idle protocol steps execute the
unchanged opponent or environment kernel. -/
abbrev focalProtocol (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) : ExecutionProtocol Unit where
  State := app.FocalState
  Action _ := app.PlayerCommand
  init := ⟨schedule, initial⟩
  active state _ := match state.remaining with
    | .player next :: _ => next = who
    | _ => False
  available _ _ := Set.univ
  terminal state := state.remaining = []
  step state legal := app.focalTransition players environment who state (legal.1 ())
  progress state hterm := by
    cases hremaining : state.remaining with
    | nil => exact False.elim (hterm hremaining)
    | cons invocation rest =>
        cases invocation with
        | player next =>
            by_cases hnext : next = who
            · let command := (players who (state.execution.principalHistory who)
                (State.observe app state.execution.native who)).support_nonempty.choose
              exact ⟨fun _ => some command, fun _ => by simp [hnext]⟩
            · exact ⟨fun _ => none, fun _ => by simp [hnext]⟩
        | environment => exact ⟨fun _ => none, fun _ => by simp⟩

/-- Signals whose only nontrivial information states are actual focal polls.
This is an analysis-only singleton-player adapter: its public signal does not
publish the focal principal's private history to any native runtime player.
All nonfocal runtime policies remain fixed transition kernels. -/
abbrev focalSignals (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    InfoSignals (app.focalProtocol players environment who schedule initial) where
  PublicSignal := Option app.FocalSite
  PrivateSignal _ := Unit
  initialPublic := app.focalSite? who ⟨schedule, initial⟩
  initialPrivate _ := ()
  publicSignal event := app.focalSite? who event.target
  privateSignal _ _ := ()
  InfoState _ := Option app.FocalSite
  initInfo _ _ signal := signal
  pushInfo _ _ _ _ signal := signal

@[simp] theorem focalSignals_infoOf (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    {state : (app.focalProtocol players environment who schedule initial).State}
    (trace : (app.focalProtocol players environment who schedule initial).Trace state) :
    (app.focalSignals players environment who schedule initial).infoOf () trace =
      app.focalSite? who state := by
  induction trace with
  | start => rfl
  | extend prior joint isLegal realized ih => rfl

/-- Information model whose only nontrivial information states are actual
polling sites of the focal principal. -/
abbrev focalInformation (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
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
    | cons invocation rest =>
        cases invocation with
        | environment =>
            simp only [focalSite?, hremaining]
            change (choice = none ↔ _)
            cases choice <;> simp [hremaining, LegalOption, focalProtocol]
        | player next =>
            by_cases hnext : next = who
            · subst next
              simp only [focalSite?, hremaining]
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
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy) :
    (app.focalInformation players environment who schedule initial).BehavioralPolicy () :=
  fun info => match info with
  | none => FinDist.pure ⟨none, by simp⟩
  | some site => (replacement site.1 site.2).map fun command =>
      ⟨some command, by simp⟩

theorem focalBehavioral_eq_of_eq_some (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy)
    (info : Option app.FocalSite) (site : app.FocalSite) (hinfo : info = some site) :
    app.focalBehavioral players environment who schedule initial replacement info =
      (replacement site.1 site.2).map fun command =>
        ⟨some command, by simp [hinfo]⟩ := by
  subst info
  rfl

/-- Read a deterministic adapter policy back as an ordinary native player
policy.  At an active information state its certified option is necessarily a
command; `wait` is only the total fallback outside that certified case. -/
def focalPolicyOfPure (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (purePolicy : (app.focalInformation players environment who schedule initial).Policy ()) :
    app.PlayerPolicy := fun history view =>
  FinDist.pure ((purePolicy (some (history, view))).1.getD .wait)

theorem focalBehavioral_focalPolicyOfPure (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
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
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (state : (app.focalProtocol players environment who schedule initial).State)
    (joint : Unit → Option app.PlayerCommand)
    (legal : (app.focalProtocol players environment who schedule initial).Legal state joint)
    (next : app.FocalState)
    (hnext : next ∈ ((app.focalProtocol players environment who schedule initial).step
      state ⟨joint, legal⟩).support) :
    (next.execution.principalHistory who).length =
      (state.execution.principalHistory who).length + if (joint ()).isSome then 1 else 0 := by
  change next ∈ (app.focalTransition players environment who state (joint ())).support at hnext
  cases hremaining : state.remaining with
  | nil => exact False.elim (legal.1 hremaining)
  | cons invocation rest =>
      cases invocation with
      | player owner =>
          by_cases howner : owner = who
          · subst owner
            cases hchoice : joint () with
            | none =>
                have hi := legal.2 ()
                simp only [hchoice] at hi
                exact False.elim (hi (by simp [hremaining]))
            | some command =>
                rw [hchoice, app.focalTransition_focal players environment who state rest command
                  hremaining] at hnext
                rw [FinDist.support_map] at hnext
                obtain ⟨execution, hexecution, rfl⟩ := hnext
                rw [app.playerStep_history_self who state.execution command execution hexecution]
                simp
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
                simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hexecution
                obtain ⟨command, _, hstep⟩ := hexecution
                rw [app.playerStep_other_history owner who (Ne.symm howner) state.execution command
                  execution hstep]
                simp
      | environment =>
          cases hchoice : joint () with
          | some command =>
              have hi := legal.2 ()
              simp only [hchoice] at hi
              have ha := hi.1
              simp [hremaining] at ha
          | none =>
              rw [hchoice,
                app.focalTransition_environment players environment who state rest hremaining,
                FinDist.support_map] at hnext
              obtain ⟨execution, hexecution, rfl⟩ := hnext
              simp only [invoke, FinDist.support_bind, Set.mem_iUnion] at hexecution
              obtain ⟨command, _, hstep⟩ := hexecution
              have heq :=
                app.environmentStep_principalHistory state.execution command execution hstep
              rw [congrFun heq who]
              simp

theorem focal_actedAt_history_length_lt (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    {state : (app.focalProtocol players environment who schedule initial).State}
    (trace : (app.focalProtocol players environment who schedule initial).Trace state) :
    ∀ info ∈ (app.focalSignals players environment who schedule initial).actedAt () trace,
      ∃ site, info = some site ∧
        site.1.length < (state.execution.principalHistory who).length := by
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend source target prior joint legal realized ih =>
      intro info hmem
      rw [InfoSignals.actedAt] at hmem
      cases hchoice : joint () with
      | none =>
          rw [hchoice] at hmem
          obtain ⟨site, hsite, hlt⟩ := ih info hmem
          refine ⟨site, hsite, ?_⟩
          have hlength := app.focal_step_history_length players environment who schedule initial
            source joint legal target realized
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
          | cons invocation rest =>
              cases invocation with
              | environment => simp [hremaining] at hactive
              | player owner =>
                  have howner : owner = who := by
                    simpa [focalProtocol, hremaining] using hactive
                  subst owner
                  have hsourceInfo :
                      (app.focalSignals players environment who schedule initial).infoOf () prior =
                        some (source.execution.principalHistory who,
                          State.observe app source.execution.native who) := by
                    rw [focalSignals_infoOf]
                    simp [focalSite?, hremaining]
                  have hlength := app.focal_step_history_length players environment who schedule
                    initial source joint legal target realized
                  simp [hchoice] at hlength
                  rcases hmem with hnow | hold
                  · refine ⟨(source.execution.principalHistory who,
                        State.observe app source.execution.native who), ?_, ?_⟩
                    · exact hnow.trans hsourceInfo
                    · change (source.execution.principalHistory who).length <
                        (target.execution.principalHistory who).length
                      omega
                  · obtain ⟨site, hsite, hlt⟩ := ih info hold
                    exact ⟨site, hsite, by omega⟩

theorem focal_actsOnceAtEachInfoState (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
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
          | cons invocation rest =>
              cases invocation with
              | environment => simp [hremaining] at hactive
              | player owner =>
                  have howner : owner = who := by
                    simpa [focalProtocol, hremaining] using hactive
                  subst owner
                  rw [focalSignals_infoOf] at hsite
                  simp only [focalSite?, hremaining] at hsite
                  cases hsite
                  exact (Nat.ne_of_lt hlt) rfl

theorem focal_actsOnceWhereItMatters (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) :
    (app.focalInformation players environment who schedule initial).ActsOnceWhereItMatters :=
  InformationModel.actsOnceWhereItMatters_of_actsOnce
    (M := app.focalInformation players environment who schedule initial)
    (app.focal_actsOnceAtEachInfoState players environment who schedule initial)

/-- Prior native snapshots in reverse chronological order. Folding this list
around a suffix trace restores the already-recorded execution prefix. -/
def focalPriorSnapshots (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
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
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (history : (app.focalProtocol players environment who schedule initial).History)
    (suffix : app.PolicyTrace) : app.PolicyTrace :=
  (app.focalPriorSnapshots players environment who schedule initial history.trace).foldl
    (fun trace snapshot => .step snapshot trace) suffix

@[simp] theorem focalRecordedTrace_init (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (suffix : app.PolicyTrace) :
    app.focalRecordedTrace players environment who schedule initial
      (app.focalProtocol players environment who schedule initial).initHistory suffix =
        suffix := rfl

@[simp] theorem focalRecordedTrace_extend (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (history : (app.focalProtocol players environment who schedule initial).History)
    (joint : Unit → Option app.PlayerCommand)
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
policy runner with only the selected principal replaced.  The statement starts
at an arbitrary history of the fixed adapter, which keeps the dependent trace
type fixed while induction consumes the remaining schedule. -/
theorem focal_runBehavioralFrom (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy)
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ((app.focalInformation players environment who schedule initial).runBehavioralFrom
      (fun _ => app.focalBehavioral players environment who schedule initial replacement)
      history.state.remaining.length history).map
        (fun result => app.focalRecordedTrace players environment who schedule initial result
          (.finish result.state.execution)) =
      (app.tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal app)
          players who replacement)
        environment history.state.remaining history.state.execution).map
          (app.focalRecordedTrace players environment who schedule initial history) := by
  induction hremaining : history.state.remaining generalizing history with
  | nil =>
      simp [hremaining, InformationModel.runBehavioralFrom, tracePolicies, focalRecordedTrace]
  | cons invocation rest ih =>
      have hterm : ¬(app.focalProtocol players environment who schedule initial).terminal
          history.state := by simp [focalProtocol, hremaining]
      simp only [List.length_cons]
      rw [InformationModel.runBehavioralFrom_succ_of_not_terminal
        (M := app.focalInformation players environment who schedule initial)
        _ rest.length hterm]
      cases invocation with
      | player next =>
          by_cases hnext : next = who
          · subst next
            have hinfo :
                (app.focalSignals players environment who schedule initial).infoOf
                    () history.trace =
                  some (history.state.execution.principalHistory who,
                    State.observe app history.state.execution.native who) := by
              rw [focalSignals_infoOf]
              simp [focalSite?, hremaining]
            let site : app.FocalSite :=
              (history.state.execution.principalHistory who,
                State.observe app history.state.execution.native who)
            let chosen (command : app.PlayerCommand) :
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
                  (replacement (history.state.execution.principalHistory who)
                    (State.observe app history.state.execution.native who)).map chosen := by
              simpa [site, chosen] using
                app.focalBehavioral_eq_of_eq_some players environment who schedule initial
                  replacement _ site hinfo
            rw [InformationModel.behavioralJoint_eq_map_of_at_most_one_active
              (M := app.focalInformation players environment who schedule initial)
              _ history.trace hterm ()
                (fun _ _ => rfl)]
            rw [hpolicy]
            simp only [Set.ofPred_eq_eq_singleton, FinDist.map_comp, FinDist.bind_map,
              Function.comp_apply, FinDist.map_bind, FinDist.map_bindOnSupport]
            simp only [tracePolicies]
            simp only [invoke, Profile.update_same]
            rw [FinDist.bind_bind]
            rw [FinDist.map_bind]
            apply FinDist.bind_congr
            intro command hcommand
            calc
              _ = (app.focalTransition players environment who history.state
                    (some command)).bindOnSupport fun state _ =>
                    (app.tracePolicies (@Profile.update Principal
                      (policySignature Principal app) _ players who replacement)
                      environment rest state.execution).map fun suffix =>
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
                    (app.tracePolicies (@Profile.update Principal
                      (policySignature Principal app) _ players who replacement)
                      environment rest state.execution).map fun suffix =>
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
              _ history.trace hterm
                (fun _ => by simp [focalProtocol, hremaining, hnext])]
            simp only [FinDist.pure_bind]
            rw [FinDist.map_bindOnSupport]
            simp only [tracePolicies]
            rw [FinDist.map_bind]
            calc
              _ = (app.focalTransition players environment who history.state none).bindOnSupport
                    fun state _ => (app.tracePolicies (@Profile.update Principal
                      (policySignature Principal app) _ players who replacement)
                      environment rest state.execution).map fun suffix =>
                        app.focalRecordedTrace players environment who schedule initial history
                          (.step history.state.execution suffix) := by
                  apply FinDist.bindOnSupport_congr
                  intro nextState hnextState
                  rw [ih (history.extend _ hnextState)
                    (app.focalTransition_other_remaining players environment who next history.state
                      nextState rest hremaining hnext hnextState)]
                  rfl
              _ = (app.focalTransition players environment who history.state none).bind
                    fun state => (app.tracePolicies (@Profile.update Principal
                      (policySignature Principal app) _ players who replacement)
                      environment rest state.execution).map fun suffix =>
                        app.focalRecordedTrace players environment who schedule initial history
                          (.step history.state.execution suffix) :=
                  FinDist.bindOnSupport_eq_bind _ _
              _ = _ := by
                  rw [app.focalTransition_other players environment who next history.state rest
                    hremaining hnext, FinDist.bind_map]
                  have hinvoke :
                      app.invoke (@Profile.update Principal (policySignature Principal app) _
                        players who replacement) environment history.state.execution
                          (.player next) =
                        app.invoke players environment history.state.execution (.player next) := by
                    simp only [invoke, Profile.update_of_ne _ _ hnext]
                  rw [hinvoke]
                  apply FinDist.bind_congr
                  intro nextExecution _
                  rw [FinDist.map_comp]
                  rfl
      | environment =>
          rw [InformationModel.behavioralJoint_eq_pure_of_no_active
            (M := app.focalInformation players environment who schedule initial)
            _ history.trace hterm
              (fun _ => by simp [focalProtocol, hremaining])]
          simp only [FinDist.pure_bind]
          rw [FinDist.map_bindOnSupport]
          simp only [tracePolicies]
          rw [FinDist.map_bind]
          calc
            _ = (app.focalTransition players environment who history.state none).bindOnSupport
                  fun state _ => (app.tracePolicies (@Profile.update Principal
                    (policySignature Principal app) _ players who replacement)
                    environment rest state.execution).map fun suffix =>
                      app.focalRecordedTrace players environment who schedule initial history
                        (.step history.state.execution suffix) := by
                apply FinDist.bindOnSupport_congr
                intro nextState hnextState
                rw [ih (history.extend _ hnextState)
                  (app.focalTransition_environment_remaining players environment who history.state
                    nextState rest hremaining hnextState)]
                rfl
            _ = (app.focalTransition players environment who history.state none).bind
                  fun state => (app.tracePolicies (@Profile.update Principal
                    (policySignature Principal app) _ players who replacement)
                    environment rest state.execution).map fun suffix =>
                      app.focalRecordedTrace players environment who schedule initial history
                        (.step history.state.execution suffix) := FinDist.bindOnSupport_eq_bind _ _
            _ = _ := by
                rw [app.focalTransition_environment players environment who history.state rest
                  hremaining, FinDist.bind_map]
                have hinvoke :
                    app.invoke (@Profile.update Principal (policySignature Principal app) _
                      players who replacement) environment history.state.execution .environment =
                      app.invoke players environment history.state.execution .environment := rfl
                rw [hinvoke]
                apply FinDist.bind_congr
                intro nextExecution _
                rw [FinDist.map_comp]
                rfl

theorem focal_runPureFrom (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution)
    (pureProfile : (i : Unit) →
      (app.focalInformation players environment who schedule initial).Policy i)
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ((app.focalInformation players environment who schedule initial).runFrom pureProfile
      history.state.remaining.length history).map
        (fun result => app.focalRecordedTrace players environment who schedule initial result
          (.finish result.state.execution)) =
      (app.tracePolicies
        (Profile.update (sig := MessageApplication.policySignature Principal app) players who
          (app.focalPolicyOfPure players environment who schedule initial (pureProfile ())))
        environment history.state.remaining history.state.execution).map
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

/-- Once non-revisitation has been established for the focal adapter, its
behavioral replacement can be drawn once as a finite law of deterministic
policies without changing the native execution law. -/
theorem exists_focal_mixed_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy)
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ∃ mixed : (i : Unit) →
        (app.focalInformation players environment who schedule initial).MixedPolicy i,
      ((app.focalInformation players environment who schedule initial).runMixedFrom mixed
        history.state.remaining.length history).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) =
        (app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who replacement)
          environment history.state.remaining history.state.execution).map
            (app.focalRecordedTrace players environment who schedule initial history) := by
  obtain ⟨mixed, hmixed⟩ :=
    InformationModel.exists_mixed_runMixedFrom_eq_runBehavioralFrom
      (M := app.focalInformation players environment who schedule initial)
        (app.focal_actsOnceWhereItMatters players environment who schedule initial)
        (fun _ => app.focalBehavioral players environment who schedule initial replacement)
        history.state.remaining.length history
  refine ⟨mixed, ?_⟩
  rw [hmixed]
  exact app.focal_runBehavioralFrom players environment who schedule initial replacement history

/-- A deterministic native command at every local history and view. -/
def IsPurePlayerPolicy (app : MessageApplication Principal) (policy : app.PlayerPolicy) : Prop :=
  ∀ history view, ∃ command, policy history view = FinDist.pure command

private theorem exists_native_policy_mixture_tracePoliciesFrom
    (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy)
    (history : (app.focalProtocol players environment who schedule initial).History) :
    ∃ mixture : FinDist app.PlayerPolicy,
      (∀ purePolicy ∈ mixture.support, app.IsPurePlayerPolicy purePolicy) ∧
        mixture.bind (fun purePolicy => (app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who purePolicy)
          environment history.state.remaining history.state.execution).map
            (app.focalRecordedTrace players environment who schedule initial history)) =
        (app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who replacement)
          environment history.state.remaining history.state.execution).map
            (app.focalRecordedTrace players environment who schedule initial history) := by
  let behavioral : (i : Unit) →
      (app.focalInformation players environment who schedule initial).BehavioralPolicy i :=
    fun _ => app.focalBehavioral players environment who schedule initial replacement
  obtain ⟨mixed, hmixed⟩ :=
    InformationModel.exists_mixed_runMixedFrom_eq_runBehavioralFrom
      (M := app.focalInformation players environment who schedule initial)
      (app.focal_actsOnceWhereItMatters players environment who schedule initial)
      behavioral history.state.remaining.length history
  let mixture : FinDist app.PlayerPolicy := (FinDist.pi mixed).map fun pureProfile =>
    app.focalPolicyOfPure players environment who schedule initial (pureProfile ())
  refine ⟨mixture, ?_, ?_⟩
  · intro purePolicy hpurePolicy history' view
    rw [show mixture = (FinDist.pi mixed).map (fun pureProfile =>
      app.focalPolicyOfPure players environment who schedule initial (pureProfile ())) from rfl,
      FinDist.support_map] at hpurePolicy
    obtain ⟨pureProfile, _, rfl⟩ := hpurePolicy
    exact ⟨_, rfl⟩
  change ((FinDist.pi mixed).map fun pureProfile =>
      app.focalPolicyOfPure players environment who schedule initial (pureProfile ())).bind _ = _
  rw [FinDist.bind_map]
  calc
    _ = ((app.focalInformation players environment who schedule initial).runMixedFrom mixed
          history.state.remaining.length history).map
            (fun result => app.focalRecordedTrace players environment who schedule initial result
              (.finish result.state.execution)) := by
        rw [InformationModel.runMixedFrom, FinDist.map_bind]
        apply FinDist.bind_congr
        intro pureProfile hpureProfile
        exact (app.focal_runPureFrom players environment who schedule initial pureProfile
          history).symm
    _ = ((app.focalInformation players environment who schedule initial).runBehavioralFrom
          behavioral history.state.remaining.length history).map
          (fun result => app.focalRecordedTrace players environment who schedule initial result
            (.finish result.state.execution)) := by rw [hmixed]
    _ = _ :=
      app.focal_runBehavioralFrom players environment who schedule initial replacement history

/-- Every randomized unilateral native policy on a fixed finite schedule is a
finite mixture of pure native policies, with the complete execution law and all
other policies unchanged. -/
private theorem exists_native_policy_mixture_tracePolicies (app : MessageApplication Principal)
    (players : Principal → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (who : Principal) (schedule : List (@Invocation Principal))
    (initial : app.PolicyExecution) (replacement : app.PlayerPolicy) :
    ∃ mixture : FinDist app.PlayerPolicy,
      (∀ purePolicy ∈ mixture.support, app.IsPurePlayerPolicy purePolicy) ∧
        mixture.bind (fun purePolicy => app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who purePolicy) environment schedule initial) =
        app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who replacement) environment schedule initial := by
  have hprefix :
      app.focalRecordedTrace players environment who schedule initial
        (app.focalProtocol players environment who schedule initial).initHistory = id := by
    funext suffix
    exact app.focalRecordedTrace_init players environment who schedule initial suffix
  simpa only [hprefix, FinDist.map_id, ExecutionProtocol.initHistory_state] using
    app.exists_native_policy_mixture_tracePoliciesFrom players environment who schedule initial
      replacement
      (app.focalProtocol players environment who schedule initial).initHistory

/-- Extract the command selected by a globally deterministic native policy.
The fallback makes this total away from the pure policies used by predrawing. -/
noncomputable def deterministicResponse (app : MessageApplication Principal)
    (policy : app.PlayerPolicy) : List app.PlayerEntry → app.View → app.PlayerCommand := by
  classical
  exact if hpure : app.IsPurePlayerPolicy policy then
      fun history view => Classical.choose (hpure history view)
    else fun _ _ => .wait

omit [DecidableEq Principal] in
theorem deterministicResponse_eq (app : MessageApplication Principal)
    (policy : app.PlayerPolicy) (hpure : app.IsPurePlayerPolicy policy) :
    (fun history view => FinDist.pure (app.deterministicResponse policy history view)) =
      policy := by
  funext history view
  rw [deterministicResponse, dif_pos hpure]
  exact (Classical.choose_spec (hpure history view)).symm

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
  obtain ⟨policies, hpure, hlaw⟩ :=
    app.exists_native_policy_mixture_tracePolicies players environment who schedule initial
      replacement
  refine ⟨policies.map app.deterministicResponse, ?_⟩
  rw [FinDist.bind_map]
  calc
    _ = policies.bind (fun policy => app.tracePolicies
          (Profile.update (sig := MessageApplication.policySignature Principal app)
            players who policy) environment schedule initial) := by
        apply FinDist.bind_congr
        intro policy hpolicy
        rw [app.deterministicResponse_eq policy (hpure policy hpolicy)]
    _ = _ := hlaw


end Interaction.MessageApplication

/-- info: 'Interaction.MessageApplication.exists_native_response_mixture_tracePolicies' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.MessageApplication.exists_native_response_mixture_tracePolicies
