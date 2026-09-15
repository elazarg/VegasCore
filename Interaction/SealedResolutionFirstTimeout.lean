/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedResolutionDeadline
import Interaction.MessageApplicationCheckpoints

/-! # The normal prerequisites of a first timeout

A positive resolution window prevents a node from becoming ready and expiring
in the same clock transition. At the first timeout-producing transition, every
expired node therefore had normally completed prerequisites before the clock
advanced. This argument uses retained readiness timestamps, rather than the
order in which the refresh scan visits nodes. It applies to every hosted
commitment service and places no restriction on player traffic.
-/

noncomputable section

namespace Interaction.SealedResolution

open MessageApplication GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable {Service : Type (max uPrincipal uValue)}

/-- A node expiring in the first timeout-producing clock step was already
ready before that step. Its prerequisites completed by events, not defaults.
This holds for every timeout added by the scan, not just its first entry. -/
theorem tick_first_timeout_ready_before
    (runtime : SealedResolution Principal Value) (hwindow : 0 < runtime.window)
    (state : ApplicationState Principal Value Service)
    (hready : state.visible.ReadySound runtime) (hclear : state.visible.timeouts = [])
    (node : Nat) (htimeout : node ∈ (runtime.tick state).visible.timeouts) :
    ∃ rule timestamp,
      runtime.program.rules[node]? = some rule ∧
      state.visible.firstReady? node = some timestamp ∧
      timestamp + runtime.window ≤ state.visible.clock + 1 ∧
      rule.requires.all (SealedProgram.done state.visible.events) = true := by
  have hdeadline : state.visible.DeadlineSound runtime := by
    intro target htarget
    simp [hclear] at htarget
  obtain ⟨rule, timestamp, hrule, hstamped, hexpired, _⟩ :=
    hdeadline.tick node htimeout
  have hprior : state.visible.firstReady? node = some timestamp := by
    cases hbefore : state.visible.firstReady? node with
    | none =>
        have horigin := runtime.refresh_firstReady?_of_none true
          { state.visible with clock := state.visible.clock + 1 } node timestamp
          (by simpa [PublicState.firstReady?] using hbefore) hstamped
        have htime := horigin.1
        rw [runtime.refresh_clock] at htime
        rw [runtime.tick_clock] at hexpired
        dsimp only at htime
        omega
    | some recorded =>
        have hpersist := runtime.refresh_firstReady?_of_some true
          { state.visible with clock := state.visible.clock + 1 } node recorded
          (by simpa [PublicState.firstReady?] using hbefore)
        have heq : recorded = timestamp := Option.some.inj (hpersist.symm.trans hstamped)
        exact congrArg some heq
  obtain ⟨priorRule, hpriorRule, hrequires⟩ := hready node timestamp hprior
  have hrules : priorRule = rule := Option.some.inj (hpriorRule.symm.trans hrule)
  subst priorRule
  refine ⟨rule, timestamp, hrule, hprior, ?_, ?_⟩
  · simpa only [runtime.tick_clock] using hexpired
  · simpa [PublicState.completed, hclear] using hrequires

variable [DecidableEq Principal]
variable (runtime : SealedResolution Principal Value)
variable (prepare : Service → Principal → Nat → Value → Service)
variable (applyMessage : ApplicationState Principal Value Service →
  Message Principal (SealedProgram.Payload Principal Value) →
    Option (ApplicationState Principal Value Service))
variable (hrecords : runtime.HandlerRecords applyMessage)

include hrecords

/-- The first timeout can only come from the application's clock command.
Submission, local delivery, replay, and every accepted or rejected inclusion
leave the timeout list unchanged. -/
theorem step_first_timeout_tick
    (before after : (runtime.host prepare applyMessage).State)
    (action : (runtime.host prepare applyMessage).Action)
    (hstep : after ∈ ((runtime.host prepare applyMessage).step before action).support)
    (hclear : before.application.visible.timeouts = [])
    (hstop : after.application.visible.timeouts ≠ []) :
    after.application.visible = (runtime.tick before.application).visible := by
  cases action with
  | privateCommand who command | submit who command | replay who command | deliver who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hstep
      subst after
      exact False.elim (hstop hclear)
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at hstep
      subst after
      apply False.elim
      apply hstop
      apply (runtime.host prepare applyMessage).includePending_application_invariant
        (fun state => state.visible.timeouts = []) ?_ before id hclear
      intro state message next hstate hnext
      obtain ⟨event, heffect⟩ := hrecords state message next hnext
      rw [heffect, runtime.refresh_false_timeouts]
      exact hstate
  | environment command =>
      simp only [MessageApplication.step, host, FinDist.map_pure,
        FinDist.mem_support_pure] at hstep
      subst after
      rfl

/-- Lift the clock origin of first timeout through the existing policy
invocation, without restricting either policy's observations or commands. -/
theorem invoke_first_timeout_tick
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).EnvironmentPolicy)
    (before after : (runtime.host prepare applyMessage).PolicyExecution)
    (invocation : @Invocation Principal)
    (hstep : after ∈ ((runtime.host prepare applyMessage).invoke players environment
      before invocation).support)
    (hclear : before.native.application.visible.timeouts = [])
    (hstop : after.native.application.visible.timeouts ≠ []) :
    after.native.application.visible = (runtime.tick before.native.application).visible := by
  rcases (runtime.host prepare applyMessage).invoke_native_step players environment
      before after invocation hstep with hsame | ⟨action, haction⟩
  · exact False.elim (hstop (congrArg (fun state => state.application.visible.timeouts)
      hsame |>.trans hclear))
  · exact runtime.step_first_timeout_tick prepare applyMessage hrecords
      before.native after.native action haction hclear hstop

/-- Every timeout at the first timeout snapshot has normally completed
prerequisites at its actual preceding invocation snapshot. The predecessor is
indexed in the same trace, so later coupling arguments can retain its relation
to the graph realization. No service or player-strategy condition is needed. -/
theorem tracePolicies_first_timeout_prerequisites
    (hwindow : 0 < runtime.window)
    (players : Principal → (runtime.host prepare applyMessage).PlayerPolicy)
    (environment : (runtime.host prepare applyMessage).EnvironmentPolicy)
    (schedule : List (@Invocation Principal))
    (initial : (runtime.host prepare applyMessage).PolicyExecution)
    (trace : (runtime.host prepare applyMessage).PolicyTrace)
    (htrace : trace ∈ ((runtime.host prepare applyMessage).tracePolicies
      players environment schedule initial).support)
    (hready : initial.native.application.visible.ReadySound runtime)
    (hclear : initial.native.application.visible.timeouts = [])
    (hstop : (trace.firstRelease (fun execution :
      (runtime.host prepare applyMessage).PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty)).native.application.visible.timeouts
        ≠ []) :
    let stop := fun execution : (runtime.host prepare applyMessage).PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    ∃ index < schedule.length,
      (trace.prefixThrough stop).length = index + 1 ∧
      trace.firstRelease stop = (trace.drop (index + 1)).first ∧
      (trace.drop index).first.native.application.visible.timeouts = [] ∧
      ∀ node ∈ (trace.firstRelease stop).native.application.visible.timeouts,
        ∃ rule timestamp,
          runtime.program.rules[node]? = some rule ∧
          (trace.drop index).first.native.application.visible.firstReady? node = some timestamp ∧
          rule.requires.all
            (SealedProgram.done (trace.drop index).first.native.application.visible.events)
              = true := by
  intro stop
  let app := runtime.host prepare applyMessage
  let cut := (trace.prefixThrough stop).length
  have hselected := trace.firstRelease_eq_drop_prefixThrough_length stop
  have hpositive : 0 < cut := by
    by_contra hnot
    have hzero : cut = 0 := by omega
    change trace.firstRelease stop = (trace.drop cut).first at hselected
    rw [hzero, PolicyTrace.drop,
      app.tracePolicies_first players environment schedule initial trace htrace] at hselected
    exact hstop (congrArg (fun execution => execution.native.application.visible.timeouts)
      hselected |>.trans hclear)
  have hlength := app.tracePolicies_length players environment schedule initial trace htrace
  have hbound : cut ≤ schedule.length :=
    (trace.prefixThrough_length_le stop).trans hlength.le
  have hindex : cut - 1 < schedule.length := by omega
  have hsucc : cut - 1 + 1 = cut := by omega
  have hbefore : (trace.drop (cut - 1)).first.native.application.visible.timeouts = [] := by
    have hfalse := trace.release_false_before_prefixThrough stop (cut - 1) (by omega)
    simpa [stop] using hfalse
  let invocation := schedule[cut - 1]'hindex
  have hinvocation : schedule[cut - 1]? = some invocation := by
    simp [invocation, hindex]
  have hinvoke := app.tracePolicies_drop_invoke players environment schedule initial trace
    htrace (cut - 1) invocation hinvocation
  have hselected' : trace.firstRelease stop = (trace.drop (cut - 1 + 1)).first := by
    simpa only [hsucc] using hselected
  rw [← hselected'] at hinvoke
  have heffect := runtime.invoke_first_timeout_tick prepare applyMessage hrecords players
    environment _ _ invocation hinvoke hbefore hstop
  have hbeforeReady := runtime.runPolicies_readySound prepare applyMessage hrecords players
    environment (schedule.take (cut - 1)) initial (trace.drop (cut - 1)).first hready
    (app.tracePolicies_drop_support players environment schedule initial trace htrace (cut - 1)).1
  refine ⟨cut - 1, hindex, hsucc.symm, hselected', hbefore, ?_⟩
  intro node hnode
  rw [heffect] at hnode
  obtain ⟨rule, timestamp, hrule, hstamp, _, hrequires⟩ :=
    runtime.tick_first_timeout_ready_before hwindow _ hbeforeReady hbefore node hnode
  exact ⟨rule, timestamp, hrule, hstamp, hrequires⟩

end Interaction.SealedResolution

/-- info: 'Interaction.SealedResolution.tick_first_timeout_ready_before'
depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tick_first_timeout_ready_before

/-- info: 'Interaction.SealedResolution.tracePolicies_first_timeout_prerequisites'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Interaction.SealedResolution.tracePolicies_first_timeout_prerequisites
