/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingSettlement
import Vegas.Compile.ApplicationGuardSoundness
import Vegas.Compile.WindowedApplicationDeadline
import Vegas.Compile.WindowedActivationFreshness

/-! # Source coupling for actual windowed binding resolution -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- An actually accepted ordinary binding at a ready source checkpoint chooses
its source value from the acceptance-time prepared snapshot. Missing or
ill-typed preparation chooses the supplied checkpoint-local fallback value.
The successful handler itself forces the authenticated canonical handle. -/
theorem handle_binding_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (id : MessageId P)
    (address : Nat) (handle : CommitmentHandle P Nat)
    (timeout : Option (PublicFallbackCode L ty))
    (fallbackValue : L.Val ty)
    (hactive : state.active = some activation)
    (hcode : runtime.image.lookup address = some (.bind
      { ((.here guard tail : SourceDecisionSite who
        (.commit name who guard tail) Γ name ty guard).bindingCode fresh build
          ((.here guard tail : SourceDecisionSite who
            (.commit name who guard tail) Γ name ty guard).compiledField fresh build)) with
        timeout := timeout }))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state ⟨id, .binding address handle⟩ = some resolved) :
    let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
      .here guard tail
    let chosen := ((state.base.prepared.lookup (who, site.compiledField fresh build)).bind
      (fun typed => typed.as? ty)).getD fallbackValue
    ∃ next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1,
      next.current.source = current.current.source.cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  dsimp only
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh build (site.compiledField fresh build)
  let timed : BindingCode P L := { code with timeout := timeout }
  obtain ⟨origin, base, horigin, _, hordered, hresolved⟩ :=
    runtime.handle_some state resolved ⟨id, .binding address handle⟩ hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base
      ⟨id, .binding address handle⟩ = some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base
      ⟨id, .binding address handle⟩ hordered
  let retimed : BindingCode P L := { timed with
    timeout := timed.timeout.map fun fallback =>
      { fallback with deadline := activation.since + runtime.windowOf timed.node } }
  have hlookup : (runtime.atOrigin activation.since).lookup address = some (.bind retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  rw [(runtime.atOrigin activation.since).handle_binding state.base address retimed hlookup
    id handle] at hunderlying
  split at hunderlying
  · rename_i haccept
    simp only [Option.some.injEq] at hunderlying
    obtain ⟨_, hcanonical, _, _, _⟩ := haccept
    change handle = (who, site.compiledField fresh build) at hcanonical
    obtain ⟨next, hsource, hnext⟩ :=
      SourceDecisionSite.bind_recoveredOr_source_coupling guard tail fresh build current
        state.base hrefines fallbackValue (fun value => unrestricted current.current.source value)
    refine ⟨next, hsource, ?_⟩
    rw [hresolved]
    change base.Refines next.current.graph.1
    rw [← hunderlying]
    simpa [hcanonical, ApplicationImage.State.bind, retimed, timed, code, site] using hnext
  · simp at hunderlying

/-- Before the active response window ends, every successful native handler at
a generated binding instruction is necessarily the authenticated ordinary
binding payload for that instruction. Expiry is not yet due, and every other
payload constructor conflicts with the active binding lookup. -/
theorem handle_before_window_binding_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (address deadline : Nat)
    (message : Message P (ApplicationImage.Payload P L))
    (hactive : state.active = some activation)
    (hkey : activation.key = address)
    (hclock : state.base.memory.clock ≤ activation.since + runtime.windowOf address)
    (hcode : runtime.image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ id,
      message = ⟨id, .binding address (who,
        (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)⟩ ∧
      let chosen := ((state.base.prepared.lookup (who,
        (.here guard tail : SourceDecisionSite who
          (.commit name who guard tail) Γ name ty guard).compiledField fresh build)).bind
            (fun typed => typed.as? ty)).getD
              (L.eval fallback.expr current.current.source.erasePubEnv)
      ∃ next : CoupledAt
          (compileCore (.commit name who guard tail) fresh build).graph
          (build.addCommitEvent name who guard fresh.1).1,
        next.current.source = current.current.source.cons chosen ∧
          resolved.base.Refines next.current.graph.1 := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let timed := fallback.bindingTimeoutCode fresh build deadline
  obtain ⟨origin, base, horigin, hcurrent, hordered, _⟩ :=
    runtime.handle_some state resolved message hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base message =
      some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hordered
  let retimed : BindingCode P L := { timed with
    timeout := timed.timeout.map fun timeout =>
      { timeout with deadline := activation.since + runtime.windowOf timed.node } }
  have hlookup : (runtime.atOrigin activation.since).lookup address = some (.bind retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  have hactiveAt : (runtime.atOrigin activation.since).activeAddress? state.base.memory =
      some address := by
    rw [hkey] at hcurrent
    simpa [atOrigin, ApplicationImage.activeAddress?, ApplicationImage.withDeadlines] using hcurrent
  have hadmitted : ∀ submittedAddress,
      message.payload.address? = some submittedAddress → submittedAddress = address := by
    intro submittedAddress hsubmitted
    by_contra hne
    have hrejected := (runtime.atOrigin activation.since).ordered_handle_reject state.base
      message submittedAddress hsubmitted (by
        rw [hactiveAt]
        exact fun heq => hne (Option.some.inj heq.symm))
    rw [hrejected] at hordered
    contradiction
  rcases message with ⟨id, payload⟩
  cases payload with
  | binding submittedAddress handle =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      rw [(runtime.atOrigin activation.since).handle_binding state.base address retimed
        hlookup id handle] at hunderlying
      split at hunderlying
      · rename_i haccept
        obtain ⟨_, hcanonical, _, _, _⟩ := haccept
        change handle = (who, site.compiledField fresh build) at hcanonical
        subst handle
        refine ⟨id, rfl, ?_⟩
        exact runtime.handle_binding_source_coupling guard tail fresh build current
          unrestricted state resolved activation id address
          (who, site.compiledField fresh build) (some ⟨deadline,
            fallback.compiled fresh build⟩)
          (L.eval fallback.expr current.current.source.erasePubEnv) hactive hcode
          hrefines hhandle
      · simp at hunderlying
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      have hrejected := runtime.handle_expireBinding_before_window state activation hactive
        address id hclock
      rw [hrejected] at hhandle
      contradiction
  | malformed data =>
      have hrejected := (runtime.atOrigin activation.since).ordered_handle_malformed
        state.base id data
      rw [hrejected] at hordered
      contradiction
  | choice submittedAddress value =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireChoice submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | conditional submittedAddress opening =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying

/-- Every successful message at an active generated binding instruction has a
source successor. Ordinary binding uses the acceptance-time snapshot (or the
fixed local fallback when unrecoverable); an accepted expiry uses the emitted
public fallback. This theorem needs no pre-window clock premise. -/
theorem handle_binding_or_expiry_source_coupling
    (runtime : WindowedApplication P L)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard)
    (state resolved : WindowedApplication.State P L)
    (activation : Activation Nat) (address deadline : Nat)
    (message : Message P (ApplicationImage.Payload P L))
    (hactive : state.active = some activation)
    (hkey : activation.key = address)
    (hcode : runtime.image.lookup address = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : state.base.Refines current.current.graph.1)
    (hhandle : runtime.handle state message = some resolved) :
    ∃ (chosen : L.Val ty)
      (next : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      next.current.source = current.current.source.cons chosen ∧
      resolved.base.Refines next.current.graph.1 ∧ resolved.FreshActivation := by
  let site : SourceDecisionSite who (.commit name who guard tail) Γ name ty guard :=
    .here guard tail
  let timed := fallback.bindingTimeoutCode fresh build deadline
  obtain ⟨origin, base, horigin, hcurrent, hordered, hresolved⟩ :=
    runtime.handle_some state resolved message hhandle
  have horiginEq : origin = activation := by
    rw [hactive] at horigin
    exact Option.some.inj horigin.symm
  subst origin
  have hunderlying : (runtime.atOrigin activation.since).handle state.base message =
      some base :=
    (runtime.atOrigin activation.since).application.withAdmission_handle_some
      (runtime.atOrigin activation.since).admitsMessage
      (runtime.atOrigin activation.since).admitsEnvironment state.base base message hordered
  let retimed : BindingCode P L := { timed with
    timeout := timed.timeout.map fun timeout =>
      { timeout with deadline := activation.since + runtime.windowOf timed.node } }
  have hlookup : (runtime.atOrigin activation.since).lookup address = some (.bind retimed) := by
    rw [atOrigin, ApplicationImage.lookup_withDeadlines, hcode]
    rfl
  have hactiveAt : (runtime.atOrigin activation.since).activeAddress? state.base.memory =
      some address := by
    rw [hkey] at hcurrent
    simpa [atOrigin, ApplicationImage.activeAddress?, ApplicationImage.withDeadlines] using hcurrent
  have hadmitted : ∀ submittedAddress,
      message.payload.address? = some submittedAddress → submittedAddress = address := by
    intro submittedAddress hsubmitted
    by_contra hne
    have hrejected := (runtime.atOrigin activation.since).ordered_handle_reject state.base
      message submittedAddress hsubmitted (by
        rw [hactiveAt]
        exact fun heq => hne (Option.some.inj heq.symm))
    rw [hrejected] at hordered
    contradiction
  rcases message with ⟨id, payload⟩
  cases payload with
  | binding submittedAddress handle =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      obtain ⟨next, hsource, hnext⟩ :=
        runtime.handle_binding_source_coupling guard tail fresh build current unrestricted
          state resolved activation id address handle (some ⟨deadline,
            fallback.compiled fresh build⟩)
          (L.eval fallback.expr current.current.source.erasePubEnv) hactive hcode
          hrefines hhandle
      exact ⟨_, next, hsource, hnext, runtime.handle_freshActivation state resolved _ hhandle⟩
  | expireBinding submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      rw [(runtime.atOrigin activation.since).handle_expireBinding state.base address retimed
        hlookup id] at hunderlying
      change (retimed.resolveTimeout? state.base.memory).map
        (fun value => state.base.defaultBind retimed ⟨retimed.ty, value⟩) =
          some (base : ApplicationImage.State P L) at hunderlying
      obtain ⟨value, hvalue, hbase⟩ := Option.map_eq_some_iff.mp hunderlying
      obtain ⟨_, _, _, timeout, htimeout, _, heval⟩ :=
        retimed.resolveTimeout?_some state.base.memory value hvalue
      have htimeout' : timeout = {
          deadline := activation.since + runtime.windowOf timed.node
          value := fallback.compiled fresh build } := by
        have := Option.some.inj htimeout.symm
        simpa [retimed, timed,
          SourceDecisionSite.PublicFallback.bindingTimeoutCode] using this
      subst timeout
      change L.Val ty at value
      change (fallback.compiled fresh build).evalStore? state.base.memory.store =
        some value at heval
      obtain ⟨hexpected, next, hsource, hnext⟩ :=
        fallback.defaultBind_source_coupling guard tail fresh build current state.base hrefines
      have hvalueEq : value = L.eval fallback.expr current.current.source.erasePubEnv := by
        rw [hexpected] at heval
        exact Option.some.inj heval.symm
      subst value
      refine ⟨_, next, hsource, ?_, runtime.handle_freshActivation state resolved _ hhandle⟩
      rw [hresolved]
      change base.Refines next.current.graph.1
      rw [← hbase]
      have hdefault : state.base.defaultBind retimed
          ⟨retimed.ty, L.eval fallback.expr current.current.source.erasePubEnv⟩ =
          state.base.defaultBind (site.bindingCode fresh build
            (site.compiledField fresh build))
            ⟨ty, L.eval fallback.expr current.current.source.erasePubEnv⟩ := by
        rfl
      rw [hdefault]
      exact hnext
  | malformed data =>
      have hrejected := (runtime.atOrigin activation.since).ordered_handle_malformed
        state.base id data
      rw [hrejected] at hordered
      contradiction
  | choice submittedAddress value =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | expireChoice submittedAddress =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying
  | conditional submittedAddress opening =>
      have haddress := hadmitted submittedAddress rfl
      subst submittedAddress
      simp [ApplicationImage.handle, hlookup] at hunderlying

/-- Resolving an active binding through an actual latest-submission environment
step carries the accepted message to its source successor. -/
theorem environment_latest_binding_source_coupling
    (runtime : WindowedApplication P L) (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (actor : P)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hpolicy : environment execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native) =
        FinDist.pure (runtime.liftEnvironmentCommand
          (runtime.image.application.latestSubmissionCommand actor
            (runtime.eraseEnvironmentView
              (MessageApplication.State.environmentView runtime.application execution.native)))))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players environment execution
      .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation := by
  let timed := fallback.bindingTimeoutCode fresh build deadline
  simp only [MessageApplication.invoke, hpolicy, FinDist.pure_bind] at hnext
  rcases runtime.image.application.latestSubmissionCommand_cases actor
    (runtime.eraseEnvironmentView
      (MessageApplication.State.environmentView runtime.application execution.native)) with
    hwait | ⟨id, hinclude⟩
  · rw [hwait] at hnext
    simp only [liftEnvironmentCommand] at hnext
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      EnvironmentPolicyCommand.toAction, FinDist.pure_bind,
      FinDist.mem_support_pure] at hnext
    subst next
    exact False.elim (hinactive hactive)
  · rw [hinclude] at hnext
    simp only [liftEnvironmentCommand] at hnext
    simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
      EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
      FinDist.mem_support_pure] at hnext
    subst next
    cases hlookup : execution.native.pool.lookup id with
    | none =>
        rw [runtime.application.includePending_missing execution.native id hlookup]
          at hinactive
        exact False.elim (hinactive hactive)
    | some message =>
        cases hhandle : runtime.handle execution.native.application message with
        | none =>
            rw [runtime.application.includePending_reject execution.native id message
              hlookup hhandle] at hinactive
            exact False.elim (hinactive hactive)
        | some resolved =>
            have hincluded := runtime.application.includePending_accept execution.native id
              message resolved hlookup hhandle
            obtain ⟨chosen, sourceNext, hsource, hresolved, hfresh⟩ :=
              runtime.handle_binding_or_expiry_source_coupling guard tail fallback fresh build
                current unrestricted execution.native.application resolved activation timed.node
                deadline message hactivation hkey hcode hrefines hhandle
            refine ⟨chosen, sourceNext, hsource, ?_, ?_⟩
            · rw [hincluded]
              exact hresolved
            · rw [hincluded]
              exact hfresh

/-- If the ordinary environment slot of an active binding block resolves the
instruction, the actual included pending message supplies a source successor.
Waiting, a missing identifier, and a rejected handler all preserve the active
address and therefore cannot inhabit this branch. -/
theorem blockEnvironment_normal_binding_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some (.bind
        (fallback.bindingTimeoutCode fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 0)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation := by
  let timed := fallback.bindingTimeoutCode fresh build deadline
  apply runtime.environment_latest_binding_source_coupling players
    (runtime.blockEnvironment roster) timed.owner guard tail fallback fresh build current
    unrestricted deadline execution next activation
  · exact runtime.blockEnvironment_normal roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      (.bind timed) hindex hactive hslot |>.trans (by
        simp [ApplicationImage.serviceCommand])
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- The reserved relay environment slot has the same source-coupling law even
when the relay player's preceding command is unrestricted. -/
theorem blockEnvironment_relay_binding_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (actor : P) (rosterIndex : Nat)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution next : runtime.application.PolicyExecution) (activation : Activation Nat)
    (instruction : ApplicationInstruction P L)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = rosterIndex + 2)
    (hwho : roster[rosterIndex]? = some actor)
    (hinstruction : instruction = .bind (fallback.bindingTimeoutCode fresh build deadline))
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? next.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution .environment).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      next.native.application.base.Refines sourceNext.current.graph.1 ∧
      next.native.application.FreshActivation := by
  apply runtime.environment_latest_binding_source_coupling players
    (runtime.blockEnvironment roster) actor guard tail fallback fresh build current unrestricted
    deadline execution next activation
  · have hpolicy := runtime.blockEnvironment_relay roster execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)
      instruction rosterIndex actor hindex (by
        rw [hinstruction]
        change runtime.image.activeAddress? execution.native.application.base.memory =
          some (fallback.bindingTimeoutCode fresh build deadline).node
        exact hactive) hslot hwho
    refine hpolicy.trans (congrArg FinDist.pure ?_)
    simp only [MessageApplication.latestSubmissionCommand, eraseEnvironmentView,
      MessageApplication.State.environmentView, WindowedApplication.application]
    cases hserial : execution.native.pool.nextSerial actor with
    | zero => rfl
    | succ serial =>
        simp only [liftEnvironmentCommand]
        split <;> rfl
  · exact hactive
  · exact hactivation
  · exact hkey
  · exact hcode
  · exact hrefines
  · exact hinactive
  · exact hnext

/-- A canonical relay reached through an actual clock-and-relay prefix carries
the concrete public fallback source successor through its complete relay pair.
Unlike the settlement-only theorem, this retains the witness supplied by the
accepted expiry handler. -/
theorem binding_relay_source_coupling_after_clock
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy) (relay sourceOwner : P)
    (base : runtime.application.PlayerPolicy)
    (hrelay : players relay = runtime.blockPlayer relay base)
    {Γ : VCtx P L} {name : VarId} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx sourceOwner Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed sourceOwner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name sourceOwner guard tail))
    (build : BuildState P L Γ) (deadline : Nat)
    (current : CoupledAt
      (compileCore (.commit name sourceOwner guard tail) fresh build).graph build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution middle after : runtime.application.PolicyExecution)
    (priorRelays : List (@Invocation P)) (rosterIndex : Nat)
    (hwho : roster[rosterIndex]? = some relay)
    (howner : instruction.submitter = some sourceOwner)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (Invocation.environment :: priorRelays).countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hmiddleActive : runtime.image.activeAddress?
      middle.native.application.base.memory = some instruction.address)
    (hmiddle : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (.environment :: priorRelays) execution).support)
    (hplayerIndex : runtime.image.instructions[(middle.principalHistory relay).length / 3]? =
      some instruction)
    (hplayerSlot : (middle.principalHistory relay).length % 3 = 2)
    (henvironmentIndex : runtime.image.instructions[middle.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (henvironmentSlot : middle.environmentHistory.length % (roster.length + 2) =
      rosterIndex + 2)
    (hafter : after ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) [.player relay, .environment] middle).support) :
    ∃ (chosen : L.Val ty)
      (next : CoupledAt
        (compileCore (.commit name sourceOwner guard tail) fresh build).graph
        (build.addCommitEvent name sourceOwner guard fresh.1).1),
      next.current.source = current.current.source.cons chosen ∧
      after.native.application.base.Refines next.current.graph.1 ∧
      after.native.application.FreshActivation ∧
      runtime.image.activeAddress? after.native.application.base.memory ≠
        some instruction.address := by
  obtain ⟨payload, resolved, hdue, hfresh, hhandle, next, hsource, hresolved⟩ :=
    runtime.binding_source_relay_eligibility_after_clock roster players guard tail fallback fresh
      build deadline current instruction activation execution middle priorRelays relay howner hindex
      hslot hactive hactivation hkey hcode hrefines hconsistent hserials hmiddleActive hmiddle
  have hlaw := runtime.block_relay_resolves_active roster players relay base hrelay middle
    instruction rosterIndex hplayerIndex hplayerSlot henvironmentIndex henvironmentSlot hwho
    hmiddleActive payload resolved hdue hfresh hhandle
  have happlication : after.native.application = resolved := by
    have hmem : after.native.application ∈
        ((runtime.application.runPolicies players (runtime.blockEnvironment roster)
          [.player relay, .environment] middle).map
            (fun result => result.native.application)).support := by
      rw [FinDist.support_map]
      exact ⟨after, hafter, rfl⟩
    rw [hlaw.1, FinDist.mem_support_pure] at hmem
    exact hmem
  refine ⟨_, next, hsource, ?_, ?_, ?_⟩
  · rwa [happlication]
  · rw [happlication]
    exact runtime.handle_freshActivation middle.native.application resolved _ hhandle
  · rw [happlication]
    exact hlaw.2

omit [DecidableEq P] in
private theorem bindingRelayPairs_environment_count (relays : List P) :
    (relays.flatMap fun relay =>
      [Invocation.player relay, Invocation.environment]).countP
        Invocation.isEnvironment = relays.length := by
  induction relays with
  | nil => rfl
  | cons relay rest ih =>
      simp only [List.flatMap_cons, List.countP_append, List.countP_cons,
        List.countP_nil, Invocation.isEnvironment, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero, Nat.zero_add, List.length_cons]
      rw [ih]
      omega

/-- If a sequence of reserved relay pairs takes an active generated binding
to an inactive state, the first resolving environment step supplies a legal
source successor. Earlier pairs may use arbitrary player policies; while the
address remains active they preserve the original source refinement, and the
inactive suffix preserves the resolved refinement and fresh activation. -/
theorem runPolicies_binding_relay_pairs_source_coupling
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (relays : List P) (rosterOffset : Nat)
    {Γ : VCtx P L} {name : VarId} {who : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed who ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name who guard tail))
    (build : BuildState P L Γ)
    (current : CoupledAt
      (compileCore (.commit name who guard tail) fresh build).graph build)
    (unrestricted : UnrestrictedBinding guard) (deadline : Nat)
    (execution final : runtime.application.PolicyExecution)
    (activation : Activation Nat)
    (hrelays : ∀ index actor, relays[index]? = some actor →
      roster[rosterOffset + index]? = some actor)
    (hbound : rosterOffset + relays.length ≤ roster.length)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length + relays.length →
      runtime.image.instructions[index / (roster.length + 2)]? =
        some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hslot : execution.environmentHistory.length % (roster.length + 2) =
      rosterOffset + 2)
    (hactive : runtime.image.activeAddress? execution.native.application.base.memory =
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = (fallback.bindingTimeoutCode fresh build deadline).node)
    (hcode : runtime.image.lookup (fallback.bindingTimeoutCode fresh build deadline).node =
      some (.bind (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hinactive : runtime.image.activeAddress? final.native.application.base.memory ≠
      some (fallback.bindingTimeoutCode fresh build deadline).node)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster)
      (relays.flatMap fun actor => [Invocation.player actor, .environment])
      execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt
        (compileCore (.commit name who guard tail) fresh build).graph
        (build.addCommitEvent name who guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      final.native.application.base.Refines sourceNext.current.graph.1 ∧
      final.native.application.FreshActivation := by
  induction relays generalizing rosterOffset execution activation with
  | nil =>
      simp only [List.flatMap_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at hfinal
      subst final
      exact False.elim (hinactive hactive)
  | cons actor rest ih =>
      have hactor : roster[rosterOffset]? = some actor := by
        simpa using hrelays 0 actor rfl
      have hoffset : rosterOffset < roster.length := by
        exact List.getElem?_eq_some_iff.mp hactor |>.1
      have hpairIndex : ∀ index, execution.environmentHistory.length ≤ index →
          index < execution.environmentHistory.length +
            [Invocation.player actor, Invocation.environment].countP
              Invocation.isEnvironment →
          runtime.image.instructions[index / (roster.length + 2)]? =
            some (.bind (fallback.bindingTimeoutCode fresh build deadline)) := by
        intro index hlo hhi
        apply hindex index hlo
        simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
          Bool.false_eq_true, ↓reduceIte] at hhi
        simp only [List.length_cons]
        omega
      rw [List.flatMap_cons, show
        [Invocation.player actor, Invocation.environment] ++
          rest.flatMap (fun relay => [Invocation.player relay, Invocation.environment]) =
        Invocation.player actor :: Invocation.environment ::
          rest.flatMap (fun relay => [Invocation.player relay, Invocation.environment]) by rfl,
        MessageApplication.runPolicies] at hfinal
      simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
      obtain ⟨afterPlayer, hplayer, hafterPlayer⟩ := hfinal
      simp only [MessageApplication.runPolicies, FinDist.support_bind,
        Set.mem_iUnion] at hafterPlayer
      obtain ⟨afterRelay, henvironment, hrest⟩ := hafterPlayer
      have hplayerRun : afterPlayer ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster) [Invocation.player actor] execution).support := by
        simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hplayer
      have hpair : afterRelay ∈ (runtime.application.runPolicies players
          (runtime.blockEnvironment roster)
          [Invocation.player actor, Invocation.environment] execution).support := by
        rw [show [Invocation.player actor, Invocation.environment] =
          [Invocation.player actor] ++ [Invocation.environment] by rfl,
          MessageApplication.runPolicies_append, FinDist.support_bind]
        exact Set.mem_iUnion.mpr ⟨afterPlayer, Set.mem_iUnion.mpr ⟨hplayerRun,
          by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment⟩⟩
      have hpublic := runtime.runPolicies_players_publicState players
        (runtime.blockEnvironment roster) [Invocation.player actor] (by simp)
        execution afterPlayer hplayerRun
      have hplayerActive : runtime.image.activeAddress?
          afterPlayer.native.application.base.memory =
          some (fallback.bindingTimeoutCode fresh build deadline).node := by
        have hmemory := congrArg Prod.fst hpublic
        change afterPlayer.native.application.base.memory =
          execution.native.application.base.memory at hmemory
        rw [hmemory]
        exact hactive
      have hplayerActivation : afterPlayer.native.application.active = some activation := by
        have hactiveEq := congrArg Prod.snd hpublic
        change afterPlayer.native.application.active = execution.native.application.active
          at hactiveEq
        exact hactiveEq.trans hactivation
      have hplayerRefines : afterPlayer.native.application.base.Refines
          current.current.graph.1 := by
        exact (runtime.runPolicies_refines_of_final_active roster players
          [Invocation.player actor] execution afterPlayer
          (.bind (fallback.bindingTimeoutCode fresh build deadline)) who
          current.current.graph.1 (by rfl) (by
            intro index hlo hhi
            simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
              Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hhi
            omega) hrefines hactive hplayerActive
          hplayerRun).1
      have hplayerLength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [Invocation.player actor] execution afterPlayer
        hplayerRun
      have hrelayLength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [Invocation.environment] afterPlayer afterRelay
        (by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment)
      by_cases hafterActive : runtime.image.activeAddress?
          afterRelay.native.application.base.memory =
          some (fallback.bindingTimeoutCode fresh build deadline).node
      · obtain ⟨hrelayRefines, hrelayActivation, _⟩ :=
          runtime.runPolicies_refines_of_final_active roster players
            [Invocation.player actor, Invocation.environment] execution afterRelay
            (.bind (fallback.bindingTimeoutCode fresh build deadline)) who
            current.current.graph.1 (by rfl) hpairIndex hrefines hactive hafterActive hpair
        cases rest with
        | nil =>
            simp only [List.flatMap_nil, MessageApplication.runPolicies,
              FinDist.mem_support_pure] at hrest
            subst final
            exact False.elim (hinactive hafterActive)
        | cons nextRelay remaining =>
            apply ih (rosterOffset := rosterOffset + 1) (execution := afterRelay)
              (activation := activation)
            · intro index candidate hcandidate
              have hshift : (actor :: nextRelay :: remaining)[index + 1]? =
                  some candidate := by
                simpa [List.getElem?_cons] using hcandidate
              simpa [Nat.add_assoc, Nat.add_comm 1 index, Nat.add_left_comm] using
                hrelays (index + 1) candidate hshift
            · simp only [List.length_cons] at hbound ⊢
              omega
            · intro index hlo hhi
              apply hindex index
              · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
                omega
              · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
                simp only [List.length_cons] at hhi ⊢
                omega
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              rw [hrelayLength, hplayerLength]
              simp only [List.length_cons] at hbound
              have hlt : rosterOffset + 2 + 1 < roster.length + 2 := by omega
              have hone : 1 % (roster.length + 2) = 1 :=
                Nat.mod_eq_of_lt (by omega)
              rw [Nat.add_mod, hslot, hone, Nat.mod_eq_of_lt hlt]
            · exact hafterActive
            · exact hrelayActivation.trans hactivation
            · exact hkey
            · exact hrelayRefines
            · exact hrest
      · obtain ⟨chosen, sourceNext, hsource, hnextRefines, hnextFresh⟩ :=
          runtime.blockEnvironment_relay_binding_source_coupling roster players actor
            rosterOffset guard tail fallback fresh build current unrestricted deadline
            afterPlayer afterRelay activation
            (.bind (fallback.bindingTimeoutCode fresh build deadline))
            (by
              rw [hplayerLength]
              apply hindex execution.environmentHistory.length
              · exact Nat.le_refl _
              · simp only [List.length_cons]
                omega)
            (by
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength
              rw [hplayerLength, hslot]) hactor rfl hplayerActive hplayerActivation hkey
            hcode hplayerRefines hafterActive
            (by simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using henvironment)
        refine ⟨chosen, sourceNext, hsource, ?_, ?_⟩
        · apply runtime.runPolicies_block_inactive_refines sourceNext.current.graph.1 roster
            players (rest.flatMap fun relay =>
              [Invocation.player relay, Invocation.environment]) afterRelay final
            (.bind (fallback.bindingTimeoutCode fresh build deadline))
          · intro index hlo hhi
            apply hindex index
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              omega
            · rw [bindingRelayPairs_environment_count] at hhi
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              simp only [List.length_cons]
              omega
          · exact hafterActive
          · exact hnextRefines
          · exact hrest
        · apply runtime.runPolicies_block_inactive_freshActivation roster players
            (rest.flatMap fun relay => [Invocation.player relay, Invocation.environment])
            afterRelay final (.bind (fallback.bindingTimeoutCode fresh build deadline))
          · intro index hlo hhi
            apply hindex index
            · simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              omega
            · rw [bindingRelayPairs_environment_count] at hhi
              simp only [List.countP_cons, List.countP_nil, Invocation.isEnvironment,
                  Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hplayerLength hrelayLength
              simp only [List.length_cons]
              omega
          · exact hafterActive
          · exact hnextFresh
          · exact hrest

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_before_window_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_before_window_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.handle_binding_or_expiry_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_binding_or_expiry_source_coupling

/-- info: 'Vegas.WindowedApplication.environment_latest_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.environment_latest_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.blockEnvironment_normal_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.blockEnvironment_normal_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.blockEnvironment_relay_binding_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.blockEnvironment_relay_binding_source_coupling

/-- info: 'Vegas.WindowedApplication.binding_relay_source_coupling_after_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.binding_relay_source_coupling_after_clock

/-- info: 'Vegas.WindowedApplication.runPolicies_binding_relay_pairs_source_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_binding_relay_pairs_source_coupling
