/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.BindingRepairInformation
import Vegas.Source.AdmissionRestriction

/-! # Coupled source prefixes with one player's failed commitments repaired

The repair relation retains deferred guards, publication status and every
foreign player's full original recall. It is a relation between existing source
configurations; it does not add states, observations or actions to either game.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def repairBinding (owner who : Player) {payload : L.Ty}
    (binding : PublicationResult (L.Val payload)) : PublicationResult (L.Val payload) :=
  if owner = who then match binding with
    | .failure => .success (L.someValue payload)
    | .success value => .success value
  else binding

namespace Config

def FocalRepair (who : Player) {Γ : SourceCtx Player L}
    (original repaired : Config Player L Γ) : Prop :=
  ∃ unpatch : ViewMap who Γ, ∃ patched : PatchMap who Γ,
    Patched unpatch patched original.state repaired.state original.history repaired.history ∧
      original.registry = repaired.registry ∧ @original.revelations = @repaired.revelations

omit [IExpr.ResultTypes L] in
theorem FocalRepair.refl (who : Player) {Γ : SourceCtx Player L}
    (config : Config Player L Γ) : FocalRepair who config config :=
  ⟨id, fun _ _ => false, Patched.refl config.state config.history, rfl, rfl⟩

omit [IExpr.ResultTypes L] in
theorem FocalRepair.foreign_view {who observer : Player} {Γ : SourceCtx Player L}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (foreign : observer ≠ who) : repaired.view observer = original.view observer := by
  obtain ⟨_, _, patched, _, _⟩ := related
  exact patched.foreign_view_eq foreign

omit [IExpr.ResultTypes L] in
theorem FocalRepair.sample {who : Player} {Γ : SourceCtx Player L} {payload : L.Ty}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (name : VarId) (value : L.Val payload) :
    FocalRepair who (sampleSuccessor name original value)
      (sampleSuccessor name repaired value) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  exact ⟨unpatch.afterSample name payload, patched.afterSample name payload,
    patched_sample invariant name payload value, congrArg Registry.weaken registry,
    congrArg Revelations.weaken revelations⟩

omit [IExpr.ResultTypes L] in
theorem FocalRepair.commit {who owner : Player} {Γ : SourceCtx Player L} {payload : L.Ty}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    (binding : PublicationResult (L.Val payload)) :
    FocalRepair who (commitSuccessor name guard original binding)
      (commitSuccessor name guard repaired
        (repairBinding owner who binding)) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  unfold repairBinding
  by_cases own : owner = who
  · subst owner
    refine ⟨unpatch.afterCommit (decide (who = who)) name who payload (fun _ => some binding),
      patched.afterCommit (decide (who = who)) name who payload (fun _ => some binding),
      ?_, ?_, ?_⟩
    · have preserved := patched_commit_own invariant name payload binding _ rfl
        (fun _ => some binding) rfl
      cases binding <;> simpa [commitSuccessor] using preserved
    · simp only [commitSuccessor, registry]
    · exact congrArg Revelations.weaken revelations
  · refine ⟨unpatch.afterCommit (decide (owner = who)) name owner payload (fun _ => none),
      patched.afterCommit (decide (owner = who)) name owner payload (fun _ => none),
      ?_, ?_, ?_⟩
    · simpa only [commitSuccessor, ite_eq_right own] using
        patched_commit_foreign invariant name owner payload own binding (fun _ => none)
          (fun _ => rfl)
    · simp only [commitSuccessor, registry]
    · exact congrArg Revelations.weaken revelations

omit [IExpr.ResultTypes L] in
theorem FocalRepair.reveal {who owner : Player} {Γ : SourceCtx Player L}
    {payload : L.Ty} {name : VarId} {original repaired : Config Player L Γ}
    (related : FocalRepair who original repaired) (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    ∃ translated : Bool,
      FocalRepair who (revealSuccessor published source original disclose)
        (revealSuccessor published source repaired translated) ∧
      (owner ≠ who → translated = disclose) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  have accepted (proposal : PublicationResult (L.Val payload)) :
      (repaired.registry.completedBy (published := published) repaired.revelations source).all
        (·.accepts (Revelations.reveal (@repaired.revelations) (published := published) source)
          (Env.cons proposal repaired.state)) =
      (original.registry.completedBy (published := published) original.revelations source).all
        (·.accepts (Revelations.reveal (@original.revelations) (published := published) source)
          (Env.cons proposal original.state)) := by
    rw [← registry, ← revelations]
    refine congrArg (List.all _) (funext fun obligation => ?_)
    exact Obligation.accepts_congr obligation _ _ _
      (fun cell => match cell with | .there prior => invariant.publicEq prior)
      (fun cell => match cell with
        | .here => rfl
        | .there prior => invariant.publicationEq prior)
  by_cases own : owner = who
  · subst owner
    let translated := if patched source (sourceObserve who repaired.state, repaired.history who)
      then false else disclose
    have proposal := proposal_eq invariant source disclose
    have result : (revealSuccessor published source repaired translated).state.get .here =
        (revealSuccessor published source original disclose).state.get .here := by
      simp only [revealSuccessor, Env.cons_get_here, translated] at proposal ⊢
      simp_rw [proposal]
      rw [accepted]
    simp only [revealSuccessor, Env.cons_get_here] at result
    refine ⟨translated, ?_, fun foreign => (foreign rfl).elim⟩
    refine ⟨unpatch.afterReveal (decide (who = who)) published name who payload (fun _ => some
      disclose),
      patched.afterReveal (decide (who = who)) published payload, ?_, ?_, ?_⟩
    · simpa only [revealSuccessor, Env.cons_get_here, result] using
        patched_reveal_own invariant published name payload
          ((revealSuccessor published source original disclose).state.get .here)
          disclose translated (fun _ => some disclose) rfl
    · simpa only [revealSuccessor] using congrArg Registry.weaken registry
    · simp only [revealSuccessor, revelations]
  · have binding := invariant.foreignEq source own
    have result : (revealSuccessor published source repaired disclose).state.get .here =
        (revealSuccessor published source original disclose).state.get .here := by
      simp only [revealSuccessor, Env.cons_get_here]
      rw [binding, accepted]
    simp only [revealSuccessor, Env.cons_get_here] at result
    refine ⟨disclose, ?_, fun _ => rfl⟩
    refine ⟨unpatch.afterReveal (decide (owner = who)) published name owner payload (fun _ => none),
      patched.afterReveal (decide (owner = who)) published payload, ?_, ?_, ?_⟩
    · simpa only [revealSuccessor, Env.cons_get_here, result] using
        patched_reveal_foreign invariant published name owner payload own
          ((revealSuccessor published source original disclose).state.get .here)
          disclose (fun _ => none)
    · simpa only [revealSuccessor] using congrArg Registry.weaken registry
    · simp only [revealSuccessor, revelations]

end Config

namespace ProtocolState

def FocalRepair (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → ProtocolState program → Prop
  | _, _, .ret _, original, repaired => Config.FocalRepair who original repaired
  | _, _, .sample _ _ _ next, original, repaired =>
      match original, repaired with
      | .inl first, .inl second => Config.FocalRepair who first second
      | .inr first, .inr second => FocalRepair who next first second
      | _, _ => False
  | _, _, .commit _ _ _ _ next, original, repaired =>
      match original, repaired with
      | .inl first, .inl second => Config.FocalRepair who first second
      | .inr first, .inr second => FocalRepair who next first second
      | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired =>
      match original, repaired with
      | .inl first, .inl second => Config.FocalRepair who first second
      | .inr first, .inr second => FocalRepair who next first second
      | _, _ => False

theorem focalRepair_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {original repaired : Config Player L Γ}
    (related : Config.FocalRepair who original repaired) :
    FocalRepair who program (entry program original) (entry program repaired) := by
  cases program <;> exact related

theorem FocalRepair.foreign_observe (who observer : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (original repaired : ProtocolState program) →
    FocalRepair who program original repaired → observer ≠ who →
      observe observer program repaired = observe observer program original
  | _, _, .ret _, original, repaired, related, foreign => related.foreign_view foreign
  | _, _, .sample _ _ _ next, original, repaired, related, foreign => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl (related.foreign_view foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)
  | _, _, .commit _ _ _ _ next, original, repaired, related, foreign => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl (related.foreign_view foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired, related, foreign => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl (related.foreign_view foreign)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (foreign_observe who observer next _ _ related foreign)

theorem FocalRepair.terminal_iff (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (original repaired : ProtocolState program) →
    FocalRepair who program original repaired →
      (terminal program repaired ↔ terminal program original)
  | _, _, .ret _, _, _, _ => Iff.rfl
  | _, _, .sample _ _ _ next, original, repaired, related => by
      cases original <;> cases repaired
      · exact Iff.rfl
      · exact related.elim
      · exact related.elim
      · exact terminal_iff who next _ _ related
  | _, _, .commit _ _ _ _ next, original, repaired, related => by
      cases original <;> cases repaired
      · exact Iff.rfl
      · exact related.elim
      · exact related.elim
      · exact terminal_iff who next _ _ related
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired, related => by
      cases original <;> cases repaired
      · exact Iff.rfl
      · exact related.elim
      · exact related.elim
      · exact terminal_iff who next _ _ related


/-- A supported legal source transition has a legal value-interface partner
when every foreign choice comes from its value menu. -/
theorem FocalRepair.step (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (original repaired target : ProtocolState program) →
    FocalRepair who program original repaired → ¬ terminal program original →
    (joint : Player → Option (OwnAction Player L)) →
    (∀ observer, ProtocolView.menu observer program admission
      (observe observer program original) (joint observer)) →
    (∀ observer, observer ≠ who → ProtocolView.menu observer program
      (CommitmentInterface.values program) (observe observer program original) (joint observer)) →
    target ∈ (ProtocolState.step program original joint).support →
    ∃ translated : Player → Option (OwnAction Player L),
      (∀ observer, observer ≠ who → translated observer = joint observer) ∧
      (∀ observer, ProtocolView.menu observer program (CommitmentInterface.values program)
        (observe observer program repaired) (translated observer)) ∧
      ∃ repairedTarget, repairedTarget ∈ (ProtocolState.step program repaired translated).support ∧
        FocalRepair who program target repairedTarget
  | _, _, .ret _, _, _, _, _, _, running, _, _, _, _ => (running trivial).elim
  | _, _, .sample name fresh law next, admission, original, repaired, target,
      related, running, joint, legal, foreign, reached => by
      cases original with
      | inl original =>
          cases repaired with
          | inr repaired => exact related.elim
          | inl repaired =>
              obtain ⟨value, supported, rfl⟩ := PMF.support_map .. ▸ reached
              refine ⟨joint, fun _ _ => rfl, ?_,
                .inr (entry next (sampleSuccessor name repaired value)), ?_, ?_⟩
              · intro observer
                have permitted := legal observer
                cases selected : joint observer <;>
                  simp [ProtocolView.menu, observe, ProtocolView.actor, selected] at permitted ⊢
              · obtain ⟨_, _, patched, _, _⟩ := related
                simp only [ProtocolState.step, Sum.elim_inl, PMF.support_map]
                refine ⟨value, ?_, rfl⟩
                rw [sourcePublicEnv_congr repaired.state original.state
                  patched.publicEq patched.publicationEq]
                exact supported
              · exact focalRepair_entry who next (related.sample name value)
      | inr original =>
          cases repaired with
          | inl repaired => exact related.elim
          | inr repaired =>
              obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
              obtain ⟨translated, same, permitted, repairedTarget, supported', related'⟩ :=
                FocalRepair.step who next admission original repaired target related running
                  joint legal foreign supported
              refine ⟨translated, same, permitted, .inr repairedTarget, ?_, related'⟩
              exact PMF.support_map .. ▸ ⟨repairedTarget, supported', rfl⟩
  | _, _, .commit (payload := payload) name owner fresh guard next, admission,
      original, repaired, target, related, running, joint, legal, foreign, reached => by
      cases original with
      | inl original =>
          cases repaired with
          | inr repaired => exact related.elim
          | inl repaired =>
              have ownLegal := legal owner
              obtain ⟨binding, admitted, chosen⟩ :
                  ∃ binding, (admission none).Admits binding ∧
                    joint owner = some (.commit owner name payload binding) := by
                cases selected : joint owner with
                | none =>
                    simp [ProtocolView.menu, observe, ProtocolView.actor, selected] at ownLegal
                | some action =>
                    simp only [ProtocolView.menu, selected, observe, Sum.elim_inl,
                      ProtocolView.actor, ProtocolView.available] at ownLegal
                    obtain ⟨_, binding, admitted, rfl⟩ := ownLegal
                    exact ⟨binding, admitted, rfl⟩
              let replacement : PublicationResult (L.Val payload) :=
                repairBinding owner who binding
              let translated := Function.update joint owner
                (some (.commit owner name payload replacement))
              have allowed : (CommitmentInterface.values
                  (.commit name owner fresh guard next) none).Admits replacement := by
                by_cases own : owner = who
                · cases binding <;> simp [replacement, repairBinding, own,
                  CommitmentInterface.values]
                · have permitted := foreign owner own
                  rw [chosen] at permitted
                  simp only [ProtocolView.menu, observe, Sum.elim_inl,
                    ProtocolView.available] at permitted
                  obtain ⟨_, result, resultAllowed, same⟩ := permitted
                  have equal : result = binding := by
                    simpa only [OwnAction.commit.injEq, heq_eq_eq, true_and] using same.symm
                  subst result
                  simpa only [replacement, repairBinding, ite_eq_right own] using resultAllowed
              have unchanged (observer : Player) (other : observer ≠ who) :
                  translated observer = joint observer := by
                by_cases ownerEq : observer = owner
                · subst observer
                  simp only [translated, Function.update_self, replacement, repairBinding,
                    ite_eq_right other]
                  exact chosen.symm
                · exact Function.update_of_ne ownerEq _ _
              have permitted (observer : Player) : ProtocolView.menu observer
                  (.commit name owner fresh guard next) (CommitmentInterface.values _)
                  (observe observer (.commit name owner fresh guard next) (.inl repaired))
                  (translated observer) := by
                by_cases same : observer = owner
                · subst observer
                  simp only [translated, Function.update_self, ProtocolView.menu, observe,
                    Sum.elim_inl, ProtocolView.actor, ProtocolView.available]
                  exact ⟨trivial, replacement, allowed, rfl⟩
                · rw [show translated observer = joint observer from
                    Function.update_of_ne same _ _]
                  have ownLegal := legal observer
                  cases selected : joint observer <;>
                    simp [ProtocolView.menu, observe, ProtocolView.actor,
                      ProtocolView.available, selected, Ne.symm same] at ownLegal ⊢
              simp only [ProtocolState.step, Sum.elim_inl, chosen,
                OwnAction.binding_commit, PMF.mem_support_pure_iff _ _] at reached
              subst target
              refine ⟨translated, unchanged, permitted,
                .inr (entry next (commitSuccessor name guard repaired replacement)), ?_, ?_⟩
              · simp only [ProtocolState.step, Sum.elim_inl, translated, Function.update_self,
                  OwnAction.binding_commit, PMF.mem_support_pure_iff _ _]
              · exact focalRepair_entry who next (related.commit name guard binding)
      | inr original =>
          cases repaired with
          | inl repaired => exact related.elim
          | inr repaired =>
              obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
              obtain ⟨translated, same, permitted, repairedTarget, supported', related'⟩ :=
                FocalRepair.step who next (fun site => admission (some site))
                  original repaired target related running joint legal foreign supported
              refine ⟨translated, same, permitted, .inr repairedTarget, ?_, related'⟩
              exact PMF.support_map .. ▸ ⟨repairedTarget, supported', rfl⟩
  | _, _, .reveal published owner name fresh source unresolved next, admission,
      original, repaired, target, related, running, joint, legal, foreign, reached => by
      cases original with
      | inl original =>
          cases repaired with
          | inr repaired => exact related.elim
          | inl repaired =>
              have ownLegal := legal owner
              obtain ⟨disclose, chosen⟩ :
                  ∃ disclose, joint owner = some (.reveal owner name disclose) := by
                cases selected : joint owner with
                | none =>
                    simp [ProtocolView.menu, observe, ProtocolView.actor, selected] at ownLegal
                | some action =>
                    simp only [ProtocolView.menu, selected, observe, Sum.elim_inl,
                      ProtocolView.actor, ProtocolView.available] at ownLegal
                    obtain ⟨_, disclose, rfl⟩ := ownLegal
                    exact ⟨disclose, rfl⟩
              obtain ⟨disclose', repairedStep, unchanged⟩ := related.reveal published source
                disclose
              let translated := Function.update joint owner (some (.reveal owner name disclose'))
              refine ⟨translated, ?_, ?_,
                .inr (entry next (revealSuccessor published source repaired disclose')), ?_, ?_⟩
              · intro observer other
                by_cases ownerEq : observer = owner
                · subst observer
                  simp only [translated, Function.update_self, unchanged other]
                  exact chosen.symm
                · exact Function.update_of_ne ownerEq _ _
              · intro observer
                by_cases same : observer = owner
                · subst observer
                  simp only [translated, Function.update_self, ProtocolView.menu, observe,
                    Sum.elim_inl, ProtocolView.actor, ProtocolView.available]
                  exact ⟨trivial, disclose', rfl⟩
                · rw [show translated observer = joint observer from
                    Function.update_of_ne same _ _]
                  have permitted := legal observer
                  cases selected : joint observer <;>
                    simp [ProtocolView.menu, observe, ProtocolView.actor,
                      ProtocolView.available, selected, Ne.symm same] at permitted ⊢
              · simp only [ProtocolState.step, Sum.elim_inl, translated, Function.update_self,
                  OwnAction.disclosure, PMF.mem_support_pure_iff _ _]
              · simp only [ProtocolState.step, Sum.elim_inl, chosen,
                  OwnAction.disclosure, PMF.mem_support_pure_iff _ _] at reached
                subst target
                exact focalRepair_entry who next repairedStep
      | inr original =>
          cases repaired with
          | inl repaired => exact related.elim
          | inr repaired =>
              obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
              obtain ⟨translated, same, permitted, repairedTarget, supported', related'⟩ :=
                FocalRepair.step who next admission original repaired target related running
                  joint legal foreign supported
              refine ⟨translated, same, permitted, .inr repairedTarget, ?_, related'⟩
              exact PMF.support_map .. ▸ ⟨repairedTarget, supported', rfl⟩

end ProtocolState


/-- Every foreign action of this actual path belongs to the value menu. -/
def ForeignValuesPrefix {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (who : Player) :
    ∀ {state}, (executionProtocol program admission initial).Trace state → Prop
  | _, .start => True
  | _, .extend (source := source) prior joint _ _ =>
      ForeignValuesPrefix program admission initial who prior ∧
        ∀ observer, observer ≠ who → ProtocolView.menu observer program
          (CommitmentInterface.values program) (ProtocolState.observe observer program source)
          (joint observer)

/-- Repairing the focal player's failed commitments produces an actual legal
value-interface path of the same length, with every foreign observation and
original action recall preserved. -/
theorem exists_values_prefix {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (who : Player)
    {state : ProtocolState program} (trace : (executionProtocol program admission
      initial).Trace state)
    (foreignValues : ForeignValuesPrefix program admission initial who trace) :
    ∃ repaired : ProtocolState program,
      ∃ repairedTrace : (executionProtocol program (CommitmentInterface.values program)
        initial).Trace
        repaired,
        repairedTrace.length = trace.length ∧
          ProtocolState.FocalRepair who program state repaired ∧
          ∀ observer, observer ≠ who →
            (informationModel program (CommitmentInterface.values program) initial).infoOf
              observer repairedTrace =
            (informationModel program admission initial).infoOf observer trace := by
  have represented : ∀ {current : (executionProtocol program admission initial).State}
      (path : (executionProtocol program admission initial).Trace current),
      ForeignValuesPrefix program admission initial who path →
      ∃ repaired : ProtocolState program,
        ∃ repairedTrace :
          (executionProtocol program (CommitmentInterface.values program) initial).Trace repaired,
          repairedTrace.length = path.length ∧
            ProtocolState.FocalRepair who program current repaired := by
    intro current path
    refine Trace.rec
      (motive := fun current path => ForeignValuesPrefix program admission initial who path →
        ∃ repaired : ProtocolState program,
          ∃ repairedTrace :
            (executionProtocol program (CommitmentInterface.values program) initial).Trace repaired,
            repairedTrace.length = path.length ∧
              ProtocolState.FocalRepair who program current repaired) ?_ ?_ path
    · intro _
      refine ⟨_, .start, rfl, ?_⟩
      exact ProtocolState.focalRepair_entry who program (Config.FocalRepair.refl who initial)
    · intro source target prior joint legal realized ih foreignValues
      obtain ⟨repaired, repairedTrace, length, related⟩ := ih foreignValues.1
      have permitted : ∀ observer, ProtocolView.menu observer program admission
          (ProtocolState.observe observer program source) (joint observer) := by
        intro observer
        cases selected : joint observer <;>
          simpa only [executionProtocol, ProtocolView.menu, selected] using legal.2 observer
      obtain ⟨translated, _, permitted', repairedTarget, realized', related'⟩ :=
        ProtocolState.FocalRepair.step who program admission source repaired target related
          legal.1 joint permitted foreignValues.2 realized
      have legal' : (executionProtocol program (CommitmentInterface.values program) initial).Legal
          repaired translated := by
        refine ⟨fun stopped => legal.1
          ((ProtocolState.FocalRepair.terminal_iff who program source repaired related).mp stopped),
          ?_⟩
        intro observer
        cases selected : translated observer <;>
          simpa only [executionProtocol, ProtocolView.menu, selected] using permitted' observer
      exact ⟨repairedTarget, repairedTrace.extend translated legal' realized',
        congrArg (· + 1) length, related'⟩
  obtain ⟨repaired, repairedTrace, length, related⟩ := represented trace foreignValues
  refine ⟨repaired, repairedTrace, length, related, ?_⟩
  intro observer foreign
  rw [show (informationModel program (CommitmentInterface.values program) initial).infoOf
    observer repairedTrace = ProtocolState.observe observer program repaired from protocol_info ..]
  rw [show (informationModel program admission initial).infoOf observer trace =
    ProtocolState.observe observer program state from protocol_info ..]
  exact ProtocolState.FocalRepair.foreign_observe who observer program state repaired related
    foreign


namespace Setup

variable (setup : Setup (Player := Player) (L := L))

def FocalRepair (who : Player) : setup.ProtocolState → setup.ProtocolState → Prop
  | none, none => True
  | some original, some repaired => ProtocolState.FocalRepair who setup.program original repaired
  | _, _ => False

theorem FocalRepair.foreign_observe {who observer : Player}
    {original repaired : setup.ProtocolState} (related : setup.FocalRepair who original repaired)
    (foreign : observer ≠ who) :
    setup.protocolObserve observer repaired = setup.protocolObserve observer original := by
  cases original <;> cases repaired
  · rfl
  · exact related.elim
  · exact related.elim
  · exact congrArg some
      (ProtocolState.FocalRepair.foreign_observe who observer setup.program _ _ related foreign)

theorem FocalRepair.terminal_iff {who : Player} {original repaired : setup.ProtocolState}
    (related : setup.FocalRepair who original repaired)
    (admission : CommitmentInterface setup.program) :
    ((setup.executionProtocol (CommitmentInterface.values setup.program)).terminal repaired ↔
      (setup.executionProtocol admission).terminal original) := by
  cases original <;> cases repaired
  · exact Iff.rfl
  · exact related.elim
  · exact related.elim
  · exact ProtocolState.FocalRepair.terminal_iff who setup.program _ _ related

/-- Repair an actual setup protocol transition without changing the setup draw. -/
theorem FocalRepair.step {who : Player} (admission : CommitmentInterface setup.program)
    {original repaired target : setup.ProtocolState}
    (related : setup.FocalRepair who original repaired)
    (joint : Player → Option (OwnAction Player L))
    (legal : (setup.executionProtocol admission).Legal original joint)
    (foreign : ∀ observer, observer ≠ who → setup.protocolMenu
      (CommitmentInterface.values setup.program) observer (setup.protocolObserve observer original)
      (joint observer))
    (reached : target ∈ ((setup.executionProtocol admission).step original ⟨joint,
      legal⟩).support) :
    ∃ translated : Player → Option (OwnAction Player L),
      (∀ observer, observer ≠ who → translated observer = joint observer) ∧
      ∃ legal' : (setup.executionProtocol (CommitmentInterface.values setup.program)).Legal
          repaired translated,
        ∃ repairedTarget,
          repairedTarget ∈ ((setup.executionProtocol (CommitmentInterface.values
            setup.program)).step
            repaired ⟨translated, legal'⟩).support ∧
          setup.FocalRepair who target repairedTarget := by
  cases original with
  | none =>
      cases repaired with
      | some repaired => exact related.elim
      | none =>
          have legal' : (setup.executionProtocol (CommitmentInterface.values setup.program)).Legal
              none joint := legal
          obtain ⟨initial, supported, rfl⟩ := PMF.support_map .. ▸ reached
          refine ⟨joint, fun _ _ => rfl, legal',
            some (ProtocolState.entry setup.program (setup.initialConfig initial)), ?_, ?_⟩
          · exact PMF.support_map .. ▸ ⟨initial, supported, rfl⟩
          · exact ProtocolState.focalRepair_entry who setup.program
              (Config.FocalRepair.refl who (setup.initialConfig initial))
  | some original =>
      cases repaired with
      | none => exact related.elim
      | some repaired =>
          obtain ⟨target, supported, rfl⟩ := PMF.support_map .. ▸ reached
          have permitted : ∀ observer, ProtocolView.menu observer setup.program admission
              (ProtocolState.observe observer setup.program original) (joint observer) := by
            intro observer
            have chosen := legal.2 observer
            cases selected : joint observer <;>
              simpa only [executionProtocol, protocolObserve, Option.map_some, Option.elim_some,
                ProtocolView.menu, selected] using chosen
          obtain ⟨translated, same, permitted', repairedTarget, supported', related'⟩ :=
            ProtocolState.FocalRepair.step who setup.program admission original repaired target
              related legal.1 joint permitted foreign supported
          have legal' : (setup.executionProtocol (CommitmentInterface.values setup.program)).Legal
              (some repaired) translated := by
            refine ⟨fun stopped => legal.1
              ((ProtocolState.FocalRepair.terminal_iff who setup.program original repaired
                related).mp
                stopped), ?_⟩
            intro observer
            have chosen := permitted' observer
            cases selected : translated observer <;>
              simpa only [executionProtocol, protocolObserve, Option.map_some, Option.elim_some,
                ProtocolView.menu, selected] using chosen
          refine ⟨translated, same, legal', some repairedTarget, ?_, related'⟩
          exact PMF.support_map .. ▸ ⟨repairedTarget, supported', rfl⟩

/-- Foreign actions along this actual setup history come from the value menu. -/
def ForeignValuesPrefix (admission : CommitmentInterface setup.program) (who : Player) :
    ∀ {state}, (setup.executionProtocol admission).Trace state → Prop
  | _, .start => True
  | _, .extend (source := source) prior joint _ _ =>
      ForeignValuesPrefix admission who prior ∧
        ∀ observer, observer ≠ who → setup.protocolMenu
          (CommitmentInterface.values setup.program) observer
          (setup.protocolObserve observer source) (joint observer)

/-- The initialized value-interface game represents every foreign player's
full information along a history where only the focal player uses failed bindings. -/
theorem exists_values_prefix (admission : CommitmentInterface setup.program) (who : Player)
    {state : (setup.executionProtocol admission).State}
    (trace : (setup.executionProtocol admission).Trace state)
    (foreignValues : setup.ForeignValuesPrefix admission who trace) :
    ∃ repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History,
      repaired.trace.length = trace.length ∧ setup.FocalRepair who state repaired.state ∧
      ∀ observer, observer ≠ who →
        (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
          observer repaired.trace = (setup.informationModel admission).infoOf observer trace := by
  have represented : ∀ {current : (setup.executionProtocol admission).State}
      (path : (setup.executionProtocol admission).Trace current),
      setup.ForeignValuesPrefix admission who path →
      ∃ repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History,
        repaired.trace.length = path.length ∧ setup.FocalRepair who current repaired.state := by
    intro current path
    refine Trace.rec
      (motive := fun current path => setup.ForeignValuesPrefix admission who path →
        ∃ repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History,
          repaired.trace.length = path.length ∧ setup.FocalRepair who current repaired.state)
      ?_ ?_ path
    · intro _
      exact ⟨(setup.executionProtocol (CommitmentInterface.values setup.program)).initHistory,
        rfl, trivial⟩
    · intro source target prior joint legal realized ih foreignValues
      obtain ⟨repaired, length, related⟩ := ih foreignValues.1
      obtain ⟨translated, _, legal', repairedTarget, realized', related'⟩ :=
        FocalRepair.step setup admission related joint legal foreignValues.2 realized
      exact ⟨repaired.extend legal' realized', congrArg (· + 1) length, related'⟩
  obtain ⟨repaired, length, related⟩ := represented trace foreignValues
  refine ⟨repaired, length, related, ?_⟩
  intro observer foreign
  rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf observer
    repaired.trace = setup.protocolObserve observer repaired.state from setup.protocol_info ..]
  rw [show (setup.informationModel admission).infoOf observer trace =
    setup.protocolObserve observer state from setup.protocol_info ..]
  exact FocalRepair.foreign_observe setup related foreign


/-- A copied foreign policy cannot choose a failed binding at a prefix that
has been represented in the initialized value game. -/
theorem copied_foreign_choice_values (admission : CommitmentInterface setup.program)
    (who observer : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (history : (setup.executionProtocol admission).History)
    (foreignValues : setup.ForeignValuesPrefix admission who history.trace)
    (running : ¬ (setup.executionProtocol admission).terminal history.state)
    (foreign : observer ≠ who) (action : Option (OwnAction Player L))
    (supported : action ∈ ((target observer
      ((setup.informationModel admission).infoOf observer history.trace)).map
        Subtype.val).support) :
    setup.protocolMenu (CommitmentInterface.values setup.program) observer
      (setup.protocolObserve observer history.state) action := by
  obtain ⟨chosen, chosenSupported, chosenEq⟩ := PMF.support_map .. ▸ supported
  have permitted := ((setup.informationModel admission).menu_adequate
    observer history.trace chosen.1).mp chosen.2
  rw [chosenEq] at permitted
  cases action with
  | none =>
      have legal := chosen.2
      rw [chosenEq] at legal
      change setup.protocolMenu admission observer
        ((setup.informationModel admission).infoOf observer history.trace) none at legal
      rw [show (setup.informationModel admission).infoOf observer history.trace =
        setup.protocolObserve observer history.state from setup.protocol_info ..] at legal
      cases current : history.state with
      | none => rfl
      | some original =>
          simpa only [protocolObserve, current, Option.map_some, protocolMenu, ProtocolView.menu]
            using legal
  | some action =>
      obtain ⟨repaired, _, related, observed⟩ :=
        setup.exists_values_prefix admission who history.trace foreignValues
      have running' : ¬ (setup.executionProtocol
          (CommitmentInterface.values setup.program)).terminal repaired.state :=
        fun stopped => running ((FocalRepair.terminal_iff setup related admission).mp stopped)
      have active' : (setup.executionProtocol (CommitmentInterface.values setup.program)).active
          repaired.state observer := by
        change (setup.protocolObserve observer repaired.state).elim False
          (fun view => ProtocolView.actor observer setup.program view = some observer)
        rw [FocalRepair.foreign_observe setup related foreign]
        exact permitted.1
      obtain ⟨site, siteView⟩ := (setup.informationModel
        (CommitmentInterface.values setup.program)).exists_informationSite_of_active
          observer repaired running' active'
      have sameInfo : (setup.informationModel admission).infoOf observer history.trace =
          (setup.valuesRestriction admission).information observer site.1 := by
        change _ = site.1
        rw [siteView, observed observer foreign]
      have actionSupported : some action ∈ ((target observer
          ((setup.informationModel admission).infoOf observer history.trace)).map
            Subtype.val).support :=
        PMF.support_map .. ▸ ⟨chosen, chosenSupported, chosenEq⟩
      rw [sameInfo, copies observer site, PMF.map_comp] at actionSupported
      obtain ⟨sourceChoice, _, same⟩ := PMF.support_map .. ▸ actionSupported
      change sourceChoice.1 = some action at same
      have allowed := sourceChoice.2
      change setup.protocolMenu (CommitmentInterface.values setup.program) observer
        site.1 sourceChoice.1 at allowed
      rw [same, siteView, observed observer foreign] at allowed
      rw [show (setup.informationModel admission).infoOf observer history.trace =
        setup.protocolObserve observer history.state from setup.protocol_info ..] at allowed
      exact allowed



/-- Embedding an actual value-interface history retains only value choices,
including at histories that have zero probability under the incumbent profile. -/
theorem values_history_foreign_values (admission : CommitmentInterface setup.program)
    (who : Player)
    (history : (setup.executionProtocol (CommitmentInterface.values setup.program)).History) :
    setup.ForeignValuesPrefix admission who
      ((setup.valuesRestriction admission).history history).trace := by
  have preserved : ∀ {current :
      (setup.executionProtocol (CommitmentInterface.values setup.program)).State}
      (path : (setup.executionProtocol (CommitmentInterface.values setup.program)).Trace current),
      setup.ForeignValuesPrefix admission who
        (restrictAvailable.trace (E := setup.executionProtocol admission)
          (included := setup.valuesAvailable_subset admission)
          (progress :=
            (setup.executionProtocol (CommitmentInterface.values setup.program)).progress)
          path) := by
    intro current path
    refine Trace.rec
      (motive := fun current path => setup.ForeignValuesPrefix admission who
        (restrictAvailable.trace (E := setup.executionProtocol admission)
          (included := setup.valuesAvailable_subset admission)
          (progress :=
            (setup.executionProtocol (CommitmentInterface.values setup.program)).progress)
          path)) ?_ ?_ path
    · exact trivial
    · intro source target prior joint legal realized ih
      refine ⟨ih, ?_⟩
      intro observer _
      have allowed :=
        ((setup.informationModel (CommitmentInterface.values setup.program)).menu_adequate
        observer prior (joint observer)).mpr
          ((setup.executionProtocol (CommitmentInterface.values setup.program)).legalOption_of_legal
            legal observer)
      change setup.protocolMenu (CommitmentInterface.values setup.program) observer
        ((setup.informationModel (CommitmentInterface.values setup.program)).infoOf observer prior)
        (joint observer) at allowed
      rw [show (setup.informationModel (CommitmentInterface.values setup.program)).infoOf observer
        prior = setup.protocolObserve observer source from setup.protocol_info ..] at allowed
      exact allowed
  exact preserved history.trace

/-- Copied opponents keep every supported focal deviation continuation represented
in the initialized value game from any embedded actual value history. Foreign
value-menu membership is derived at each
step from actual retained information sites. -/
theorem deviation_history_values_representation [Fintype Player]
    (admission : CommitmentInterface setup.program) (who : Player)
    (source : ∀ player, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy player)
    (target : ∀ player, (setup.informationModel admission).BehavioralPolicy player)
    (copies : (setup.valuesRestriction admission).ExtendsProfile source target)
    (deviation : (setup.informationModel admission).BehavioralPolicy who)
    (start : (setup.executionProtocol (CommitmentInterface.values setup.program)).History)
    (fuel : ℕ) (history : (setup.executionProtocol admission).History)
    (supported : history ∈ ((setup.informationModel admission).runBehavioralFrom
      (Function.update target who deviation) fuel
      ((setup.valuesRestriction admission).history start)).support) :
    ∃ repaired : (setup.executionProtocol (CommitmentInterface.values setup.program)).History,
      repaired.trace.length = history.trace.length ∧
        setup.FocalRepair who history.state repaired.state ∧
        ∀ observer, observer ≠ who →
          (setup.informationModel (CommitmentInterface.values setup.program)).infoOf
            observer repaired.trace =
          (setup.informationModel admission).infoOf observer history.trace := by
  have invariant : ∀ (fuel : ℕ) (start last : (setup.executionProtocol admission).History),
      setup.ForeignValuesPrefix admission who start.trace →
      last ∈ ((setup.informationModel admission).runBehavioralFrom
        (Function.update target who deviation) fuel start).support →
      setup.ForeignValuesPrefix admission who last.trace := by
    intro fuel
    induction fuel with
    | zero =>
        intro start last initial reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact initial
    | succ fuel ih =>
        intro start last initial reached
        by_cases stopped : (setup.executionProtocol admission).terminal start.state
        · rw [(setup.informationModel admission).runBehavioralFrom_of_terminal
            _ _ stopped] at reached
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact initial
        · rw [(setup.informationModel admission).runBehavioralFrom_succ_of_not_terminal
            _ fuel stopped, PMF.support_bind] at reached
          obtain ⟨draw, selected, continued⟩ := Set.mem_iUnion₂.mp reached
          rw [PMF.mem_support_bindOnSupport_iff] at continued
          obtain ⟨nextState, realized, continued⟩ := continued
          apply ih (start.extend draw.2 realized) last ?_ continued
          refine ⟨initial, ?_⟩
          intro observer foreign
          obtain ⟨draws, drawsSupported, same⟩ := PMF.support_map .. ▸ selected
          have localSupport := (independentProduct_support_iff _ draws).mp drawsSupported observer
          have targetSupport : draws observer ∈
              (target observer ((setup.informationModel admission).infoOf observer
                start.trace)).support :=
            by simpa only [Function.update_of_ne foreign] using localSupport
          have chosen := setup.copied_foreign_choice_values admission who observer source target
            copies start initial stopped foreign (draws observer).1
            (PMF.support_map .. ▸ ⟨draws observer, targetSupport, rfl⟩)
          have jointEq : (draws observer).1 = draw.1 observer :=
            congrArg (fun selected => selected.1 observer) same
          rw [jointEq] at chosen
          exact chosen
  exact setup.exists_values_prefix admission who history.trace
    (invariant fuel ((setup.valuesRestriction admission).history start) history
      (setup.values_history_foreign_values admission who start) supported)

end Setup

end Vegas.SourceProgram
