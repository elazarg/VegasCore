/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageApplication
import Interaction.MessageApplicationPolicies

/-! # Prescribed graph policies for the public-message runtime -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

abbrev Entry (runtime : GraphRuntime Player L Δ) := runtime.application.PlayerEntry
abbrev Command (runtime : GraphRuntime Player L Δ) := runtime.application.PlayerCommand

def preparedRaw {runtime : GraphRuntime Player L Δ}
    (history : List (Entry runtime)) (site : Nat) : Option (Raw L) :=
  history.findSome? fun entry =>
    match entry.command with
    | .privateCommand (.prepare slot raw) => if slot = site then some raw else none
    | _ => none

def rememberedDisclosure {runtime : GraphRuntime Player L Δ} (history : List (Entry runtime))
    (site : Nat) : Option Bool :=
  history.findSome? fun entry =>
    match entry.command with
    | .privateCommand (.rememberDisclosure disclose) =>
        if entry.beforeView.application.publicState.pc = site then some disclose else none
    | _ => none

def submittedAt {runtime : GraphRuntime Player L Δ}
    (history : List (Entry runtime)) (site : Nat) : Bool :=
  history.any fun entry =>
    match entry.command with
    | .submit (.commitment submittedSite _) => submittedSite = site
    | .submit (.opening submittedSite _ _) => submittedSite = site
    | .submit (.withhold submittedSite) => submittedSite = site
    | _ => false

private def findVar (context : VCtx Player L) (name : VarId) (binding : BindTy Player L) :
    Option (HasVar context name binding) :=
  match context with
  | [] => none
  | (headName, headBinding) :: tail =>
      if h : (headName, headBinding) = (name, binding) then
        some (h ▸ HasVar.here)
      else (findVar tail name binding).map HasVar.there

private def observedBindChoice {target : VCtx Player L} (who : Player)
    (observation : Observation L who target) (name : VarId) (payload : L.Ty) :
    PublicationResult (L.Val payload) :=
  match findVar target name (.sealed who (R.result payload)) with
  | none => .failure
  | some source =>
      match observation.cells.get source with
      | none => .failure
      | some encoded => R.valueEquiv payload encoded

/-- Project authenticated compiler commands to the graph's logical own-action
history. Entries unrelated to the fixed graph are deliberately ignored. -/
def projectLogicalHistory {runtime : GraphRuntime Player L Δ}
    {target : VCtx Player L} (who : Player) (observation : Observation L who target)
    (history : List (Entry runtime)) :
    {Γ Δ : VCtx Player L} → Graph Player L Γ Δ → Nat → Nat → List (OwnAction Player L)
  | _, _, .ret _, _, _ => []
  | _, _, .sample _ _ _ next, site, fuel =>
      match fuel with
      | 0 => []
      | fuel + 1 => projectLogicalHistory who observation history next (site + 1) fuel
  | _, _, .bind name owner (payload := payload) _ next, site, fuel =>
      match fuel with
      | 0 => []
      | fuel + 1 =>
          let tail := projectLogicalHistory who observation history next (site + 1) fuel
          if owner = who then OwnAction.bind owner name payload
            (observedBindChoice who observation name payload) :: tail else tail
  | _, _, .resolve _ owner bindingName _ _ _ next, site, fuel =>
      match fuel with
      | 0 => []
      | fuel + 1 =>
          let tail := projectLogicalHistory who observation history next (site + 1) fuel
          if owner = who then OwnAction.resolve owner bindingName
            ((rememberedDisclosure history site).getD false) :: tail else tail

def projectDecisionView {runtime : GraphRuntime Player L Δ}
    (who : Player) (history : List (Entry runtime))
    {Γ₀ target : VCtx Player L} (graph : Graph Player L Γ₀ Δ) (site : Nat)
    (observation : Observation L who target) : DecisionView who target :=
  (observation, projectLogicalHistory who observation history graph 0 site)

def compileAt (runtime : GraphRuntime Player L Δ) (who : Player)
    {Γ₀ : VCtx Player L} (whole : Graph Player L Γ₀ Δ) :
    {Γ : VCtx Player L} → (graph : Graph Player L Γ Δ) → BehavioralPolicy who graph →
      Nat → List (Entry runtime) → runtime.application.View → FinDist (Command runtime)
  | _, .ret _, _, _, _, _ => FinDist.pure .wait
  | _, .sample _ _ _ next, policy, site, history, view =>
      if view.application.publicState.pc = site then FinDist.pure .wait
      else compileAt runtime who whole next policy (site + 1) history view
  | Γ, .bind _name owner (payload := payload) _fresh next, policy, site, history, view =>
      if _hpc : view.application.publicState.pc = site then
        if howner : owner = who then
          if submittedAt history site then FinDist.pure .wait
          else match preparedRaw history site with
            | some _ => FinDist.pure (.submit (.commitment site (who, .prepared site)))
            | none =>
                if hwho : view.application.who = who then
                  if hΓ : view.application.publicState.Γ = Γ then
                    let observation : Observation L who Γ :=
                      hΓ ▸ (hwho ▸ view.application.privateObservation)
                    (policy.1 howner (projectDecisionView who history
                      whole site observation)).map fun choice =>
                        .privateCommand (.prepare site ⟨R.result payload,
                          (R.valueEquiv payload).symm choice⟩)
                  else FinDist.pure .wait
                else FinDist.pure .wait
        else FinDist.pure .wait
      else compileAt runtime who whole next policy.2 (site + 1) history view
  | Γ, .resolve _outputName owner bindingName (payload := payload) _fresh source checks next,
      policy, site, history, view =>
      if _hpc : view.application.publicState.pc = site then
        if howner : owner = who then
          if submittedAt history site then FinDist.pure .wait
          else match rememberedDisclosure history site with
            | none =>
                if hwho : view.application.who = who then
                  if hΓ : view.application.publicState.Γ = Γ then
                    let observation : Observation L who Γ :=
                      hΓ ▸ (hwho ▸ view.application.privateObservation)
                    (policy.1 howner (projectDecisionView who history
                      whole site observation)).map fun disclose =>
                        .privateCommand (.rememberDisclosure disclose)
                  else FinDist.pure .wait
                else FinDist.pure .wait
            | some disclose =>
                if hwho : view.application.who = who then
                  if hΓ : view.application.publicState.Γ = Γ then
                    let observation : Observation L who Γ :=
                      hΓ ▸ (hwho ▸ view.application.privateObservation)
                    let publicValues : PublicValues Γ := hΓ ▸ view.application.publicState.values
                    let ownedSource : HasVar Γ bindingName (.sealed who (R.result payload)) :=
                      howner ▸ source
                    match disclose, observation.cells.get ownedSource with
                    | true, some encoded =>
                        let proposal := R.valueEquiv payload encoded
                        match acceptedProposal checks publicValues proposal with
                        | .success _ =>
                            match lookupBinding view.application.publicState.bindings
                                bindingName with
                            | some handle => FinDist.pure
                                (.submit (.opening site handle ⟨R.result payload, encoded⟩))
                            | none => FinDist.pure .wait
                        | .failure => FinDist.pure (.submit (.withhold site))
                    | _, _ => FinDist.pure (.submit (.withhold site))
                  else FinDist.pure .wait
                else FinDist.pure .wait
        else FinDist.pure .wait
      else compileAt runtime who whole next policy.2 (site + 1) history view

/-- Compile one graph behavioral policy to the runtime's observation-local
player policy. The fixed graph and its policy tail are traversed together. -/
def compilePlayerPolicy (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (who : Player) (policy : BehavioralPolicy who graph) :
    runtime.application.PlayerPolicy :=
  fun history view => compileAt runtime who graph graph policy 0 history view

def compileProfile (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (profile : BehavioralProfile graph) :
    Player → runtime.application.PlayerPolicy :=
  fun who => compilePlayerPolicy runtime graph who (profile who)

end Vegas.GraphRuntime
