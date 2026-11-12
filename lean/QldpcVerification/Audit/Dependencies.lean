import Lean

/-! Proof-path regression checks. This elaborator traverses the types and bodies
of project constants, including private constants, rather than relying on imports.
It supplies no mathematical axiom or proof term. -/

namespace QldpcVerification.Audit

open Lean Elab Command

private def projectName (n : Name) : Bool :=
  n.toString.startsWith "QldpcVerification." ||
    n.toString.startsWith "_private.QldpcVerification."

private partial def closure (env : Environment) (todo : List Name)
    (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
    if seen.contains name then closure env rest seen
    else
      let seen := seen.insert name
      match env.find? name with
      | none => closure env rest seen
      | some info =>
        let deps := info.getUsedConstantsAsSet.toList.filter projectName
        closure env (deps ++ rest) seen

syntax (name := guardDependencies)
  "#guard_dependencies " ident " requires " "[" ident,* "]"
  " excludes " "[" str,* "]" : command

@[command_elab guardDependencies] def elabGuardDependencies : CommandElab := fun stx => do
  match stx with
  | `(command| #guard_dependencies $target:ident requires [$needed:ident,*]
      excludes [$excluded:str,*]) =>
    let env ← getEnv
    let name := target.getId
    unless (env.find? name).isSome do
      throwErrorAt target "unknown dependency-audit target {name}"
    let deps := closure env [name]
    for required in needed.getElems do
      unless deps.contains required.getId do
        throwErrorAt required "{name} does not depend on required theorem {required.getId}"
    for forbidden in excluded.getElems do
      let fragment := forbidden.getString
      for dep in deps.toList do
        if (dep.toString.splitOn fragment).length > 1 then
          throwErrorAt forbidden "{name} still depends on forbidden declaration {dep}"
  | _ => throwUnsupportedSyntax

end QldpcVerification.Audit
