import OmegaBound.FinalBound

/-! Regenerates `release/native-roots.tsv` and `release/native-surface.tsv` from the built
environment (run by `release/reproduce.sh native`, which sorts and compares them).

* Native roots: every constant of an `OmegaBound`/`PLATFORM` module whose type or value applies
  `Lean.ofReduceBool` directly, tagged CLOSURE if it lies in the constant closure (types and values)
  of the four capstone declarations and OUTSIDE otherwise, with the evaluated auxiliary definitions.
* Compiled surface: the constants with `@[extern]` or `@[implemented_by]` reachable from those
  evaluated definitions, that is, the code whose compiled behaviour `native_decide` trusts.

Output directory: `$NATIVE_OUT` (default: the current directory). -/

open Lean Meta

partial def auditClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut todo := roots
  while !todo.isEmpty do
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      match env.find? n with
      | none => pure ()
      | some ci => for m in ci.getUsedConstantsAsSet.toList do
          if !seen.contains m then todo := m :: todo
  return seen

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => `_current

-- first arguments of every `Lean.ofReduceBool` application in e
partial def reduceBoolArgs (e : Expr) : Array Name := Id.run do
  let mut out := #[]
  let rec go (e : Expr) (acc : Array Name) : Array Name :=
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let acc := if f.isConstOf ``Lean.ofReduceBool && args.size > 0 then
          (match args[0]!.getAppFn with | .const n _ => acc.push n | _ => acc.push `_nonconst) else acc
      args.foldl (fun a x => go x a) (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc
  out := go e out
  return out

#eval show CoreM Unit from do
  let dir := (← IO.getEnv "NATIVE_OUT").getD "."
  let env ← getEnv
  let caps : List Name := [`OmegaBound.omegaMM_lt_2371339, `OmegaBound.omegaMM_lt_2371339_allFields,
    `OmegaBound.ADVXXZFinal.omegaMM_lt_target114, `OmegaBound.ADVXXZGeneral.omegaMM_lt_target_allFields]
  let C := auditClosure env caps
  let mut out := ""
  let mut evalRoots : NameSet := {}
  let mut nDirect := 0
  for (n, ci) in env.constants.toList do
    let m := modOf env n
    if !((`OmegaBound).isPrefixOf m || (`PLATFORM).isPrefixOf m) then continue
    let direct := match ci.value? with
      | some v => v.getUsedConstants.contains ``Lean.ofReduceBool
      | none => false
    let directT := ci.type.getUsedConstants.contains ``Lean.ofReduceBool
    if direct || directT then
      nDirect := nDirect + 1
      let args := match ci.value? with | some v => reduceBoolArgs v | none => #[]
      for a in args do evalRoots := evalRoots.insert a
      out := out ++ s!"{m}\t{n}\t{if C.contains n then "CLOSURE" else "OUTSIDE"}\t{args.toList}\n"
  IO.FS.writeFile (dir ++ "/native-roots.tsv") out
  -- compiled-code surface: definitions reachable from the evaluated aux defs
  let E := auditClosure env evalRoots.toList
  let mut surf := ""
  for n in E.toList do
    let ib := Lean.Compiler.getImplementedBy? env n
    let ex := isExtern env n
    if ib.isSome || ex then
      surf := surf ++ s!"{n}\t{modOf env n}\t{ib}\t{ex}\n"
  IO.FS.writeFile (dir ++ "/native-surface.tsv") surf
  IO.println s!"closure {C.size} direct {nDirect} evalRoots {evalRoots.size} evalClosure {E.size}"
  for c in caps do
    let ax ← collectAxioms c
    IO.println s!"AXIOMS {c}: {ax.toList}"
