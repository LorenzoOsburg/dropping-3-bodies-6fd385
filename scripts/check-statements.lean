module

import Lean

open Lean

private def readDeclaration (environment : Environment) (moduleName declarationName : Name) :
    IO ConstantInfo := do
  match environment.find? declarationName with
  | some declaration =>
    unless (environment.getModuleIdxFor? declarationName).map
        (environment.header.moduleNames[·.toNat]!) == some moduleName do
      throw (IO.userError s!"{declarationName} is not declared in {moduleName}")
    pure declaration
  | none => throw (IO.userError s!"Missing declaration {declarationName} in {moduleName}")

/-- Compare elaborated theorem types in two separate local Lean environments. -/
public def main (args : List String) : IO Unit := do
  let challenge :: solution :: declarations := args
    | throw (IO.userError "Expected challenge module, solution module, and theorem names")
  let challengeName := challenge.toName
  let solutionName := solution.toName
  initSearchPath (← findSysroot)
  let challengeEnv ← importModules #[{ module := challengeName }] {} (level := .exported)
  let solutionEnv ← importModules #[{ module := solutionName }] {} (level := .exported)
  for name in declarations do
    let expected ← readDeclaration challengeEnv challengeName name.toName
    let actual ← readDeclaration solutionEnv solutionName name.toName
    unless expected.levelParams == actual.levelParams && expected.type == actual.type do
      throw (IO.userError s!"Different elaborated theorem types for {name}")
    IO.println s!"Matched {name}"
