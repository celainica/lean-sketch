/-
Copyright (c) 2024 BICMR@PKU. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: Tony Beta Lambda
-/
import Lean
import Analyzer.Types

namespace Lean

/-- Return the name of the module in which a declaration was defined. -/
def Environment.getModuleFor? (env : Environment) (declName : Name) : Option Name :=
  match env.getModuleIdxFor? declName with
  | none =>
    if env.constants.map₂.contains declName then
      env.header.mainModule
    else
      none
  | some idx => env.header.moduleNames[idx.toNat]!

end Lean

open Lean Elab Command

namespace Analyzer.Process.Module

def getModulesForReferences (refs : Std.HashSet Name) : TermElabM (Std.HashMap Name (Option Name × Option System.FilePath)) := do
  let env ← getEnv
  let sysroot ← findSysroot
  let ssp := (← initSrcSearchPath) ++ [sysroot / "src" / "lean"]
  let mut moduleMap : Std.HashMap Name (Option Name × Option System.FilePath) := {}
  for ref in refs do
    let moduleName := env.getModuleFor? ref
    let filePath ← match moduleName with
      | some modName => do
        try
          let leanPath ← findLean ssp modName
          let normalizedPath ← IO.FS.realPath leanPath
          pure (some normalizedPath)
        catch _ =>
          pure none
      | none => pure none
    moduleMap := moduleMap.insert ref (moduleName, filePath)
  return moduleMap

def getResult : CommandElabM ModuleInfo := do
  let env ← getEnv
  let imports := env.header.imports.map fun i => i.module
  let docstring := getMainModuleDoc env |>.toArray |>.map fun d => d.doc
  return {
    imports,
    docstring,
  }

end Analyzer.Process.Module
