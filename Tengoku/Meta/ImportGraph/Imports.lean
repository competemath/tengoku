module

public import Tengoku.Meta.ImportGraph.Export.DotFile
public import Tengoku.Meta.ImportGraph.Export.Gexf
public import Tengoku.Meta.ImportGraph.Graph.Filter
public import Tengoku.Meta.ImportGraph.Graph.TransitiveClosure
public import Tengoku.Meta.ImportGraph.Imports.FromSource
public import Tengoku.Meta.ImportGraph.Imports.ImportGraph
public import Tengoku.Meta.ImportGraph.Imports.Redundant
public import Tengoku.Meta.ImportGraph.Imports.RequiredModules
public import Tengoku.Meta.ImportGraph.Imports.Unused
public import Tengoku.Meta.ImportGraph.Lean.Environment
public import Tengoku.Meta.ImportGraph.Lean.Name
public import Tengoku.Meta.ImportGraph.Lean.WithImportModules
public import Tengoku.Meta.ImportGraph.Util.FindSorry
public meta import Tengoku.Meta.ImportGraph.Export.DotFile
public meta import Tengoku.Meta.ImportGraph.Export.Gexf
public meta import Tengoku.Meta.ImportGraph.Graph.Filter
public meta import Tengoku.Meta.ImportGraph.Graph.TransitiveClosure
public meta import Tengoku.Meta.ImportGraph.Imports.FromSource
public meta import Tengoku.Meta.ImportGraph.Imports.ImportGraph
public meta import Tengoku.Meta.ImportGraph.Imports.Redundant
public meta import Tengoku.Meta.ImportGraph.Imports.RequiredModules
public meta import Tengoku.Meta.ImportGraph.Imports.Unused
public meta import Tengoku.Meta.ImportGraph.Lean.Environment
public meta import Tengoku.Meta.ImportGraph.Lean.Name
public meta import Tengoku.Meta.ImportGraph.Lean.WithImportModules
public meta import Tengoku.Meta.ImportGraph.Util.FindSorry

import Lean

open Lean

-- deprecated 2026-02-01
#eval do
  logWarning "`ImportGraph.Imports` is deprecated! use a subset of`import ImportGraph` instead."
