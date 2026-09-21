import VersoManual

import CrushManual.Overview
import CrushManual.GettingStarted
import CrushManual.UsingCrush
import CrushManual.Configuration
import CrushManual.Extending
import CrushManual.Troubleshooting
import CrushManual.Benchmarks

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "lean-crush User Manual" =>
%%%
authors := ["lean-crush contributors"]
shortTitle := "lean-crush"
%%%

lean-crush is an SMT hammer for Lean 4.
It selects Lean facts, translates them and the negated goal to SMT-LIB, and asks
an external solver whether they are inconsistent. Successful calls either
construct a checked Lean proof or use an explicit solver-trust policy.

Start with {ref "getting-started"}[Getting Started], then
{ref "using-crush"}[Using the Tactic]. The overview describes the pipeline;
the remaining chapters are references for options, extensions, diagnostics,
and recorded benchmark results.

{include 0 CrushManual.Overview}

{include 0 CrushManual.GettingStarted}

{include 0 CrushManual.UsingCrush}

{include 0 CrushManual.Configuration}

{include 0 CrushManual.Extending}

{include 0 CrushManual.Troubleshooting}

{include 0 CrushManual.Benchmarks}
