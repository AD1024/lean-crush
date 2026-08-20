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
It translates the local proof context and the negated goal to SMT-LIB, asks an
external solver whether they are inconsistent, and reports a model, an unknown
result, or discharges the Lean goal.

The overview explains the complete pipeline and when to use each major feature.
The remaining chapters cover installation, tactic usage, options, extension
APIs, failure diagnosis, and benchmark results.

{include 0 CrushManual.Overview}

{include 0 CrushManual.GettingStarted}

{include 0 CrushManual.UsingCrush}

{include 0 CrushManual.Configuration}

{include 0 CrushManual.Extending}

{include 0 CrushManual.Troubleshooting}

{include 0 CrushManual.Benchmarks}
