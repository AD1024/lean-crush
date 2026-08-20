import VersoManual
import CrushManual

open Verso Doc
open Verso.Genre Manual

def config : Config where
  sourceLink := some "https://github.com/AD1024/lean-crush"
  issueLink := some "https://github.com/AD1024/lean-crush/issues"
  extraFiles := [("figures", "figures")]
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2

def main := manualMain (%doc CrushManual) (config := { config with })
