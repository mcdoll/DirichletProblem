import VersoManual
import DirichletProblem.Sobolev.Docs

open Verso.Genre Manual

def main := manualMain (%doc DirichletProblem.Sobolev.Docs) (options := ["--output", "html"])
