import VersoManual
import DirichletProblem.Documentation

open Verso.Genre Manual

def main := manualMain (%doc DirichletProblem.Documentation) (options := ["--output", "html"])
