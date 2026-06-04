import VersoManual
import Lean

import DirichletProblem.Sobolev.Basic
import DirichletProblem.Sobolev.Restrict
import DirichletProblem.Sobolev.SupportedIn

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false

#doc (Manual) "Sobolev spaces on domains" =>

# Sobolev spaces

{docstring Sobolev}

## Embeddings and traces

We have the classical Sobolev embedding theorem and the trace theorem:

{docstring Sobolev.toZeroAtInfty}

{docstring Sobolev.restrictFst}

# Sobolev spaces on domains

{docstring SobolevRestrict}
