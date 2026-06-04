import VersoManual
import DirichletProblem.Mathlib.Analysis.Distribution.Documentation
import DirichletProblem.Mathlib.Analysis.InnerProductSpace.Documentation
import DirichletProblem.Sobolev.Documentation

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.style.setOption false
set_option linter.hashCommand false

set_option pp.rawOnError true

#doc (Manual) "Dirichlet problem" =>

%%%
authors := ["Moritz Doll"]
%%%

This is an ongoing project of formalizing the Dirichlet problem for the Laplacian
on a bounded domain in Lean.

We start by giving a very quick overview of the problem.
Consider a bounded domain with smooth boundary $`Ω` of $`\mathbb{R}^n`.
The Laplacian $`Δ` on functions is given by the sum of all second derivatives,
$$`Δ f = ∑_{j = 1}^n ∂_j^2 f.`

The Dirichlet problem is to find the solution of the boundary value problem
$$`\begin{aligned}
  -\Delta u &= f \quad \text{ in } Ω\\
  u|_{∂ Ω} &= 0 \quad \text{ on } ∂Ω
\end{aligned}`
for a given function $`f`, which is assumed to be at least in $`L^2(Ω)`.

While this problem looks rather innocent, it involves quite a bit of functional analysis.
Moreover, we will investigate the spectral theory of the Dirichlet-Laplacian.

{include 1 DirichletProblem.Mathlib.Analysis.InnerProductSpace.Documentation}
{include 1 DirichletProblem.Mathlib.Analysis.Distribution.Documentation}
{include 1 DirichletProblem.Sobolev.Documentation}
