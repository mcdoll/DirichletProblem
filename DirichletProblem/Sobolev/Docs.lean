import VersoManual
import DirichletProblem.Sobolev.Basic

open Verso.Genre
open Verso.Genre.Manual
open Verso.Genre.Manual.InlineLean

set_option linter.style.setOption false
set_option linter.hashCommand false

set_option pp.rawOnError true

#doc (Manual) "Sobolev spaces" =>

%%%
authors := ["Moritz Doll"]
%%%

test {lean}`Sobolev`

```lean
#check Sobolev
```

bar
