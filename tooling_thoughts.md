---
header-includes: |
    \usepackage{pset}
    \usepackage[margin=1in]{geometry}
    \usepackage{mathrsfs}
---
# Ocaml

## Pros
+ Andrew is very familiar, Perry used to be.
+ Good tooling
    + Makes it more likely we can do analysis on real programs
+ Could use tools written by Kincaid (Duet)
    - Not well documented though
## Cons
- Not as interesting to Andrew?
## Tools
+ Frama-C
    * Provides parsing and tons of functionality
    * We could potentially write our thing as a plugin and release it
    * https://frama-c.com/index.html
    * http://frama-c.com/download/frama-c-plugin-development-guide.pdf
    * Documentation is ugly but there


# Rust

## Pros
+ Andrew is extremely familiar
+ If we have time, could be fun to start hyperoptimizing/benchmarking
## Cons
- Perry doesn't know it
* Tooling might not be as good as Ocaml (TODO)
## Tools
* Electrolysis
    * https://github.com/Kha/electrolysis
    - Seems unmaintained
    - Uses highly unstable rust API (from 2 years ago)
    - Documentation seems sparse
- lang-c
    * https://github.com/vickenty/lang-c
    + Lightweight C parser
    - No documentation
    - Very few stars


# Elixir

## Pros
+ New language for Kincaid
+ Interesting to Perry
## Cons
- Perry hasn't written anything in it, Andrew doesn't know it
~ Tooling unclear (TODO iff there's a chance we use it)
    ~ If researching tooling, bear in mind that we could also use Erlang stuff

