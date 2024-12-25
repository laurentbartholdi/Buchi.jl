# Buchi

A library for omega-automata. ⚠ ⚠ ⚠ Work in progress! ⚠ ⚠ ⚠ 

This library implements, in pure Julia, Büchi automata with full acceptance condition; and provides bindings for the [spot](https://spot.lre.epita.fr/) library.

It is based on the same shared library as the package [Spot](https://github.com/sisl/Spot.jl), but is quite different, in that this package is centered on automata while Spot is centered on LTL formulas and their translation to automata.

In particular, this package implements a dictionary between any alphabet and the Boolean expressions required for Spot.

A sample:
```julia
julia> using Buchi

julia> a,b,c,d = grigorchuk()
(a = CBuchiAutomaton(2 state(s), 4 transition(s)…), b = CBuchiAutomaton(5 state(s), 10 transition(s)…), c = CBuchiAutomaton(5 state(s), 10 transition(s)…), d = CBuchiAutomaton(5 state(s), 10 transition(s)…))

julia> o = Buchi.diagonal(CBuchiAutomaton(1=>1=>1,1=>2=>1))
CBuchiAutomaton(1 state(s), 2 transition(s)…)

julia> a^2 == b^2 == c^2 == d^2 == b*c*d == o
true

julia> OmegaWord([1])*a == OmegaWord([2],[1])
true
```

[![Build Status](https://github.com/laurentbartholdi/Buchi.jl/actions/workflows/CI.yml/badge.svg?branch=main)](https://github.com/laurentbartholdi/Buchi.jl/actions/workflows/CI.yml?query=branch%3Amain)
