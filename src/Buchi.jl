module Buchi

using DataStructures
using GraphViz
using CxxWrap

module Spot

using CxxWrap, Libdl

get_path() = joinpath(@__DIR__,"../deps/lib","libspot_buchi.$(Libdl.dlext)")

@wrapmodule get_path

function __init__()
    @initcxx
end

end

"""BuchiAutomaton{A}

The abstract type of Büchi automata over alphabet `A`.

The interface of Büchi automata contains at least the methods
* `states(A)`, a range of states
* `nstates(A)`, the number of states
* `ntransitions(A)`, the number of transitions
* `initial(A)`, `isinitial(A,s)`
* `acceptance_string(A)`, a string describing its acceptance condition
* `A[s]`, an iterator over transitions starting from state `s`
* `A[]`, an iterator over all transitions

Every transition itself is a nested pair, src => cond => dst,
with "cond" either a letter or a pair (letter,acceptance), and "src" is missing
in case of iteration over transitions starting at s
"""
abstract type BuchiAutomaton{A} end

export states, nstates, ntransitions, initial, isinitial

Base.length(A::BuchiAutomaton) = nstates(A)
Base.:(^)(A::BuchiAutomaton,n::T) where T <: Integer = Base.power_by_squaring(A,n)

include("helpers.jl") # more data structures
include("words.jl") # infinite words
include("cbuchi.jl") # closed Büchi automata
include("spot.jl") # non-deterministic Büchi automata, in Spot
include("examples.jl") # examples of automata

################
#! construct from regexp (with ω)

const acc_chars = ['⓪','①','②','③','④','⑤','⑥','⑦','⑧','⑨','⑩','⑪','⑫','⑬','⑭','⑮','⑯','⑰','⑱','⑲','⑳','㉑','㉒','㉓','㉔','㉕','㉖','㉗','㉘','㉙','㉚','㉛','㉜','㉝','㉞','㉟','㊱','㊲','㊳','㊴','㊵','㊶','㊷','㊸','㊹','㊺','㊻','㊼','㊽','㊾','㊿']
# '⓿', '❶', '❷', '❸', '❹', '❺', '❻', '❼', '❽', '❾', '❿', '⓫', '⓬', '⓭', '⓮', '⓯', '⓰', '⓱', '⓲', '⓳', '⓴' # the sizes change a lot on my font

const split_initial = Ref(true)
function display_dot(io,A::BuchiAutomaton{Ta}) where Ta
    do_split = split_initial[]
    for (_,(_,t))=A[] # test if there is an incoming edge
        do_split &= !isinitial(A,t)
    end
        
    dot = IOBuffer()
    println(dot, """digraph buchi {
  graph [label="$(acceptance_string(A))" fontsize=10 labelloc=t]
""")
    
    for s=states(A)
        do_split && isinitial(A,s) && continue
        shape = isinitial(A,s) ? "square" : "circle"
        println(dot, """  $s [shape="$shape",margin=0,fixedsize=true,height=0.33]""")
    end
    init = -1
    for (s,(a,t))=A[]
        s,t = Int(s), Int(t)
        if isa(a,Ta)
            acc = ""
        else
            a,acc = a[1],join(acc_chars[i+1] for i=a[2])
        end
        label = """[label="$(letterstring(A,a))$acc",fontsize=10]"""
        if do_split && isinitial(A,s)
            println(dot,"  $init [style=invis,fixedsize=true,height=0,width=0,label=\"\"]")
            println(dot,"  $init -> $t $label")
            init -= 1
        else
            println(dot,"  $s -> $t $label")
        end
    end
    println(dot,"}")
    (@isdefined debug_display_dot) && println("display_dot:\n",join(readlines(seekstart(dot)),"\n"))
    
    img = GraphViz.load(seekstart(dot))
    display("image/svg+xml", img)
end

"""Methods:

* isempty
* ∈

"""

# evaluate, enumerate (growth, entropy)

# languages: intersect, union, Kleene star, etc.

# minimize!

# compose, project

# examine truncation, action on length-n prefixes

end

# save in HOA format

# add SimpleTraits (deterministic, ...) HasFactory on dictionaries, ...

# add project operation on looping automata CBuchi
