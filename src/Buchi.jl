module Buchi

using DataStructures
using GraphViz
using CxxWrap
using FileIO

# a submodule containing bindings to the spot C++ library
module Spot

using CxxWrap, Libdl

get_path() = joinpath(@__DIR__,"../deps/$VERSION/lib","libspot_buchi.$(Libdl.dlext)")

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
const debug_display_dot = Ref(false)
function display_dot(io,A::BuchiAutomaton{Ta}) where Ta
    do_split = split_initial[]
    for (_,(_,t))=A[] # test if there is an incoming edge
        do_split &= !isinitial(A,t)
    end
        
    dot = IOBuffer()
    println(dot, """digraph buchi {
  graph [label=<$(acceptance_string(A))> fontsize=10 labelloc=t]
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
            a,acc = a[1],join("""<FONT COLOR="Green">"""*acc_chars[i+1]*" </FONT>" for i=a[2])
        end
        label = "[label=<$(letterstring(A,a))$acc>,fontsize=10]"
        if do_split && isinitial(A,s)
            println(dot,"  $init [style=invis,fixedsize=true,height=0,width=0,label=\"\"]")
            println(dot,"  $init -> $t $label")
            init -= 1
        else
            println(dot,"  $s -> $t $label")
        end
    end
    println(dot,"}")
    debug_display_dot[] && println("display_dot:\n",join(readlines(seekstart(dot)),"\n"))
    
    img = GraphViz.load(seekstart(dot))
    display("image/svg+xml", img)
end

const BA_SPECIAL = (','=>'‚','-'=>'—','>'=>'›')
const BA_SPECIAL_REVERSE = tuple((a=>b for (b,a)=Buchi.BA_SPECIAL)...)
ba_encode(s) = replace(string(s),BA_SPECIAL...)
ba_decode(s) = replace(s,BA_SPECIAL_REVERSE...)

function parse_ba(stream)
    # initial state
    l = readline(stream)
    state_num = Dict(l=>1)
    states = [l]
    alphabet_num = Dict{String,Int}()
    alphabet = String[]
    finals = Int[]
    transitions = Tuple{Int,String,Int}[]
    while true
        l = readline(stream)
        isempty(l) && break
        m = match(r"(.*),(.*)->(.*)",l)
        if m==nothing
            haskey(state_num,l) || error("Line '$l' is neither a transition nor a final state")
            push!(finals,state_num[l])
        else
            s = ba_decode(m[1])
            if !haskey(alphabet_num,s)
                push!(alphabet,s)
                alphabet_num[s] = length(alphabet)
            end
            if !haskey(state_num,m[2])
                push!(states,m[2])
                state_num[m[2]] = length(states)
            end
            if !haskey(state_num,m[3])
                push!(states,m[3])
                state_num[m[3]] = length(states)
            end
            push!(transitions,(state_num[m[2]],s,state_num[m[3]]))
        end
    end

    if false
        # we can try to guess the type, and evaluate etc., but it seems
        # better to just return strings, and do the matching later.
        alphabet = eval.(Meta.parse.(alphabet))
        T = promote_type(typeof.(alphabet)...)
        alphabet = convert(Vector{T},alphabet)
        alphabet_num = convert(Dict{T,Int},alphabet_num)
        transitions = convert(Vector{Tuple{Int,T,Int}},transitions)
    end
    (states = states, state_num, alphabet_num, alphabet, transitions, finals)
end

"""
#!! TODO:

* extract top of automaton, or of two automata, match their vertices, construct
in this manner an idempotent; i.e. compute limit of a sequence of automata

* implement isunivalent, isinjective, issurjective, istotal, issymmetric, istransitive, isreflexive, isantisymmetric for relations

* evaluate, enumerate (growth, entropy)

* examine truncation, action on length-n prefixes

* add SimpleTraits (deterministic, ...) HasFactory on dictionaries, ...

* allow "initial=n" and "initial=[n₀,n₁,...]" to creation of automata

* have general BuchiAutomaton(A,newtransitions) for code genericity

set_aliases() to set aliases in Spot automaton; call it before printing, to implement dict.
get_aliases()
"""
end
