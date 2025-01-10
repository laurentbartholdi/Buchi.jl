# implementation of Büchi automata in spot

################################################################
# boolean decision trees

export →, ↔

Base.show(io::IO, b::Spot.BDD) = show(io, "text/plain", b)
Base.show(io::IO, mime::MIME"text/plain", b::Spot.BDD) = print(io, "<BDD formula id=",Spot.id(b),">")
Base.:(==)(b::Spot.BDD,c::Spot.BDD) = Spot.id(b)==Spot.id(c)
Base.isless(b::Spot.BDD,c::Spot.BDD) = Spot.id(b)<Spot.id(c)
Base.hash(b::Spot.BDD,h::UInt) = hash(Spot.id(b),h)
Base.:(&)(b::Spot.BDD,c::Spot.BDD) = Spot.bdd_and(b,c)
Base.:(|)(b::Spot.BDD,c::Spot.BDD) = Spot.bdd_or(b,c)
Base.:(⊻)(b::Spot.BDD,c::Spot.BDD) = Spot.bdd_xor(b,c)
Base.:(!)(b::Spot.BDD) = Spot.bdd_not(b)
→(b::Spot.BDD,c::Spot.BDD) = Spot.bdd_imp(b,c)
↔(b::Spot.BDD,c::Spot.BDD) = Spot.bdd_biimp(b,c)
# apply

################################################################
# a dictionary between symbols used at the Julia level with atomic
# propositions used by spot.

export APDict, APDictFactory

"""APDict{Ta}

While `spot` has words and automata over "conditions", which are Boolean
expressions in "atomic propositions", our automata and words are over
a type `Ta`. An `APDict{Ta}` establishes a correspondence between `Ta` and
binary-encoded Boolean expressions.

`APDict{Ta}` is an abstract type, that supplies methods
* `bdd_dict(::APDict)` for access to an underlying dictionary of boolean decision diagrams
* `getindex(::APDict,::Ta)` to obtain a corresponding `BDD`
* `(::APDict)(::BDD)` to obtain a corresponding `Ta`
* `get_aut(::APDict)` to access an underlying automaton, only used to register atomic propositions
* `get_factory(::APDict)` to access, if it exists, an `APDictFactory` that produces dictionaries for tuples.
"""
abstract type APDict{Ta} end

struct PlainAPDict{Ta} <: APDict{Ta}
    s2i::Dict{Ta,Spot.BDD}
    i2s::Dict{Spot.BDD,Ta}
    aut::StdLib.SharedPtrAllocated{Spot.TWAGraph} # an automaton just to store the variables
end
PlainAPDict{Ta}(aut::StdLib.SharedPtrAllocated{Spot.TWAGraph}) where Ta = PlainAPDict{Ta}(Dict(),Dict(),aut)
Base.show(io::IO, dict::PlainAPDict) = print(io,"APDict(",keys(dict.s2i),")")
bdd_dict(d::PlainAPDict) = Spot.get_dict(d.aut)
Base.getindex(d::PlainAPDict{Ta},a::Ta) where Ta = d.s2i[a]
(d::PlainAPDict)(v::Spot.BDD) = d.i2s[v]
get_aut(d::PlainAPDict) = d.aut
get_factory(d::PlainAPDict) = error("Plain AP dictionaries have no factory")

function int2var(i,aps)
    naps = length(aps)
    s = digits(i-1,base=2,pad=naps)
    reduce(&, s[k]==1 ? aps[k] : !aps[k] for k=1:naps)
end

function APDict(vars::AbstractVector{Ta}) where Ta
    d = PlainAPDict{Ta}(Spot.make_twa_graph(Spot.make_bdd_dict()))

    naps = Int(ceil(log2(length(vars))))
    aps = Spot.BDD[]

    for i=1:naps
        v = Spot.register_ap(d.aut,string("v",i))
        push!(aps,Spot.bdd_ithvar(v))
    end

    for (i,a)=enumerate(vars)
        v = int2var(i,aps)
        d.s2i[a] = v
        d.i2s[v] = a
    end    
    d
end
APDict(v::Ta, tail::Ta...) where Ta = APDict([v,tail...])

# disable lookup for "trivial" dictionary where we keep the BDD
struct TrivialAPDict <: APDict{Spot.BDDAllocated}
    aut::CxxWrap.StdLib.SharedPtrAllocated{Buchi.Spot.TWAGraph} # an automaton just to store the variables
end
Base.show(io::IO, dict::TrivialAPDict) = print(io,"APDict()")
bdd_dict(d::TrivialAPDict) = Spot.get_dict(d.aut)
Base.getindex(d::TrivialAPDict,a::Spot.BDD) = a
(d::TrivialAPDict)(v::Spot.BDD) = v
get_aut(d::TrivialAPDict) = d.aut
get_factory(d::TrivialAPDict) = error("Trivial AP dictionaries have no factory")

APDict() = TrivialAPDict(Spot.make_twa_graph(Spot.make_bdd_dict()))
APDict(a::StdLib.SharedPtrAllocated{Spot.TWAGraph}) = TrivialAPDict(a)

letterstring(A,a::Spot.BDD) = Spot.string_psl(a,bdd_dict(A.d))

# tuple dictionary, if the objects are tuples. This gives access to
# maps between alphabets given by imbedding as a coordinate / projecting.
struct APDictFactory{Ta}
    d0::PlainAPDict{Ta}
    d::Vector{PlainAPDict} # one plain dictionary for each arity of tuples
    bdd::Dict{Tuple{Ta,Int},Spot.BDD} # BDDs for individual variables
    recoders::Dict{Tuple{Int,Vector{Int}},Vector{UInt32}} # cache
end
Base.show(io::IO, factory::APDictFactory) = print(io,"APDictFactory(",length(factory.d),",",keys(factory.d0.s2i),")")

alltuples(n,vars) = n==0 ? [()] : [(a...,v) for a=alltuples(n-1,vars) for v=vars]

#!!! todo: get rid of variable n, make it extensible on-the-fly

"""APDictFactory(n::Int,vars::Vector{Ta})

A "factory" is a holder for dictionaries over tuples of `Ta`. It supplies methods
* `getindex(::APDictFactory,n::Int)` to produce a dictionary on n-tuples
* `getindex(::APDictFactory)` to produce a dictionary on elements of `Ta`
"""
function APDictFactory(n::Int,vars::AbstractVector{Ta}) where Ta
    naps = Int(ceil(log2(length(vars))))
    bdd_dict = Spot.make_bdd_dict()
    aut = Spot.make_twa_graph(bdd_dict)
    d0 = PlainAPDict{Ta}(Spot.make_twa_graph(bdd_dict))
    
    factory = APDictFactory{Ta}(d0,[],Dict(),Dict())

    aps = Array{Spot.BDD,2}(undef,naps,n) # create AP variables for all dicts
    for i=1:n, j=1:naps
        v = Spot.register_ap(aut,string("v",i,"_",j))
        aps[j,i] = Spot.bdd_ithvar(v)
    end

    for i=1:n, (j,v)=enumerate(vars) # bdd[v,i] is the variable v in coord i
        factory.bdd[v,i] = int2var(j,view(aps,:,i))
    end

    # populate d0
    for j=1:naps
        Spot.register_ap(d0.aut,string("v1_",j))
    end
        
    for t=vars
        v = factory.bdd[t,1]
        d0.s2i[t] = v
        d0.i2s[v] = t
    end

    # populate d[1:n]
    for i=1:n
        aut = Spot.make_twa_graph(bdd_dict)
        d = PlainAPDict{NTuple{i,Ta}}(aut)

        for ii=1:i, j=1:naps # only register those variables that are really used
            Spot.register_ap(aut,string("v",ii,"_",j))
        end
        
        for t=alltuples(i,vars)
            v = reduce(&, factory.bdd[t[ii],ii] for ii=1:i)
            d.s2i[t] = v
            d.i2s[v] = t
        end
        push!(factory.d,d)
    end    

    factory
end

struct TupleAPDict{N,Ta} <: APDict{NTuple{N,Ta}}
    d::PlainAPDict{NTuple{N,Ta}}
    factory::APDictFactory{Ta}
end
Base.show(io::IO, d::TupleAPDict{N}) where N = print(io, "APDict(",keys(d.factory.d0.s2i),"^",N,")")
bdd_dict(d::TupleAPDict) = bdd_dict(d.d)
Base.getindex(d::TupleAPDict,a) = d.d[a]
(d::TupleAPDict)(v) = d.d(v)
get_aut(d::TupleAPDict) = get_aut(d.d)
get_factory(d::TupleAPDict) = d.factory

struct HillyAPDict{Ta} <: APDict{Ta}
    d::PlainAPDict{Ta}
    factory::APDictFactory{Ta}
end
Base.show(io::IO, d::HillyAPDict{N}) where N = print(io, "APDict(",keys(d.factory.d0.s2i),"^)")
bdd_dict(d::HillyAPDict) = bdd_dict(d.d)
Base.getindex(d::HillyAPDict,a) = d.d[a]
(d::HillyAPDict)(v) = d.d(v)
get_aut(d::HillyAPDict) = get_aut(d.d)
get_factory(d::HillyAPDict) = d.factory

Base.getindex(factory::APDictFactory{Ta},n::Integer) where Ta = TupleAPDict{n,Ta}(factory.d[n],factory)
Base.getindex(factory::APDictFactory{Ta}) where Ta = HillyAPDict{Ta}(factory.d0,factory)

################################################################

export SpotOmegaWord, rawword

struct SpotOmegaWord{Ta} <: AbstractPeriodicVector{Ta}
    d::APDict{Ta}
    x::CxxWrap.StdLib.SharedPtrAllocated{Spot.TWAWord}
end
SpotOmegaWord(d::APDict{Ta}) where Ta = SpotOmegaWord(d,Spot.make_twa_word(bdd_dict(d)))

function SpotOmegaWord(d::APDict{Ta},w::OmegaWord{Ta}) where Ta
    sw = SpotOmegaWord(d)
    for a=w.preperiod
        Spot.push_prefix!(sw.x,d[a])
    end
    for a=w.period
        Spot.push_cycle!(sw.x,d[a])
    end
    sw
end

function SpotOmegaWord(d::APDict{Ta},preperiod::AbstractVector{Ta},period::AbstractVector{Ta}) where Ta
    sw = SpotOmegaWord(d)
    for a=preperiod
        Spot.push_prefix!(sw.x,d[a])
    end
    for a=period
        Spot.push_cycle!(sw.x,d[a])
    end
    sw
end

SpotOmegaWord(d::APDict{Ta},v::AbstractVector{Ta},args...) where Ta = SpotOmegaWord(d,OmegaWord{Ta}(v,args...))

function __get_preperiod_period(w)
    preperiod = UInt32[]
    period = UInt32[]
    Spot.get_prefix_cycle(w.x,preperiod,period)
    preperiod, period
end

function OmegaWord(w::SpotOmegaWord{Ta}) where Ta
    preperiod, period = __get_preperiod_period(w)
    buchipreperiod = Ta[w.d(Spot.bdd_from_int(i)) for i=preperiod]
    buchiperiod = Ta[w.d(Spot.bdd_from_int(i)) for i=period]
    OmegaWord(buchipreperiod,buchiperiod)
end

Base.show(io::IO, w::SpotOmegaWord) = show(io, "text/plain", w)
function Base.show(io::IO, mime::MIME"text/plain", sw::SpotOmegaWord)
    w = OmegaWord(sw)
    for a=w.preperiod
        print(io, letterstring(sw,a))
    end
    print(io, "(")
    for a=w.period
        print(io, letterstring(sw,a))
    end
    print(io, ")ʷ")
end

rawword(w::SpotOmegaWord) = SpotOmegaWord(APDict(get_aut(w.d)),w.x)

Base.size(w::SpotOmegaWord) = length.(__get_preperiod_period(w))
Base.copy(w::SpotOmegaWord) = w # seems immutable

Base.hash(w::SpotOmegaWord,h::UInt64) = hash(OmegaWord(w))
Base.:(==)(u::SpotOmegaWord,v::SpotOmegaWord) = OmegaWord(u)==OmegaWord(v)
Base.isless(u::SpotOmegaWord,v::SpotOmegaWord) = isless(OmegaWord(u),OmegaWord(v))

function Base.getindex(w::SpotOmegaWord,i::T) where T <: Integer
    preperiod, period = __get_preperiod_period(w)
    c = (i ≤ length(preperiod) ? preperiod[i] : period[mod1(i-length(preperiod),length(period))])
    w.d(Spot.bdd_from_int(c))
end
function Base.getindex(w::SpotOmegaWord{A},i::InfiniteUnitRange) where A
    sw = SpotOmegaWord(w.d)
    preperiod, period = __get_preperiod_period(w)
    
    if i.start≤length(preperiod)+1
        Spot.append_preperiod!(w.x,preperiod[i.start:end])
        Spot.append_period!(w.x,period)
    else
        n = mod1(i.start-length(preperiod),length(period))
        if n==0
            Spot.append_period!(w.x,period)
        else
            Spot.append_period!(w.x,w.period[n:end])
            Spot.append_period!(w.x,w.period[1:n-1])
        end
    end
    sw
end
function Base.getindex(w::SpotOmegaWord,i::InfiniteStepRange)
    sw = SpotOmegaWord(w.d)
    preperiod, period = __get_preperiod_period(w)
    spreperiod = preperiod[i.start:i.step:end]
    Spot.append_preperiod!(w.x,spreperiod)
    r = range(i.start+i.step*length(spreperiod)-length(preperiod),step=i.step,length=length(period))
    Spot.append_period!(w.x,period[mod1.(r,length(period))])
    sw
end

function Base.map(f::Function,w::SpotOmegaWord)
    sw = SpotOmegaWord(w.d)
    preperiod, period = __get_preperiod_period(w)
    mapper = a->Spot.id(w.d(f(w.d[Spot.bdd_from_int(a)])))
    Spot.append_preperiod!(w.x,map(mapper,preperiod))
    Spot.append_period!(w.x,map(mapper,period))
    sw
end

function Base.zip(ws::SpotOmegaWord...)
    prefixlen = maximum(size.(ws,1))
    period = lcm(size.(ws,2)...)
    SpotOmegaWord(ws.d,zip((w[1:prefixlen] for w=ws)...) |> collect,zip((w[prefixlen+1:prefixlen+period] for w=ws)...) |> collect)
end

################################################################

export SpotAutomaton, AcceptBuchi, AcceptCoBuchi
export split_edges, canonicalize, postprocessor, rawautomaton
export leftone, rightone, intersecting_word, simplify, project

abstract type Acceptance end
struct AcceptBuchi <: Acceptance n::Int end
struct AcceptCoBuchi <: Acceptance n::Int end
AcceptBuchi() = AcceptBuchi(1)
AcceptCoBuchi() = AcceptCoBuchi(1)
AcceptAll() = AcceptBuchi(0)

"""SpotAutomaton{Ta}

A wrapper for Büchi automata in `spot`, including an `APDict`

While automata in `spot` have conditions on their edges, which are
Boolean expressions in some "atomic propositions", a `SpotAutomaton`
is an automaton on a language whose letters have type `Ta`.
"""
struct SpotAutomaton{Ta} <: BuchiAutomaton{Ta}
    d::APDict{Ta}
    x::CxxWrap.StdLib.SharedPtrAllocated{Spot.TWAGraph}
end

SpotAutomaton(w::SpotOmegaWord{Ta}) where Ta = SpotAutomaton{Ta}(w.d,Spot.as_automaton(w.x))
states(A::SpotAutomaton) = 0:nstates(A)-1
nstates(A::SpotAutomaton) = Int(Spot.num_states(A.x))
ntransitions(A::SpotAutomaton) = Int(Spot.num_edges(A.x))
initial(A::SpotAutomaton) = Spot.get_init_state_number(A.x)
isinitial(A::SpotAutomaton,i) = i == initial(A)
function acceptance_string(A::SpotAutomaton)
    Spot.name(Spot.acc(A.x),"d")*" ≐ "*Spot.to_text(Spot.get_acceptance(A.x))
end

"""SpotAutomaton(w::SpotOmegaWord)
SpotAutomaton(d::APDict,[acc::Union{AcceptBuchi,AcceptCoBuchi}],[n::Integer],vs::Pair...)

Create a new automaton over letters of type `Ta`. The arguments are:
* `d`, an AP dictionary between type `Ta` and BDDs
* `acc`, an optional acceptance condition (for now, `AcceptBuchi(n)` and `AcceptCoBuchi(n)` are allowed)
* 
"""
function SpotAutomaton(d::APDict{Ta}) where Ta
    aut = Spot.make_twa_graph(bdd_dict(d))
    Spot.copy_ap_of(aut,get_aut(d))
    SpotAutomaton{Ta}(d,aut)
end

function SpotAutomaton(d::APDict,n::Integer,vs::Pair...)
    A = SpotAutomaton(d)
    resize!(A,n)
    for edge=vs
        push!(A,edge)
    end
    A
end

function SpotAutomaton(d::APDict,v::Pair,vs::Pair...)
    n = 0
    for (s,(_,t))=vs
        n = max(n,s,t)
    end
    SpotAutomaton(d,n+1,v,vs...)
end

function SpotAutomaton(d::APDict,acc::AcceptBuchi,args...)
    aut = SpotAutomaton(d,args...)
    Spot.set_generalized_buchi!(aut.x,acc.n)
    aut
end

function SpotAutomaton(d::APDict,acc::AcceptCoBuchi,args...)
    aut = SpotAutomaton(d,args...)
    Spot.set_generalized_co_buchi!(aut.x,acc.n)
    aut
end

isptrnull(p) = unsafe_load(convert(Ptr{Ptr{Nothing}},p.cpp_object))==C_NULL
function SpotOmegaWord(A::SpotAutomaton{Ta}) where Ta
    w = Spot.accepting_word(A.x)
    isptrnull(w) && error("Could not find accepting word")
    SpotOmegaWord{Ta}(A.d,w)
end

function accepting_run(A::SpotAutomaton{Ta}) where Ta
    r = Spot.accepting_run(A.x)
    isptrnull(r) && error("Could not find accepting word")
    SpotOmegaWord{UInt32}(A.d,r)
end
    
Base.show(io::IO, A::SpotAutomaton) = print(io, "SpotAutomaton(", nstates(A)," ",pluralize(nstates(A),"state"),", ", ntransitions(A)," ",pluralize(ntransitions(A),"transition"),"…)")

const spot_show_native = Ref(false)
function Base.show(io::IO, mime::MIME"text/plain", A::SpotAutomaton)
    if isdefined(Main, :IJulia) && Main.IJulia.inited
        if spot_show_native[]
            dot = String(Buchi.Spot.string_dot(A.x,""))
            img = GraphViz.load(IOBuffer(dot))
            display("image/svg+xml", img)
        else
            display_dot(io,A |> split_edges)
        end
    else
        show(io,A)
    end
end

struct EdgeIterator{Ta,X} d::APDict{Ta}; x::X end
Base.IteratorSize(::Type{EdgeIterator{Ta,X}}) where {Ta,X} = Base.SizeUnknown()
Base.eltype(::Type{EdgeIterator{Ta,Spot.TWAStateOut}}) where Ta = Pair{Tuple{Ta,Vector{UInt32}},UInt32}
Base.eltype(::Type{EdgeIterator{Ta,Spot.TWAAllTrans}}) where Ta = Pair{UInt32,Pair{Tuple{Ta,Vector{UInt32}},UInt32}}
Base.getindex(a::SpotAutomaton{Ta},i::Integer) where Ta = EdgeIterator{Ta,Spot.TWAStateOut}(a.d,Spot.out(a.x,i))
Base.getindex(a::SpotAutomaton{Ta}) where Ta = EdgeIterator{Ta,Spot.TWAAllTrans}(a.d,Spot.edges(a.x))
Base.iterate(ei::EdgeIterator) = iterate(ei,Spot.begin(ei.x))

function Base.iterate(ei::EdgeIterator{Ta,X},iter) where {Ta,X}
    Spot.isdone(ei.x,iter) && return nothing

    src,cond,dst,acc = Spot.get(iter)
    out = (ei.d(cond),Spot.fill(acc)) => dst
    if X==Spot.TWAAllTrans out = src => out end
    out, Spot.incr(iter)
end

function Base.resize!(A::SpotAutomaton,n)
    n>nstates(A) && Spot.new_states!(A.x,n-nstates(A))
    A
end

function Base.push!(g::SpotAutomaton{Ta},edge::Pair{T,Pair{Ta,T}}) where {Ta,T<:Integer}
    Spot.new_edge!(g.x,edge.first,edge.second.second,g.d[edge.second.first])
    g
end

function Base.push!(g::SpotAutomaton{Ta},edge::Pair{T,Pair{Tuple{Ta,U},T}}) where {Ta,T<:Integer,U<:Integer}
    cond = edge.second.first
    Spot.new_edge!(g.x,edge.first,edge.second.second,g.d[cond[1]],cond[2])
    g
end

function Base.push!(g::SpotAutomaton{Ta},edge::Pair{T,Pair{Tuple{Ta,Vector{U}},T}}) where {Ta,T<:Integer,U<:Integer}
    cond = edge.second.first
    acc = convert(Vector{UInt32},cond[2])
    Spot.new_edge!(g.x,edge.first,edge.second.second,g.d[cond[1]],acc)
    g
end

function Base.append!(g::SpotAutomaton,edges)
    for e=edges push!(g,e) end
    g
end

Base.isempty(g::SpotAutomaton) = Spot.is_empty(g.x)

"""simplifty(A::SpotAutomaton)

Run the postprocessor with default options, to simplify the automaton `A`.
"""
simplify(g::SpotAutomaton) = postprocessor()(g)

"""canonicalize(A::SpotAutomaton)

Reorder the states of `A` in canonical order.
"""
canonicalize(g::SpotAutomaton) = SpotAutomaton(g.d,Spot.canonicalize(g.x))

"""rawautomaton(A::SpotAutomaton)

Replace the `APDict` of `A` by a trivial dictionary, with letters of type BDD.
"""
rawautomaton(g::SpotAutomaton) = SpotAutomaton(APDict(get_aut(g.d)),g.x)

"""split_edges(A::SpotAutomaton{Ta})

Split all edges of the automaton `A` into minimal Boolean expressions (maximal conjunctions of atomic propositions), so they correspond to letters in `Ta`.
"""
split_edges(g::SpotAutomaton) = SpotAutomaton(g.d,Spot.split_edges(g.x))

"""project(A::SpotOmegaWord,inds::Union{Int,Vector{Int}})
project(A::SpotAutomaton,inds::Union{Int,Vector{Int}})

Project the word or automaton by a letter-to-letter map on tuples, specified by `inds`.

For example, if `A` has alphabet `NTuples{3,Ta}`, then `project(A,[1,3])` will map the tuple `(:x,:y,:z)` to `(:x,:z)` and `project(A,2)` will map  `(:x,:y,:z)` to `:y`; while if `A` has alphabet `Ta` or `Tuple{Ta}`, then `project(A,[0,1,0,1])` map `:x`, respectively `(:x,)`, to `(Any,:x,Any,:x)`.
"""          
project(A::SpotOmegaWord, inds::Integer) = __project_word(A,1,[inds],true)
project(A::SpotOmegaWord, inds::AbstractVector{T}) where T <: Integer = __project_word(A,1,inds,false)
project(A::SpotOmegaWord{NTuple{M,Ta}}, inds::Integer) where {Ta,M} = __project_word(A,M,[inds],true)
project(A::SpotOmegaWord{NTuple{M,Ta}}, inds::AbstractVector{T}) where {Ta,M,T <: Integer} = __project_word(A,M,inds,false)
project(A::SpotAutomaton, inds::Integer) = __project_aut(A,1,[inds],true)
project(A::SpotAutomaton, inds::AbstractVector{T}) where T <: Integer = __project_aut(A,1,inds,false)
project(A::SpotAutomaton{NTuple{M,Ta}}, inds::Integer) where {Ta,M} = __project_aut(A,M,[inds],true)
project(A::SpotAutomaton{NTuple{M,Ta}}, inds::AbstractVector{T}) where {Ta,M,T <: Integer} = __project_aut(A,M,inds,false)

diagonal(A::SpotAutomaton) = project(A,[1,2])
    
function __recoder_dict(A,m,inds,strip)
    n = length(inds)
    factory = get_factory(A.d)
    recoder = get!(factory.recoders,(m,inds)) do
        @assert all(i->0≤i≤m,inds)

        result = UInt32[]

        for (t,v)=factory.d[m].s2i
            u = reduce(&, factory.bdd[t[inds[i]],i] for i=1:n if inds[i]≠0)

            iv = Spot.id(v)
            while length(result)≤iv push!(result,~UInt32(0)) end
            result[1+iv] = Spot.id(u)
        end
        result
    end
    (recoder,strip ? (n==1 ? factory[] : error("n > 1")) : factory[n])
end

function __project_word(A::SpotOmegaWord,m,inds,strip)
    recoder, newdict = __recoder_dict(A,m,inds,strip)
    SpotOmegaWord(newdict,Spot.recode_word(A.x,recoder))
end

function __project_aut(A::SpotAutomaton,m,inds,strip)
    recoder, newdict = __recoder_dict(A,m,inds,strip)
    SpotAutomaton(newdict,Spot.recode_aut(A.x,get_aut(newdict),recoder))
end

Base.show(io::IO, pp::Spot.PostProcessor) = print(io,"PostProcessor(…)")
const OT_FLAGS = Dict(:TGBA => Spot.OT_TGBA,
                     :GeneralizedBuchi => Spot.OT_GeneralizedBuchi,
                     :BA => Spot.OT_BA,
                     :Monitor => Spot.OT_Monitor,
                     :Generic => Spot.OT_Generic,
                     :Parity => Spot.OT_Parity,
                     :ParityMin => Spot.OT_ParityMin,
                     :ParityMax => Spot.OT_ParityMax,
                     :ParityOdd => Spot.OT_ParityOdd,
                     :ParityEven => Spot.OT_ParityEven,
                     :ParityMinOdd => Spot.OT_ParityMinOdd,
                     :ParityMaxOdd => Spot.OT_ParityMaxOdd,
                     :ParityMinEven => Spot.OT_ParityMinEven,
                     :ParityMaxEven => Spot.OT_ParityMaxEven,
                     :CoBuchi => Spot.OT_CoBuchi,
                     :Buchi => Spot.OT_Buchi)
const OP_FLAGS = Dict(:Small => Spot.OP_Small,
                      :Deterministic => Spot.OP_Deterministic,
                      :Complete => Spot.OP_Complete,
                      :SBAcc => Spot.OP_SBAcc,
                      :Unambiguous => Spot.OP_Unambiguous,
                      :Colored => Spot.OP_Colored)
const OL_FLAGS = Dict(:Low => Spot.OL_Low, :Medium => Spot.OL_Medium,
                      :High => Spot.OL_High)
function postprocessor(; outputtype = nothing, preference = nothing, level = nothing)
    pp = Spot.PostProcessor()
    outputtype≠nothing && Spot.set_type(pp,OT_FLAGS[outputtype])
    if isa(preference,Nothing)
    elseif isa(preference,Integer)
        Spot.set_pref(pp,preference)
    elseif isa(preference,Symbol)
        Spot.set_pref(pp,OP_FLAGS[preference])
    elseif isa(preference,Vector{Symbol})
        Spot.set_pref(pp,reduce(|,OP_FLAGS[v] for v=preference))
    else
        error("Unknown preference $preference")
    end
    level≠nothing && Spot.set_level(pp,OL_FLAGS[level])
    pp
end
function (pp::Spot.PostProcessor)(A::SpotAutomaton)
    B = SpotAutomaton(A.d,Spot.run(pp,A.x))
    Spot.copy_ap_of(B.x,A.x) # sometimes the postprocessor drops APs
    B
end

"""intersecting_word(A::SpotAutomaton,B::SpotAutomaton)

Returns a word that is accepted by both `A` and `B`, or `nothing` if no such word exists.
"""
function intersecting_word(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    u = Spot.intersecting_word(A.x,B.x)
    isptrnull(u) ? nothing : SpotOmegaWord(A.d,u)
end

function Base.isdisjoint(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    !Spot.intersects(A.x,B.x)
end

function Base.:(∈)(w::SpotOmegaWord{Ta},A::SpotAutomaton{Ta}) where Ta
    @assert w.d==A.d
    Spot.intersects(w.x,A.x)
end

function Base.:(∩)(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    SpotAutomaton(A.d,Spot.product(A.x,B.x))
end

function Base.:(∪)(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    SpotAutomaton(A.d,Spot.product_or(A.x,B.x))
end

# beware! A,B have to be deterministic
function Base.:(⊻)(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    SpotAutomaton(A.d,Spot.product_xor(A.x,B.x))
end
Base.symdiff(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta = A ⊻ B

# beware! A,B have to be deterministic
function ↔(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    @assert Spot.prop_deterministic(A.x)
    SpotAutomaton(A.d,Spot.product_xnor(A.x,B.x))
end

function Base.:(⊆)(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    Spot.contains(A,B)
end

function Base.:(==)(A::SpotAutomaton{Ta},B::SpotAutomaton{Ta}) where Ta
    @assert A.d==B.d
    Spot.are_equivalent(A.x,B.x)
end

function Base.:(~)(A::SpotAutomaton{Ta}) where Ta
    SpotAutomaton(A.d,Spot.complement(A.x))
end

function parse_hoa(str::AbstractString,dict::APDict{Ta} = APDict()) where Ta
    A = Spot.parse_hoa_string(str,bdd_dict(dict))
    isptrnull(A) && error("Could not parse automaton")
    SpotAutomaton{Ta}(dict,A)
end

# todo: add support for aliases, to be built into dictionary
function fileio_load(name::File,dict::APDict{Ta} = APDict()) where Ta
    A = Spot.parse_hoa(filename(name),bdd_dict(dict))
    isptrnull(A) && error("Could not parse automaton")
    SpotAutomaton{Ta}(dict,A)
end

function fileio_save(name::File,A::SpotAutomaton)
    Spot.save_hoa(filename(name),A.x)
end

print_hoa(g::SpotAutomaton) = print(Buchi.Spot.string_hoa(g.x))

function Base.:(*)(A::SpotAutomaton{NTuple{N,Ta}},B::SpotAutomaton{Ta}) where {N,Ta}
    @assert get_factory(A.d) == get_factory(B.d)

    # collapse the last of A with B
    B₁ = project(B,[zeros(Int,N-1)...;1])
    C = intersect(A,B₁)
    project(C,1:N-1)
end

function Base.:(*)(A::SpotAutomaton{Ta},B::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta}
    @assert get_factory(A.d) == get_factory(B.d)

    # collapse A with the first of B
    A₁ = project(A,[1;zeros(Int,N-1)...])
    C = intersect(A₁,B)
    project(C,2:N)
end

function Base.:(*)(A::SpotAutomaton{NTuple{M,Ta}},B::SpotAutomaton{NTuple{N,Ta}}) where {M,N,Ta}
    @assert get_factory(A.d) == get_factory(B.d)

    # collapse the last of A with the first of B
    A₁ = project(A,vcat(1:M,zeros(Int,N-1)))
    B₁ = project(B,vcat(zeros(Int,M-1),1:N))
    C = intersect(A₁,B₁)
    project(C,vcat(1:M-1,M+1:M+N-1))
end

Base.:(*)(A::SpotAutomaton{NTuple{N,Ta}},w::SpotOmegaWord{Ta}) where {N,Ta} = A*SpotAutomaton(w)

Base.:(*)(w::SpotOmegaWord{Ta},A::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta} = SpotAutomaton(w)*A

function Base.:(*)(A::SpotAutomaton{NTuple{2,Ta}},w::SpotOmegaWord{Ta}) where Ta
    @assert get_factory(A.d) == get_factory(w.d)
    u = intersecting_word(A,project(SpotAutomaton(w),[0,1]))
    u==nothing && error("Could not find word in product")
    global uuuu
    uuuu = u
    project(u,1)
end

function Base.:(*)(w::SpotOmegaWord{Ta},A::SpotAutomaton{NTuple{2,Ta}}) where Ta
    @assert get_factory(A.d) == get_factory(w.d)
    u = intersecting_word(project(SpotAutomaton(w),[1,0]),A)
    u==nothing && error("Could not find word in product")
    project(u,2)
end

function Base.inv(A::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta}
    project(A,N:-1:1)
end

Base.one(A::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta} = leftone(A)

"""leftone(A)

A left unit, i.e. an element `E` with `E*A == A`.
This is what is also returned by `one`.
"""
function leftone(A::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta}
    project(A,ones(Int,N))
end

"""rightone(A)

A right unit, i.e. an element `E` with `A*E == A`.
"""
function rightone(A::SpotAutomaton{NTuple{N,Ta}}) where {N,Ta}
    project(A,fill(N,N))
end

# conversion
function SpotAutomaton(d::APDict{Ta},A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    B = SpotAutomaton(d,nstates(A))
    # by default, initial is 0, and acceptance condition is true
    for (s,(a,t))=A[]
        push!(B,s-1=>a=>t-1)
    end
    B
end

function CBuchiAutomaton(A::SpotAutomaton{Ta}) where Ta
    to_monitor_deterministic = postprocessor(outputtype = :Monitor, preference = :Deterministic)

    A₁ = to_monitor_deterministic(A) |> split_edges
    CBuchiAutomaton{Int,Ta}(nstates(A₁),[1+s=>a=>1+t for (s,((a,_),t))=A₁[]],initial=1+initial(A₁))
end

#!!! keep acceptance condition too
#!!! for modularity: BuchiAutomaton(A,newtransitions) should produce
#    an automaton with same acceptance, dict etc. as A but new transitions
function subautomaton(A::SpotAutomaton{Ta}, s) where Ta
    lookup = zeros(Int,nstates(A))
    lookup[begin.+s] = 0:length(s)-1
    B = SpotAutomaton{Ta}(A.d,(lookup[begin+s]=>a=>lookup[begin+t] for (s,(a,t))=A[] if lookup[begin+s]≠0 && lookup[begin+t]≠0))
end

function __dfs_spot_top(A,s,seen,result,radius) # need new version, 0-based
    seen[begin+s] && return
    seen[begin+s] = true
    push!(result,s)
    radius==0 && return
    for (_,t)=A[s]
        __dfs_top(A,t,seen,result,radius-1)
    end
end

function top(A::SpotAutomaton{Ta},radius,root=initial(A)) where Ta
    seen = falses(nstates(A))
    result = Int[]
    __dfs_top(A,root,seen,result,radius)
    subautomaton(A,result)
end
