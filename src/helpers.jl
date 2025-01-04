# every once in a while, we want an object to be iterable in one way, and
# also another. We encapsulate it in an Iterator{} structure.
struct Iterator{T} x::T end

pluralize(n::Real, singular::AbstractString, plural::AbstractString=singular*"s") = n == 1 ? singular : plural

################################################################

"""IntRefinablePartition{T}

A refinable integer partition data structure, following Valmari.

It is created by RefinablePartition{T}(n) giving the coarse partition 1:n

The elementary operations are
* mark(p,x) to mark object x
* split(p) to separate all marked objects from the partition (i.e. refine by potentially cutting every part in two)
* collect(p) to return a list of all the parts
"""
struct IntRefinablePartition{T} <: AbstractVector{Vector{T}}
    FP::Vector{UnitRange{Int}}
    E::Vector{T}
    L::Vector{Int}
    S::Vector{Int}
    marked::Vector{Int} # elements in FP[s]:marked[s] are marked
    touched::Vector{Int}
end

function IntRefinablePartition{T}(n::Int) where {T}
    if n==0
        FP = UnitRange{Int}[]
    else
        FP = [1:n]
    end
    E = [i for i=1:n]
    L = [i for i=1:n]
    S = ones(Int,n)
    
    IntRefinablePartition{T}(FP,E,L,S,zeros(Int,length(FP)),[])
end
IntRefinablePartition(n::Int) = IntRefinablePartition{Int}(n)

function sanitycheck(P::IntRefinablePartition)
    @assert length(P.FP)==length(P.marked)
    @assert length(P.E)==length(P.L)==length(P.S)
    @assert all(e->P.E[P.L[e]]==e, 1:length(P.E))
    @assert all(i->P.L[P.E[i]]==i, 1:length(P.E))
    @assert all(e->P.L[e]∈P.FP[P.S[e]], 1:length(P.E))
    @assert all(s->(s∈P.touched ? P.marked[s]∈P.FP[s] : P.marked[s]==first(P.FP[s])-1), 1:length(P.FP))
end

Base.length(P::IntRefinablePartition) = length(P.FP)
Base.size(P::IntRefinablePartition) = (length(P.FP),)

function mark(P::IntRefinablePartition{T},e::T) where T
    s = P.S[e]
    if P.marked[s]<first(P.FP[s])
        push!(P.touched,s)
    end
    i = P.L[e]
    if i≤P.marked[s] # already marked
        return
    end
    P.marked[s] += 1
     # swap e with the marked[s]'th element of set s
    j = P.marked[s]
    P.E[i] = P.E[j]
    P.L[P.E[i]] = i
    P.E[j] = e
    P.L[e] = j

    nothing
end

function split(P::IntRefinablePartition)
    while !isempty(P.touched)
        s = pop!(P.touched)
        j = P.marked[s]

        set0, set1 = first(P.FP[s]):j, j+1:last(P.FP[s])
        if length(set0) < length(set1)
            set0, set1 = set1, set0
        end
        if isempty(set1) # all marked, nothing to do
            P.marked[s] = first(P.FP[s])-1 # reset mark            
            continue
        end
        P.FP[s] = set0
        P.marked[s] = first(set0)-1 # reset mark
        push!(P.marked,first(set1)-1)
        push!(P.FP,set1)
        for i=set1
            P.S[P.E[i]] = length(P)
        end
    end
end

Base.getindex(P::IntRefinablePartition, s::T) where T <: Int = view(P.E,P.FP[s])
              
################################################################

"""VectorVector{T}

A vector of Vector{T}, without the memory overhead coming from
allocating gazillions of tiny vectors.
"""
struct VectorVector{Ti,Ta} <: AbstractVector{Vector{Ta}}
    A::Vector{Ta}
    F::Vector{Ti}
end

Base.length(v::VectorVector) = length(v.F)-1
Base.size(v::VectorVector) = (length(v),)
         
Base.copy(v::VectorVector) = typeof(v)(copy(v.A),copy(v.F))
function Base.copyto!(v::VectorVector{Ti,Ta},w::VectorVector{Ti,Ta}) where {Ti,Ta}
    resize!(v.A,length(w.A))
    copyto!(v.A,w.A)
    resize!(v.F,length(w.F))
    copyto!(v.F,w.F)
    v
end

Base.:(==)(v::VectorVector{Ti,Ta},w::VectorVector{Ti,Ta}) where {Ti,Ta} = v.A==w.A && v.F==w.F
Base.isless(v::VectorVector{Ti,Ta},w::VectorVector{Ti,Ta}) where {Ti,Ta} = isless((v.A,v.F),(w.A,w.F))
Base.hash(v::VectorVector,h::UInt64) = hash(v.A,hash(v.F,h))

Base.getindex(v::VectorVector,i::U) where U <: Integer = view(v.A,v.F[i]+1:v.F[i+1])

function Base.resize!(v::VectorVector,n)
    while n>length(v)
        push!(v.F,length(v.A))
    end
end

function Base.push!(v::VectorVector{Ti,Ta},p::Pair{Ti,Ta}) where {Ti,Ta}
    s,t = p
    s<length(v) && error("can only push at last entry")
    resize!(v,s)
    push!(v.A,t)
    v.F[end] += 1
    v
end

function Base.append!(v::VectorVector{Ti,Ta},data::Vector{Pair{Ti,Ta}}) where {Ti,Ta}
    for d=data
        push!(v,d)
    end
    v
end

VectorVector{Ta}(arg...) where Ta = VectorVector{Int,Ta}(arg...)
VectorVector(data::Vector{Pair{Ti,Ta}}; kwargs...) where {Ti,Ta} = VectorVector{Ti,Ta}(data; kwargs...)
VectorVector{Ti,Ta}(head::Pair{Ti,Ta},tail...; kwargs...) where {Ti,Ta} = VectorVector{Ti,Ta}([head,tail...]; kwargs...)
VectorVector{Ti,Ta}(; kwargs...) where {Ti,Ta} = VectorVector{Ti,Ta}([], [0])
function VectorVector{Ti,Ta}(data; sorted = false) where {Ti,Ta}
    v = VectorVector{Ti,Ta}()
    if sorted
        append!(v,data)
    else
        m = 0 # first determine the sizes of the various sets
        for (s,t)=data
            resize!(v,s)
            v.F[s] += 1
            m += 1
        end
        for s=1:length(v)
            v.F[s+1] += v.F[s]
        end
        resize!(v.A,m)
        for (s,t)=data # then put them in
            v.A[v.F[s]] = t
            v.F[s] -= 1
        end
    end
    v
end

Base.getindex(v::VectorVector) = Iterator{typeof(v)}(v)
Base.length(i::Iterator{T}) where T <: VectorVector = length(i.x.A)
Base.eltype(::Type{Iterator{VectorVector{Ti,Ta}}}) where {Ti,Ta} = Pair{Ti,Ta}
nentries(v::VectorVector) = length(v[])
Base.getindex(v::Iterator{T}, i) where T <: VectorVector = searchsortedfirst(v.x.F,i)-1 => v.x.A[i]

function Base.iterate(v::Iterator{T}, state=(1,1)) where T <: VectorVector
    s,t = state
    t>length(v.x.A) && return nothing
    x = s => v.x.A[t]
    while s<length(v.x.F) && t>=v.x.F[s+1] s += 1 end
    x, (s,t+1)
end

"""delete!(v[],a)

Remove all entries `a` from v
"""
function Base.delete!(v::Iterator{VectorVector{Ti,Ta}},hole::Union{Ta,Function}) where {Ti,Ta}
    shift = 0
    i = 1
    j = 2
    while i≤length(v)
        if (isa(hole,Ta) && v.x.A[i]==hole) || (isa(hole,Function) && hole(v.x.A[i]))
            shift += 1
        elseif shift>0
            v.x.A[i-shift] = v.x.A[i]
        end
        while j≤length(v.x.F) && i==v.x.F[j]
            v.x.F[j] -= shift
            j += 1
        end
        i += 1
    end
    if shift>0
        resize!(v.x.A,length(v)-shift)
    end
    v
end

function Base.deleteat!(v::VectorVector{Ti,Ta},i::Ti) where {Ti,Ta}
    shift = v.F[i+1]-v.F[i]
    if shift==0 # v[i] is already empty
        deleteat!(v.F,i)
    else
        deleteat!(v.A,v.F[i]+1:v.F[i+1])
        deleteat!(v.F,i)
        for j=i:length(v.F)
            v.F[i] -= shift
        end
    end
    v
end

function Base.deleteat!(v::VectorVector{Ti,Ta},inds::BitVector) where {Ti,Ta}
    shift = 0
    todelete = falses(length(v.A))
    for i=1:length(v.F)
        if i<length(v.F) && inds[i]
            for j=v.F[i]+1:v.F[i+1] todelete[j] = true end
            shift += v.F[i+1]-v.F[i]
        end
        if shift>0
            v.F[i] -= shift
        end
    end
    deleteat!(v.A,todelete)
    deleteat!(v.F,[inds;false])
    v
end

function Base.deleteat!(v::VectorVector{Ti,Ta},inds) where {Ti,Ta}
    shift = 0
    todelete = Ti[]
    shiftedto = 0
    for i=inds
        for j=v.F[i]+1:v.F[i+1] push!(todelete,j) end
        newshift = v.F[i+1]-v.F[i]
        if shift>0 && shiftedto<i
            for j=shiftedto+1:i v.F[j] -= shift end
        end
        shiftedto = i        
        shift += newshift
    end
    for j=shiftedto+1:length(v.F) v.F[j] -= shift end

    deleteat!(v.A,todelete)
    deleteat!(v.F,inds)
    v
end
