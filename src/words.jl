################################################################
# infinite ordinals
struct InfiniteOrdinal{N} <: Integer end

Base.show(io::IO, ::InfiniteOrdinal{0}) = print(io, "ω")
Base.show(io::IO, ::InfiniteOrdinal{1}) = print(io, "ω₁")
const ω = InfiniteOrdinal{0}()
const ω₁ = InfiniteOrdinal{1}()

export ω, ω₁, OmegaWord, PeriodicVector
export distance, confinality

Base.string(::InfiniteOrdinal{0}) = "ω"
Base.string(::InfiniteOrdinal{1}) = "ω₁"

@generated Base.:(==)(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {M,N} = :($(N==M))
Base.:(==)(::InfiniteOrdinal, ::Int) = false
Base.:(==)(::Integer, ::InfiniteOrdinal) = false

@generated Base.isless(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {N,M} = :($(isless(N, M)))
Base.isless(a::Integer, ::InfiniteOrdinal) = isfinite(a)
Base.isless(::InfiniteOrdinal, ::Integer) = false

@generated Base.:(<)(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {N,M} = :($(N < M))
Base.:(<)(a::Integer, ::InfiniteOrdinal) = true
Base.:(<)(::InfiniteOrdinal, ::Integer) = false

@generated Base.:(≤)(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {N,M} = :($(N ≤ M))
Base.:(≤)(a::Integer, ::InfiniteOrdinal) = true
Base.:(≤)(::InfiniteOrdinal, ::Integer) = false

@generated Base.min(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {N,M} = :(InfiniteOrdinal{$(min(N,M))}())
@generated Base.max(::InfiniteOrdinal{N}, ::InfiniteOrdinal{M}) where {N,M} = :(InfiniteOrdinal{$(max(N,M))}())
Base.min(a::Integer, ::InfiniteOrdinal) = a
Base.max(a::Integer, b::InfiniteOrdinal) = b
Base.min(::InfiniteOrdinal, b::Integer) = b
Base.max(a::InfiniteOrdinal, b::Integer) = a

Base.hash(::InfiniteOrdinal{N}) where N = 0xdeadbeef + N*0xdeadbeef00000000

################################################################
# unit ranges ending in ω
struct InfiniteUnitRange{T} <: AbstractUnitRange{T}
    start::T
end

Base.:(:)(start::T, ::InfiniteOrdinal{0}) where T <: Integer = InfiniteUnitRange{T}(start)

Base.show(io::IO, r::InfiniteUnitRange) = print(io, r.start,":ω")

Base.last(r::InfiniteUnitRange) = ω
Base.length(r::InfiniteUnitRange) = ω
Base.:(+)(r::InfiniteUnitRange{T},a::T) where T <: Integer = InfiniteUnitRange{T}(r.start+a)
Base.:(+)(a::T,r::InfiniteUnitRange{T}) where T <: Integer = r+a
Base.:(-)(r::InfiniteUnitRange{T},a::T) where T <: Integer = r+(-a)

Base.intersect(r::InfiniteUnitRange{T},s::InfiniteUnitRange{T}) where T <: Integer = InfiniteUnitRange{T}(max(r.start,s.start))
Base.intersect(r::InfiniteUnitRange{T},s::UnitRange{T}) where T <: Integer = max(r.start,s.start):s.stop
Base.intersect(r::UnitRange{T},s::InfiniteUnitRange{T}) where T <: Integer = s ∩ r
Base.intersect(r::InfiniteUnitRange{T},s::StepRange{T}) where T <: Integer = max(r.start+mod(s.start-r.start,s.step),s.start):s.step:s.stop
Base.intersect(r::StepRange{T},s::InfiniteUnitRange{T}) where T <: Integer = s ∩ r

Base.issubset(r::InfiniteUnitRange{T},s::InfiniteUnitRange{T}) where T <: Integer = (r.start ≥ s.start)
Base.issubset(r::UnitRange{T},s::InfiniteUnitRange{T}) where T <: Integer = (r.start ≥ s.start)
Base.issubset(r::InfiniteUnitRange{T},s::UnitRange{T}) where T <: Integer = false
Base.issubset(r::StepRange{T},s::InfiniteUnitRange{T}) where T <: Integer = (r.start ≥ s.start)
Base.issubset(r::InfiniteUnitRange{T},s::StepRange{T}) where T <: Integer = false

Base.in(a::T,r::InfiniteUnitRange{T}) where T <: Integer = (a ≥ r.start)
Base.in(a,r::InfiniteUnitRange{T}) where T <: Integer = false
Base.in(::InfiniteOrdinal,r::InfiniteUnitRange{T}) where T <: Integer = false
              
################################################################
# step ranges ending in ω
struct InfiniteStepRange{T} <: OrdinalRange{T,T}
    start::T
    step::T
end

Base.:(:)(start::T, step::T, ::InfiniteOrdinal{0}) where T <: Integer = InfiniteStepRange{T}(start,step)

Base.show(io::IO, r::InfiniteStepRange) = print(io, r.start,":",r.step,":ω")

Base.last(r::InfiniteStepRange) = ω
Base.length(r::InfiniteStepRange) = ω
Base.step(r::InfiniteStepRange) = r.step

Base.:(+)(r::InfiniteStepRange{T},a::T) where T <: Integer = InfiniteStepRange{T}(r.start+a,r.step)
Base.:(+)(a::T,r::InfiniteStepRange{T}) where T <: Integer = InfiniteStepRange{T}(a+r.start,r.step)
Base.:(+)(r::InfiniteUnitRange{T},s::InfiniteUnitRange{T}) where T <: Integer = InfiniteStepRange{T}(r.start+s.start,T(2))
Base.:(+)(r::InfiniteUnitRange{T},s::InfiniteStepRange{T}) where T <: Integer = InfiniteStepRange{T}(r.start+s.start,1+s.step)
Base.:(+)(r::InfiniteStepRange{T},s::InfiniteUnitRange{T}) where T <: Integer = InfiniteStepRange{T}(r.start+s.start,r.step+1)
Base.:(+)(r::InfiniteStepRange{T},s::InfiniteStepRange{T}) where T <: Integer = InfiniteStepRange{T}(r.start+s.start,r.step+s.step)
Base.:(-)(r::InfiniteStepRange{T},a::T) where T <: Integer = InfiniteStepRange{T}(r.start-a,r.step)

Base.:(*)(r::InfiniteUnitRange{T},a::T) where T <: Integer = InfiniteStepRange{T}(r.start*a,a)
Base.:(*)(a::T,r::InfiniteUnitRange{T}) where T <: Integer = InfiniteStepRange{T}(a*r.start,a)
Base.:(*)(r::InfiniteStepRange{T},a::T) where T <: Integer = InfiniteStepRange{T}(r.start*a,a*r.step)
Base.:(*)(a::T,r::InfiniteStepRange{T}) where T <: Integer = InfiniteStepRange{T}(a*r.start,a*r.step)

function Base.intersect(r::InfiniteStepRange{T},s::InfiniteStepRange{T}) where T <: Integer
    d, u, v = gcdx(r.step,s.step)
    period = r.step÷d*s.step
    if mod(r.start-s.start,d)==0
        start = r.start + u*(s.start-r.start)÷d*r.step
        InfiniteStepRange{T}(max(r.start + mod(start-r.start,period),s.start + mod(start-s.start,period)),period)        
    else
        one(T):zero(T)
    end
end
Base.intersect(r::InfiniteStepRange{T},s::InfiniteUnitRange{T}) where T <: Integer = InfiniteStepRange{T}(max(r.start,s.start + mod(r.start-s.start,r.step)),r.step)
Base.intersect(r::InfiniteUnitRange{T},s::InfiniteStepRange{T}) where T <: Integer = s ∩ r
Base.intersect(r::InfiniteStepRange{T},s::UnitRange{T}) where T <: Integer = max(r.start,s.start + mod(r.start-s.start,r.step)):r.step:s.stop
Base.intersect(r::UnitRange{T},s::InfiniteStepRange{T}) where T <: Integer = s ∩ r
function Base.intersect(r::InfiniteStepRange{T},s::StepRange{T}) where T <: Integer
    d, u, v = gcdx(r.step,s.step)
    period = r.step÷d*s.step
    if mod(r.start-s.start,d)==0
        start = r.start + u*(s.start-r.start)÷d*r.step
        max(r.start + mod(start-r.start,period),s.start + mod(start-s.start,period)):period:s.stop
    else
        one(T):zero(T)
    end
end
Base.intersect(r::StepRange{T},s::InfiniteStepRange{T}) where T <: Integer = s ∩ r

Base.issubset(r::InfiniteStepRange{T},s::InfiniteStepRange{T}) where T <: Integer = (r.start ≥ s.start && rem(r.step,s.step)==0 && rem(r.start-s.start,gcd(r.step,s.step))==0)
Base.issubset(r::InfiniteStepRange{T},s::InfiniteUnitRange{T}) where T <: Integer = (r.start ≥ s.start)
Base.issubset(r::InfiniteUnitRange{T},s::InfiniteStepRange{T}) where T <: Integer = (r.start ≥ s.start && isone(s.step))
Base.issubset(r::UnitRange{T},s::InfiniteStepRange{T}) where T <: Integer = (r.start ≥ s.start && isone(s.step))
Base.issubset(r::InfiniteStepRange{T},s::UnitRange{T}) where T <: Integer = false
Base.issubset(r::StepRange{T},s::InfiniteStepRange{T}) where T <: Integer = (r.start ≥ s.start && rem(r.step,s.step)==0 && rem(r.start-s.start,gcd(r.step,s.step))==0)
Base.issubset(r::InfiniteStepRange{T},s::StepRange{T}) where T <: Integer = false

Base.in(a::T,r::InfiniteStepRange{T}) where T <: Integer = (a ≥ r.start && rem(a-r.start,r.step)==0)
Base.in(a,r::InfiniteStepRange{T}) where T <: Integer = false
Base.in(::InfiniteOrdinal,r::InfiniteStepRange{T}) where T <: Integer = false

################################################################
# periodic words
abstract type AbstractPeriodicVector{A} end

function _prefix_function(w)
    n = length(w)
    pi = [0]
    j = 0
    for i in 2:n
        while j > 0 && w[i] != w[j + 1]
            j = pi[j]
        end
        if w[i] == w[j + 1]
            j += 1
        end
        push!(pi,j)
    end
    return pi
end

function _trim(preperiod::Vector{T},period::Vector{T},copy=0) where T
    n = length(period)
    pi = _prefix_function(period)
    len_period = n - pi[n]
    if n % len_period == 0 && len_period < n # can reduce period
        n = len_period
        if copy==1
            period = period[1:n]
            copy = 2 # remember we copied the period
        else
            resize!(period,n)
        end
    end
    m = length(preperiod)
    m₀,n₀ = m,n
    while m₀>0 && preperiod[m₀] == period[n₀]
        n₀ = (n₀==1 ? n : n₀-1)
        m₀ -= 1
    end
    if m₀!=m # can shorten preperiod
        if copy==0
            resize!(preperiod,m₀)
        else
            preperiod = preperiod[1:m₀]
        end
        if mod(m-m₀,n)!=0
            if copy==1
                oldperiod = period
                period = Vector{T}(undef,n)
                for i=n₀+1:n period[i-n₀] = oldperiod[i] end
                for i=1:n₀ period[i+n-n₀] = oldperiod[i] end
            else # permute in-place
                circshift!(period,n-n₀)
            end
        end
    end
    return preperiod,period
end

struct PeriodicVector{A} <: AbstractPeriodicVector{A}
    preperiod::Vector{A}
    period::Vector{A}
    PeriodicVector{A}(preperiod,period;copy=false) where A = new(_trim(preperiod,period,copy)...)
    PeriodicVector(preperiod::Vector{A},period::Vector{A};kwargs...) where A = PeriodicVector{A}(preperiod,period;kwargs...)
    PeriodicVector{A}(v::Vector{A};kwargs...) where A = PeriodicVector{A}(A[],v;kwargs...)
    PeriodicVector(v::Vector{A};kwargs...) where A = PeriodicVector(A[],v;kwargs...)
end

"""OmegaWord{A}

An ω-word, with period and preperiod of type `A`
"""
struct OmegaWord{A} <: AbstractPeriodicVector{A}
    preperiod::Vector{A}
    period::Vector{A}
    OmegaWord{A}(preperiod,period;copy=false) where {A} = new(_trim(preperiod,period,copy)...)
    OmegaWord(preperiod::Vector{A},period::Vector{A};kwargs...) where A = OmegaWord{A}(preperiod,period;kwargs...)
    OmegaWord{A}(v::Vector{A};kwargs...) where {A} = OmegaWord{A}(A[],v;kwargs...)
    OmegaWord(v::Vector{A};kwargs...) where A = OmegaWord{A}(A[],v;kwargs...)
end

Base.size(v::AbstractPeriodicVector) = (length(v.preperiod),length(v.period))
Base.size(v::AbstractPeriodicVector,i) = (i==1 ? length(v.preperiod) : i==2 ? length(v.period) : 1)

letterstring(i::Integer) = string(i)
letterstring(c::Char) = string(c)
letterstring(s::Symbol) = string(s)
letterstring(t::Tuple) = join([letterstring(i) for i=t],":")
letterstring(a,b) = letterstring(b) # discard extra information on container

function Base.show(io::IO, ::MIME"text/plain", w::OmegaWord)
    for a=w.preperiod
        print(io, letterstring(a))
    end
    print(io, "\e[4;1m")
    for a=w.period
        print(io, letterstring(a))
    end
    print(io, "\e[0m")
end
Base.copy(w::AbstractPeriodicVector) = typeof(w)(copy(w.preperiod,w.period))

Base.hash(w::AbstractPeriodicVector,h::UInt64) = hash(w.preperiod,hash(w.period,h))
function Base.:(==)(u::AbstractPeriodicVector,v::AbstractPeriodicVector)
    return u.preperiod==v.preperiod && u.period==v.period
end
function Base.isless(u::AbstractPeriodicVector,v::AbstractPeriodicVector) # lexicographic
    if u.preperiod==v.preperiod && u.period==v.period
        return false
    end
    i = 1
    while true
        if u[i]!=v[i]
            return isless(u[i],v[i])
        end
        i += 1
    end
end

Base.getindex(w::AbstractPeriodicVector,i::T) where T <: Integer = (i ≤ length(w.preperiod) ? w.preperiod[i] : w.period[mod1(i-length(w.preperiod),length(w.period))])

Base.getindex(w::AbstractPeriodicVector,i::UnitRange) = [w[j] for j=i]
Base.getindex(w::AbstractPeriodicVector,i::StepRange) = [w[j] for j=i]
function Base.getindex(w::AbstractPeriodicVector{A},i::InfiniteUnitRange) where A
    if i.start≤length(w.preperiod)+1
        typeof(w)(w.preperiod[i.start:end],w.period)
    else
        n = mod1(i.start-length(w.preperiod),length(w.period))
        if n==0
            typeof(w)(A[],w.period)
        else
            typeof(w)(A[],vcat(w.period[n:end],w.period[1:n-1]))
        end
    end
end
function Base.getindex(w::AbstractPeriodicVector,i::InfiniteStepRange)
    preperiod = w.preperiod[i.start:i.step:end]
    r = range(i.start+i.step*length(preperiod)-length(w.preperiod),step=i.step,length=length(w.period))
    typeof(w)(preperiod,w.period[mod1.(r,length(w.period))])
end

Base.length(w::AbstractPeriodicVector) = ω

Base.map(f::Function,w::OmegaWord) = OmegaWord(map(f,w.preperiod),map(f,w.period))

function Base.zip(ws::OmegaWord...)
    prefixlen = maximum(size.(ws,1))
    period = lcm(size.(ws,2)...)
    OmegaWord(zip((w[1:prefixlen] for w=ws)...) |> collect,zip((w[prefixlen+1:prefixlen+period] for w=ws)...) |> collect)
end

"""distance(u,v)

Returns the usual distance between words `u`,`v`, namely `2^{-d}` if
 u`,`v` agree on their first `d` letters, and `0` if `u=v`.
"""
function distance(u::AbstractPeriodicVector{A},v::AbstractPeriodicVector{A}) where A
    u==v && return 0.0
    d = 1.0
    i = 1
    while true
        u[i]≠v[i] && return d
        i += 1
        d *= 0.5
    end
end

"""confinality(u)

The unique purely-periodic word that is almost-everywhere the same as `u`.

To test whether `u`,`v` are confinal, one can test `confinality(u)==confinality(v)`
"""
confinality(u::AbstractPeriodicVector) = u[1+length(u.preperiod)*length(u.period):ω]
