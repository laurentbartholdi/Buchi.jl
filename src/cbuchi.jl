"""CBuchiAutomaton{Ti,A}

The class of closed, deterministic Büchi automata.
The states are of type `Ti<:Int`, and `A` is an alphabet, typically tuples.
"""
struct CBuchiAutomaton{Ti,Ta} <: BuchiAutomaton{Ta}
    x::VectorVector{Ti,Pair{Ta,Ti}} # the transitions

    function CBuchiAutomaton{Ti,Ta}() where {Ti,Ta}
        new(VectorVector{Ti,Pair{Ta,Ti}}())
    end

    CBuchiAutomaton{Ti,Ta}(data; kwargs...) where {Ti,Ta} = CBuchiAutomaton{Ti,Ta}(1, data; kwargs...)
    CBuchiAutomaton{Ti,Ta}(head, tail...; kwargs...) where {Ti,Ta} = CBuchiAutomaton{Ti,Ta}(1, [head,tail...]; kwargs...)

    function CBuchiAutomaton{Ti,Ta}(n::Integer, data; sorted = false, minimize = true, initial = 1) where {Ti,Ta}
        if isa(initial,Int) && initial≠1 # swap 1 and initial
            data = ((s==initial ? 1 : s==1 ? initial : s)=>a=>(t==initial ? 1 : t==1 ? initial : t) for (s,(a,t))=data)
        elseif isa(initial,AbstractVector)
            n += 1
            # move 1 out of the way
            newdata = [(s==1 ? n : s)=>a=>(t==1 ? n : t) for (s,(a,t))=data]
            # and add transitions from 1 to all initial
            for i=initial, (s,(a,t))=data
                i==s && push!(newdata,1=>a=>(t==1 ? n : t))
            end
            data = newdata
        end
        A = new(VectorVector{Ti,Pair{Ta,Ti}}(data; sorted = sorted))
        resize!(A,n)

        sorted || sortstates!(A)
        if minimize && nstates(A)>0
            remove_unreachables!(A)
            remove_deadends!(A)
            minimize!(A)
        end
        A
    end

    CBuchiAutomaton{Ti,Ta}(::Val{nothing},data) where {Ta,Ti} = new(data) # save constructor
end

export CBuchiAutomaton
export reinitialize, minimize, minimize!

initial(A::CBuchiAutomaton) = 1
isinitial(A::CBuchiAutomaton,i) = i==initial(A)
nstates(A::CBuchiAutomaton) = length(A.x)
ntransitions(A::CBuchiAutomaton) = length(A[])
states(A::CBuchiAutomaton) = Base.OneTo(nstates(A))
acceptance_string(A::CBuchiAutomaton) = "looping"
Base.getindex(A::CBuchiAutomaton,s) = A.x[s]
Base.collect(A::CBuchiAutomaton) = collect(A.x)

Base.copy(A::CBuchiAutomaton) = typeof(A)(Val(nothing),copy(A.x))
Base.copyto!(A::CBuchiAutomaton,B::CBuchiAutomaton) = (copyto!(A.x,B.x); A)

function Base.getindex(A::CBuchiAutomaton{Ti,Ta},s,a::Ta) where {Ti,Ta}
    for t=A[s]
        if t.first==a return t.second end
    end
    return 0
end
function Base.getindex(A::CBuchiAutomaton{Ti,Ta},s,a::Tc,b...) where {Ti,Tc,Ta <: Tuple{Tc,Vararg}}
    a = (a,b...)
    k = length(a)
    (t.first[k+1:end]=>t.second for t=A[s] if t.first[1:k]==a)
end

Base.getindex(A::CBuchiAutomaton) = Iterator{typeof(A.x)}(A.x)
Base.iterate(A::CBuchiAutomaton, state = 1) = iterate(A.x, state)
Base.eltype(::Type{CBuchiAutomaton{Ti,Ta}}) where {Ti,Ta} = Pair{Ta,Ti}
Base.push!(A::CBuchiAutomaton,p) = (push!(A.x,p); A)
Base.append!(A::CBuchiAutomaton,data) = (append!(A.x,data); A)

Base.resize!(A::CBuchiAutomaton,n) = (resize!(A.x, n); A)

Base.:(==)(A::CBuchiAutomaton{Ti,Ta},B::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta} = A.x==B.x # our automata are normalized
Base.isless(A::CBuchiAutomaton{Ti,Ta},B::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta} = isless(A.x,B.x)
Base.hash(A::CBuchiAutomaton,h::UInt64) = hash(A.x,h)

function Base.show(io::IO, A::CBuchiAutomaton)
    print(io, "CBuchiAutomaton(", nstates(A)," ",pluralize(nstates(A),"state"),", ", ntransitions(A)," ",pluralize(ntransitions(A),"transition"),"…)")
end

function Base.show(io::IO, ::MIME"text/plain", A::CBuchiAutomaton)
    if isdefined(Main, :IJulia) && Main.IJulia.inited
        display_dot(io,A)
    else
        show(io, A)
    end
end

function sortstates!(A::CBuchiAutomaton)
    for s=states(A)
        sort!(A[s],lt=(a,b)->a.first<b.first)
    end
end    

CBuchiAutomaton(data::Vector{Pair{Ti,Pair{Ta,Ti}}}; kwargs...) where {Ta,Ti <: Int} = CBuchiAutomaton{Ti,Ta}(0, data; kwargs...)
CBuchiAutomaton(n::Integer, data::Vector{Pair{Ti,Pair{Ta,Ti}}}; kwargs...) where {Ta,Ti <: Int} = CBuchiAutomaton{Ti,Ta}(n, data; kwargs...)
CBuchiAutomaton(head::Pair,tail...; kwargs...) = CBuchiAutomaton(0,[head;tail...]; kwargs...)

function __unreachables_scan(A,s,unseen)
    s>nstates(A) && return # this is a hanging edge, it will disappear as deadend
    if unseen[s]
        unseen[s] = false
        for (_,t)=A[s]
            __unreachables_scan(A,t,unseen)
        end
    end
end

"""remove_unreachables!(A)

Removes from A all states that cannot be reached from the initial state
"""
function remove_unreachables!(A::CBuchiAutomaton{Ti,Ta},r=initial(A)) where {Ti,Ta}
    n = nstates(A)
    unseen = trues(n)
    __unreachables_scan(A,r,unseen)
    if any(unseen)
        deleteat!(A.x,unseen)
        relabel = Ti[]
        j = 1
        for i=1:n
            if unseen[i]
                push!(relabel,0)
            else
                push!(relabel,j)
                j += 1
            end
        end
        for i=1:nstates(A), j=1:length(A[i])
            (a,t) = A[i][j]
            A[i][j] = a=>relabel[t]
        end
    end
    A
end

"""remove_deadends!(A)

Remove all transitions in A that don't lead to an infinite cycle
"""
function remove_deadends!(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    # reverse lookup
    from = VectorVector{Ti}(t=>s for (s,(_,t))=A[])

    looseedges = false  # first delete all edges pointing to an inexistant state
    for s=1:nstates(A), i=1:length(A[s])
        if A[s][i].second>nstates(A)
            A[s][i] = A[s][i].first=>0
            looseedges = true
        end
    end

    activity = [count(p->p.second≠0,A[s]) for s=states(A)]
    queue = filter(s->activity[s]==0, states(A))
    dead = falses(nstates(A))

    idle = true
    while !isempty(queue)
        t = pop!(queue)
        t == initial(A) && continue # never delete initial state
        dead[t] = true
        for s=from[t]
            idle = false
            activity[s] -= 1
            for i=1:length(A[s])
                if A[s][i].second==t # mark transition as dead
                    A[s][i] = A[s][i].first=>0
                end
            end
            if activity[s]==0
                push!(queue,s)
            end
        end
    end

    if any(dead) || looseedges
        delete!(A.x[],pair->pair.second==0)
    end        
    if any(dead)
        newstate = Ti[] # get new state numbers
        t = 1
        for s=states(A)
            if dead[s]
                push!(newstate,0)
            else
                push!(newstate,t)
                t += 1
            end
        end
        for i=1:length(A.x.A) #! don't peek in the structure!
            A.x.A[i] = A.x.A[i].first=>newstate[A.x.A[i].second]
        end
        deleteat!(A.x,dead)
    end
    A
end

function __remove_scan(A,s,alive)
    if !alive[s]
        alive[s] = true
        for (a,t)=A[s]
            __remove_scan(A,t,alive)
        end
    end
end

"""minimize(A)

Returns an automaton equivalent to A in which all states are different. This is the minimal automaton equivalent to A, if A has no unreachable state nor dead end.
"""
function minimize(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    nstates(A)≤1 && return A

    B = IntRefinablePartition(nstates(A))
    C = IntRefinablePartition(ntransitions(A))

    # make initial partition: split cords according to their label
    sort!(C.E,lt=(i,j)->A.x.A[i].first<A.x.A[j].first) #! hack
    a = A.x.A[1].first
    m = 1
    pop!(C.FP); pop!(C.marked)
    for i=1:ntransitions(A)
        t = C.E[i]
        if A.x.A[t].first ≠ a # cut partition here
            a = A.x.A[t].first
            push!(C.FP,m:i-1)
            push!(C.marked,m-1)
            m = i
        end
        C.S[t] = length(C.FP)+1
        C.L[t] = i
    end
    push!(C.FP,m:ntransitions(A))
    push!(C.marked,m-1)
    
    # reverse lookup
    from = VectorVector{Ti}(t=>i for (i,(s,(_,t)))=enumerate(A[]))

    # tails of transitions
    tail = [s for (s,(_,t))=A[]]

    b = 2
    c = 1
    while c ≤ length(C)
        for i=C[c]
            mark(B,tail[i])
        end
        split(B)
        c += 1
        while b ≤ length(B)
            for i=B[b], j=from[i]
                mark(C,j)
            end
            split(C)
            b += 1
        end
    end

    order = [i for i=1:length(B)]
    order[B.S[initial(A)]] = 1 # make initial state be 1
    order[1] = B.S[initial(A)]
    
    start = B.S[initial(A)]
    transitions = Pair{Ti,Pair{Ta,Ti}}[]
    for i=1:ntransitions(A)
        if B.L[tail[i]] == first(B.FP[B.S[tail[i]]])
            push!(transitions,order[B.S[tail[i]]]=>A.x.A[i].first=>order[B.S[A.x.A[i].second]])
        end
    end
    M = CBuchiAutomaton{Ti,Ta}(transitions, minimize=false)
    M = subautomaton(M,dfs_reachables(M,1),minimize=false)
    #! make it more efficient by not creating the structure right now, and finding the correct DFS order
end
minimize!(A::CBuchiAutomaton) = copyto!(A, minimize(A))

function CBuchiAutomaton{Ti,Tuple{Ta}}(w::OmegaWord{Ta}) where {Ti,Ta}
    pp,p = size(w)
    v = CBuchiAutomaton{Ti,Tuple{Ta}}()
    for i=1:pp
        push!(v,i=>(w.preperiod[i],)=>i+1)
    end
    for i=1:p
        push!(v,pp+i=>(w.period[i],)=>pp+mod1(i+1,p))
    end
    v
end
CBuchiAutomaton(w::OmegaWord{Ta}) where Ta = CBuchiAutomaton{Int,Tuple{Ta}}(w)

function __language_rec(A,head; maxn,states,word,words)
    tail = head÷2
    found = false
    if head>tail≥1 && states[tail]==states[head] # we found a cycle
        w = OmegaWord(word[1:tail-1],word[tail:end])
        w∈words && return
        push!(words,w)
        found = true
    end
    if head≥maxn && found
        return
    end
    for (a,t)=A[states[head]]
        
        push!(states,t)
        push!(word,a)
        __language_rec(A,head+1; maxn,states,word,words)
        pop!(word)
        pop!(states)
    end
end

function language(A::CBuchiAutomaton{Ti,Ta}; length = ω) where {Ti,Ta}
    states = Ti[initial(A)]
    word = Ta[]
    words = Set{OmegaWord{Ta}}()

    __language_rec(A,1; maxn=length,states,word,words)
    words
end

function OmegaWord{Ta}(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    words = language(A)
    length(words)==0 && error("Automaton accepts nothing")
    length(words)>1 && error("Automaton accepts more than one word")
    first(words)
end
OmegaWord(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta} = OmegaWord{Ta}(A)
OmegaWord{Ta}(A::CBuchiAutomaton{Ti,Tuple{Ta}}) where {Ti,Ta} = OmegaWord{Ta}(projection(A,1))
OmegaWord(A::CBuchiAutomaton{Ti,Tuple{Ta}}) where {Ti,Ta} = OmegaWord{Ta}(A)

function Base.:(∈)(w::OmegaWord{Ta},A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    s = initial(A)
    for a = w.preperiod
        s = A[s,a]
        s == 0 && return false
    end
    ss = s
    while true
        for a = w.period s = A[s,a]; s == 0 && return false end
        s == ss && return true
        for a = w.period ss = A[ss,a]; ss == 0 && return false end
        s == ss && return true
        for a = w.period ss = A[ss,a]; ss == 0 && return false end
        s == ss && return true
    end
end

function __isnotempty_scan(A,s,visited,stack)
    s>nstates(A) && return false # we're out of edges

    if !visited[s]
        # mark the current node as visited and part of recursion stack
        visited[s] = stack[s] = true

        # recur on all the successors
        for (_,t)=A[s]
            if !visited[t] && __isnotempty_scan(A,t,visited,stack)
                return true
            elseif stack[t]
                return true
            end
        end

        # remove the vertex from recursion stack
        stack[s] = false
    end
    false
end

Base.isempty(A::CBuchiAutomaton) = !__isnotempty_scan(A,initial(A),falses(nstates(A)),falses(nstates(A)))

"""subautomaton(A,s)

Returns the subautomaton of `A` on the list of states `s`
"""
function subautomaton(A::CBuchiAutomaton{Ti,Ta}, s; minimize = true) where {Ti,Ta}
    lookup = zeros(Ti,nstates(A))
    lookup[s] = 1:length(s)
    B = CBuchiAutomaton{Ti,Ta}((lookup[s]=>a=>lookup[t] for (s,(a,t))=A[] if lookup[s]≠0 && lookup[t]≠0), minimize = minimize)
end

"""dfs_reachables(A)

Returns a list of states of `A` reachable from 1, in depth-first-search order.
"""
function dfs_reachables(A::CBuchiAutomaton{Ti,Ta}, r = initial(A)) where {Ti,Ta}
    result = Ti[]
    unseen = trues(nstates(A))
    __dfs_reachables_scan(A,r,result,unseen)
    result
end

function __dfs_reachables_scan(A,s,result,unseen)
    if unseen[s]
        unseen[s] = false
        push!(result,s)
        for (_,t)=A[s]
            __dfs_reachables_scan(A,t,result,unseen)
        end
    end
end

"""reinitialize(A,r)

Returns an automaton in which the initial state is r.
"""
function reinitialize(A::CBuchiAutomaton{Ti,Ta}, r) where {Ti,Ta}
    subautomaton(A,dfs_reachables(A,r))
end

function __dfs_top(A,s,seen,result,radius)
    seen[s] && return
    seen[s] = true
    push!(result,s)
    radius==0 && return
    for (_,t)=A[s]
        __dfs_top(A,t,seen,result,radius-1)
    end
end

"""top(A,radius)

Returns the top of the automaton of given radius; namely the subautomaton
spanned by all states at distance at most `radius` from the initial state.

The returned automaton is not minimized.
"""
function top(A::CBuchiAutomaton,radius,root=initial(A))
    seen = falses(nstates(A))
    result = Int[]
    __dfs_top(A,root,seen,result,radius)
    subautomaton(A,result;minimize=false)
end

"""spheres(A)

Returns a list `S` of lists of states of `A`, where `S[1+i]` is the list of all states at distance `i` from the initial state.
"""
function spheres(A::BuchiAutomaton,root=initial(A))
    queue = Queue{Pair{Int,Int}}()
    dist = fill(typemax(Int),nstates(A))
    sphere = Vector{Int}[]
    enqueue!(queue,root=>0)
    while !isempty(queue)
        s,r = dequeue!(queue)
        dist[s]≤r && continue
        dist[s]=r
        while length(sphere)≤r push!(sphere,[]) end
        push!(sphere[r+1],s)
        for (_,t)=A[s]
            enqueue!(queue,t=>r+1)
        end
    end
    sphere
end
################################################################
# operations for transducers

function diagonal(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    CBuchiAutomaton{Ti,Tuple{Ta,Ta}}(s=>(a,a)=>t for (s,(a,t))=A[],minimize=false)
end

function mul_word_automaton(w::OmegaWord{Tw},A::CBuchiAutomaton{Ti,Ta}) where {Tw,Ti,Ta <: Tuple{Tw,Vararg}}
    pp, p = size(w)
    Tb = Tuple{Ta.parameters[2:end]...}
    newstates = Dict{Tuple{Ti,Ti},Ti}()
    B = CBuchiAutomaton{Ti,Tb}()

    queue = Queue{Tuple{Ti,Ti,Ti}}()
    enqueue!(queue,(initial(A),1,initial(B))) # states in A,w,B
    nstates = 1

    while !isempty(queue)
        s,t,u = dequeue!(queue)
        newt = (t==pp+p ? pp+1 : t+1)

        for (a,news)=A[s]
            a[1]==w[t] || continue
            push!(B,u=>a[2:end]=>get!(newstates,(news,newt)) do
                  # allocate new state
                  nstates += 1
                  enqueue!(queue,(news,newt,nstates))
                  nstates
                  end)
        end
    end
    resize!(B,nstates)
    remove_deadends!(B)
end

function Base.:(*)(w::OmegaWord{Ta},A::CBuchiAutomaton{Ti,Tuple{Ta,Tb}}) where {Ti,Ta,Tb}
    OmegaWord(mul_word_automaton(w,A))
end

function mul_automaton_word(A::CBuchiAutomaton{Ti,Ta},w::OmegaWord{Tw}) where {Ti,Ta <: Tuple,Tw}
    pp, p = size(w)
    @assert Ta.parameters[end]==Ta
    Tb = Tuple{Ta.parameters[1:end-1]...}
    newstates = Dict{Tuple{Ti,Ti},Ti}()
    B = CBuchiAutomaton{Ti,Tb}()

    queue = Queue{Tuple{Ti,Ti,Ti}}()
    enqueue!(queue,(initial(A),1,initial(B))) # states in A,w,B
    nstates = 1

    while !isempty(queue)
        s,t,u = dequeue!(queue)
        newt = (t==pp+p ? pp+1 : t+1)

        for (a,news)=A[s]
            a[2]==w[t] || continue
            push!(B,u=>a[1:end-1]=>get!(newstates,(news,newt)) do
                  # allocate new state
                  nstates += 1
                  enqueue!(queue,(news,newt,nstates))
                  nstates
                  end)
        end
    end
    resize!(B,nstates)
    remove_deadends!(B)
end

function Base.:(*)(A::CBuchiAutomaton{Ti,Tuple{Ta,Tb}},w::OmegaWord{Tb}) where {Ti,Ta,Tb}
    OmegaWord(mul_automaton_word(A,w))
end

function Base.:(*)(A::CBuchiAutomaton{Ti,Ta},B::CBuchiAutomaton{Ti,Tb}) where {Ti,Ta,Tb}
    @assert Ta.parameters[end] == Tb.parameters[1]

    newstates = Dict{Set{Tuple{Ti,Ti}},Ti}()
    Tc = Tuple{Ta.parameters[1:end-1]...,Tb.parameters[2:end]...}
    C = CBuchiAutomaton{Ti,Tc}()

    nstates = 1
    queue = Queue{Pair{Set{Tuple{Ti,Ti}},Ti}}()
    enqueue!(queue,Set([(initial(A),initial(B))])=>nstates) # initial states, and state in product

    while !isempty(queue)
        ss,u = dequeue!(queue)
        tt = Dict{Tc,Set{Tuple{Ti,Ti}}}()
        for (s,t)=ss, (a,news)=A[s], (b,newt)=B[t]
            if a[end]==b[1]
                c = (a[1:end-1]...,b[2:end]...)
                push!(get!(tt,c,Set()),(news,newt))
            end
        end
        for (c,uu)=tt
            push!(C,u=>c=>get!(newstates,uu) do
                  # allocate new state
                  nstates += 1
                  enqueue!(queue,uu=>nstates)
                  nstates
                  end)
        end
    end
    resize!(C,nstates)
    remove_deadends!(C)

    C = minimize(C)
    subautomaton(C,dfs_reachables(C,1))
end

function Base.inv(A::CBuchiAutomaton{Ti,Ta}) where {Ti,Ta}
    Tb = Tuple{reverse(collect(Ta.parameters))...}
    B = CBuchiAutomaton{Ti,Tb}(t=>reverse(a)=>u for (t,(a,u))=A[]; minimize=false)
    subautomaton(B,dfs_reachables(B,initial(A)),minimize=false)
end

function Base.one(A::CBuchiAutomaton) #! optimize!
    A*inv(A)
end

function allwords(A::CBuchiAutomaton{Ti,Ta},n::Integer,root=initial(A)) where {Ti,Ta}
    if n==0
        return [Ta[]]
    end
    result = Vector{Ta}[]
    for (a,s)=A[root], w=allwords(A,n-1,s)
        push!(result,[a,w...])
    end
    result
end

function projection(A::CBuchiAutomaton{Ti,Ta},i) where {Ti,Ta <: Tuple}
    Tb = Ta.parameters[i]
    CBuchiAutomaton{Ti,Tb}(s=>a[i]=>t for (s,(a,t))=A[])
end
projection(i::Integer) = A->projection(A,i)

# more general projections
