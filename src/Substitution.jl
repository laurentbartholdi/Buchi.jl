using DataStructures
using Buchi

struct Substitution{T}
	graph::Dict{T,Vector{T}}
end

Substitution(pairs::Pair{Char,String}...) = Substitution{Char}(Dict(s=>[a for a=v] for (s,v)=pairs))

# Read a character with our substitution
(s::Substitution{T})(a::T) where T = s.graph[a]

# Read a string with our substitution
(s::Substitution{Char})(w::String) = join(join(s(c)) for c in w)

# Definition for vectors
(s::Substitution{T})(w::Vector{T}) where T = vcat((s(a) for a=w)...)

function lang(s::Substitution, n::Int)
	l = Set()
	todo = Deque{Vector{Char}}()
	for a in keys(s.graph)
		w = [a]
		while length(w) < n
			w = s(w)
		end
		for i in 1:length(w)-n+1
			push!(l,w[i:i+n-1])
			push!(todo,w[i:i+n-1])
		end
		while !isempty(todo)
			w = s(pop!(todo))
			for i in 1:length(w)-n+1
				if !in!(w[i:i+n-1],l)
					push!(todo,w[i:i+n-1])
				end
			end
		end
	end
	return l
end

function raut(s::Substitution)
	l = sort(collect(lang(s,4)))
	sl = [[] for w in l]
	ind = [Set{Int}() for w in l]
	for i in 1:length(l)
		w=l[i]
		v=s(w)
		k1=length(s(w[1]))
		k2=length(s(w[2]))
		for j in k1:(k1+k2-1)
			append!(sl[i],[(v[j:j+3],j-k1+1)])
			push!(ind[findfirst(x->x==v[j:j+3],l)],j-k1+1)
		end
	end
#	@info sl
	k=1
	statename = Dict{Tuple{Vector{Char},Int},Int}()
	namestate = Dict{Int,Tuple{Vector{Char},Int}}()
	indv=[]
	for i in 1:length(ind)
		append!(indv,[sort(collect(ind[i]))])
		for j in indv[i]
			statename[(l[i],j)]=k
			namestate[k]=(l[i],j)
			k+=1
		end
	end
#	@info indv,statename,namestate
	n=k-1
	edges = []
	k=1
	for i in 1:length(l)
		for j in indv[i]
			for w in sl[i]
				if w==sl[i][end]
					append!(edges,[n+statename[w]=>((join(w[1][1:3]),w[2]),(join(w[1][2:4]),1))=>n+k])
				else
					append!(edges,[n+statename[w]=>((join(w[1][1:3]),w[2]),(join(w[1][2:4]),w[2]+1))=>k])
				end
				append!(edges,[statename[w]=>((join(w[1][1:3]),w[2]),(join(w[1][1:3]),w[2]))=>k])
			end
			k+=1
		end
	end
	return edges
end

function red(vertices::Int,ed::Vector{Pair{Int,Int}})
	edges = ed
	todo = [i for i=1:vertices]
	dead = Set{Int}()
	while !isempty(todo)
		v = pop!(todo)
#		@info "Checking "*string(v)*": "
#		@info isempty(filter(x->x[1]==v,edges))
		if isempty(filter(x->x[1]==v,edges))
			push!(dead,v)
#			@info string(v)*" is dead!"
			for e in filter(x->x[2]==v,edges)
				push!(todo,e[1])
			end
			filter!(x->x[2]!=v,edges)
		end
	end
	active = []
	for i in 1:vertices
		if !(i in dead) append!(active,i) end
	end
	return active
end

function aut(s::Substitution)
	sigma=keys(s.graph)
	n=length(sigma)
	m = maximum([length(s(a)) for a in sigma])
	l = []
	sl=[[] for i in 1:(n^4)]
    k=0
	for a in sigma for b in sigma for c in sigma for d in sigma
		k+=1
        w=[a,b,c,d]
        append!(l,[w])
		v=s(w)
		k1=length(s(w[1]))
		k2=length(s(w[2]))
		sl[k] = [(v[j:j+3],j-k1+1) for j in k1:(k1+k2-1)]
        end end end end
	statename = Dict{Tuple{Vector{Char},Int},Int}()
#	namestate = Dict{Int,Tuple{Vector{Char},Int}}()
	for i in 1:(n^4)
		for j in 1:m
			statename[(l[i],j)]=((i-1)*m + j)
#			namestate[(i-1)*m + j]=(l[i],j)
		end
	end
	edges=[]
	for i in 1:(n^4)
		for w in sl[i]
			if w==sl[i][end]
				append!(edges,[(m*n^4+statename[w])=>((join(w[1][1:3]),w[2]),(join(w[1][2:4]),1))=>(m*n^4+(i-1)*m+j) for j in 1:m])
			else
				append!(edges,[(m*n^4+statename[w])=>((join(w[1][1:3]),w[2]),(join(w[1][2:4]),w[2]+1))=>((i-1)*m +j) for j in 1:m])
			end
			append!(edges,[statename[w]=>((join(w[1][1:3]),w[2]),(join(w[1][1:3]),w[2]))=>((i-1)*m+j) for j in 1:m])
		end
	end
	active = red(2*m*n^4,[e[1]=>e[2][2] for e in edges])
	actives = Set(active)
	filter!(e->((e[1] in actives)&&(e[2][2] in actives)),edges)
	oldtoact = Dict([active[i]=>i for i in 1:length(active)])
	edges = [oldtoact[e[1]]=>e[2][1]=>oldtoact[e[2][2]] for e in edges]
#	statename = Dict([namestate[active[i]]=>i for i in 1:div(length(active),2)])
#	namestate = Dict([i=>namestate[active[i]] for i in 1:div(length(active),2)])
	return edges
end

s = Substitution('a'=>"ab",'b'=>"a")

println(aut(s))
println(raut(s))
tau = CBuchiAutomaton{Int,Tuple{Tuple{String,Int},Tuple{String,Int}}}(raut(s),minimize=false)


