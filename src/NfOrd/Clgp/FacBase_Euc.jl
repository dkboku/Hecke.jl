################################################################################
#
#  Factor base over (Euclidean) Rings
#
################################################################################

# Note that T must admit gcd's and base must consist of elements x for which
# valuation(_, x) is definied.
# works (at least) for fmpz and nmod_poly, so it can be used for the
# smoothness test

function compose(a::node{T}, b::node{T}, check = false) where T
  if check && !isone(gcd(a.content, b.content))
    error("input not coprime")
  end
  return node{T}(a.content * b.content, a, b)
end

# assume that the set or array consists of pairwise coprime elements
function FactorBase(x::Union{Set{T}, AbstractArray{T, 1}}; check::Bool = true) where T
  if length(x)==0
    z = FactorBase{T}(T(1), x)
    return z
  end
  ax = [ node{T}(p) for p in x]
  while length(ax) > 1
    bx = [ compose(ax[2*i-1], ax[2*i], check) for i=1:div(length(ax), 2)]
    if isodd(length(ax))
      push!(bx, ax[end])
    end
    ax = bx
  end
  z = FactorBase{T}(ax[1].content, x)
  z.ptree = ax[1]
  return z
end

function show(io::IO, B::FactorBase{T}) where T
  print(io, "Factor base with \n$(B.base) and type $T")
end

function issmooth(c::FactorBase{T}, a::T) where T
  @assert a != 0
  g = gcd(c.prod, a)
  while g != 1 
    a = div(a, g)
    g = gcd(g, a)
  end
  return a == 1 || a==-1
end

function issmooth!(c::FactorBase{fmpz}, a::fmpz)
  @assert a != 0
  g = gcd(c.prod, a)
  if g==1
    return a==1 || a==-1, a
  end
  b = copy(a)
  while g != 1 
    divexact!(b, b, g)
    gcd!(g, g, b)
  end
  return b == 1 || b==-1, b
end


function isleaf(a::node{T}) where T
  return !(isdefined(a, :left) || isdefined(a, :right))
end

function _split(c::node{T}, a::T) where T
  if isleaf(c)
    return [gcd(a, c.content)]
  end
  if isdefined(c, :left)
    l = gcd(a, c.left.content)
    if l != 1
      ls = _split(c.left, l)
    else
      ls = Array{T, 1}()
    end
  else
    ls = Array{T, 1}()
  end
  if isdefined(c, :right)
    r = gcd(a, c.right.content)
    if r != 1 
      rs = _split(c.right, r)
    else
      rs = Array{T, 1}()
    end
  else
    rs = Array{T, 1}()
  end
  return vcat(ls, rs)
end

function factor(c::FactorBase{T}, a::T) where T
  @assert a != 0
  f = Dict{T, Int}()
  lp = _split(c.ptree, a)
  for i in lp
    if mod(a, i)==0  ## combine: use divmod and do val of rest
                     ## to save a division
      v = remove(a, i)
      f[i] = v[1]
      a = v[2]
      if a == 1 || a==-1  ## should be isunit (think poly)
        break
      end
    end
  end
  assert(a==1 || a==-1)
  return f
end

function factor(c::FactorBase{T}, a::fmpq) where T  ## fractions over T
  @assert a != 0
  f = Dict{T, Int}()
  n = abs(num(a))
  d = den(a)
  lp = _split(c.ptree, n*d)
  for i in lp
    if mod(d, i)==0
      v = remove(d, i)
      if isdefined(f, :i)
        f[i] -= v[1]
      else
        f[i] = -v[1]
      end
      d = v[2]
      if d == 1 && n == 1
        break
      end
    end
    if mod(n, i)==0
      v = remove(n, i)
      if isdefined(f, :i)
        f[i] += v[1]
      else
        f[i] = v[1]
      end
      n = v[2]
      if d == 1 && n==1
        break
      end
    end
  end
  @hassert :ClassGroup 1 d == 1 && n == 1 
  return f
end
