#####################################################################################

function lift_poly_monomials(R::FmpqMPolyRing, B::fmpq, L::Array{Int,1})
    # return a polynomial which is the sum of monomial(s) represented by
    #  B w.r.t. L where L[i] -> var(i) and L is list of primes
    nr = length(L)
    Y = gens(R)
    if length(Y) < nr
       return print("Wrong number of Variables have been Used!")
    end
    Rx, X = PolynomialRing(ZZ, [" "*string(i) for i in Y])
    f = R(1)
    Bx = ZZ(B)
    for k in 1:nr
        i =  valuation(Bx,L[k])
        Bx =  div(Bx, fmpz(L[k])^i)
        f = f*Y[k]^i
    end
    return f
end

function p_adic_valuation(B::fmpz, p::Int)
    j = -1
    H = ZZ(1)
    while true
        j = j+1
        H = H*p
        if mod(B, H)!=0
            return j, div(B, div(H, p))
        end
    end
end
#####################################################################################

function poly_root(f::fmpq_poly)
    # return  roots of linearly factorizable polynomal f
    d = factor(f)
    L = [i[1] for i in d]
    N = [i[2] for i in d]
    K = fmpq[]
    for i in 1:length(L)
       if N[i] != 1 || degree(L[i]) > 1
          return [] #A Given Poly Is Not Yet Linearly factorized or is not squarefree
       end
    end
    for i=1:length(L)
        push!(K, -1*coeff(L[i], 0))
    end
    return K
end
#####################################################################################

function transposed_vandermondeMatrix(list_root::Array{fmpq, 1}, list_prime::Array{Int, 1})
     # return a transposed Vandermonde matrix
    S = parent(list_root[1])
    nr = length(list_root)
    M = MatrixSpace(S, nr, nr)(S(0))
    N = fmpq[]
    for j in 1:nr
       for i in 1:nr
           push!(N, list_root[j]^(i-1)) # prime power starts with 0
       end
    end
    for j in 1:nr
       for i in 1:nr
           M[i, j] = N[nr*(j-1)+i]
       end
    end
    return M
end

#####################################################################################
#                  Sparse Multivariate Interpolation                                #
#####################################################################################

function sparseMultiPolyInterpolation(R::FmpqMPolyRing, Br::fmpq_poly, La::Array{fmpq,1}, lpr::Array{Int64, 1}, Vr::Array{fmpq_mpoly,1})
    # Br the minimal polynomial of the sequence La
    S = parent(La[1])
    # compute the roots of f using factorization algorithm
    Lr = poly_root(Br)
    if length(Lr) == 0
       return 0 # Br is not factorizable or linearly fact.
    end
    # F1 is a List of Monomials
    F1 = fmpq_mpoly[]
    for j in 1:length(Lr)
       push!(F1, lift_poly_monomials(R, Lr[j], lpr))
    end
    # F2 is the transposed Vandermonde Matrix
    F2 = transposed_vandermondeMatrix(Lr, lpr)
    #  compute the coefficients of the monomials in F1
    nr = nrows(F2)
    T = MatrixSpace(S, nr, 1)
    T = matrix(La[1:nr])
    V = inv(F2) # compute inverse of the matrix F2
    Z = V*T # determine the coefficient ci
    g = R(0)
    for j in 1:nrows(Z)
        g = g + F1[j]*Z[j,1]
    end
    return g
end

################################################################################
#         Berlekamp Massey Algorithm                                           #
################################################################################

function BerlekampMassey(R::FmpqMPolyRing, L::Array{fmpq,1}, M)
    # M is an option parameter 
    R_s = parent(L[1])
    L = [R_s(L[i]) for i in 1:length(L)]
    Vr = gens(R)
    lv = [Vr[length(Vr)]]
    Ry, ZY = PolynomialRing(R_s, "ZY")
    h = Ry(0)
    De = R_s(1)
    n = length(L)
    sp = 0 # int
    if length(M) == 0
       g0 = Ry(1) # poly
       g1 = Ry(1)
       B0 = Ry(0)
       l0 = 0
       s = 0
       D1 = R_s(0) # rational number
    else
       sp = M[5]
       g0 = M[1]
       B0 = M[2]
       l0 = M[3]
       De = M[4]
       LL = M[6]
       for i in 1:length(L)
          push!(LL, L[i])
       end
       L = LL
    end
    for j in (sp+1): (n+sp)
       s = degree(g0)
       la = []
       for i in 0:s
           push!(la,coeff(g0,s-i))
       end
       d = R_s(0)
       for k in 0:s
           d = d + la[k+1]*L[j-s+k]
       end
       D1 = d
       if D1 == 0
           if 2*l0 < j && j>1
               s = degree(g0)
               for i in 0:s
                   h = Ry([coeff(g0,s-i) for i in 0:s])
               end
               return  (j-1, h)
           end
           g1 = g0
           B0 = ZY*B0
       else
           if(D1 != 0 && (2*l0) < j)
               g1 = g0 - (D1*ZY*B0)*De^-1
               B0 = g0
               l0 = j-l0
               De = D1
           else
               if (D1 != 0 && (2*l0) >= j)
                   g1 = g0 - (D1*ZY*B0)*De^-1
                   B0 = ZY*B0
               end
           end
       end
       g0 = g1
    end
    return (g0,B0,l0,De,n+sp,L)
end

################################################################################

function test_the_shift(g::fmpq_mpoly)
    R = g.parent # current ring
    n = length(gens(R)) # number of variables
    sh = shifting_point(n)
    J = evaluate(g,sh)
    i = 0
    while J == 0 
        i++
        sh = shifting_point(n)
        J = evaluate(g,sh)
    end
    return(sh)
end

################################################################################

function shifting_point(pa::Int)
    # choose a shift w.r.t pa (the number of parameters)
    h = Int[]
    push!(h, rand(ZZ,1:20)) # random integer between 1 and 20
    for i in 2:pa
        push!(h, rand(ZZ, h[i-1]+2:h[i-1]+7))
    end
    return h
end

################################################################################

function list_of_primes(pa::Int, M)
    # find distinct pa prime(s) up to permutations
    p = Int(3)
    L = Int[]; l = Int[]; l1 = Int[]
    if length(M) > 0
        p = M[1]
    end
    for j in 1:pa
        push!(L, p)
        p = next_prime(p)
    end
    l1 = L
    for j in 1:length(L)
        k = 1+rand(UInt)%length(l1)
        push!(l, l1[k])
        l1 = deleteat!(l1,k)
    end
    return l
end

################################################################################

function shift_variables(f::fmpq_mpoly, shft::Array{Int, 1})
    R = f.parent
    L = gens(R)
    for j in 1:length(shft)
       L[j] = L[j] + shft[j]
    end
    f = evaluate(f, L)
    return f
end

################################################################################

function return_coef_indx_wrtk(L::Array{fmpq_mpoly, 1}, k::Int)
    l = fmpq[]
    for j in 1:length(L)
        push!(l, coeff(L[j], k))
    end
    return l
end

################################################################################

function SubList(L::Array{Array{fmpq,1},1})
    if length(L[2]) == 0
        return L[1]
    else
        return L[1]-L[2]
    end
end

################################################################################

function MultiRationalInterpolation(f::fmpq_mpoly, g::fmpq_mpoly)
    # g must denominator polynomial and assume gcd(f, g) = 1
    R = f.parent
    Vr = gens(R)
    n = length(Vr)
    ln = length(f)
    if ln < length(g)
       ln = length(g)
    end
    shft = test_the_shift(g)
    println("shft $shft")
    #shft = [16, 19, 25, 27, 30, 35, 42, 49, 55, 58]
    nP = list_of_primes(n, [])
    #nP = [11, 17, 7, 3, 13, 29, 31, 23, 19, 5]
    println("nP $nP")
    F = shift_variables(f,shft)
    G = shift_variables(g,shft)
    c = coeff(G, length(G))
    F = F//c
    G = G//c
    Ra, V = PolynomialRing(QQ, ["Y"*string(i) for i in 1:length(Vr)+1])
    vr = gens(Ra)
    vR = [vr[i]*vr[length(vr)] for i in 1:length(vr)-1]
    F = evaluate(F, vR)
    G = evaluate(G, vR)
    L = []; LD = fmpq_mpoly[]; LN = fmpq_mpoly[]
    iN = 0; nf = ln
    for j in iN: nf
        L = [V[1]^0*i^j for i in nP]
        push!(L, V[length(V)])
        push!(LN, evaluate(F, L))
        push!(LD, evaluate(G, L))
    end
    #return LN, LD, F, G, Ra
    F1 = _inner_lift_poly(Ra, F, LN, shft, nP, iN, nf)
    F2 = _inner_lift_poly(Ra, G, LD, shft, nP, iN, nf)
    F1 = evaluate(change_base_ring(c*F1, a->R(a)), gens(R))
    F2 = evaluate(change_base_ring(c*F2, a->R(a)), gens(R))
    return F1, F2
end

################################################################################

function _inner_lift_poly(Rp::FmpqMPolyRing, F::fmpq_mpoly, _FN::Array{fmpq_mpoly,1}, shft::Array{Int,1}, nP::Array{Int,1}, iN::Int, nf::Int)
    FN = deepcopy(_FN)
    rV = gens(Rp)
    lk1 = fmpq[];l3 = fmpq[]; l3n = fmpq[];lp = fmpq[]
    lup = fmpq_mpoly[]; lk3 = fmpq_mpoly[]
    pn = Rp(0); pl = Rp(0); plm = Rp(0)
    for i in 1:length(FN[1])
       l3 = return_coef_indx_wrtk(FN, i)
       l3 = [l3, lk1]
       lk1 = fmpq[]
       l3 = SubList(l3)
       bp = BerlekampMassey(Rp, l3, [])
       if length(bp) == 2
          if bp[1] == 1
             lup = [lk3,fmpq_mpoly[]] # if l3 = 0, ..., 0
          else
             l3 = l3[1:bp[1]]
             pn = sparseMultiPolyInterpolation(Rp, bp[2],l3,nP, rV)
             pl = pn+pl
             lup = evaluate_f_at_given_points(pn, shft)
             lup = [lup,lk3]
          end
       else
          l3n = bp[6]
          while true
             iN = nf+1
             nf = 2*iN
             LN = fmpq_mpoly[]
             for j in iN: nf
                 L = [rV[1]^0*i^j for i in nP]
                 push!(L, rV[length(rV)])
                 push!(LN, evaluate(F, L))
             end
             l3 = return_coef_indx_wrtk(LN, i)
             append!(FN, LN)
             if i > 1
                for j in iN:nf
                   L = [fmpq(i)^j for i in nP]
                   push!(L, fmpq(1)) # we have one more variable
                   push!(lk1, evaluate(plm, L))
                end
                l3 = [l3,lk1]
                lk1 = fmpq[]
                l3 = SubList(l3)
             end
             lp = bp
             l3n = append!(l3n, l3)
             bp = BerlekampMassey(Rp, l3,lp)
             if length(bp) == 2
                 # at this step BerlekampMassey algorithm terminated early
                 l3n = l3n[1:bp[1]]
                 pn = sparseMultiPolyInterpolation(Rp, bp[2],l3n,nP, rV)
                 pl = pn+pl
                 lup = evaluate_f_at_given_points(pn,shft)
                 lup = [lup,lk3]  
                 break
             end
          end
       end
       if i < length(FN[1])
          # unshift the shifted parameters see also SubList
          lk3 = Add_poly_list(lup)
          plm = lk3[1]
          L = fmpq[]
          for j in 0:nf
               L = [fmpq(k)^j for k in nP]
               push!(L, fmpq(1)) # we have one more variable
               push!(lk1, evaluate(plm, L))
          end
          lk3 = deleteat!(lk3,1)
       end
    end
    return pl
end

################################################################################
function IsallElemZero(l::Array)
     for i in 1:length(l)
         if l[i] > 0
            return 0
         end
     end
     return 1
end

################################################################################

function  Add_poly_list(lup::Array{Array{fmpq_mpoly, 1}, 1})
    # return a list of the sum of two polynomials in the list lup
    #println("lup $length(lup[1])")
    if length(lup[2]) == 0
        return lup[1]
    else
        return lup[1] + lup[2]
    end
end

################################################################################

function _inner_mpoly_to_univar(f::fmpq_mpoly, int_v::Int)
     # write a given multivariate polynomial f as univariate g w.r.t the
     # variable gen(parent(f), int_v) and return the coefficients of tail(g) 
     L = terms(f)
     list_coeffs = fmpq_mpoly[] # expect all of them are non-zero
     R = f.parent
     c = Int(0)
     d = Int(0)
     g = R(0)
     v = gen(R, int_v)
     for t in L
        d = degree(t, int_v)
        if c < d
           c = d
        end
     end
     for j in c-1:-1:0
        for t in L
            if degree(t,int_v) == j
                g = g + divexact(t, v^j)
            end
        end
        push!(list_coeffs, g)
        g = R(0)
     end
     return list_coeffs
end

function mpoly_to_univar(f::fmpq_mpoly, int_v::Int, only_non_zero::Bool)
     R = parent(f)
     L = terms(f)
     list_coeffs = fmpq_mpoly[]
     list_exps = Int[]
     v = gen(R, int_v)
     for t in L
       d = degree(t, int_v)
       i = findfirst(x -> x == d, list_exps)
       if i == nothing
         push!(list_exps, d)
         push!(list_coeffs, divexact(t, v^d))
       else
         list_coeffs[i] += divexact(t, v^d)
       end 
     end
     return list_coeffs, list_exps
end

function fmpq_mpoly_to_univar(f::fmpq_mpoly, int_v::Int, only_non_zero::Bool)
     # write a given multivariate polynomial f as univariate g w.r.t the 
     # variable gen(parent(f), int_v) and return the coefficients of g and corr_g degrees
     # if only_non_zero=false, return all coeffs of g if not, returns non-zero coeffs only 
     R = parent(f)
     L = terms(f)
     D = Dict{Int, fmpq_mpoly}()
     v = gen(R, int_v)
     for t in L
       d = degree(t, int_v)
       if haskey(D, d)
         D[d] += divexact(t, v^d)
       else
         D[d] = divexact(t, v^d)
       end
     end
     if !only_non_zero
       for i = 0:degree(f, int_v)
         if !haskey(D, i)
           D[i] = zero(R)
         end
       end
     end
     return D
end
################################################################################

function  evaluate_f_at_given_points(f::fmpq_mpoly, shft::Array{Int,1})
    # if x1, ..., xn are variables of the base ring, this procedure does
    # the following: evaluate f at (x1*xn+shft[1], ..., x(n-1)*xn+shft[n-1], 1)
    # then return poly_monom_withmaxdeg(evaluated polynomial)
    R = parent(f)
    if f == 0
        return fmpq_mpoly[] #
    else
      a_int = Int(0)
      for i in 1:length(shft)+1
          if degree(f, i) != 0
             a_int = a_int + 1
          end
      end
      if a_int == 0
         return [f] # constant polynomial nothing to shift
      end
    end
    Vr_variable = gens(R)
    f = shift_variables(f, shft)
    KL = [Vr_variable[i]*Vr_variable[length(Vr_variable)] for i in 1:length(Vr_variable)-1]
    push!(KL, R(1))
    f1 = evaluate(f, KL)
    f2 = poly_monom_withmaxdeg(f1)
    return f2
end
