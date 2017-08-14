```@meta
CurrentModule = Hecke
```

## Creation

```@docs
Order(::AnticNumberField, ::Array{nf_elem, 1})
Order(::AnticNumberField, ::FakeFmpqMat)
EquationOrder(::AnticNumberField)
```

### Example

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(QQ, "x");
K, a = NumberField(x^2 - 2, "a");
O = EquationOrder(K)
```

## Basic properties

```@docs
signature(::NfOrd)
nf(::NfOrd)
```

```@docs
maximal_order(::AnticNumberField)
maximal_order(::AnticNumberField, ::Array{fmpz, 1})
make_maximal(::NfOrd)
```

```@repl
using Hecke; # hide
Qx, x = PolynomialRing(QQ, "x");
K, a = NumberField(x^2 - 2, "a");
R = EquationOrder(K)
T = maximal_order(R)
```

## Elements

### Creation

```@docs
call(::NfOrd, ::nf_elem)
call(::NfOrd, ::fmpz)
call(::NfOrd, ::Array{fmpz, 1})
call(::NfOrd, ::Array{Int, 1})
call(::NfOrd)
```

### Basic properties

```@docs
parent(::NfOrdElem)
elem_in_nf(::NfOrdElem)
elem_in_basis(::NfOrdElem)
discriminant(::Array{NfOrdElem, 1})
==(::NfOrdElem, ::NfOrdElem)
zero(::NfOrd)
one(::NfOrd)
iszero(::NfOrdElem)
isone(::NfOrdElem)
```

### Arithmetic

```@docs
-(::NfOrdElem)
+(::NfOrdElem, ::NfOrdElem)
-(::NfOrdElem, ::NfOrdElem)
*(::NfOrdElem, ::NfOrdElem)
^(::NfOrdElem, ::Int)
mod(::NfOrdElem, ::Int)
powermod(::NfOrdElem, ::fmpz, ::Int)
```

### Miscallenous

```@docs
representation_mat(::NfOrdElem)
representation_mat(::NfOrdElem, ::AnticNumberField)
trace(::NfOrdElem)
norm(::NfOrdElem)
rand(::NfOrd, ::Int)
minkowski_map(::NfOrdElem, ::Int)
conjugates_arb(::NfOrdElem, ::Int)
conjugates_arb_log(::NfOrdElem, ::Int)
t2(::NfOrdElem, ::Int)
```

## Ideals

### Creation

```@docs
ideal(::NfOrd, ::Int)
ideal(::NfOrd, ::fmpz)
ideal(::NfOrd, ::fmpz_mat)
ideal(::NfOrd, ::NfOrdElem)
ring_of_multipliers(::NfOrdIdl)
*(::NfOrd, ::NfOrdElem)
```

### Arithmetic

```@docs
==(::NfOrdIdl, ::NfOrdIdl)
+(::NfOrdIdl, ::NfOrdIdl)
*(::NfOrdIdl, ::NfOrdIdl)
lcm(::NfOrdIdl, ::NfOrdIdl)
```

### Miscaellenous

```@docs
order(::NfOrdIdl)
basis(::NfOrdIdl)
basis_mat(::NfOrdIdl)
basis_mat_inv(::NfOrdIdl)
minimum(::NfOrdIdl)
norm(::NfOrdIdl)
in(::NfOrdElem, ::NfOrdIdl)
idempotents(::NfOrdIdl, ::NfOrdIdl)
mod(::NfOrdElem, ::NfOrdIdl)
pradical(::NfOrd, p::fmpz)
```

## Fractional ideals

### Creation

```@docs
frac_ideal(::NfOrd, ::fmpz_mat)
frac_ideal(::NfOrd, ::fmpz_mat, ::fmpz)
frac_ideal(::NfOrd, ::FakeFmpqMat)
frac_ideal(::NfOrd, ::NfOrdIdl)
frac_ideal(::NfOrd, ::NfOrdIdl, ::fmpz)
frac_ideal(::NfOrd, ::nf_elem)
frac_ideal(::NfOrd, ::NfOrdElem)
```

### Arithmetic
```@docs
==(::NfOrdFracIdl, ::NfOrdFracIdl)
```

### Miscaellenous

```@docs
order(::NfOrdFracIdl)
basis_mat(::NfOrdFracIdl)
basis_mat_inv(::NfOrdFracIdl)
basis(::NfOrdFracIdl)
norm(::NfOrdFracIdl)
```
