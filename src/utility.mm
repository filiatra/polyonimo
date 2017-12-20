##########################################################################
##########################################################################
##                                                                      ##
##  polyonimo:-utility                                                  ##
##                                                                      ##
##  This Source Code Form is subject to the terms of the Mozilla Public ##
##  License, v. 2.0. If a copy of the MPL was not distributed with this ##
##  file, You can obtain one at http://mozilla.org/MPL/2.0/.            ##
##                                                                      ##
##  Author: Angelos Mantzaflaris, 2017                                  ##
##                                                                      ##
##########################################################################
##########################################################################

utility := module()
    
description "Polyonimo utility Module";
    
option package;
    
export
num_comb,
first_comb,
next_comb,
comb_place,
num_perm,
first_perm,
next_perm,
perm_sign,
multichoose,
first_mon,
next_mon,
num_mon,
first_point,
num_points,
next_point,
first_binary,
next_binary,
allQsums;

local 
mac_dim,
ifirst_point,
inext_point,
mfirst_mon,
mnext_mon,
mnum_mon
;

#
# Next r-combination of [1..n] after c in lex-order
# nops(c)=r
#
next_comb := proc( c::Or(list,Vector), n::integer)
	  local nc,r,i,j;

	  nc:=c;
	  r:= nops(c);
	  if c=[seq(n-r+1..n)] then return NULL; fi; #finished

	  i:=r;
	  while c[i]=n-r+i do
	  	i:=i-1;
	  od;

	  nc[i]:=c[i]+1;
	  for j from i+1 to r do
	     nc[j]:= nc[i]+j-i;
	  od;
nc;
end:

#
# Lex-first r-combination of [1..n]
#
first_comb:= proc(n::integer,r::integer)
if r<=n then
   return [seq(1..r)];
else
   print(`Warning: r>n combination requested`,r,n);
   return NULL;
fi;
end:

#
# Number of r-combination of [1..n]
#
num_comb:=proc(n::integer,r::integer)
binomial(n,r);
end:

comb_place := proc( c::Or(list,Vector,set) )
local i, s := 1;
    for i to nops(c) do
        s := s + binomial(c[i],i);
    od:
return s;
end:

#################################################################

#
# Next permutation of [1..n] after c in lex-order
# nops(c)=n
#
next_perm := proc( c::Or(list,Vector))
local t, n, nc,k,j;
    n:=nops(c);
    if c=[seq(n-k, k=0..n-1)] then return NULL; fi; #finished
    nc:=c;

    j:=n-1;
    k:=n;
    while nc[j]>nc[j+1] do
        j:=j-1;
    od; # j is the largest index with c[j]<c[j+1]
    while nc[j]>nc[k] do
        k:=k-1;
    od; # c[k] is the smallest element>c[j] with k>c[j]
    #interchange c[j] and c[k]
    t:=nc[k]; nc[k]:=nc[j]; nc[j]:=t;

    # Update lex-order
    k:=n;
    j:=j+1;
    while k>j do
        #interchange c[j] and c[k]
        t:=nc[j]; nc[j]:=nc[k]; nc[k]:=t;
        k:=k-1;
        j:=j+1;
    od; # all elements after jth position in increasing order
nc;
end:

#
# Lex-first permutation of [1..n]
#
first_perm:= proc(n::integer)
   return [seq(1..n)];
end:

#
# Returns the sign (parity) of the permutation
#
perm_sign := proc(c::list)
local s:=1, i, j, n:=nops(c);
    #if nops(convert(c,set))=n then
    for i to n-1 do
        for j from i+1 to n do
            if c[i]>c[j] then s:=-s; fi;
        od;
    od;
    #else print(`Invalid input`); fi;
    s;
end:


#
# Number of r-combination of [1..n]
#
num_perm:=proc(n::integer)
factorial(n);
end:

#################################################################

# Macaulay's matrix dimension for s eq in n vars in depth dp
mac_dim:= proc(s::integer,n::integer,dp::integer )
    s*binomial(dp-1+n,dp-1), binomial(dp+n,dp);
end:

#################################################################

# All k-tuples of element-sum n
multichoose := (n,d) -> map2(map, `-`, combinat[composition](d+n,n), 1):

#
# Lex-last degree r monomial in n variables
#
first_mon:= proc(r::integer,n::integer)
    return [seq(0,k=1..n-1),r];
end:

#
# Lex-bigger next degree r monomial in n variables after c
#
next_mon := proc( c::Or(list,Vector), r::integer)
local nc,n,i;

    n:= nops(c);
    if c[1]=r then return NULL; fi; #finished
    nc:=c;

    i:=n;
    while c[i]=0 do
        i:=i-1;
    od;

    nc[i-1]:=nc[i-1]+1;
    #complete first non-zero element from the right with nc[i]-1
    if i=n then
        nc[i]:=nc[i]-1;
    else
        nc[n]:=nc[i]-1;
        nc[i]:=0;
    fi;
    nc;
end:

#
# Number of monomails of deg=r in n variables
#
num_mon:=proc(r::integer, n::integer)
binomial(n+r-1,n-1);
end:

#################################################################

#
# Lex-first degree r monomial in n variables
#
mfirst_mon:= proc(r::integer,n::integer)
    return [r,seq(0,k=1..n-1)];
end:

#
# Lex-smaller next degree r monomial in n variables after c
#
mnext_mon := proc( c::Or(list,Vector), r::integer)
local nc,n,i,j;

    n:= nops(c);
    if c[n]=r then return NULL; fi; #finished
    nc:=c;

    i:=1;
    while c[i]=0 do
        i:=i+1;
    od;

    nc[i+1]:=nc[i+1]+1;
    #complete first non-zero element from the right with nc[i]-1
    if i=1 then
        nc[i]:=nc[i]-1;
    else
        nc[1]:=nc[i]-1;
        nc[i]:=0;
    fi;
    nc;
end:

#################################################################

#
# First lattice point in the box [low,upp]
#
first_point:= proc(low::Or(list,Vector),upp::Or(list,Vector))
option inline;
    copy(low);
end:

#
# Number of lattice points in the box [low,upp]
#
num_points:= proc(low::Or(list,Vector),upp::Or(list,Vector))
option inline;
    mul(upp[k]-low[k]+1, k=1..LinearAlgebra:-Dimension(low));
end:

#
# Next lattice point in [low,upp] after p
# equiv: lex-next point in the cartesian product [low[1],upp[1]]x..x[low[n],upp[n]]
#
next_point:=proc(p::Or(list,Vector),low::Or(list,Vector),upp::Or(list,Vector))
local np, i, n;

    # = on vectors bug Maple 13
    if LinearAlgebra:-Equal(p,upp) then return false; fi; #finished
#    np:= copy(p);#bug Maple 13: p passed by reference, terminating value..
    n := LinearAlgebra:-Dimension(p);#nops(p);

    i:=n;
    while p[i]=upp[i] do i:=i-1; od;
    p[i]:= p[i]+1;

    i:=i+1;
    while i<=n do p[i]:=low[i]; i:=i+1; od;
#np;
return true;
end:

#################################################################

#
# First lattice point in the box [low,upp]
#
ifirst_point:= proc(low::Or(list,Vector),upp::Or(list,Vector))
    return low;
end:

#
# Next lattice point in [low,upp] after p
# equiv: lex-next point in the cartesian product [low[1],upp[1]]x..x[low[n],upp[n]]
#
inext_point:=proc(p::Or(list,Vector),low::Or(list,Vector),upp::Or(list,Vector))
local np, i, n;

    if p=upp then return NULL; fi; #finished
    np:=p;
    n :=nops(p);

    i:=1;
    while p[i]=upp[i] do
        i:=i+1;
    od;
    np[i]:=np[i]+1;

    i:=i-1;
    while i>=1 do
        np[i]:=low[i];
        i:=i-1;
    od;
np;
end:

#################################################################

#
# First binary string of lennth n
#
first_binary:= proc(n::integer)
    return [seq(0,i=1..n)];
end:

#
# Lex-next binary string of lennth n after s
#
#(to be done)
next_binary:= proc(s::Or(list,Vector))
    local n;
    n :=nops(s);
    if s=[seq(1,i=1..n)] then return NULL; fi; #finished

    return [seq(0,i=1..n)];
end:

### all q-sums by dynamic programming
    allQsums := proc(nis::Vector)
    local n, grps, i, q, Subs, ss, summs;
        grps:=LinearAlgebra:-Dimension(nis): unassign('i');
        unassign('n');
        n:=ColumnDimension(dis)-1;
        summs := Array(0..n):
        for i from 0 to n do
            summs[i]:={}
        od:
        unassign('i');
        Subs := subsets({seq(i,i=1..grps)}):
        while not Subs[finished] do
            ss:=Subs[nextvalue]();
            q := 0:
            for i in ss do q := q + nis[i] od;
            summs[q] := summs[q] union {ss};
        od:
        eval(summs);
    end:

end: #utility
