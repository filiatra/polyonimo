##########################################################################
##########################################################################
##                                                                      ##
##  polyonimo:-resultant                                                ##
##                                                                      ##
##  This Source Code Form is subject to the terms of the Mozilla Public ##
##  License, v. 2.0. If a copy of the MPL was not distributed with this ##
##  file, You can obtain one at http://mozilla.org/MPL/2.0/.            ##
##                                                                      ##
##  Author: Angelos Mantzaflaris, 2017                                  ##
##                                                                      ##
##########################################################################
##########################################################################

resultant := module()

description "Polyonimo resultants Module";

option package;

export
mDegree,
mBezout,
mBezoutUnmixed;

local 
detStats,
minrankSystem,
allsums,
solveMatrixKernel,
critVect,
macVect,
unmixedSylvVect,
biVarSylvVect,
bilinearSylvVect,
Sdim,
dimKv,
dimKvp,
computeCoHdim,
complexDim,
CoHzero,
MakeComplex,
MakeKv,
MakeKvp,
printBlocks,
printCohs,
printSpaces,
makeSysMatrix,
makeMatrix,
Sylvmat,
SylvmatIndex,
multmap,
coeffof,
allvars,
lstmonof,
monbasis,
Makepoly,
MakeExtremepoly,
Makesystem,
homogenizePoly,
is_determ,
next_lex_rect,
sort_dim,
dBounds,
allDetVecs,
Jdiscr,
BezoutianPoly,
Bezoutmat;

uses LinearAlgebra, combinat;

#statementSequence

#########################################################################
#########################################################################

### detStats
detStats := proc(dl::list)
local t, i, j, c, d, n := nops(dl);
c := NULL;
for i to n do
   d := dl[i][-1]:
   t := 1:
   for j from i+1 to n do
      if d=dl[j][-1] then
         t := t + 1;
         i := i + 1;
      else
         break;
      fi:
   od:
   c := c, [t,d];
od:
[c];
end:

### Minrank
minrankSystem := proc(N::integer, r::integer)
local l, deg, i, g;
    l:= Vector([(N-r)^2, seq(r,i=1..N-r)]):
    deg:= Matrix(N-r+1, 1 + (N-r)*N):
    
    for i to N-r+1 do
        deg[i, 1+(N-r)*N] := 1;
    od:

    for g from 1 to N-r do
        for i from 1 to N do
            deg[1  , (g-1)*N + i ] := 1;
            deg[g+1, (g-1)*N + i ] := 1;
        od:        
    od:
    l, deg;
end:
    
### all q-sums by dynamic programming
allsums := proc(nis::Vector)
	local n, grps, i, q, Subs, ss, summs;
    grps:=LinearAlgebra:-Dimension(nis): unassign('i');
	unassign('n');
    n:=convert(nis, `+`);
	summs := array(0..n):
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

#Multidegree with respect to vector nis
mDegree := proc(g, nis::Vector, var )
local deg, i, vars;
vars:=allvars(nis, var);

deg:=NULL;
for i to nops(var) do
    deg:=deg, degree(g, [seq( var[i][k], k=1..nis[i] )] );
od;
Vector([deg]);
end:

# Plain Sylv: solveMatrixKernel(M,v[2]);
#
# Note: values to reciprocals should be consider false
#
solveMatrixKernel := proc(M::Matrix, cols::list, dual:= false)
local V, c, ct, ksz, i, j, vals, psol, sols, l, dn, ind, vv, nvv, cnt, k;
    # Assume that the matrix is transposed
    if dual then
        V:= NullSpace(Transpose(M)):
    else
        V:= NullSpace(M):
    fi:

    ksz:= nops(V):
    print("Kernel has size", ksz);
    print("Kernel:", seq(convert(V[k],list),k=1..ksz) );
    
    sols:=NULL;
    for i to ksz do
        cnt:= 1;
        psol:=NULL;
        for c in cols do
            if dual then c := map( x->1/x, c): fi:
            ind := convert({1} union indets(c),list):
            nvv:= nops(ind):
            vv:= Vector(nvv):
            for j to nops(c) do
                for k to nops(ind) do
                    if c[j]=ind[k]   then vv[k]:=j; break: fi:
                    if c[j]=1/ind[k] then ind[k]:=1/ind[k];
                        vv[k]:=j;
                        break:
                    fi:
                od:
            od:
            if member(0,convert(vv,list),'_i_') then
                ERROR("Not found", ind[_i_]);
            fi:
            
            #print(ind,c,vv);
            #print(i);
            #print( nops(V[i]), nops(c));
            l := V[i][cnt..cnt+nops(c)-1];
            if l[vv[1]]<> 0 then
                l := l / l[vv[1]];
                vals:=NULL;
                #print(convert(c,list));
                #print(map(ifactor,convert(l,list)));
                #print(seq(ind[j] = l[vv[j]], j=2..nvv));
                psol:= psol, [seq(ind[j] = l[vv[j]], j=2..nvv)];
            fi:
            cnt := cnt + nops(c);
        od;
        sols:= sols, ListTools:-MakeUnique(ListTools:-Flatten([psol]));
    od:
    sols;
end:


#########################################################################
# Degree vectors of interest
#########################################################################

# Critical degree  vector
critVect:= proc(nis::Vector, dis::Matrix)
	local grps,n,r,s;
	grps := Dimension(nis);
	n:=convert(nis,`+`);
    s:=convert([seq(Column(dis,i),i=1..n+1)],`+`);
	r:= s - nis - Vector(grps,1);
	r;
end:

# Macaulay's matrix degree vector
macVect:= proc(nis::Vector, dis::Matrix)
	local grps,n,s;
	grps := Dimension(nis);
	n:=convert(nis,`+`);
    s:=convert([seq(Column(dis,i),i=1..n+1)],`+`);
	s - nis; #! differs by one from the critical degree..
end:

# degree vector for unmixed Sylvester matrix
# We use the identity permutation
unmixedSylvVect:= proc(nis::Vector, dis::Vector)
local grps, i, mis, s;
    grps := Dimension(nis);
    s:= 1:
    mis:=Vector(grps);
    for i to grps do
        s := s + nis[i];
        mis[i] := s * dis[i] - nis[i];
    od;
    mis;
end:


# degree vector for bivariate Koszul matrix
biVarSylvVect:= proc(nis::Vector, dis::Matrix, ind::integer:=1)
if ind=1 then
    RETURN(Vector([add(deg[1,i],i=1..n+1)-1, -1 ]) );
fi:
if ind=2 then
    RETURN(Vector([-1, add(deg[2,i],i=1..n+1)-1 ]) );
fi:
0;
end:

bilinearSylvVect:= proc( nis::vector, i::integer := 1)
local mis, n, d, s;
n:= nis[1]+nis[2]:
d:=vector([1,1]):
s:= vector([seq(1,k=0..n)]):

if i=1 then
  mis := vector([1,nis[1]+1]);
else if i=2 then
  mis := vector([nis[2]+1,1]);
else # i=3
  mis := vector([-1,nis[1]+1]);
fi:
fi:
mis;
end:

#########################################################################
# Dimensions
#########################################################################

# Bezout bound
mBezout:= proc(nis::Vector, dis::Matrix, j::integer := -1)
	local k, fct, grps,n, dd;
    
	n:=convert(nis,`+`);
	grps := Dimension(nis);
    if [grps,n+1] <> [Dimension(dis)] then ERROR(`BAD DIMS ! `) fi;
    
    fct:= 1;
    for k to grps do
        fct := fct * factorial(nis[k]);
    od:

    if grps=n then dd:=dis; else
    # Expand the degree matrix    
    dd:= Matrix(< seq(seq(dis[m,..],i=1..nis[m]),m=1..grps) >);
    fi:

    if j=-1 then# Total degree of resultant
        RETURN( convert([seq( Permanent(DeleteColumn(dd,i)),i=1..n+1)],`+`) /fct);
    else# Number of solutions of square system (ie. without f_j)
        RETURN( Permanent(DeleteColumn(dd,j)) /fct );
    fi:
end:

#Unmixed and Scaled Bezout bound
mBezoutUnmixed:= proc(nis::Vector, dis::Vector,
                      sis::Vector := Vector([seq(1,i=1..1+Dimension(nis))]) )
    description "Unmixed and Scaled Bezout bound";
	local grps,n;
	n:=convert(nis,`+`);
	grps := Dimension(nis);
	RETURN(	convert([seq(dis[i]^nis[i],i=1..grps)],`*`)*
   		convert(convert(sis,list),`*`)*
		convert([seq(1/sis[i], i=1..n+1)],`+`)*factorial(n)/
		convert([seq(factorial(nis[i]),i=1..grps)],`*`)	);
end:

### Dimension of space of m-homo polynomials of multidegree uis.
# The negative entries are assumed dualized.
# Beware that the negatives do not have the same meaning as in H(..)
# (Kunneth formula)
Sdim:= proc(nis::Vector,uis::Vector)
local k, grps, dim;
grps:= Dimension(nis); dim:=1;

for k to grps do
    if uis[k]>=0 then dim := dim * numbcomb( uis[k]+nis[k],nis[k]);
    else              dim := dim * numbcomb(-uis[k]+nis[k],nis[k]);
    fi;
od;
dim;
end:


### Dimension of Kv
dimKv:=proc(nis::Vector,dis::Matrix,mis::Vector,summs::array,Nu::integer)
 local n,grps, i,p, dimK;

 grps:=Dimension(nis):
# if grps <> Dimension(dis)[1] then ERROR(`BAD DIMS`) fi;
# if grps <> Dimension(mis) then ERROR(`BAD DIMS for m-vector`) fi;
    unassign('i');
    n:=convert(nis,`+`);
    dimK := 0;
    for p from max(0,Nu) to min(n+1,Nu+n) do
        dimK := dimK + dimKvp(nis,dis,mis,Nu,p);
    od:
    eval(dimK);
end:# dimKv

#### Dimension of Kvp
dimKvp:= proc(nis::Vector, dis::Matrix, mis::Vector, nu::integer,p::integer)
	local c,Kvp,n,grps,q,dim,k,v;
	grps:=Dimension(nis);
	n:=convert(nis, `+`); q:=p-nu;
    dim:=0;	for c in choose([seq(1..n+1)],p) do
                v := mis - convert([Vector(grps),seq(dis[..,i],i=c)],`+`);
                dim:=dim + computeCoHdim(nis, q, v );
            od;
	RETURN(dim);
end:# dimKvp

computeCoHdim := proc(nis::Vector,q::integer,mpd::Vector )
 local r, i, nonz, goodsum, dimH,dimHs, zerotest, summs;

    summs:=allsums(nis): ##ADD as argument to save time
    r:=Dimension(nis):
    dimH:=0;
    for nonz in summs[q] do  # sum_summs
  goodsum:=false;dimHs:=1;
        i:=0;
  while dimHs>0 and i<r do
    i:=i+1;  # prod
    if member(i,nonz) then # H^ni (mpd_i)
      if mpd[i] >= -nis[i] then #print(i,nonz,mpd[i],nis[i]);
        goodsum:=true; dimHs:=0;
        else dimHs := dimHs * numbcomb(-mpd[i]-1,nis[i]); fi;
    else if mpd[i] < 0 then #print(i,mpd[i]);
        goodsum:=true; dimHs := 0;
        else dimHs := dimHs * numbcomb(mpd[i]+nis[i],nis[i]); fi;
    fi;
  od:#while (i)
  if not goodsum then
     if dimHs=0 then ERROR(`BAD computation`) fi;
  fi;
  dimH := dimH + dimHs;
 od:
 eval(dimH);
end:    # coHdim

# Input: A Complex
# Output: the dimension of all non-zero cohomology groups
complexDim := proc (KK)
local Kv, h, u, prod, i, r, d1, dd, n, grps;
    dd:= NULL;
    n:=convert(convert(KK[2],list),`+`);
	grps := Dimension(KK[2]);

    #compute block dimensions
    for Kv in KK[1] do
        d1:=NULL;
        for r from 2 to nops(Kv) do
            for h from 2 to nops(Kv[r]) do
                u:= KK[4]-
                convert([Vector(grps),seq(Column(KK[3],i),i=Kv[r][h][2])],`+`);
                prod:=1; #compute dim H^q
                for i from 1 to grps do
                    if u[i]<0 then
                        prod:= prod* numbcomb( -u[i]-1    ,KK[2][i] );
                    else 
                        prod:= prod* numbcomb( u[i]+KK[2][i],KK[2][i] );
                    fi;
                od;
                d1:= d1, prod;
                #CohDim(Kv[r], KK[2], KK[3], KK[4], KK[5]); #Kp, l, d, s, m                
            od:
        od;
        dd:= dd, [d1];
    od:
    dd;
end:

### true iff H^q(mpd)=0
CoHzero := proc(grp::set, q::integer, nis::Vector, mpd::Vector)
  local r, i,n, nonz, goodsum;
  n:=convert(nis,`+`);
  r:= Dimension(nis);
    for i from 1 to r do
        if member(i,grp) then
            if mpd[i] >= -nis[i] then RETURN(true); fi;
        else
            if mpd[i] < 0 then RETURN(true); fi;
        fi;
    od;
    RETURN(false);
end:

#########################################################################
# Computation of Complex
#########################################################################

### Compute the Wayman Complex
MakeComplex:=proc(nis::Vector, dis::Matrix, mis::Vector)
	local i,summs, Kv, c,n, K;

	summs:=allsums(nis);
    n:=convert(nis,`+`);

    if Dimension(mis)<>n then
        ERROR(`Wrong dimensions in degree vectorsNot Determinantal`); fi;
    
	K:= NULL;
	for i in seq(-e, e=-n-1..n) do
		Kv := MakeKv(nis,dis,mis,i,summs);
		if not Kv=[] then
			K:= K, Kv;
		fi;
    od;
    # 1     2      3      5 ---Complex---
    [[K], (nis), (dis), (mis)];
end:

### Make term Kv###
MakeKv:= proc(nis::Vector, dis::Matrix, mis::Vector, nu::integer, summs::array)
	local b, Kv, n, p, Kvp;
    n:=convert(nis,`+`);
	Kv:=nu;	for p in seq(0..n+1) do
		Kvp := MakeKvp(nis,dis,mis,nu,p, summs );
		if not Kvp=[] then
			Kv:= Kv, Kvp;
		fi;	od;
	if Kv=nu then RETURN([]); else RETURN([Kv]); fi;end:

###### Make term Kv,p
MakeKvp:= proc(nis::Vector, dis::Matrix, mis::Vector, nu::integer, p::integer, summs::array)
	local c,Kvp,n,q,s, grps;
	n:=convert(nis, `+`);
	grps := Dimension(nis);
    q:=p-nu;
	if q<0 or q>n then RETURN([]); fi;
    Kvp:= p ;
    for c in choose([seq(1..n+1)],p) do # improve ?
        for s in summs[q] do
            if not CoHzero(s,q, nis, mis-convert([Vector(grps),seq(Column(dis,i),i=c)],`+`) ) then
                Kvp:=Kvp, [ s , c];
                break;
            fi;od;od;
    if Kvp=p then RETURN([]); else RETURN([Kvp]); fi;
end:

### Print Kv,p 's
printBlocks:= proc( KK )
  local v, p, sum;

  for v to nops(KK[1]) do
     sum:=0;
     for p from 2 to nops(KK[1][v]) do
	sum:= sum+  K[ KK[1][v][1] , KK[1][v][p][1] ] ;
     od;
  print(K[ KK[1][v][1] ]= sum  );
  od;
end:

### Prints the complex as H^q 's
printCohs:= proc( KK )
local u, r, q, v, p, h, sum, grps;
    r:= Dimension(KK[2]);
    grps := Dimension(KK[2]);
    
  for v to nops(KK[1]) do
      sum:=1;
     for p from 2 to nops(KK[1][v]) do
	 q:= KK[1][v][p][1] - KK[1][v][1];
	 for h from 2 to nops(KK[1][v][p]) do
         u:= KK[4]-
         convert([Vector(grps),seq(Column(KK[3],i),i=KK[1][v][p][h][2])],`+`);
         sum:= sum* H[q]( seq(u[i], i=1..r) );
     od;
     od;
  print( K[KK[1][v][1]]= sum );
  od;
end:

### Prints the complex terms identified as polynomial spaces
printSpaces:= proc( KK )
local k, u, r, q, v, p, h, sum, grps;
    r:= Dimension(KK[2]);
    grps := Dimension(KK[2]);
    unassign('S');
    for v to nops(KK[1]) do
      sum:=1;
     for p from 2 to nops(KK[1][v]) do
	 q:= KK[1][v][p][1] - KK[1][v][1];
	 for h from 2 to nops(KK[1][v][p]) do
         u:= KK[4]-
         convert([Vector(grps),seq(Column(KK[3],i),i=KK[1][v][p][h][2])],`+`);
         for k to grps do
             if u[k]<0 then
                 u[k]:=u[k]+KK[2][k]+1;
             fi;
             # note: degree 0 is not distingushed for primal/dual
             sum:= sum*S( seq(u[i], i=1..r) );
         od;
     od;
     od;
  print( K[KK[1][v][1]]= sum );
  od;
end:


#########################################################################
# Matrix assembly
#########################################################################

makeSysMatrix:= proc(nis::Vector, dis::Matrix, mis::Vector,
                     letters::list := [a,b,c,d,e,f,g,h])
    local n, sys, var;
    n:=convert(nis, `+`);
    var:= [seq( cat(x,i), i=1..Dimension(nis))];
    sys:= Makesystem(nis,dis,letters,var);
    makeMatrix(nis,dis,mis,sys,var);
end:

### The Matrix K_1 -> K_0
makeMatrix:= proc(nis::Vector, dis::Matrix, mis::Vector, sysp:=[], varp:=[] )
  local sys, var, n, KK, matr, row, col, rows, cols, d1, d2;

n:=convert(nis, `+`);

if varp = [] then
   var:= [seq( cat(x,i), i=1..Dimension(nis))];
  else
    var:=varp;
fi:

if sysp = [] then
    sys:= Makesystem(nis,dis,[seq( cat(c,i-1), i=1..n+1)],var) ;
else
    sys:= sysp;
fi;

  #compute the complex
  KK:=MakeComplex(nis,dis,mis);

  #for now demand det/al complex
  if not nops(KK[1])=2 then ERROR(`Not Determinantal`) fi;

  #compute block dimensions
  d1:=0;
  for row from 2 to nops(KK[1][1]) do
	d1:= d1, CohDim(KK[1][1][row], nis, dis, mis);
  od; d1:= [d1];
  d2:=0;
  for col from 2 to nops(KK[1][2]) do
	d2:= d2, CohDim(KK[1][2][col], nis, dis, mis);
  od; d2:= [d2];

  rows:= NULL;
  for row from 2 to nops(KK[1][1]) do
     cols:= NULL;
     for col from 2 to nops(KK[1][2]) do
	    if KK[1][1][row][1]-1 < KK[1][2][col][1] then matr:= matrix( d1[row] , d2[col] , 0 ); #Zero map
       else if KK[1][1][row][1]-1 = KK[1][2][col][1] then
             matr:=   Sylvmat(KK[1][1][row],KK[1][2][col], sys, nis, dis, mis, var) ;
       else  matr:= Bezoutmat(KK[1][1][row],KK[1][2][col], sys, nis, dis, mis, var) ;
       fi;fi;
       cols:= cols, convert(matr,Matrix);
     od;
     rows:= rows, [cols];
  od;
  Matrix([rows], storage=sparse);
end:

### Sylvester Matrix block K_{1,p}->K_{0,p-1}
Sylvmat:= proc(KK1 ,  KK0, f, nis::Vector, dis::Matrix, mis::Vector , var)
local p,n,i, r,c, u ,v, mat, cols,rows, grps, k;
    
    n:=convert(nis,`+`);
    grps := Dimension(nis);
    p:= KK1[1];
    
    rows:=NULL;
  for r from 2 to nops(KK1) do
     cols:=NULL;
     u:= (mis-convert([Vector(grps),seq(Column(dis,i),i=KK1[r][2])],`+` ));
     for k to grps do if u[k]<0 then u[k]:=u[k]+nis[k]+1; fi;od;
     for c from 2 to nops(KK0) do
        v:= ( mis- convert([Vector(grps),seq(Column(dis,i),i=KK0[c][2])],`+`) );
        for k to grps do if v[k]<0 then v[k]:=v[k]+nis[k]+1; fi;od;#Dual!
        if convert(KK0[c][2],set) subset convert(KK1[r][2],set) then
            i:=1; while i<p and KK1[r][2][i]=KK0[c][2][i] do i:=i+1; od; k:=KK1[r][2][i];
            mat:= ( ((-1)^(i+1))*multmap(f[k], u, v, nis, var ) );
        else
            mat:= matrix( Sdim(nis,u), Sdim(nis,v), 0);
        fi;
         cols:= cols, convert(mat, Matrix);
     od;
      rows:= rows,[cols];
  od;
    Matrix([rows]);
end:

### Sylvester Matrix block indexing K_{1,p}->K_{0,p-1}
SylvmatIndex:= proc(nis::Vector, dis::Matrix, mis::Vector , varp:=[])
  local KK, KK0, KK1, grps, i, var, u,  cols, rows, row, r, c, k;
    
    #compute the complex
    KK:=MakeComplex(nis,dis,mis);
    
    grps := Dimension(nis);
    
    rows:=NULL;
    for row from 2 to nops(KK[1][1]) do
        KK1:= KK[1][1][row];
        for r from 2 to nops(KK1) do
            u:= (mis-convert([Vector(grps),seq(Column(dis,i),i=KK1[r][2])],`+` ));
            for k to grps do if u[k]<0 then u[k]:=u[k]+nis[k]+1; fi;od;
            rows:= rows, [monbasis(nis,u,varp)];
            #rows:= rows, monbasis(nis,u,varp);
        od;
    od:
    cols:=NULL;
    for row from 2 to nops(KK[1][1]) do
        KK0:= KK[1][2][row];
        for c from 2 to nops(KK0) do
            u:= ( mis- convert([Vector(grps),seq(Column(dis,i),i=KK0[c][2])],`+`) );
            for k to grps do if u[k]<0 then u[k]:=u[k]+nis[k]+1; fi;od;#Dual!
            cols:= cols, [monbasis(nis,u,varp)];
            #cols:= cols, monbasis(nis,u,varp);
        od;
    od:
[rows],[cols];
end:

### Matrix of multihomogeneous multiplication map
multmap:= proc(f, sp1::Vector, sp2::Vector, nis::Vector, var::list)
local i,j,row,col, vars, mat;
    
    row := [monbasis(nis,sp1,var)];
    col := [monbasis(nis,sp2,var)];    
    vars:= allvars(nis,var);
    
    mat := NULL;
    for i to nops(row) do
        for j to nops(col) do
            mat := mat, coeffof(expand(col[j]/row[i]), f , vars ) ;
        od;
    od;
    Matrix(nops(row),nops(col),[mat]);
end:

###return the coeff. of p in variables var of the monomial m:
coeffof := proc(m,p,var)
local lm,lc,k;
  lc := [coeffs(p,var,'lm')];
  lm := [lm];
  if member(m,lm,'k') then lc[k] else 0 fi;
end:

#all variables, var the vector of group names, for example bihomo: [x,y]
allvars:= proc(nis::Vector,var)
local i,vars;

vars:= NULL;
for i to Dimension(nis) do
if not var[i]=0 then
vars:= vars, seq( var[i][k], k=1..nis[i] );
fi; od;
[vars];
end:

###List the monomials of a polynomial p in the variables var:
lstmonof := proc(p,var)
local lm,r,c;
  lm := NULL;
  r := sort(p,var,tdeg);
  while r <> 0 do
     c := tcoeff(r,var,'lstmonof123m');
     lm := lm, lstmonof123m;
     r := expand(r-c*lstmonof123m);
  od;
  lm;
#op(sort([lm], proc (a, b) options operator,
# arrow;Groebner:-TestOrder(a, b, grlex(op(var))) end proc));
op(sort([lm], proc (a, b) options operator, arrow;Groebner:-TestOrder(a, b, tdeg(op(ListTools:-Reverse(var)))) end proc));
#op(sort([lm], proc (a, b) options operator, arrow;Groebner:-TestOrder(a, b, plex(op(ListTools:-Reverse(var)))) end proc));
end:

### The natural monomial basis of S(mdeg)
monbasis := proc(nis::Vector,mdeg::Vector,var)
  local p, g, gvar, vars;
  vars:=NULL;
  if not ( nops(var)= Dimension(nis) and nops(var)=Dimension(mdeg)) then
    ERROR(`Wrong dimensions`); fi;
  p:=1;
  for g from 1 to Dimension(nis) do
       if var[g]=0 then next fi;

      if mdeg[g]>=0 then 
          gvar:= seq( var[g][k], k=1..nis[g] );
          p:= p*expand( (1+convert([gvar] , `+`))^mdeg[g] );
      else
          gvar:= seq( var[g][k], k=1..nis[g] );
          gvar:=gvar, cat(XtraDegVar,g); #degeneracy quick fix
          p:= p * expand( (1+convert( [seq(1/gvar[k], k=1..nis[g])],`+`) )^(-mdeg[g]) );

          #gvar:= op(dualVars([seq( var[g][k], k=1..nis[g])]));
          #p:= p*expand( (1+convert([gvar], `+`))^(-mdeg[g]) );
      fi;

      vars:= vars, gvar;
  od;
  lstmonof(expand(p),[vars]);
end:

#########################################################################
# Polynomials
#########################################################################

### Make polynomial with m-degree di
Makepoly:= proc(nis::Vector,di::Vector, c, var )
  local vars, p, i, s;

    vars:=allvars(nis,var);
    
    i:=0;p:=0;
    s:=[monbasis(nis, di, var)];
    unassign('c');
    for i from 1 to nops(s) do
#        p:= p + c[i-1] * s[i];
 TP:
     p:= p + c[degree(s[i],vars[1]),degree(s[i],vars[2])] * s[i];
    od;
    p;
end:

### Make extreme polynomial with degree dis
MakeExtremepoly:= proc(nis::vector,dis::vector, c, var )
  local v, p, i,j,dd, vars;

  vars:= allvars(nis,var);
  dd:= evalm(dis);
  p:=1;v:=1;
  for i to vectdim(nis) do
     for j to nis[i] do
       p:= p*(1+ vars[v]^dd[i] );
       v:= v+1;
  od;od;

  v:= [lstmonof(evalm(p),vars)];
  p:=0;
  for i from 1 to nops(v) do
     p:= p+ c[i-1]*v[i];
  od;
  p;
end:

### Make multihomogeneous system
Makesystem:= proc(nis::Vector, dis::Matrix, coef:=[seq(cat(c,i), i=0..convert(nis,`+`))], var:= [seq( cat(x,i), i=1..Dimension(nis))] )
  local i,n,lst;
  n:=convert(nis,`+`);
  lst:=NULL;
  for i from 1 to n+1 do
      lst:= lst, Makepoly(nis, Column(dis,i), coef[i] ,var);
  od;
  [lst];

end:

homogenizePoly := proc(p, nis::Vector, pdeg::Vector, var::list)
local vars, hp, mm, mdeg, grps;
    vars:=allvars(nis,var);
    grps := Dimension(nis);
    
    hp := 0;
    for mm in coeffs(collect(p, vars, 'distributed'), [x, y]) do
        mdeg := mDegree(mm,nis,var);
        hp := hp + mm * mul( var[k][0]^(pdeg[k]-mdeg[k]), k=1..grps);
    od:
    hp;
end:

#########################################################################
# Computational search for degree vectors
#########################################################################

is_determ := proc(nis::Vector,dis::Matrix,mis::Vector, summs::array)
 local n,grps, Nu, i,p,c, s,q;
 grps:=Dimension(nis):
# if grps <> Dimension(dis) then ERROR(`BAD DIMS`) fi;
# if grps <> Dimension(mis) then ERROR(`BAD DIMS for m-vector`) fi;
    unassign('i');
    n:=convert(nis, `+`);

    for Nu in {-1,2} do
        for p from max(0,Nu) to min(n+1,Nu+n) do
            for c in choose([seq(1..n+1)],p) do
                q := p-Nu:
                for s in summs[q] do
                    if not CoHzero(s,q,nis,mis-convert([Vector(grps),seq(dis[..,i],i=c)],`+`))
                    then RETURN(false) fi:
                od:
            od:
        od:
    od:
    RETURN(true);
end:	# is_determ
    
# find/return next vector (following mis) in lex-order
next_lex_rect:=proc(mis::Vector,low::Vector,upp::Vector)
 local i, j, r, nxt;

 nxt := copy(mis);
 r :=Dimension(mis);
 #if r <> vectdim(low) then ERROR(`BAD DIMS`) fi;
 #if r <> vectdim(upp) then ERROR(`BAD DIMS`) fi;
 for i from r to 1 by -1 do if mis[i]<upp[i] then
   nxt[i]:=mis[i]+1;
   for j from i+1 to r do nxt[j]:=low[j]; od;
   RETURN(nxt);
   fi;
 od;
 eval(0);
end:# next_lex_rect

### true iff l1<l2
sort_dim:=proc(l1,l2)
 local i;
 if l1[-1]<l2[-1] then RETURN(true)
 else RETURN(false)  fi;
end: # sort_dim

dBounds := proc(nis::Vector,dis::Matrix)
local grps, low, upp, i;
    grps:=Dimension(nis):

    low := Vector(grps);
    for i from 1 to grps do
        #low[i]:=  min(-max(dis[i,..]),-nis[i]);
        low[i]:=  max(-max(dis[i,..]),-nis[i]);
    od:
    unassign('i');

    upp := Vector(grps);
    for i from 1 to grps do
        upp[i]:= convert(dis[i,..], `+`) - 1 + min( max(dis[i,..])-nis[i], 0);
    od;
    #print("Bounds:",low, upp);
low,upp;    
end:

                
allDetVecs := proc(nis::Vector,dis::Matrix)
 local	cand,
	tmp, misD, low,upp, grps,n,i, goodmis, summs, cnt,
	msmall,small,mbig,big;

 grps:=Dimension(nis):
 n:=convert(nis, `+`);

 goodmis:={};
 summs:=allsums(nis):

 #compute the bounds
 low, upp := dBounds(nis,dis);
# LOOSEN BOUNDS (for testing)
#low := low - Vector(grps,2);
#upp := upp + Vector(grps,2);

 cand:=low;
 cnt:=1;
 while cand <> 0 do

  # necessary condition
#  msmall := false; mbig:=false;
# for i from 1 to grps do
#   if cand[i]<small*dis[i] then msmall:=true; break; fi;
# od:#i
# for i from 1 to grps do
#   if cand[i] >= big*dis[i]-nis[i] then mbig:=true; break; fi;
# od:#i

     if #msmall and mbig and
     is_determ(nis,dis,cand,summs) then
#         print("found",cand);
      misD:=[op(convert(cand,list)), dimKv(nis,dis,cand,summs,0)];
      goodmis:=eval(goodmis) union {eval(misD)};
  fi;
  cand := next_lex_rect(cand,low,upp);

  cnt:=cnt+1;
 od;

# matadd(matadd(upp,low,1,-1),Vector(grps,1));
# unassign('i');
# tmp :=product(%[i],i=1..grps);
# if cnt-1 <> tmp then ERROR(`bad count`,cnt-1,tmp) fi;

 sort(convert(goodmis,list), sort_dim);
end:	# allDetVecs


#########################################################################
# Bezout Matrix assembly
#########################################################################


# Determinant of the discrete Jacobian
Jdiscr := proc(lp::list, vx)
local N,i,j,k,vxi,mtr,s;

  N := nops(lp);
  if nops(vx) <> N-1 then print(nops(lp), vx );
    ERROR(`the number of polynomials must be the number of variables +1 `);
  fi;
  mtr := array(1..N,1..N);
  for i from 1 to N do mtr[i,1] := lp[i] od;

  for j from 2 to N do
     for i from 1 to N do
       mtr[i,j]:= subs(vx[j-1]= cat(_,vx[j-1]) ,mtr[i,j-1]); ## vy[j-1]
     od;
  od;

  for j from N to 2 by -1 do
     for i from 1 to N do
       mtr[i,j] := quo(mtr[i,j]-mtr[i,j-1], cat(_,vx[j-1]) - vx[j-1], cat(_,vx[j-1]));
     od;
  od;

  det(convert(mtr,matrix));
end:

### Bezoutian block of S(sp1)->S(sp2)
BezoutianPoly:= proc(f,sp1::vector,sp2::vector,nis::vector,var, grp:={} )
  local i,j,row,col, nvar, nvars, ovar, ovars, Bpol, mat;

  if grp={} then grp:={seq(1..nops(var))} fi;

  nvar:=NULL; ovar:=NULL;
  for i to nops(var) do
         if member(i,grp ) then
	    nvar:= nvar,cat(_,var[i]);
	    ovar:= ovar, var[i];
	 else
	    nvar:= nvar, 0;
	    ovar:= ovar, 0;
	 fi;
  od;
  nvar:= [nvar]; ovar:= [ovar]; # new variables

  nvars := allvars(nis,nvar);
  ovars := allvars(nis,ovar);

  Bpol:= Jdiscr(f,ovars ); # introduces the new variables inside
  row:= [monbasis(nis,sp1, var)];
  col:= [monbasis(nis,sp2,nvar)];

  nvars:= [op(allvars(nis,var)),op(nvars)];
  mat:= NULL;
  for i to nops(row) do
    for j to nops(col) do
     mat := mat, coeffof(col[j]*row[i], Bpol , nvars );
    od;
  od;
  matrix(nops(row),nops(col),[mat]);
end:

### Bezoutian block of S(sp1)->S(sp2)
BezoutianPoly:= proc(f,sp1::vector,sp2::vector,nis::vector,var, grp:={} )
  local i,j,row,col, nvar, nvars, ovar, ovars, Bpol, mat;

  if grp={} then grp:={seq(1..nops(var))} fi;

  nvar:=NULL; ovar:=NULL;
  for i to nops(var) do
         if member(i,grp ) then
	    nvar:= nvar,cat(_,var[i]);
	    ovar:= ovar, var[i];
	 else
	    nvar:= nvar, 0;
	    ovar:= ovar, 0;
	 fi;
  od;
  nvar:= [nvar]; ovar:= [ovar];

  nvars := allvars(nis,nvar);
  ovars := allvars(nis,ovar);

  Bpol:= Jdiscr(f,ovars );
  row:= [monbasis(nis,sp1, var)];
  col:= [monbasis(nis,sp2,nvar)];

  nvars:= [op(allvars(nis,var)),op(nvars)];
  mat:= NULL;
  for i to nops(row) do
    for j to nops(col) do
     mat := mat, coeffof(col[j]*row[i], Bpol , nvars );
    od;
  od;
  matrix(nops(row),nops(col),[mat]);
end:

### Bezoutian block K_{1,a}->K_{0,b}
# see also http://math.rice.edu/~hargis/VIGRE/fast-computation-of-the.pdf
# see the map:
# http://www.orcca.on.ca/TechReports/TechReports/2007/TR-07-02.pdf,
# page 2
Bezoutmat:= proc(KK1 ,  KK0, f, nis::vector, dis::vector, sis::vector, mis::vector , var)
  local p, pols, subsvar, n,grps, r,c, rows, cols, u,v, k, mat;

  n:=convert(convert(nis,list),`+`);
  grps := vectdim(nis);
  p:= KK0[1];

  rows:=NULL;
  for r from 2 to nops(KK1) do
     cols:=NULL;
     u:= evalm(mis-convert([seq(sis[i],i=KK1[r][2])],`+` )*dis);
     for k to grps do if u[k]<0 then u[k]:=-u[k]-nis[k]-1; fi;od;
     for c from 2 to nops(KK0) do
        v:= evalm( mis- convert([seq(sis[i],i=KK0[c][2])],`+`)*dis ) ;
        for k to grps do if v[k]<0 then v[k]:=-v[k]-nis[k]-1; fi;od;
	if convert(KK0[c][2],set) subset convert(KK1[r][2],set) then
	   pols:= convert(convert(KK1[r][2],set) minus convert(KK0[c][2],set), list);
           subsvar:= KK1[r][1] minus KK0[c][1]; # partial Bezoutian
           mat:= BezoutianPoly( [seq(f[k],k=pols)] ,u,v,nis,var, subsvar );
        else
          mat:= matrix( Sdim(nis,u), Sdim(nis,v), 0);
	fi;
	cols:= cols, convert(mat, Matrix);
     od;
     rows:= rows,[cols] ;
  od;
Matrix([rows]);
end:

end:#end resultant
