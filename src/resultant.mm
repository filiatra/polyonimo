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
# Bezout bound computations
    mBezout,
    mBezoutUnmixed,
# Generators of multihomogeneous polynomials
    makePoly,
    makeSystem,
    makeExtremePoly,
# Automated computation of resultant matrix
    findResMatrix,
# Brute force search
    bruteSearch,
# Complex and matrix computation based on degree vector
    makeComplex,
    printComplex,
    makeMatrix,
    SylvmatIndex, #to do
# Utility
    mDegree;
    
local 
#export
# Data structures and helpers for complex
    NewCOMPLEX,
    NewCOMP,
    NewTERM,
    NewCOH,
    makeKv,
    makeKpq,
    dimension,
    blockStructure,
    firstTerm,
    lastTerm,
# Specific resultant formulas
    critVect,
    macVect,
    unmixedSylvVect,
    biVarSylvVect,
    bilinearSylvVect,
# Polynomial manipulation
    coeffof,
    lstmonof,
    multmap,
    monbasis,
    allvars,
    homogenizePoly,
# Brute search helpers
    isCohZero,
    nzCohDim,
    dimKv,
    dimKpq,
    dimHq,
    Sdim,
    allsums,
    is_determ,
    next_lex_rect,
    detStats,
    sortPerm,
    columnsum,
# sortFormulas -> compute all dimensions
    solveMatrixKernel,
# Matrix generator helpers
    Sylvmat,
    dBounds,
    Jdiscr,
    BezoutianPoly,
    Bezoutmat;
    
uses LinearAlgebra, combinat;
    
#statementSequence
    
#########################################################################
# WCOMPLEX data structure
#########################################################################
    
# K_{*}
    NewCOMPLEX := proc(_grp::Vector, _deg::Matrix, _mvc::Vector, _K::Array(WTERM):=[])
        
        if Dimension(_mvc)<>Dimension(_grp) then
            ERROR(`Wrong dimensions in degree vectors.`); fi;
        
        return Record('nv'=convert(_grp,`+`), 'ng'=Dimension(_grp), 'grp'=_grp, 'deg'=_deg, 'mvc'=_mvc, 'K'=K);
    end:
    
# K_{v}
    NewTERM := proc(_v::integer, _S:= [])
        return Record('v'=_v, 'S'=_S);
    end:
    
# K_{p,q}, v=p-q
    NewCOMP := proc(_p::integer, _q::integer, _C := []) # bug: _C::list(WCOMP)
        return Record('p'=_p, 'q'=_q, 'C'=_C);
    end:
    
# H^q(mdeg)
    NewCOH := proc(_fis::set, grp::Vector, _mdeg::Vector)
    local i, prod := 1, qq:= NULL;
        for i to Dimension(_mdeg) do
            if _mdeg[i]<0 then
                prod:= prod* numbcomb(-_mdeg[i]-1     , grp[i] );
                qq:= qq, i; # extra
            else
                prod:= prod* numbcomb( _mdeg[i]+grp[i], grp[i] );
            fi;
        od;
#add(`if`(i<0, 1, 0), i=_mdeg); 
        return Record('exp'={qq}, 'fis'=_fis, 'mdeg'=_mdeg, 'dim'=prod );
    end:
    
# First nonzero term in the complex (index bigger than last term)
    firstTerm := proc(KK::WCOMPLEX)
        op(op(KK:-K)[1])[2];
    end:
    
# Last nonzero term in the complex (index lower than first term)
    lastTerm := proc(KK::WCOMPLEX)
        op(op(KK:-K)[1])[1];
    end:
    
# Dimension of complex terms
    dimension := overload(
        [
            proc(a::WTERM) option overload;
            local v, res := 0;
                for v in a:-S do
                    res := res + dimension(v);
                od:
                return res;
            end,
            
            proc(b::WCOMP) option overload;
            local v, res := 0;
                for v in b:-C do
                    res := res + v:-dim;
                od:
                return res;
            end,
            
            proc(c::WCOH) option overload;
                return c:-dim;
            end
        ]
                         ):
    
#########################################################################
#########################################################################
    
### detStats
# how many vectors yield which matrix dimension
#todo: update wrt bruteSearch
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
    
### all q-sums by dynamic programming
    allsums := proc(nis::Vector)
    local n, grps, i, q, Subs, ss, summs;
        grps:=LinearAlgebra:-Dimension(nis): unassign('i');
        unassign('n');
        n:=convert(nis, `+`);
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
# Note: values to reciprocals should be considered false
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
        s:=add(Column(dis,i),i=1..n+1);
        r:= s - nis - Vector(grps,1);
        r;
    end:
    
# Macaulay's matrix degree vector
    macVect:= proc(nis::Vector, dis::Matrix)
    local grps,n,s;
        grps := Dimension(nis);
        n:=convert(nis,`+`);
        s:=add(Column(dis,i),i=1..n+1);
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
    
# Mixed bilinear system
# ...
    
#########################################################################
# Dimensions
#########################################################################
    
# Bezout bound
    mBezout:= proc(nis::Vector, dis::Matrix, j::integer := -1)
    local k, fct, grps,n, dd;
        
        n:=convert(nis,`+`);
        grps := Dimension(nis);
        if [grps,n+1] <> [Dimension(dis)] then ERROR(`BAD DIMS ! `) fi;
        
        fct := mul(factorial(nis[k]), k=1..grps);
        
        if grps=n then dd:=dis; else
            # Expand the degree matrix    
            dd:= Matrix(< seq(seq(dis[m,..],i=1..nis[m]),m=1..grps) >);
        fi:
        
        if j=-1 then# Total degree of resultant
            RETURN( add( Permanent(DeleteColumn(dd,i)),i=1..n+1) / fct);
        else# Number of solutions of square system (ie. without f_j)
            RETURN( Permanent(DeleteColumn(dd,j)) / fct );
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
    dimKv:=proc(nis::Vector,dis::Matrix,mis::Vector,Nu::integer)
    local n,grps, i,p, dimK;
        
        grps:=Dimension(nis):
        unassign('i');
        n:= convert(nis,`+`);
        dimK := 0;
        for p from max(0,Nu) to min(n+1,Nu+n) do
            dimK := dimK + dimKpq(nis,dis,mis,p,p-Nu);
        od:
        eval(dimK);
    end:# dimKv
    
#### Dimension of Kpq
    dimKpq:= proc(nis::Vector, dis::Matrix, mis::Vector, 
                  p::integer,q::integer)
    local c,Kvp,grps,dim,k,v;
        grps:=Dimension(nis);
        dim:=0;
        for c in choose([seq(1..convert(nis,`+`)+1)],p) do
            v := mis - columnsum(dis,c);
            dim:=dim + dimHq(nis, v, q);
        od;
        RETURN(dim);
    end:# dimKpq
    
# Dimension of H^q(mpd)
    dimHq := proc(nis::Vector, mpd::Vector, q::integer)
    local i, k:= 1, dim:=1;
        if isCohZero(nis,mpd,q) then return 0; else return nzCohDim(nis,mpd); fi:
    end:
    
# Check for vanishing of H^q(mpd)
    isCohZero := proc(nis::Vector, mpd::Vector, q::integer)
    local i, qq::integer := 0;
        for i to Dimension(nis) do
            if mpd[i] < -nis[i] then 
                qq:= qq + nis[i]; 
            else 
                if mpd[i] < 0 then 
                    return true;
                fi:
            fi:
        od;
        return(q<>qq);
    end:
    
#Dimension of a non-zero H^q(mpd)
    nzCohDim := proc(nis::Vector, mpd::Vector)
    local i, dim::integer :=1;
        for i to Dimension(nis) do
            if mpd[i]<0 then
                dim:=dim*numbcomb(-mpd[i]-1,nis[i]);
            else
                dim:=dim*numbcomb(mpd[i]+nis[i],nis[i]); 
            fi;
        od;
        return dim;
    end:
    
#########################################################################
# Computation of Complex
#########################################################################
    
### Compute the Wayman Complex
    makeComplex := proc(nis::Vector, dis::Matrix, mis::Vector)
    local kfirst, klast:= NULL, i, Kv, KK, tmp := NULL;
        
        KK:= NewCOMPLEX(nis,dis,mis);
        
        for i from -KK:-nv to KK:-nv + 1 do
            Kv := makeKv(nis,dis,mis,i);
            if not Kv:-S = [] then
                tmp := tmp, Kv;
                if ( klast=NULL ) then
                    klast:= i;
                else
                    kfirst := i;
                fi:
            fi;
        od;
        KK:-K := Array(klast..kfirst,[tmp], datatype=WTERM);
        return KK;
    end:
    
### Make term Kv
    makeKv:= proc(nis::Vector, dis::Matrix, mis::Vector, nu::integer)
    local b, Kv, n, p, Kpq, tmp := NULL;
        n:=convert(nis,`+`);
        
        Kv:= NewTERM(nu);
        for p in seq(0..n+1) do
            Kpq := makeKpq(nis,dis,mis,nu,p);
            if not Kpq:-C = [] then
                tmp := tmp, Kpq;
            fi;	
        od;
        Kv:-S := [tmp];
        return Kv;
    end:
    
###### Make term Kp,q
    makeKpq:= proc(nis::Vector, dis::Matrix, mis::Vector, nu::integer, p::integer)
    local c,n,q,s, grps, mdeg, tmp := NULL;
        n:=convert(nis, `+`);
        grps := Dimension(nis);
        q:=p-nu;
        if q<0 or q>n then 
            return NewCOMP(p,q);
        fi;
        for c in choose({seq(1..n+1)},p) do # improve ?
            mdeg := mis-columnsum(dis,c):
            if not isCohZero(nis, mdeg, q) then
                tmp := tmp, NewCOH(c, nis, mdeg, grp); #
            fi;
        od;
#print("NewCOMP(p,q,[tmp])",NewCOMP(p,q,[tmp])); # BUG
        return NewCOMP(p,q,convert([tmp],list));
#Kpq:= NewCOMP(p,q); Kpq:-C := [tmp]: Kpq;
    end:
    
    
### Print the complex
    printComplex:= proc( KK::WCOMPLEX, plevel::integer := 1)
    local h, u, k, d1, d2, v, p, sum;
        
        unassign('K');
        
        if plevel=0 then
            sum:= 0, "--->";
            for v from firstTerm(KK) to lastTerm(KK) by -1 do #  ( K_1, K_0, .. )
                sum:= sum, K[ KK:-K[v]:-v ], "--->";
            od;
            print( sum, 0 );
            return;
        fi:
        
        if plevel=1 then
            for v from firstTerm(KK) to lastTerm(KK) by -1 do #  ( K_1, K_0, .. )
                sum:=0;
                for p to nops(KK:-K[v]:-S) do # ( K_{1,1} , K_{1,2} , .. )
                    sum:= sum +  K[ KK:-K[v]:-v, KK:-K[v]:-S[p]:-p ] ;
                od;
                print(K[ KK:-K[v]:-v ]= sum  ); # K[ KK:-K[v]:-nu ] = sum
            od;
            return;
        fi:
        
        if plevel=2 then
            for v from firstTerm(KK) to lastTerm(KK) by -1 do #  ( K_1, K_0, .. )
                sum:=1;
                for p to nops(KK:-K[v]:-S) do
                    for h to nops(KK:-K[v]:-S[p]:-C) do
                        u:= KK:-K[v]:-S[p]:-C[h]:-mdeg;
                        sum:= sum* H[ KK:-K[v]:-S[p]:-q ]( seq(u[i], i=1..KK:-ng) )
                    od;
                od;
                print( K[ KK:-K[v]:-v ] = sum );
            od;
            return;
        fi:
        
        if plevel=3 then
            unassign('S');
            for v from firstTerm(KK) to lastTerm(KK) by -1 do #  ( K_1, K_0, .. )
                sum:=1;
                for p to nops(KK:-K[v]:-S) do
                    for h to nops(KK:-K[v]:-S[p]:-C) do
                        u:= copy(KK:-K[v]:-S[p]:-C[h]:-mdeg);
                        for k to KK:-ng do if u[k]<0 then u[k]:=u[k] + KK:-grp[k] + 1; fi; od:
                        # note: degree 0 is not distingushed for primal/dual
                        sum:= sum*S( seq(u[i], i=1..KK:-ng) );
                    od;
                od;
                print( K[ KK:-K[v]:-v ]= sum );
            od;
            return;
        fi:
        
        if plevel=4 then
            d1, d2 := blockStructure(KK,1,0);
            print( Matrix(nops(d1), nops(d2), (i,j)-> [d1[i],d2[j]]) );
            return;
        fi:
        
# exterior alg.
        if plevel=5 then
            for v from firstTerm(KK) to lastTerm(KK) by -1 do #  ( K_1, K_0, .. )
                sum:=1;
                for p to nops(KK:-K[v]:-S) do
                    for h to nops(KK:-K[v]:-S[p]:-C) do
                        u:= KK:-K[v]:-S[p]:-C[h]:-mdeg;
                        sum:= sum* (Lambda^(KK:-K[v]:-S[p]:-C[h]:-fis))[op(KK:-K[v]:-S[p]:-C[h]:-exp)];
                    od;
                od;
                print( K[ v ] = sum );
            od;
            return;
        fi:
        ERROR(`Print level can only be 0..5`);
    end:
    
    
#########################################################################
# Matrix assembly
#########################################################################
    
    findResMatrix := proc(nis::Vector, dis::Matrix, ivar::list(symbol) :=[],
                          mis::Vector := Vector(), 
                          letters::list(symbol) := ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o'])
    local vv,vd,  KK::WCOMPLEX, sys, var::list, mvec::Vector;
        
        if (Dimension(mis)=0) then
            vv, vd := bruteSearch(nis,dis):
            
            if nops(vv)=0 then
                lprint(`No matrix found.`);
                return Matrix();
            else
                mvec := vv[-1];
                lprint(`Degree vector `, convert(mvec,list), `dimension`, vd[-1] );
            fi:
        else
            mvec := mis;
        fi:
        
        KK := makeComplex(nis, dis, mvec):
        printComplex(KK,1);
        
        if (ivar=[]) then
            var:= ['x','y','z','u','v','w','s','t'][1..Dimension(nis)];
        else
            var := ivar;
        fi:
        
        sys:= makeSystem(nis, dis, letters, var);
        if _nresults = 1 or _nresults = undefined then
            return makeMatrix(KK, sys, var);
        else
            return makeMatrix(KK, sys, var), sys;
        fi:
    end:
    
### The Matrix K_1 -> K_0
    makeMatrix:= proc(KK::WCOMPLEX, sysp:=[], varp:=[])
    local ddeg, sys, var, n, matr, row, col, rows, cols, d1, d2;
        
        n:= KK:-nv;
        
        if varp = [] then
            var:= ['x','y','z','u','v','w','s','t'][1..KK:-ng];
        else
            var:=varp;
        fi:
        
        if sysp = [] then
            unassign('c');
            sys:= makeSystem(KK:-grp, KK:-deg, [seq( cat(c,i-1), i=1..KK:-nv+1)],var) ;
        else
            sys:= sysp;
        fi;
        
        #for now demand det/al complex
        if not ArrayNumElems(KK:-K)=2 then ERROR(`Not Determinantal`) fi;
        
        #compute block dimensions
        d1, d2 := blockStructure(KK,1,0);
        #print(d1, d2);
        
        rows:= NULL;
        for row to nops(KK:-K[1]:-S) do 
            cols:= NULL;
            for col to nops(KK:-K[0]:-S) do
                ddeg := KK:-K[1]:-S[row]:-q - KK:-K[0]:-S[col]:-q + 1;
                if ddeg=0 then 
                    matr:= Matrix( d1[row] , d2[col] , 0, storage=sparse ); #Zero map
                else if ddeg=1 then
                         matr:= Sylvmat(KK, 1,row, 0,col, sys, var);
                         #print("Sylv", row, col,"-->", Dimension(matr));
                     else  
                         matr:= Bezoutmat(KK, 1,row, 0,col, sys, var);
                         #print("Bez", row, col,"-->", Dimension(matr));
                     fi;fi;
                
                cols:= cols, matr;
            od;
            rows:= rows, [cols];
        od;
        Matrix([rows], storage=sparse);
    end:
    
    
### Sylvester Matrix block K_{1,p}->K_{0,p-1}
    Sylvmat:= proc(KK::WCOMPLEX, 
                   n1::integer, t1::integer, 
                   n0::integer, t0::integer, f, var)
    local p::integer, i::integer, r::WCOH, c::WCOH, _u::Vector , _v::Vector, mat::Matrix, cols, rows, grps::integer, k::integer;
        
        if ( n1-n0 <> 1) then ERROR(`Terms not consecutive`) fi;
        
        grps := KK:-ng;
        p:= KK:-K[n1]:-S[t1]:-p;
        if (p - KK:-K[n0]:-S[t0]:-p <> 1) then ERROR(`Terms not consistent`) fi;
        
        rows:=NULL;
        for r in KK:-K[n1]:-S[t1]:-C do
            cols:=NULL;
            _u:= copy(r:-mdeg);
            for k to grps do if _u[k]<0 then _u[k]:=_u[k] + KK:-grp[k] + 1; fi;od;
            for c in KK:-K[n0]:-S[t0]:-C do
                _v:= copy(c:-mdeg);
                for k to grps do if _v[k]<0 then _v[k]:=_v[k] + KK:-grp[k] + 1; fi;od;#Dual!
                if c:-fis subset r:-fis then
                    i:=1; while i<p and r:-fis[i]=c:-fis[i] do i:=i+1; od; k:=r:-fis[i];
                    mat:= ( ((-1)^(i+1))*multmap(f[k], _u, _v, KK:-grp, var ) );
                else
                    mat:= Matrix(r:-dim, c:-dim, 0, storage=sparse);
                fi;
                cols:= cols, mat;
            od;
            rows:= rows,[cols];
        od;
        Matrix([rows], storage=sparse);
    end:
    
### Sylvester Matrix block indexing K_{1,p}->K_{0,p-1}
    SylvmatIndex:= proc(nis::Vector, dis::Matrix, mis::Vector , varp:=[])
    local KK, KK0, KK1, grps, i, var, u,  cols, rows, row, r, c, k;
        
        #compute the complex
        KK:=makeComplex(nis,dis,mis);
        
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
        #print(row,col);
        
        mat := Matrix(nops(row), nops(col), storage=sparse);
        for i to nops(row) do
            for j to nops(col) do
                mat[i,j] := coeffof(expand(col[j]/row[i]), f , vars );
            od;
        od;
        #print(mat);
        return mat;
#todo: return row,col ? _nresults
    end:
    
###return the coeff. of p in variables var of the monomial m:
    coeffof := proc(m, p, var)
    local lm, mlist, k;
        mlist := [coeffs(p,var,'lm')];
        if member(m,{lm},'k') then return mlist[k]; else return 0; fi;
    end:
    
# todo
# coeffof := proc(m,mlist)
    
    
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
#op(sort([lm], proc (a, b) options operator, arrow;Groebner:-TestOrder(a, b, tdeg(op(ListTools:-Reverse(var)))) end proc));
        op(sort([lm], proc (a, b) options operator, arrow;Groebner:-TestOrder(a, b, plex(op(ListTools:-Reverse(var)))) end proc));
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
    makePoly:= proc(nis::Vector,di::Vector, c, var )
    local vars, p, i, s;
        
        vars:=allvars(nis,var);
        
        i:=0;p:=0;
        s:=[monbasis(nis, di, var)];
        unassign('c');
        for i from 1 to nops(s) do
#        p:= p + c[i-1] * s[i];
# TP-indexing:
            p:= p + c[degree(s[i],vars[1]),degree(s[i],vars[2])] * s[i];
        od;
        p;
    end:
    
### Make extreme polynomial with degree dis
    makeExtremePoly:= proc(nis::Vector,dis::Vector, c, var )
    local v, p, i,j, vars;
        
        vars:= allvars(nis,var);
        p:=1;v:=1;
        for i to Dimension(nis) do
            for j to nis[i] do
                p:= p*(1+ vars[v]^nis[i] );
                v:= v+1;
            od;od;
        
        v:= [lstmonof(evalm(p),vars)];
        p:=0;
        for i from 1 to nops(v) do
            #p:= p+ c[i-1]*v[i];
            p:= p + c[degree(v[i],vars[1]),degree(v[i],vars[2])] * v[i];
        od;
        p;
    end:
    
### Make multihomogeneous system
    makeSystem:= proc(nis::Vector, dis::Matrix, 
                      coef:=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o'][1..1+convert(nis,`+`)], 
                      var:= ['x','y','z','u','v','w','s','t'][1..Dimension(nis)] )
    local i,n,lst;
        n:=convert(nis,`+`);
        lst:=NULL;
        for i from 1 to n+1 do
            lst:= lst, makePoly(nis, Column(dis,i), coef[i] ,var);
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
    
    columnsum:= proc(dis::Matrix, c)
    option inline;
        convert([Vector(RowDimension(dis)),seq(dis[..,i],i=c)],`+`)
# Maple>13: add(dis[..,i],i=c)
    end:
    
    sortPerm := proc(data)
    local i::integer, ind::list(integer) := [seq(1..nops(data))];
        sort(ind, proc(a,b) data[a]<data[b] end);
    end:
    
    is_determ := proc(nis::Vector,dis::Matrix,mis::Vector)
    local n,grps, Nu, i,p,c, s: # A::table
        grps:=Dimension(nis):
# if grps <> Dimension(dis) then ERROR(`BAD DIMS`) fi;
# if grps <> Dimension(mis) then ERROR(`BAD DIMS for m-vector`) fi;
        unassign('i');
        n:=convert(nis, `+`);
        
        # Maple 16:
        #c := firstcomb[{seq(1..n+1)},p]; .. combinat[nextcomb](c,p)
        
        for Nu in [2,-1] do
            for p from max(0,Nu) to min(n+1,Nu+n) do
                for c in choose([seq(1..n+1)],p) do
#                    if not isCohZero(nis,mis-convert([Vector(grps),seq(dis[..,i],i=c)],`+`), p-Nu)
                    if not isCohZero(nis,mis-columnsum(dis,c), p-Nu)
                    then RETURN(false) fi:
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
    
    
    bruteSearch := proc(nis::Vector,dis::Matrix)
    local	cand::Vector, low, upp, grps, n, i, goodmis, cnt;
        
        grps:=Dimension(nis):
        n:=convert(nis, `+`);
        
        goodmis:=NULL;
        
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
            is_determ(nis,dis,cand) then
#         print("found",cand);
#      misD:=[op(convert(cand,list)), dimKv(nis,dis,cand,0)];
                goodmis:= goodmis, cand;
            fi;
            cand := next_lex_rect(cand,low,upp);
            
            cnt:=cnt+1;
        od;
        
# matadd(matadd(upp,low,1,-1),Vector(grps,1));
# unassign('i');
# tmp :=product(%[i],i=1..grps);
# if cnt-1 <> tmp then ERROR(`bad count`,cnt-1,tmp) fi;
        
        if _nresults = 1 or _nresults = undefined then
            return [goodmis];
        else
            upp := NULL;
            for cand in [goodmis] do
                upp := upp, dimKv(nis,dis,cand,0);
            od:
            upp:=[upp]:
            low := sortPerm(upp);
            return [goodmis][low], upp[low];
        fi:
    end:	# bruteSearch
    
    
#########################################################################
# Bezout Matrix assembly
#########################################################################
    
    blockStructure:= proc(KK::WCOMPLEX, n1::integer, n0::integer)
    local d1, d2, row, col;
        if ( n1-n0 <> 1) then ERROR(`Terms not consecutive`) fi;
        
        #compute block dimensions
        d1:=NULL;
        for row in KK:-K[n1]:-S do 
            d1:= d1, dimension(row);
        od; 
        
        d2:=NULL;
        for col in KK:-K[n0]:-S do
            d2:= d2, dimension(col);
        od;
        
#Matrix(nops(d1), nops(d2), (i,j)-> [d1[i],d2[j]] );
        [d1], [d2];
    end:#blockStructure
    
    
# Determinant of the discrete Jacobian wrt 
    Jdiscr := proc(lp::list, vx::list)
    local N,i,j,k,vxi,s, mtr, mtr2;
        
        N := nops(lp);
        if nops(vx) <> N-1 then print(nops(lp), vx );
            ERROR(`The number of polynomials must be the number of variables +1 `);
        fi;
        mtr := Array(1..N,1..N);
        for i from 1 to N do mtr[i,1] := lp[i] od;
        
        for j from 2 to N do
#print( cat(_,vx[j-1]) );
            for i from 1 to N do
                mtr[i,j]:= subs(vx[j-1]= cat(_,vx[j-1]) ,mtr[i,j-1]); ## vy[j-1]
            od;
        od;
        
#print(mtr);
        
        mtr2 := Array(1..N,1..N);
        for i from 1 to N do mtr2[i,1] := lp[i] od;
        
        for j from 2 to N do
#print( cat(_,vx[j-1]) );
            for i from 1 to N do
                #mtr2[i,j] := quo(mtr[i,j]-mtr[i,j-1], cat(_,vx[j-1]) - vx[j-1], cat(_,vx[j-1]));
#       mtr2[i,j] := expand( simplify((mtr[i,j]-mtr[i,j-1])/(cat(_,vx[j-1]) - vx[j-1])) );
                mtr2[i,j] := (((mtr[i,j]-mtr[i,j-1])/(cat(_,vx[j-1]) - vx[j-1])) );
            od;
        od;
        
#print(mtr2);
        mtr2 := expand(simplify(mtr2) );
#print("J=", mtr2);
        
        Determinant(convert(mtr2,Matrix));
    end:
    
### Bezoutian block of S(sp1)->S(sp2)
    BezoutianPoly:= proc(f,sp1::Vector,sp2::Vector,nis::Vector,var, grp:={} )
    local i,j,row,col, nvar, nvars, ovar, ovars, Bpol, mat;
        
        if grp={} then grp:={seq(1..nops(var))} fi;
        
        nvar:=NULL; ovar:=NULL;
        for i to nops(var) do
#  for i from nops(var) to 1 by -1 do
            if member(i,grp) then
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
        
#  print( collect(Bpol, [op(ovars),op(nvars)], distributed) );
        
        row:= [monbasis(nis,sp1, nvar)];
        col:= [monbasis(nis,sp2, ovar)];
        
#  print(Sdim(nis,sp1),Sdim(nis,sp2));
#  print(nops(row), nops(col));
#  print(sp1, row," ** ", sp2, col);
        
        nvars:= [op(allvars(nis,var)),op(nvars)];
        mat:= NULL;
        for i to nops(row) do
            for j to nops(col) do
                mat := mat, coeffof(expand(col[j]*row[i]), Bpol , nvars );
            od;
        od;
        Matrix(nops(row),nops(col),[mat]);
    end:
    
### Bezoutian block K_{1,a}->K_{0,b}
# see also http://math.rice.edu/~hargis/VIGRE/fast-computation-of-the.pdf
# see the map:
# http://www.orcca.on.ca/TechReports/TechReports/2007/TR-07-02.pdf,
# page 2
    Bezoutmat:= proc(KK::WCOMPLEX,
                     n1::integer, t1::integer, 
                     n0::integer, t0::integer, f, var)
        
    local p, pols, subsvar, n,grps, r,c, rows, cols, _u, _v, k, mat;
        
        if ( n1-n0 <> 1) then ERROR(`Terms not consecutive`) fi;
        
        n:= KK:-nv;
        grps := KK:-ng;
        p:= KK:-K[n1]:-S[t1]:-p;
        if (p - KK:-K[n0]:-S[t0]:-p <> n+1) then ERROR(`Terms not consistent`) fi;
        
        rows:=NULL;
        for r in KK:-K[n1]:-S[t1]:-C do
            cols:=NULL;
            _u:= copy(r:-mdeg);
            for k to grps do if _u[k]<0 then _u[k]:=-_u[k] - KK:-grp[k] - 1; fi;od;
#     for k to grps do if _u[k]<0 then _u[k]:=_u[k] + KK:-grp[k] + 1; fi;od;
            for c in KK:-K[n0]:-S[t0]:-C do
                _v:= copy(c:-mdeg);
                for k to grps do if _v[k]<0 then _v[k]:=-_v[k] - KK:-grp[k] - 1; fi;od;
#        for k to grps do if _v[k]<0 then _v[k]:=_v[k] + KK:-grp[k] + 1; fi;od;
                if c:-fis subset r:-fis then
                    pols:= r:-fis minus c:-fis;
                    subsvar:= r:-exp minus c:-exp; # partial Bezoutian
                    mat:= BezoutianPoly( [seq(f[k],k=pols)] ,_u, _v, KK:-grp, var, subsvar );
                    #print("Bmat:", mat);
                else
                    mat:= Matrix(r:-dim, c:-dim, 0, storage=sparse);
                fi;
                cols:= cols, mat;
            od;
            rows:= rows,[cols] ;
        od;
        Matrix([rows], storage=sparse);
    end:
    
end:#end resultant
