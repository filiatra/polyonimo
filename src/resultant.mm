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
#utils
    inputData,
# Bezout bound computations
    mBezout,
    mBezoutUnmixed,
# Generators of multihomogeneous polynomials
    makePoly,
    makeRandomPoly,
    makeSystem,
    makeRandomSystem,
    makeExtremePoly,
# Automated computation of resultant matrix
    findResMatrix,
# Brute force search
    bruteSearch,
# Complex and matrix computation based on degree vector
    makeComplex,
    printComplex,
    wcDimension,
    makeMatrix,
    makeAllMatrices,
    matrixIndex,
    makeMacaulayMap,
# Utility
    mDegree,
    allvars,
# Specific resultant formulas
    vec_macaulay,
    vec_sylvester,
    vec_1bilinear,
    vec_critical,
    vec_koszul,
    vec_koszul2,
    vec_bezout;
local
#export
# Data structures and helpers for complex
    NewCOMPLEX,
    NewCOMP,
    NewTERM,
    NewCOH,
    blockStructure,
# Polynomial manipulation
    coeffOf,
    getCoeff,
    listTerms,
    lstmonof,
    multmap,
    monbasis,
    homogenizePoly,
# Brute search helpers
    isCohZero,
    nzCohDim,
    dimKv,
    dimKpq,
    dimHq,
    Sdim,
    getTerm,
    isDeterminantal,
    isUnmixed,
    detStats,
    sortPerm,
    columnsum,
# sortFormulas -> compute all dimensions
    solveMatrixKernel,
# Matrix generator helpers
    Sylvmat,
    toDegreeVector,
    degreeBounds,
    discreteJac,
    getPerm,
    BezoutianBlock,
    Bezoutmat,
    BezToMatrix;

uses LinearAlgebra, combinat;

#statementSequence



#mFitStructure := proc(sysp::list, varp::list

#    grp --> partition of N into r groups ?
#    for k to nops(sysp) do
#        md := mDegree(sys[k],grp,var,false)
#    od:

#end:


#########################################################################
# Input the system data and rename to our format
#########################################################################

# Converts to input usable from the functions
inputData := proc(_sys::list, _deg_list::list, _var_partition::list,
                  ivar::list(symbol) :=['X','Y','Z','U','V','W','S','T'][1..nops(_var_partition)])
local _i, _lm, _degm, _sysm, _r, _av, _avbefore;

    _r := nops(_var_partition);
    _lm := Vector(_r);

    for _i to _r do
        _lm[_i] := nops(_var_partition[_i]);
    od:

    _av := allvars(_lm,ivar);
    _avbefore:= ListTools:-Flatten(_var_partition, 1);
    _sysm := subs(seq(_avbefore[k]=_av[k], k=1..nops(_av)), _sys);
    _degm := Matrix(ArrayTools:-Alias(Matrix(_deg_list),[_r,nops(_sys)],Fortran_order) );

    _lm, ivar, _degm, _sysm;
end:



# Renames variables to _var_partition TODO
#outputData := proc(_sys::list, , _var_grp::list, _var_partition::list)


#########################################################################
# WCOMPLEX data structure
#########################################################################

# K_{*}
    NewCOMPLEX := proc(_grp::Vector, _deg::Matrix, _mvc::Vector, _fill::boolean := false)
        local n1, KK, i, tp, tv := NULL;
         n1 := ColumnDimension(_deg);
        if Dimension(_mvc)<>Dimension(_grp) then
            ERROR(`Wrong dimensions in degree vectors.`); fi;

        return Record('nv'=convert(_grp,`+`), 'ng'=Dimension(_grp),
                      'grp'=_grp, 'deg'=_deg, 'mvc'=_mvc,
                      'K'= Array(-n1-1..n1) );
    end:

# K_{v}
    NewTERM := proc(_v::integer, _n::integer)
        return Array(max(0,_v).._n+min(1,_v), datatype=Or(`WCOMP`,integer));
    end:

# K_{p,q}, v=p-q
    NewCOMP := proc(_C::list(WCOH) := [])
        return _C;
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

# Dimension of complex terms
    wcDimension := overload(
        [
            proc(a::WTERM) option overload;
            local v, res := 0;
                for v in rtable_elems(a) do
                    res := res + wcDimension(rhs(v));
                od:
                return res;
            end,

            proc(b::WCOMP) option overload;
            local v, res := 0;
                for v in b do
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

#Multidegree with respect to vector nis (variables are first unfolded if unfold=true)
    mDegree := proc(g, nis::Vector, var, unfold::boolean := true )
    local deg, i, _cnt;
        deg:=NULL;
        if (unfold) then
            for i to nops(var) do
                deg:=deg, degree(g, [seq(var[i][k], k=1..nis[i] )] );
            od;
        else
            _cnt := 1:
            for i to nops(var) do
                deg:=deg, degree(g, var[_cnt.._cnt+nis[i]-1] );
                _cnt := _cnt + nis[i];
            od;
        fi:
        [deg];
    end:

# Plain Sylv: solveMatrixKernel(M,v[2]);
#
# Note: values to reciprocals should be considered false
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
    vec_critical:= proc(nis::Vector, dis::Matrix)
    local grps := Dimension(nis);
        add(Column(dis,i),i=1..ColumnDimension(dis)) - nis - Vector(grps,1);
    end:

# Macaulay matrix degree vector
    vec_macaulay:= proc(nis::Vector, dis::Matrix)
        # differs by one from the critical degree..
        add(Column(dis,i),i=1..ColumnDimension(dis)) - nis;
    end:

# Degree vector for unmixed Sylvester matrix
# we use the permutation prm (identity by default)
# Dual counterparts are not considered
    vec_sylvester := proc(nis::Vector, dis::Matrix,
                          prm::list:=[seq(1..Dimension(nis))])
    local grps, i, mis, s;

        grps := Dimension(nis);
        if not isUnmixed(nis,dis) then return []; fi;
        for i to grps do
            if min(nis[i], dis[i,1])>1 then return []; fi:
        od:

        s:= 1:
        mis:=Vector(grps);
        for i to grps do
            s := s + nis[prm[i]];
            # add(dis[prm[i],r],r=s..s+nis[prm[i]])
            mis[prm[i]] := s * dis[prm[i],1] - nis[prm[i]];
        od;
        mis;
    end:

# Degree vector for bivariate Koszul matrix
    vec_koszul2:= proc(nis::Vector, dis::Matrix, ind::integer:=1)
        local n1 := ColumnDimension(dis);
        if ind=1 then
            RETURN(Vector([add(dis[1,i],i=1..n1)-1, -1 ]) );
        fi:
        if ind=2 then
            RETURN(Vector([-1, add(dis[2,i],i=1..n1)-1 ]) );
        fi:
        0;
    end:

# Degree vector for Koszul matrix
# Dual counterparts are not considered
    vec_koszul:= proc(nis::Vector, dis::Matrix,
                      prm::list:=[seq(1..Dimension(nis))])
    local k, t, grps := Dimension(nis), U:=Vector(grps,0), CT;
        #! dis=[1,..,1]
        CT := 1: # class CT=1,2,..,ceil((grps-1)/2)
        for k to grps do
            U[prm[k]]:= 1+add(l[prm[s]],s=1..k-1);
            # class CT
            for t to CT do U[p[t]]:=U[p[t]]-2; od:
        od:
    end:

    # Note: 3+3 duals/transposed
    vec_1bilinear:= proc( nis::Vector, i::integer := 1)
    local mis, n, d, s;
        n:= nis[1]+nis[2]:
        d:=Vector([1,1]):
        s:= Vector([seq(1,k=0..n)]):

        if i=1 then
            mis := Vector([1,nis[1]+1]);
        else if i=2 then
                 mis := Vector([nis[2]+1,1]);
             else # i=3
                 mis := Vector([-1,nis[1]+1]);
             fi:
        fi:
        mis;
    end:

    vec_bezout := proc(nis::Vector, dis::Matrix)
        local pp, mv, i, j, v, t, n1:=ColumnDimension(dis), r := RowDimension(dis);

        # Consider permutation n1,...,nr of nis
        # consider permutation d0,...,dn of dis

        mv := Vector(r):
        pp := Vector(r):

        t := utility:-first_perm(n1):
        while t<>NULL do #print("t",t);

            v := utility:-first_perm(r ):
            while v<>NULL do #print("v",v);

                for i to r do
                    pp[i] := # i.e. nis[1]+..+nis[i]
                    add(`if`(v[k]<=v[i], nis[k], 0), k=1..r);

                    mv[i] := -nis[i] + add(dis[i,t[k]],k=1..pp[i]+1) - 1;
                od:

                print(convert(mv,list));

                v := utility:-next_perm(v);
            od:
            t := utility:-next_perm(t);
        od:

    end:

# Mixed bilinear system
# ...

#########################################################################
# Dimensions
#########################################################################

# Bezout bound
    mBezout:= proc(nis::Vector, dis::Matrix, j::integer := -1)
    local k, fct, grps,n, dd;

        n:=ColumnDimension(dis)-1;
        grps := Dimension(nis);
        if [grps,n+1] <> [Dimension(dis)] then ERROR(`BAD DIMS ! `) fi;

        # Note: factorial corresponds to Prod(vol(Simplex_k)).
        # Formula generalizes to arbitrary products of "sparse Newton
        # polytopes" (not multihomogeneous anymore) by changing thi
        # factor to Prod(vol(Polytope_k)), see Emiris-Vidunas 2014.
        fct := mul(factorial(nis[k]), k=1..grps);

        if grps=n then dd:=dis; else
            # Expand the degree matrix
            # This is  McLennan'99 permanent formula for general case
            dd:= Matrix(< seq(seq(dis[m,..],i=1..nis[m]),m=1..grps) >);
        fi:

        # Note: maple computation of permanent in Maple might be
        # slow. Ryser'1963 seems to be the state of the art, also
        # using Gray codes

        if j=-1 then# Total degree of resultant
            RETURN( add( Permanent(DeleteColumn(dd,i)),i=1..n+1) / fct);
        else# Number of solutions of square system (ie. without f_j)
            RETURN( Permanent(DeleteColumn(dd,j)) / fct );
        fi:
    end:

# Unmixed and Scaled Bezout bound
    mBezoutUnmixed:= proc(nis::Vector, dis::Vector,
                          sis::Vector := Vector([seq(1,i=1..1+Dimension(nis))]) )
    description "Unmixed and Scaled Bezout bound";
    local grps,n;
        n:=ColumnDimension(dis)-1;
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
        n:= ColumnDimension(dis)-1;
        dimK := 0;
        for p from max(0,Nu) to min(n+1,Nu+n) do
            dimK := dimK + dimKpq(nis,dis,mis,p,p-Nu);
        od:
        eval(dimK);
    end:# dimKv

#### Dimension of Kpq
    dimKpq:= proc(nis::Vector, dis::Matrix, mis::Vector,
                  p::integer,q::integer)
    local c,Kvp,grps,dim,k,v, n1:= ColumnDimension(dis);
        grps:=Dimension(nis);
        dim:=0;
        c := utility:-first_comb(n1,p);
        while c<>NULL do
            v := mis - columnsum(dis,c);
            dim:=dim + dimHq(nis, v, q);
            c := utility:-next_comb(c,n1);
        od:
        RETURN(dim);
    end:# dimKpq

# Dimension of H^q(mpd)
    dimHq := proc(nis::Vector, mpd::Vector, q::integer)
    local i, k:= 1, dim:=1;
        if isCohZero(nis,mpd,q) then return 0;
        else return nzCohDim(nis,mpd); fi:
    end:

# Returns the q if a non-zero term K_{p,q} exists, or -1 otherwise
    getTerm := proc(nis::Vector, mm::Vector, pd::Vector)
    local i, qq::integer := 0;
        for i to Dimension(nis) do
            if mm[i] + nis[i] < pd[i] then
                qq:= qq + nis[i];
            else
                if mm[i] < pd[i] then
                    return(-1);
                fi:
            fi:
        od;
        return(qq);
    end:

# Check for vanishing of H^q(mpd)
    isCohZero := proc(nis::Vector, mpd::Vector, q::integer)
    local i, qq::integer := 0;
        #qq := add(`if`(mpd[i] < -nis[i], nis[i], 0), i=nis);
        #qz := add(`if`(mpd[i] < 0, nis[i], 0), i=nis);
        #return q==qq and q==qz
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

# Dimension of a non-zero H^q(mpd)
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
    local n1, p, c, mmd, q, kfirst::integer, klast::integer, i, Kv, KK, tmp := NULL;

    KK := NewCOMPLEX(nis,dis,mis);
    n1 := ColumnDimension(dis);

    for p from 0 to n1 do
        c := utility:-first_comb(n1,p);
        while c<>NULL do
            mmd := columnsum(dis,c):
            q:= getTerm(nis, mis, mmd);
            if q<>-1 then
               if KK:-K[p-q]    = 0 then KK:-K[p-q]:= NewTERM(p-q,n1-1); fi:
               if KK:-K[p-q][p] = 0 then KK:-K[p-q][p]:= NewCOMP();      fi:
                  KK:-K[p-q][p]:= [op(KK:-K[p-q][p]),
                  NewCOH(convert(c,set), nis, Add(mis,mmd,1,-1), nis)];
            fi:
            c := utility:-next_comb(c,n1);
        od:# while c
    od: #for p
    return KK;
    end:

### Print the complex
    printComplex:= proc( KK::WCOMPLEX, plevel::integer := 1)
    local h, u, k, d1, d2, v, p, sum;

        unassign('K');

        if plevel=0 then
            sum:= 0, " ---> ";
            for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
                sum:= sum, K[ lhs(v) ], "--->";
            od;
            print( sum, 0 );
            return;
        fi:

        if plevel=1 then
            for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
                sum:=0;
                for p in rtable_elems(rhs(v)) do
                    sum:= sum +  K[lhs(p),
                                   lhs(p)  -  lhs(v) ] ; # K_{p,q}, q=p-v
                od;
                #if (sum<>0) then print( K[ lhs(v) ]= sum ); fi:
                print(K[ lhs(v) ]= sum  );
            od;
            return;
        fi:

        if plevel=2 then

            for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
                sum:=1;
                for p in rtable_elems(rhs(v)) do
                    for h to nops(rhs(p)) do
                        u:= rhs(p)[h]:-mdeg;
                         sum:= sum* H[lhs(p)-lhs(v)]( seq(u[i], i=1..KK:-ng) );
                    od;
                od;
                #if (sum<>1) then print( K[ lhs(v) ]= sum ); fi:
                print(K[ lhs(v) ]= sum  );
            od;
            return;
        fi:

        if plevel=3 then
            unassign('S');
            for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
                sum:=1;
                for p in rtable_elems(rhs(v)) do # ( K_{1,1} , K_{1,2} , .. )
                    for h to nops(rhs(p)) do
                        u:= rhs(p)[h]:-mdeg;
                        sum:= sum*S( seq(`if`(u[i]<0, cat(-u[i]-KK:-grp[i]-1,_), u[i] ), i=1..KK:-ng) );
                    od;
                od;
                #if (sum<>1) then print( K[ lhs(v) ]= sum ); fi:
                print(K[ lhs(v) ]= sum  );
            od;
            return;
        fi:

        if plevel=4 then
            #sum:= 0, " ---> ";
            #for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
            #    d1, d2 := blockStructure(KK,lhs(v),lhs(v)-1);
            #    sum:= sum, Matrix(nops(d1), nops(d2), (i,j)-> [d1[i],d2[j]]), "--->";
            #od;
            #print( sum, 0 );
            #return;
            d1, d2 := blockStructure(KK,1,0);
            print( Matrix(nops(d1), nops(d2), (i,j)-> [d1[i],d2[j]]) );
            return;
        fi:

        # exterior alg.
        if plevel=5 then
            for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
                sum:=1;
                for p in rtable_elems(rhs(v)) do # ( K_{1,1} , K_{1,2} , .. )
                    for h to nops(rhs(p)) do
                        #u:= copy(rhs(p)[h]:-mdeg);
                        #for k to KK:-ng do if u[k]<0 then u[k]:=u[k] + KK:-grp[k] + 1; fi; od:
                        # note: degree 0 is not distingushed for primal/dual
                        sum:= sum *
                        # (Lambda^(rhs(p)[h]:-fis))[op(rhs(p)[h]:-exp)];
	                   Lambda^(rhs(p)[h]:-fis);
                    od;
                od;
            print( K[ lhs(v) ] = sum );
            od;
            return;
        fi:

	# All dimensions
	if plevel=6 then
		sum := NULL;
		for v in ListTools:-Reverse(convert(rtable_elems(KK:-K),list)) do
			sum := sum, wcDimension(rhs(v));
	        od;
		print(sum);
		return sum;
	fi:

        ERROR(`Print level can only be 0..6`);
    end:


#########################################################################
# Matrix assembly
#########################################################################

    # to do, minimize mBezout number, return nis, dis
    # getOptimalData := proc(sys::list, ivar::list)

    # to do
    #findResMatrix2 := proc(sys::list, ivar::list, nis::Vector := [], idis::Matrix := [])

    findResMatrix := proc(nis::Vector, dis::Matrix,
                          ivar::list(symbol) :=['x','y','z','u','v','w','s','t'][1..Dimension(nis)],
                          mis::Vector := Vector(),
                          letters::list(symbol) := ['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o'])
    local vv,vd,  KK::WCOMPLEX, sys, var::list, mvec::Vector;

        if ivar = [] then
            var:= ['x','y','z','u','v','w','s','t'][1..KK:-ng];
        else
            var:=ivar;
        fi:

        if (Dimension(mis)=0) then
            vv, vd := bruteSearch(nis,dis):

            if nops(vv)=0 then
                lprint(`No matrix found.`);
                return Matrix();
            else
                mvec := vv[-1];
                lprint("Degree vector",convert(mvec,list),"Dimension",vd[-1] );
            fi:
        else
            mvec := mis;
        fi:

        sys:= makeSystem(nis, dis, letters, var);

        KK := makeComplex(nis, dis, mvec):
        printComplex(KK,3);
        #print(matrixIndex(KK,var) );

        if _nresults = 1 or _nresults = undefined then
            return makeMatrix(KK, sys, var);
        else
            return makeMatrix(KK, sys, var), sys;
        fi:
    end:

makeAllMatrices:= proc(KK::WCOMPLEX, sysp:=[], varp:=['x','y','z','u','v','w','s','t'][1..KK:-ng])
local i, n := convert(KK:-grp,`+`), MM;
    MM:= NULL:
    for i from n to 1 by -1 do
        if KK:-K[i]<>0 then
            #mi:= matrixIndex(KK,[x], i, i-1);
            MM := MM, makeMatrix(KK,ff,varp, i,i-1);
        fi:
    od:
MM;
end:

### The Matrix K_v1 -> K_v0
    makeMatrix:= proc(KK::WCOMPLEX, sysp:=[], varp:=['x','y','z','u','v','w','s','t'][1..KK:-ng], v1::integer := 1, v0::integer := 0)
    local ddeg, sys, var, matr, row, col, rows, cols, n:= KK:-nv; #, d1, d2;

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
            for ddeg to nops(sys) do
                if mDegree(sys[ddeg],KK:-grp,var)<>convert(KK:-deg[..,ddeg],list) then
                   WARNING("Degree mismatch");
                    lprint("Equation", ddeg, "has degree",mDegree(sys[ddeg],KK:-grp,var),
                          "instead of", convert(KK:-deg[..,ddeg],list)); print(sys[ddeg]);
                fi:
            od:
        fi;
        #for now demand det/al complex
#        if not ArrayNumElems(KK:-K,'NonZero')=2 then ERROR("Not Determinantal") fi;
        if v1-v0 <> 1 then ERROR("Terms not consecutive") fi;

        #compute block dimensions
        #d1, d2 := blockStructure(KK,1,0);
        #print(d1, d2);

        rows:= NULL;
        for row in rtable_elems(KK:-K[v1]) do
            cols:= NULL;
             for col in rtable_elems(KK:-K[v0]) do
                ddeg := lhs(row) - lhs(col); # p1-p0 = q1 - q0 + 1
                if ddeg<=0 then
                    matr:= Matrix( wcDimension(rhs(row)), wcDimension(rhs(col)), 0, storage=sparse);
                else if ddeg=1 then
                         matr:= Sylvmat(KK, v1,lhs(row), v0,lhs(col), sys, var);
                         #print("Sylv", lhs(row), lhs(col),"-->", Dimension(matr));
                     else
                         matr:= Bezoutmat(KK, v1,lhs(row), v0,lhs(col), sys, var);
                         #print("Bez", lhs(row), lhs(col) ,"-->", Dimension(matr));
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
    local i::integer, r::WCOH, c::WCOH, _u::Vector , _v::Vector, mat::Matrix, cols, rows, grps::integer, k::integer;

        if ( n1-n0 <> 1) then ERROR(`Terms not consecutive`) fi;
        if (t1 - t0 <> 1) then ERROR(`Terms not consistent`) fi;

        grps := KK:-ng;
        rows:=NULL;
        for r in KK:-K[n1][t1] do
            cols:=NULL;
            _u:= toDegreeVector(r:-mdeg, KK:-grp);
            for c in KK:-K[n0][t0] do
                _v:= toDegreeVector(c:-mdeg, KK:-grp);
                if c:-fis subset r:-fis then
                    i:=1; while i<t1 and r:-fis[i]=c:-fis[i] do i:=i+1; od; k:=r:-fis[i];
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

### Monomials indexing the matrix of K_{v1}->K_{v0}
    matrixIndex:= proc(KK::WCOMPLEX, varp:=['x','y','z','u','v','w','s','t'][1..KK:-ng], v1::integer := 1, v0::integer := 0)
    local grps, var, _u, cols, rows, row, r, k;

        if varp = [] then
            var:= ['x','y','z','u','v','w','s','t'][1..KK:-ng];
        else
            var:=varp;
        fi:

        grps := KK:-ng;

        rows:=NULL;
        if (0<>KK:-K[v1]) then 
        for row in rtable_elems(KK:-K[v1]) do
           for r in rhs(row) do
               _u:= toDegreeVector(r:-mdeg, KK:-grp);
               rows:= rows, [monbasis(KK:-grp,_u,var)];
            od;
         od:
        fi:
        
        cols:=NULL;
        if (0<>KK:-K[v0]) then 
        for row in rtable_elems(KK:-K[v0]) do
             for r in rhs(row) do
            _u:= toDegreeVector(r:-mdeg, KK:-grp);
                cols:= cols, [monbasis(KK:-grp,_u,var)];
            od;
         od:
        fi:
        [rows],[cols];
    end:

### Matrix of multihomogeneous multiplication map
    multmap:= proc(f, sp1::Vector, sp2::Vector, nis::Vector, var::list)
    local i,j, row, col, vars, _c, _m, mat;

        row := [monbasis(nis,sp1,var)];
        col := [monbasis(nis,sp2,var)];
        vars:= allvars(nis,var);
        #print(row,col);

        _c, _m := listTerms(f, vars);

        mat := Matrix(nops(row), nops(col), storage=sparse);
        for i to nops(row) do
            for j to nops(col) do
                mat[i,j] := getCoeff(expand(col[j]/row[i]), _c, _m );
                #print(i,j,"mon:", expand(col[j]/row[i]) , " gets:", mat[i,j]);
            od;
        od;
        return mat;
#todo: return row,col ? _nresults
    end:

#########################################################################
# Polynomials
#########################################################################

###return the coeff. of p in variables var of the monomial m:
    coeffOf := proc(m, p, vars) # p::polynom(anything,var)
    local _m_list, _c_list, k;
        _m_list, _c_list := listTerms(p, vars);
        getCoeff(m, _m_list, _c_list);
    end:

    listTerms := proc(p, vars::list)
    local _m_list, _c_list;
        _c_list := [coeffs(expand(p),vars,'_m_list')];
        _c_list, [_m_list];
    end:

    getCoeff := proc(_mon, _c_list::list, _m_list::list)
    local k;
        if member(_mon,_m_list,'k') then return _c_list[k]; else return 0; fi;
    end:

#all variables, var the vector of group names, for example bihomo: [x,y]
    allvars:= proc(nis::Vector, var::list)
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
            print("nis,mdeg,var:", convert(nis,list), convert(mdeg,list),var );
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

### Make polynomial with m-degree di
    makePoly:= proc(nis::Vector,di::Vector, c, var )
    local vars, p, i, s;

        vars:=allvars(nis,var);

        i:=0;p:=0;
        s:=[monbasis(nis, di, var)];
        unassign('c');
        for i from 1 to nops(s) do
            p:= p + c[seq(degree(s[i],vars[k]),k=1..nops(vars))] * s[i];
        od;
        p;
    end:

### Make random polynomial with m-degree di
    makeRandomPoly:= proc(nis::Vector, di::Vector, var, sz:=1..100)
    local _c_list, rlist, roll, sf;
        randomize();
        unassign('c');
        sf := makePoly(nis,di,c,var);
        _c_list := [coeffs(sf,allvars(l,var))];
        roll := rand(sz);
        rlist := [seq(_c_list[k]=roll(),k=1..nops(_c_list))];
        subs(op(rlist), sf); #, rlist;
    end:

### Make extreme polynomial with degree dis
    makeExtremePoly:= proc(nis::Vector,dis::Vector, c, var )
    local v, p, i,j, vars;

        vars:= allvars(nis,var);
        p:=1;v:=1;
        for i to Dimension(nis) do
            for j to nis[i] do
                p:= p*(1+ vars[v]^dis[i] );
                v:= v+1;
            od;od;

        v:= [lstmonof(evalm(p),vars)];
        p:=0;
        for i from 1 to nops(v) do
            p:= p + c[seq(degree(v[i],vars[k]),k=1..nops(vars))] * v[i];
        od;
        p;
    end:

### Make multihomogeneous system
    makeSystem:= proc(nis::Vector, dis::Matrix,
                      coef:=['a','b','c','d','e','f','g','h','i','j','k','l','m','n','o'][1..ColumnDimension(dis)],
                      var:= ['x','y','z','u','v','w','s','t'][1..Dimension(nis)] )
    local i,n1,lst;
        n1:=ColumnDimension(dis);
        lst:=NULL;
        for i from 1 to n1 do
            lst:= lst, makePoly(nis, Column(dis,i), coef[i] ,var);
        od;
        [lst];

    end:

### Make random multihomogeneous system
    makeRandomSystem:= proc(nis::Vector, dis::Matrix,
                      var:= ['x','y','z','u','v','w','s','t'][1..Dimension(nis)], sz:=1..100)
    local i,n1,lst;
        n1:=ColumnDimension(dis);
        lst:=NULL;
        for i from 1 to n1 do
            lst:= lst, makeRandomPoly(nis, Column(dis,i), var, sz);
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
    # Short version
     option inline;
        convert([Vector(RowDimension(dis)),seq(dis[..,i],i=c)],`+`)
    # Hand-coded version
    #    s:= Vector(RowDimension(dis)):
    #    for i in c do
    #        for j to Dimension(s) do
    #            s[j] := s[j] + dis[j,i];
    #        od:
    #    od:
    #    s;
    end:

    sortPerm := proc(data)
    local i::integer, ind::list(integer) := [seq(1..nops(data))];
        sort(ind, proc(a,b) evalb(data[ind[a]]<=data[ind[b]]) end);
    end:

    isUnmixed := proc(nis::Vector,dis::Matrix)
        local p, n1;

        n1:=ColumnDimension(dis):
        for p from 2 to n1 do
           if not Equal(dis[..,1],dis[..,p]) then return false; fi:
       od:
       return true;
    end:

    isDeterminantal := proc(nis::Vector,dis::Matrix,mis::Vector)
    local n1, grps, i, p, q, c:
        grps:=Dimension(nis):
        unassign('i');
        n1:=ColumnDimension(dis):

        # Maple 16:
        #c := firstcomb[{seq(1..n+1)},p]; .. combinat[nextcomb](c,p)

        for p from 0 to n1 do
          c := utility:-first_comb(n1,p);
          while c<>NULL do
             q:= getTerm(nis,mis, columnsum(dis,c) );
             if q<>-1 and p <> q and p <> q+1 then RETURN(false) fi:
            c := utility:-next_comb(c,n1);
          od:
        od:

        RETURN(true);
    end: # isDeterminantal

    degreeBounds := proc(nis::Vector,dis::Matrix)
    local grps, low, upp, i;
        grps:=Dimension(nis):

        low := Vector(grps);
        for i from 1 to grps do
            low[i]:=  max(-max(dis[i,..]),-nis[i]);
        od:
        unassign('i');

        upp := Vector(grps);
        for i from 1 to grps do
            upp[i]:= convert(dis[i,..],`+`) - 1 + min( max(dis[i,..])-nis[i], 0);
        od;
        #print("Bounds:",low, upp);
        low,upp;
    end:

    # Discover all vectors by brute force
    bruteSearch := proc(nis::Vector,dis::Matrix)
    local cand::Vector, low, upp, result, grps, n1, p, ind, c, cnt:=1, mmd, q;
        grps:=Dimension(nis):
        n1:=ColumnDimension(dis):

	if( convert(nis,`+`)+1 <> Dimension(dis)[2]) then
	        WARNING("Not codimension 1");
	fi:

        result:=NULL;

        #compute the bounds
        low, upp := degreeBounds(nis,dis);
        # LOOSEN BOUNDS (for testing)
        #low := low - Vector(grps,2);
        #upp := upp + Vector(grps,2);
	#print("bounds: ", low, upp);

        # Impl. 1 vs 2
        #print("vec:", 2^(ColumnDimension(dis)),
        #"cand:", mul(upp[i]-low[i]+1, i=1..Dimension(low)) );

$define Impl1 1
$ifdef Impl1
# Implementation 1
    ind := Array(1..utility:-num_points(low,upp),
                 fill=true, datatype=boolean):
    for p from 0 to n1 do
        c := utility:-first_comb(n1,p);
        while c<>NULL do
            mmd := columnsum(dis,c):

            cand:= utility:-first_point(low,upp); cnt:=1:
            do
                if ind[cnt]=true then
                    q:= getTerm(nis, cand, mmd);
                    if q<>-1 and p <> q and p <> q+1 then
                        ind[cnt]:=false;
                    fi:
                fi:
                if not utility:-next_point(cand,low,upp) then break; fi: cnt := cnt+1:
            od: #while cand
            c := utility:-next_comb(c,n1);
        od:# while c
    od: #for p

    cand:= utility:-first_point(low,upp);
    cnt:=1:
     do
        if ind[cnt]=true then result := result, Copy(cand); fi:
        if not utility:-next_point(cand,low,upp) then break; fi: cnt := cnt+1:
    od:

$else

# Implementation 2
        cand:= utility:-first_point(low,upp);
        do
            # necessary condition
            #  msmall := false; mbig:=false;
            # for i from 1 to grps do
            #   if cand[i]<small*dis[i] then msmall:=true; break; fi;
            # od:#i
            # for i from 1 to grps do
            #   if cand[i] >= big*dis[i]-nis[i] then mbig:=true; break; fi;
            # od:#i

            if #msmall and mbig and
            isDeterminantal(nis,dis,cand) then
                #print("found",cand);
                result:= result, Copy(cand);
            fi;
            if not utility:-next_point(cand,low,upp) then break; fi:
        od;

$endif # impl

        if _nresults = 1 or _nresults = undefined then
             return ([result]);
        else
            upp := NULL;
            for cand in [result] do
                upp := upp, dimKv(nis,dis,cand,0);
            od:
            upp:=[upp]:
            low := sortPerm(upp);
            return [result][low], upp[low];
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
        for row in rtable_elems(KK:-K[n1]) do
            d1:= d1, wcDimension(rhs(row));
        od;

        d2:=NULL;
        for col in rtable_elems(KK:-K[n0]) do
            d2:= d2, wcDimension(rhs(col));
        od;

        #Matrix(nops(d1), nops(d2), (i,j)-> [d1[i],d2[j]] );
        [d1], [d2];
    end:#blockStructure


# Determinant of the discrete Jacobian
    discreteJac := proc(lp::list, nis::Vector, var::list,
                        vy::list, # sub. to
                        vx::list  # sub. from
                       )
    local vxs, vars, svar, ovar, svars, ovars, N, i, j, mtr0, mtr;

        vxs  := allvars(nis,vx  ); # sub. from
        vars := allvars(nis,var ); # lp-vars

        svar := NULL: ovar := NULL:
        for i to nops(vx) do
            if vx[i] <> vy[i] then
                svar:= svar, vy[i];
                ovar:= ovar, vx[i];
            else
                svar:= svar, 0;
                ovar:= ovar, 0;
            fi:
        od:
        svar:=[svar]; ovar:=[ovar];
        svars := allvars(nis,svar);
        ovars := allvars(nis,ovar);

        N := nops(lp);
        if nops(svars) <> N-1 then
            #print(nops(lp), svars );
            ERROR("The number of polynomials must be the number of variables +1", svars, nops(lp));
        fi;

        mtr0 := Matrix(N,N);
        for i from 1 to N do
            mtr0[i,1] := subs(seq(vars[k]=vxs[k],k=1..nops(vxs) ), lp[i]);
        od;

        for j from 2 to N do
            for i from 1 to N do
                mtr0[i,j]:= subs(ovars[j-1]= svars[j-1], mtr0[i,j-1]);
            od;
        od;
        #print("setup:", svar, mtr0);

        mtr := Matrix(N,N);
        mtr[..,1] := mtr0[..,1];
        for j from 2 to N do
            for i from 1 to N do
                mtr[i,j] := expand(simplify(((mtr0[i,j]-mtr0[i,j-1])
                                             /(svars[j-1] - ovars[j-1]))));
            od;
        od;
        #print("final:", mtr);

        Determinant(mtr);
    end:

    getPerm := proc(mm::Vector, deg::Matrix, grps::set)
    local tmp, i, k, n:=Dimension(mm),
        s:=Vector([seq(1..n)]), ss := false;
        #s:=Vector([seq(n-k,k=0..n-1)]);

    while (ss) do

    for k in grps do
        for i in grps do
            if  mm[k]+1 = add(deg[k,j],j=1..i) then
                s[k]:= i;
#print("s=",convert(s,list), "due to ", "k=",k,"i=", i);
            fi:
        od:
    od:
#print("perm=",convert(s,list));

od:

    if convert(s,set)<>{seq(1..n)} then
        #ERROR("Perm:",convert(s,list));
        WARNING("Perm. problem");
        print(convert(s,list));
        #s:=Vector([seq(1..n)]);        # 15/3
        s:=Vector([seq(n-k,k=0..n-1)]); # 17/1
        print("fix to", convert(s,list));
    fi:
        s;
    end:

    toDegreeVector := proc(_u::Vector, nis::Vector)
    local k, dvec::Vector := Vector(Dimension(nis));
        for k to Dimension(nis) do
            dvec[k] := `if`(_u[k]<0, _u[k] + nis[k] + 1, _u[k]);
        od;
            dvec;
    end:

    BezToMatrix := proc(Bpol, nis, rvar, cvar)
       local sp1,sp2,row,col,nvars,_c,_m,mat,i,j;

       sp1 := -Vector(mDegree(Bpol,nis,rvar));
       sp2 := Vector(mDegree(Bpol,nis,cvar));

       row:= [monbasis(nis, sp1, rvar)];
       col:= [monbasis(nis, sp2, cvar)];
       print(rvar, sp1, row, cvar, sp2, col);

       nvars:= [op(allvars(nis,rvar)),op(allvars(nis,cvar))];
       _c, _m := listTerms(Bpol, nvars );
       print(_c);print(_m);

       mat := Matrix(nops(row),nops(col));
       for i to nops(row) do
           for j to nops(col) do
               mat[i,j] := getCoeff(expand(col[j]/row[i]), _c, _m );
           od;
       od;
        #print("Det", factor(Determinant(mat)) );

       mat;
   end:

### Bezoutian block of S(sp1)->S(sp2)
    BezoutianBlock:= proc(f,hp1::Vector,hp2::Vector,nis::Vector,
                         dis::Matrix, var::list, grp::set:={2017} )
    local _c, _m, i, j, row, col, nvars, Bpol, mat, sp1, sp2, cvar, rvar;
        sp1:= toDegreeVector(hp1, nis);
        sp2:= toDegreeVector(hp2, nis);
        if grp={2017} then grp:={seq(1..nops(var))} fi;

        rvar:=NULL; cvar:=NULL;
        for i to nops(var) do
            rvar:= rvar, `if`(hp1[i]<0,cat(_,var[i]),var[i]);
            cvar:= cvar, `if`(hp2[i]<0,cat(_,var[i]),var[i]);
            #if member(i,grp) then .. else .. fi:
        od;
        rvar:=[rvar]; cvar:=[cvar];

        _c:= convert(getPerm(sp2, dis, grp),list):
        Bpol:= discreteJac(f, nis[_c], var[_c], rvar[_c], cvar[_c] );
        #print("from", rvar, "to", cvar, "perm", _c);
        #print("Bez", collect(Bpol, [x[1],y[1],_x[1],_y[1]], distributed) );
        #print("Bez deg", mDegree(Bpol,nis,rvar), "-", mDegree(Bpol,nis,cvar) );
        #print("BMAT", BezToMatrix(Bpol, nis, rvar, cvar) );

        row:= [monbasis(nis, sp1, rvar)];
        col:= [monbasis(nis, sp2, cvar)];
        #print(rvar, sp1, row, cvar, sp2, col);

        nvars:= [op(allvars(nis,rvar)),op(allvars(nis,cvar))];
        _c, _m := listTerms(Bpol, nvars );
        mat := Matrix(nops(row),nops(col));
        for i to nops(row) do
            for j to nops(col) do
                mat[i,j] := getCoeff(expand(col[j]/row[i]), _c, _m );
            od;
        od;
        mat;
    end:

### Bezoutian block K_{1,a}->K_{0,b}
# see also http://math.rice.edu/~hargis/VIGRE/fast-computation-of-the.pdf
# see the map:
# http://www.orcca.on.ca/TechReports/TechReports/2007/TR-07-02.pdf,
# page 2
    Bezoutmat:= proc(KK::WCOMPLEX,
                     n1::integer, t1::integer,
                     n0::integer, t0::integer, f, var)

    local pols, subsvar, n,grps, r,c, rows, cols, _u, _v, k, mat, ii,i;

        n:= KK:-nv;
        grps := KK:-ng;

        if ( n1-n0 <> 1) then ERROR("Terms not consecutive", n1, n0) fi;
        if ( t1-t0 <  2) then ERROR("Terms not consistent" , t1, t0) fi;

        rows:=NULL;
        for r in KK:-K[n1][t1] do
            cols:=NULL;
            for c in KK:-K[n0][t0] do
                if c:-fis subset r:-fis then
                    pols:= r:-fis minus c:-fis;
                    subsvar:= r:-exp minus c:-exp; # partial Bezoutian:
                    i:=0: for ii in c:-fis do if member(ii,r:-fis,'t') then i:=i+t; fi: od:
                    #print("p:", c:-fis, r:-fis, "sgn", i);
                    mat:= ((-1)^(i)) *
                    BezoutianBlock( [seq(f[k],k=pols)] ,r:-mdeg, c:-mdeg, KK:-grp, KK:-deg, var, subsvar );
                else
                    mat:= Matrix(r:-dim, c:-dim, 0, storage=sparse);
                fi;
                cols:= cols, mat;
            od;
            rows:= rows,[cols] ;
        od;
        Matrix([rows], storage=sparse);
    end:

#for use in makeMacaulayMap
Epick := proc (_m,_dis, _n, _d) options operator, arrow;
local j:=_n+1, i:=0;
    if _d-degree(_m) >=_dis[1,j] then i := i+1: fi:
    for j from _n to 1 by -1 do
      if degree(_m,x[j])>=_dis[1,j] then
        i := i+1:
        if i>1 then break; fi:
      fi:
    od:
return j;
end proc:

makeMacaulayMap := proc(nis::Vector, dis::Matrix, sys:=[], varp:=['x','y','z','u','v','w','s','t'][1..Dimension(nis)])
local KK, n:= convert(nis,`+`), mac := vec_macaulay(nis,dis),
    _S:= NULL, _E1 := NULL, _E0;

    KK := makeComplex(nis,dis,mac):
    mi := matrixIndex(KK,[x], 1, 0);
    
    #Get redundant rows
    mii := mi[1];
    sii := [seq({},i=1..n+1)]: sii[1]:= {seq(1..nops(mii[1]))}:
    rii := [seq({},i=1..n+1)]:
    for i from 2 to n+1 do
        for j from i to n+1 do
            rii[j]:= rii[j] union remove( _q -> degree( mii[j][_q],x[i-1])< deg[1,i-1],  {$ 1..nops(mii[j])} );
        od:
        rii[i] := sort(rii[i]):
    od:
    print("removed", seq( mii[j][convert(rii[j],list)], j=1..n+1) );

    print("Rows:", mii[1][convert(sii[1],list)]);
    c:= nops(mii[1]): #shift indices
    for i from 2 to n+1 do
        sii[i]:= {seq(1..nops(mii[i]))} minus rii[i];
        print("Rows:", mii[i][convert(sii[i],list)]);
        #rii[i]:= rii[i] +~ c;
        sii[i]:= sii[i] +~ c;
        c:= c + nops(mii[i]):
    od:

    print("Cols:", mi[2][1]);

    mii := mi[2][1]:
    erii := [seq({},i=1..n+1)]:
    ecii := NULL;
    for i to nops(mii) do
        c := Epick(mii[i],dis,n,mac[1]);
        if c<>0 then
            ecii := ecii, i;
            erii[c] := erii[c]union
            select(_q -> mi[1][c][_q]=mii[i]/(x[c]^dis[1,c]), {$1..nops(mi[1][c])});
            #print("select", seq(mi[1][c][_q]=mii[i]/(x[c]^dis[1,c]), _q=1..nops(mi[1][c])) );
        fi:
    od:
    ecii := {ecii};
    print("e-col",mi[2][1][convert(ecii,list)]);

    mii := mi[1];
    c:= nops(mii[1]): #shift indices
    for i from 2 to n+1 do
        erii[i]:= erii[i] +~ c;
        c:= c + nops(mii[i]):
    od:
    print("e-row", erii);
    
    #print( sii);
    erii := ListTools:-Flatten(map(convert,erii,list));
    ecii := convert(ecii,list);
    MM := makeMatrix(KK,sys,[x], 1,0):
    MM[ListTools:-Flatten(map(convert,sii,list)),..],
    erii, ecii;
end:


end:#end resultant
