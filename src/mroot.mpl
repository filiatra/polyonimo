##
##    Title: 	mroot - Multiple Roots and primal-dual structure
##    Authors: 	Angelos Mantzaflaris <Firstname.Lastname@oeaw.ac.at>
##              Bernard Mourrain     <FirstnameLastname@inria.fr>
##
## 2010-2012
## See A.M. & B.M., `Deflation and Certified Isolation of Singular
## Zeros of Polynomial Systems`
##
## Last Modification: 7/2012
##
## ----------------------------------------------------------------------


#
# The module mroot
#
mroot := module()

export
#local
# Deflation
deflate, deflate_lin, deflate_incr, deflate_lvz,
deflate_only, deflate_hint,
new_system0,new_system,new_system1,new_system2,
deflate_system,new_system4,
get_system,
pert_poly, pert_system, pert_point,
#Newton's method
newton, newton_mod,
newton_next, newton_step,
#Combinatorics
first_comb, next_comb,
first_mon, next_mon,
mac_dim, int_dim,
#Interval arithmetic operations
mat_add,mat_sub,mat_prod,
eval_on_ints,istart,iend,
X_xs,i_box,mbox,dom_size,
dom_center, inclusion,
# Operations on polynomials
coeffof,lstcoefof, lstterms,
lstmonof, lstmonsof,exp_of,
dual_monomial, add_noise,
diff_poly, diff_system,
#Operations on matrices
dmatrix2diffs, matrix2polys, matrix2diffs,
rmaximal_minor, cmaximal_minor,
nkernel, ncorank, m_inverse,
# Operations on differentials
has_term, add_df, sadd_df, sub_df,
remove_zero,sremove_zero,
to_function,
to_polynomial,to_monomial,
refine_basis, symb_diff,
int_df, diff_df,
scalar_df, coefmatrix,
add_var, symbolic_dual,
parametric_basis,
generic_dual,
unify_coef, uadd_var,
# lex-ordering on differentials
rlex_c,grlex_c,grlex_df,lex_c, lex_df,
rlex_min,total_deg, leading_df, trailing_df,
# Operations in the quotient
normal_form, mult_table, mult_mat,
# Dual Basis computation
macaulay_block, cand_set,
macaulay_step, mourrain_step, mourrain_parametric,
# Auxiliary
check_list, get_var, rump,
sign_of, app_funct,
#Tests
bench_systems, run_tests,
cyclicn, kssn, expmultn,
#Experimental
make_basis_pair,
dual_constraints_1, closedness_equations,
delta,
CoeffsOfLinComb, PolyLinearComb, set_coeff,
parametric_mult_table;

export
# rev-lex compare on differentials
rlex_df,
# Topological degee computation
topological_degree,
# Implicit curve branches computation
curve_branches,
# Certify root in domain
certify_root,
# Compute primal-dual orthogonal pair
basis_pair,
# Apply Rump's test
rump_test,
rump_iter,
#Macaulay's method
macaulay0,
macaulay,
# Integration method
mourrain0,
mourrain,
hilbert_func
;

option package;

use LinearAlgebra in


CoeffsOfLinComb:= proc( L::list(polynom), V::set(name):= indets(L, And(name, Not(constant))) )
local c, k, C:= {c[k] $ k= 1..nops(L)},
    S:= solve({coeffs(expand(`+`((C*~L)[])), V)}, C),
    F:= indets(rhs~(S), name) intersect C=~1;
    eval([C[]], eval(S,F) union F);
end proc:

PolyLinearComb:= proc(F::list(polynom), f::And(polynom, Not(identical(0))),
                      V::set(name):= indets([F,f], And(name, Not(constant)))  )
local C:= CoeffsOfLinComb([f, F[]], V);
    if C[1]=0 then (false, []) else (true, -C[2..] /~ C[1]) end if
end proc:


delta:= proc(i::integer, j::integer)
if i=j then return 1; else return 0; fi;
end:

##
## Deflation by perturbation of the system
##
deflate := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local i,k,j, n, AA, DD,N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    DD,AA:= basis_pair( expand(f),var,z,tol ) ; # compute dual basis
    #DD,AA:= mourrain( expand(f),var,z,tol ) ; # compute dual basis
    #print("Basis Pair:", to_polynomial(DD), AA ) ;
    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N:= new_system(  expand(f),var, z, per, DD, AA ); #make perturbed system

    J2:=VectorCalculus:-Jacobian( N[1], var ) ; # compute Jacobian
    J2:= subs(
        seq(N[2][i]=z[i],i=1..n),
        seq(N[2][i]=0,i=n+1..nops(N[2])  ), J2);

    #print(N[1]);
    #print(Matrix(<N[1]>),N[2]);
    #print(`J=`, J2 );
    #print(rmaximal_minor(J2), n );

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind + [seq(n,i=1..n)] ;
    else
        ind:= rmaximal_minor(J2,tol)+ [seq(n,i=1..n)]; # reduntant columns
    fi;
    print(`Rows:`,ind-[seq(n,i=1..n)]);
    #print(`Removing vars:`, N[2][ind] );
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );


    J1:= VectorCalculus:-Jacobian( N[1], N[2] );# compute augmented jacobian
    #print(J1);

    J1:= VectorCalculus:-Jacobian(
        subs(seq(N[2][ind[j]]=0,j=1..n), N[1]),
        subsop(seq( ind[j]=NULL,j=1..n),N[2]) );# compute jacobian

    #print(J1);
    print(`det`,evalf(
          subs( seq(N[2][i]=z[i],i=1..n),
                seq(N[2][i]=0,i=n+1..nops(N[2]) ),
                Determinant(J1)
              )));

subs(seq(N[2][ind[j]]=0,j=1..n), N[1]), subsop(seq( ind[j]=NULL,j=1..n),N[2]);
end:

##
## Deflation by LVZ/Zheng
deflate_lvz := proc( f::list, var::list, z::list, tol:=0 , v::symbol:=`a`)
local k,n, A, DD,N, J,Jev, rnum, vvars, i, R, rk ;
    n:=nops(var);

    unassign(v);
    vvars:= [seq(v[k],k=1..n)];
    rnum:= rand(1..100):

    J  :=VectorCalculus:-Jacobian( f, var ) ; # compute Jacobian
    Jev:= subs(seq(var[i]=z[i],i=1..n), J );
    rk := ncorank( Transpose(Jev) ); #default tolerance
    #print(Jev);

    A:= J . Matrix(<vvars>);
    A:= convert(A[..,1],list);

    R:=NULL;
    #print(rk);
    for i to rk do
        R:= R, ( Matrix([seq(rnum(),i=1..n)]) . Matrix(<vvars>) )[1,1];
    od;
    R:= [R];
    R[1]:= R[1] - 1;

[op(f),op(A), op(R) ], [op(var),op(vvars)];
end:


##
## Deflation by incremental dual computation
## (under construction)
deflate_incr := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local t, t1, i, n, BB, DD,N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(a, 1 .. nops(f))];

    # Compute D_1
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    BB:=[1];
    DD:= mourrain_step( expand(f),var,z,[DD], tol,BB ) ; # compute dual
    t:= coefmatrix(DD,var);
    t1:= cmaximal_minor( t[1], tol );
    BB:= t[2][t1] ; # corresponding primal

    print(`Computed:`, to_polynomial(DD), BB ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    for i to nops(DD) do
        print(to_polynomial(
            symbolic_dual(DD[i], cat(`a`,i) )
             ) );
    od;

DD;
end:

#
# Replaces coefficient of a dual element with variables ai
#
add_var := proc ( df::Matrix, _aa:= `a` )
    local n,m,un,j,sd ;

    n,m:= Dimension(df);
    sd:= copy(df);
    for j to m do
        sd[n,j]:= sd[n,j]*_aa;
        od;
sd;
end:

uadd_var := proc ( df::Matrix, aa:= `a` )
    local aav, n,q,un,j,sd ;

    n,q:= Dimension(df);
    sd:= copy(df);
    #sd:=unify_coef(sd,m,vars);
    aav:= [cat( aa, 1..q)];

    for j to q do
        sd[n,j]:= aav[j];
    od;
sd;
end:


#
# generic_dual
#
generic_dual := proc(dp::integer,n::integer,  aa:= `a` )
    local s,sd,c,rows,t1,t2,tt1,tt2,p,k, res,
    var, CC, SS, t, Ev, DD,un, i,j, lv;

    unassign(aa);
    var:= get_var(n);

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    DD:=[];
    SS:=NULL;

    for j to dp do

        # Base variable name for depth j
        lv:= aa; #cat(aa,j);

        # Get candidate set
        DD:= cand_set( [Ev, SS] ) ;

        # Add properly variables
        un:=[ seq(lv[k], k=1..nops(DD) )];
        t:= Matrix(n+1,1):
        for i to nops(DD) do
            DD[i]:= add_var(DD[i], un[i]);
            t:= sadd_df(t, DD[i]);
        od;
        SS:= SS, t;
    od;

    SS:= [Ev, SS] ;

   #### Compute Conditions (i)
    s := nops(DD);
    sd:= nops(SS)-1;

    c:=first_comb(n,2);
    rows:=NULL;
    while c <> NULL do
        t1:=[ seq(diff_df(SS[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(SS[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        p:=0;

        for k to sd do
            p:= p + un[(c[1]-1)*sd + k] * tt1[k]
            - un[(c[2]-1)*sd + k] * tt2[k];
        od;
        #print(lstcoefof(p,var) ) ;

        c:=next_comb(c,n);
    od;#all combinations

    #print("symbolic_dual_OUT:", SS);
[SS[-1], [lstcoefof(p,var)]] ;
end:



# Sets the coefficient of monomial mm of df to some value
set_coeff := proc(df::Matrix, mm::list, _val)
    local n,m,j,sd ;

    n,m:= Dimension(df); n:=n-1:
    sd:= copy(df);
    for j to m do
	if convert(sd[1..n,j],list)=mm then
	  sd[n+1,j]:= _val;
        fi:
    od;
sd;
end:

#
# symbolic_dual
#
symbolic_dual := proc(n::integer, BB)
    local s,sd,c,rows,t1,t2,tt1,tt2,p,k, res, DDq, ccond:=NULL, #EX, _ex,
    Bor:=NULL, H, var, SS, SSq, t, Ev, DD,un, i,j, lv, q, _b := 1;

    H := hilbert_func( BB );

    var:= get_var(n);
    #EX := exp_of(BB,convert(indets(BB),list));

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    DD:=[];
    SS:=NULL;

    lv :=[a,b,g,h,l,o,q,r,t,u,v,w]:

    SS := Ev;
    p:=0;
    ce := 0:
    for j from 2 to nops(H) do

        # Get candidate set
        DD:= cand_set( [SS] ) ;

        #Remove elements of BB ..
#        for _ex to nops(EX) do
#            for i to nops(DD) do
#        	DD[i]:= set_coeff(DD[i], EX[_ex], 0);
#        od:od:
        
        #print("DD",DD);

        sd:= nops([SS]);
        SSq := NULL;
        for q to H[j] do
            # Add properly variables
            #print("Element",j,q, "lower basis:", sd);

            unassign(lv[j-1]);
            un:=[ seq(lv[j-1][q,k], k=1..nops(DD) )];

            t:= Matrix(n+1,1):
            for i to nops(DD) do
                DDq:= add_var(DD[i], un[i]);
                t:= sadd_df(t, DDq);
            od;
            SSq := SSq, t;

            #### Compute Conditions (i)
            c:=first_comb(n,2);
            rows:=NULL;
            while c <> NULL do
                t1:=[ seq(diff_df([SS][j], c[2]),j=1..sd)];
                t2:=[ seq(diff_df([SS][j], c[1]),j=1..sd)];
                tt1:= to_polynomial(t1,var);
                tt2:= to_polynomial(t2,var);
                p := 0;
                for k to sd do
                    p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                          - un[ (k-1)*n + c[2] ] * tt2[k];
                od:
                ccond := ccond, lstcoefof(expand(p),var);
                c:=next_comb(c,n);
            od;#all combinations
            #print("Cond:", [lstcoefof(p,var)]);
            
            ##### Condition (iii), MM2011
            t1 := to_polynomial(t,var);
            for i from 2 to _b+H[j] do
                tt1:= coeffof(BB[i],t1,var);
                if 0<>tt1 then
                    Bor := Bor, tt1 = delta(_b+q,i);
                fi:
            od;
            #for i to H[j] do
            #    Bor := Bor , coeffof(BB[_b+q],t1,var) = delta(_b+q,i);
            #od:
        od:#q
        _b := _b + q - 1;

        SS := SS, SSq;
#        print("Curr", SS);
    od: #nops(HH)

    #print("symbolic_dual_OUT:", SS);
[SS], [Bor], [ccond]; #[lstcoefof(expand(p),var)];
end:

#
# Generates order 1 constraints as polynomial equations
#
dual_constraints_1:= proc( f::list, var::list, z::list )
local n, un, c, M, C, p;

    n:=nops(var);
    un:=[cat(`a`,1..n)];

    c:=first_comb(n,2);
    M:=Matrix(nops(f),s);
    C:=NULL;
    while c <> NULL do
        p:= un[c[1]] - un[c[2]] ;
        C:= C, p;
        c:=next_comb(c,n);
    od;
    #for c in c2 do
    #    p:= un[c[1]] - un[c[2]] ;
    #    C:= C, p;
    #od;
[C];
end:

#
# Deflate by adding linear perturbation on the equations
#
deflate_lin := proc( f::list, var::list, z::list, tol:=0, my_ind:=[],DB:=[] )
local i,k,j,n ,N, J1,J2,DD, ind, per ;
    n:=nops(var);
    #per:=[cat(e, 1 .. nops(f))];

    #DD,AA:= basis_pair( expand(f),var,z,tol ) ; # compute dual basis
    if DB=[] then
        DD := mourrain  ( expand(f),var,z,tol )[1] ;
        else
        DD:= DB;
    fi;

    #print( to_polynomial(DD), AA ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N[1], var ) ; # compute Jacobian
    J2:= subs(
        seq(N[2][i]=z[i],i=1..n),
        seq(N[2][i]=0,i=n+1..nops(N[2])  ), J2);

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind + [seq(n,i=1..n)] ;
    else
        ind:= rmaximal_minor(J2, max(1e-6,tol) )+ [seq(n,i=1..n)];
    fi;
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    print(`Rows:`, ind -[seq(n,i=1..n)] );

    N:= new_system1(expand(f),var, DD); #make augmented system


subs(seq(N[2][ind[j]]=0,j=1..n), N[1]), subsop(seq( ind[j]=NULL,j=1..n),N[2]);
end:

#
# Deflate without adding any new variables
#
deflate_only := proc( f::list, var::list, z::list, tol:=0, my_ind:=[] )
local i,k,j,w,n, AA, DD,N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    DD,AA := basis_pair ( expand(f) ,var,z, tol ) ;
    #DD,AA := mourrain ( expand(f) ,var,z, tol ) ;
    print("Basis Pair:", to_polynomial(DD), AA ) ;

    if nops(DD)=1 then
        lprint(`Warning: Simple root detected.`);
    fi;

    N, w:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N, var ) ; # compute Jacobian
    J2:= subs(seq(var[i]=z[i],i=1..n) , J2);
    #print( N, nops(N) );
    #print( J2, Dimension(J2) );

    if my_ind<>[] then #allow to choose which columbns to remove
        ind:= my_ind;
    else
        ind:= rmaximal_minor(J2, tol); # full-minor columns
    fi;
    print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    print(`Rows:`, ind );

[ seq( N[ind[j]],j=1..n) ], var;
end:

#
# Input is system f, variables var, differentials DD, and list II of indices [i,j]
# Output is DD_i f_j for all indices [i,j] in II
# to be used together with deflation_hint
#
get_system:= proc ( fsys::list,var::list,DD::list, II::list )
    local ff, c;
   # print("get_system_IN", fsys,var,DD,II);

    ff:=NULL;
    for c in II do
            ff:= ff, diff_poly(fsys[ c[2]],var,DD[c[1]])  ;
    od;

   # print("get_system_OUT:", ff);
[ff];
end:


#
# Gives you a hine (the indices) of which diffs and equations provide
# a deflated system
#
deflate_hint := proc( f::list, var::list, z::list, DD::list, tol:=0 )
local i,k,n, AA, N, J1,J2, ind, per ;
    n:=nops(var);
    per:=[cat(e, 1 .. nops(f))];

    #DD,AA := basis_pair ( expand(f) ,var,z, tol ) ;
    #DD,AA := mourrain ( expand(f) ,var,z, tol ) ;
    #print("Basis Pair:", to_polynomial(DD), AA ) ;

    #if nops(DD)=1 then
    #    lprint(`Warning: Simple root detected.`);
    #fi;

    N:= new_system2(expand(f),var, DD ); #make augmented system
    J2:=VectorCalculus:-Jacobian( N, var ) ; # compute Jacobian
    J2:= subs(seq(var[i]=z[i],i=1..n) , J2);
    #print( N, nops(N) );
    #print( J2, Dimension(J2), tol );

    ind:= rmaximal_minor(J2, tol); # full-minor columns

    #print("Diff,Poly=", seq( D[ind[k]-1 mod nops(DD)+1]*P[iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) );
    #print(`Rows:`, ind );

[seq( [ ind[k]-1 mod nops(DD)+1 , iquo(ind[k]-1,nops(DD))+1], k=1..nops(ind)) ];
end:

#
# Maximum length of a rectangular domain
#
dom_size:= proc(dom::list)
    local t,s,i;

    s:=dom[1][2]-dom[1][1];
    for i from 2 to nops(dom) do
        t:=dom[i][2]-dom[i][1];
        if t>s then s:=t; fi;
    od;
s;
end:

#
# Center of a rectangular domain
#
dom_center:= proc(dom::list)
local i;
    [seq( (iend(dom[i])+istart(dom[i]))/2 , i=1..nops(dom) )];
end:


#
#
# Certify a multiple root of the approximate system f inside dom
#
certify_root := proc( f::list,var::list, dom::list )
    local k,tol, DF, n, z;

    n:=nops(dom);
    tol:= dom_size(dom);
    z := [seq( (dom[k][1]+dom[k][2])/2, k=1..n) ];

    print(`Certify tol:`,tol,`point:`,z   ) ;

    DF:= deflate ( f  , var , z , tol , []);
    #DF:= deflate_lin( f  , var , z , tol , []);

    print(`New system size:`,nops(DF[2]) ) ;

print(
    rump_test( DF[1], DF[2], i_box(dom, nops(DF[2]), tol) )
);
DF;
end:

rump_iter := proc( f::list,var::list, xs::list, XX::list, miter:=100)
    local E, es, i ;

    i:=1;
    E:= convert( rump_test( f,var,xs,XX ), list);
    es:=xs;
    while i<miter do
        i:=i+1;
        es:=dom_center(X_xs(E,xs));
        print("Next:", es );
        print(es,E);
        E:= convert( rump_test( f,var,es,E ), list);
    od;
X_xs(E,es);
end:

#
# Apply Rump's test for a simple root close to xs in a given range XX
#
rump_test :=proc ( f::list,var::list, xs::list, XX::list )

local i,E;
    E:= rump(f,var,xs,XX);#
    print(`Inclusion:`, E );
    print(xs,XX);

    for i to nops(var) do
        if not inclusion(E[i,1],XX[i]) then
            print(`At position`,i,`:`, evalr(E[i,1]+xs[i]),evalr(XX[i]+xs[i]) );
            RETURN(false);
        fi;
        #E[i,1]:= evalr(E[i,1]+xs[i]);
    od:
print(`Inclusion made.`);
E;
end:

#
# Compute Rump's inclusion formula
#
rump := proc ( f::list,var::list, xs::list, X::list)
local j, Id, J, R, M, fev;

J:= VectorCalculus:-Jacobian(f, var);
Id:= Matrix(nops(var),shape=identity) ;

#Jacobian evaluated on X+xs
M:= eval_on_ints( var, X_xs(X,xs), J ) ;

#print(`M=`,M);
#print(f,var, J);
#print( subs( seq( var[j]=xs[j],j=1..nops(var)),J )  ) ;

    print(`det`,
          #subs( seq( var[j]=xs[j],j=1..nops(var)),J ),
      ` = `,
          Determinant(subs( seq( var[j]=xs[j],j=1..nops(var)),J )) ) ;

# Inverse of Jacobian evaluated on initial approximation

#print(`J=`, J);
#print( subs( seq( var[j]=xs[j],j=1..nops(var)),J ) ) ;
#print( Determinant(subs( seq( var[j]=xs[j],j=1..nops(var)),J )) ) ;

R:= MatrixInverse(
    subs( seq( var[j]=xs[j],j=1..nops(var)),J )  ) ;

# Evaluation of f over xs

fev:= Transpose(Matrix( subs(seq(var[j]=xs[j],j=1..nops(var)), f )  )) ;
#print(`f_ev =`, fev);
#print(`R.M =`, mat_prod(R,M));

# Rump's Formula: -R.fev + (Id-R.M).X
mat_add( -R.fev , mat_prod(  mat_sub(Id,mat_prod(R,M)),
               Transpose(Matrix(X)))  ) ;
end:


#mult := proc (f,var,z, tol:=0, comp:=rlex)
#nops( get_dbasis(f,var,z,tol,rlex) );
#end:

#
# Sets coeff of primal monomial to 1
# (not used)
#
refine_basis:=  proc(A::list, dual_basis::list, var::list )
    local RB,i,j, n,m,c,k;
    n:= nops(var);
    RB:=dual_basis;
    for i to nops(A) do
        j:=1;
        while j<= Dimension(RB[i])[2] do

            if Column(RB[i],j)[1..n]=A[i][1..n] then
                RB[i]:= scalar_df( RB[i], 1/RB[i][n+1,j] ) ;
                #break;
            fi;

            for k to i-1 do
                if Column(RB[i],j)[1..n]=A[k][1..n] then
                    RB[i]:= sub_df( RB[i],scalar_df(RB[k],RB[i][n+1,j]));
                fi;
            od;
            j:=j+1;
        od;
    od;
RB;
end:

#
# Given a monomial/list of monomials in var, computes the dual element(s).
# (not used)
#
dual_monomial := overload([

proc(var::list, A::list) option overload;
    local n,i,j,t,Dset;
    n:=nops(var);

    Dset:=NULL;
    for i from 1 to nops(A) do
        t:=Matrix(n+1,1);
        t[n+1]:=1;

        for j from 1 to nops(var) do
            t[j,1] := degree (A[i], var[j]);
        od;
        #print( A[i], t );
        Dset:= Dset, t;
    od;
[Dset];
end,

proc(var::list, A) option overload;
    local n,j,t;
    n:=nops(var);

    t:=Matrix(n+1,1);
    t[n+1]:=1;

    for j from 1 to nops(var) do
        t[j,1] := degree (A, var[j]);
    od;
t;
end
]);
#
# Replaces coefficient of a dual element with variables ai
#
symb_diff := proc ( df::Matrix, aa:= `a` )
    local n,m,un,j,sd ;

    n,m:= Dimension(df);
    un:=[cat(aa,1..m)];

    sd:= copy(df);
    for j to m do
        sd[n,j]:= un[j];
        od;
sd;
end:


#
# Get all equations
#
new_system0:= proc (f::list, var::list, dual_basis::list)
    local n, g,i,j,ff,t, fu;
    n:=nops(var);

    ff:=NULL;
    for i to nops(dual_basis) do
        for j to nops(f) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i])  ;
        od;
    od;

expand([ff]);
end:


#
# Perturbe wrt a quotient basis
#
new_system:= proc ( f::list, var::list, z::list, per::list, dual_basis::list, pr_basis)
    local pp,all, n,g,i,j,ff,t, fu;
    all:=op(var);
    n:=nops(var);

    pp,all:= pert_system( f,z, var, per , pr_basis ) ;

    ff:=NULL;
        for j to nops(f) do
    for i to nops(dual_basis) do
            ff:= ff, diff_poly(pp[j],var,dual_basis[i])  ;
        od;
    od;

[ff],all;
end:

#
# apply linear perturbation e[j,i] on equations
#
new_system1:= proc ( f::list, var::list, dual_basis::list, AA::list )
    local pp,all, n,g,i,j,ff,t, fu;
    all:=op(var);
    n:=nops(var);
    t:=nops(f);
    ff:=NULL;

    for j to t do
        #ff:= ff, f[j];
        for i from 1 to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i]) + e[j,i];
            #subs(seq(var[j]=var[j]-z[j],j=1..nops(z)), AA[j]) * e[j,i]  ;
            all:=all , e[j,i];
        od;
    od;
    ff:=[ff];
    #print(`New system is:`, Matrix(<ff>) );

ff,[all];
end:



#
# Just add equations, not variables
#
new_system2:= proc ( f::list,var::list,dual_basis::list )
    local i,j,ff ;

    ff:=NULL;
    for j to nops(f) do
        for i to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i])  ;
        od;
    od;

[ff],var;
end:

#
# Make system with dual coefficients as variables
# DD must have symbolic coefficients, BB it's dual monomial basis
#
deflate_system:= proc ( f::list,var::list, z::list, tol:= 0, ch:=[], iv:= {} )
    local J2, ind,i,j,ff , B, A, H, P, nvar, avar, v, p;

    # Compute primal-dual pair
    B, A := mourrain( f, var, z , tol);
    print("Pair: ", B, A );

    # extract hilbert function
    #H    := hilbert_func( B );
    # compute parametric dual
    P    := parametric_basis( A, B,  nops(var) ) ;
    print("Parametrized dual: ", P );

    nvar:= convert(indets(P),list);
    avar:= [op(var),op(nvar)];

    # Apply parametric dual elements to f
    ff:=NULL;
    for j to nops(f) do
        for i to nops(P) do
            ff:= ff, diff_poly(f[j],var, P[i])  ;
        od;
    od;
    ff:= simplify([ff]);
    print(ff, avar );

    # Get approximate values of the parameters
    B:= subs( seq(var[i]=z[i],i=1..nops(var) ) , ff );
    H:= NULL;
    for p in B do
        if nops(indets(p) )>0 then H := H, p; fi;
    od;
    H:= [H] ;
    v:= solve( H , convert(nvar,set) );
    print("System : ", H );
    if iv<>{} then v:= iv; fi;

    print("Initial point: ", v);


    # Approximate root of the deflated system
    p:= [op(z), op(subs( v, nvar))];

    J2:=VectorCalculus:-Jacobian( ff, avar ) ; # compute Jacobian
    J2:= subs(seq(avar[i]=p[i],i=1..nops(p)) , J2);
    print("J=", J2);

    ind:= rmaximal_minor(J2, tol); # full-minor columns
    if ch<>[] then ind:= ch; fi;

    print(`Rows:`, ind );

    [ seq( ff[ind[j]],j=1..nops(ind)) ], avar, p;
#ff;
end:


#
# Compute the dual basis given the primal basis A incrementally
# Oslo2012
parametric_basis := proc( AA::list, BB::list, n::integer, aa:= `a` )
local NZ,s,sd,c,rows,t1,t2,tt1,tt2,p,k, res,
    var, SS, t, Ev, Dl,un, i,j, lv, m, r, H, u , Dl0, v, free, R, CC, CCs;
    CCs:= NULL;

    H:= hilbert_func( BB );

    unassign(aa);
    var:= get_var(n);

    Ev:= Matrix(n+1,1): Ev[n+1,1]:=1:
    Dl:=[];
    SS:= NULL;

    j:=1;
    for u from 2 to nops(H) do

        ## Get candidate set for degree u-1
        Dl0:= cand_set( [Ev,  SS ] );

        for v to H[u] do

            #j := add(H[k],k=1..u-1) + v ; # element counter
            j := j+1;
            #print("--------------------- Element #", j, " deg=", u-1, "-------------------------");

            if  Dimension(BB[j])[2]=1 then
                t1:= BB[j];
                t1[n+1,1]:= 1;
                SS:= SS, t1;
                print("got: ", to_polynomial(t1)) ;
                next;
            fi;

            # Base parameter name for functional j
            lv:=cat(aa,j);

            ## Candidate set for element j
            Dl:= NULL;
            for k to nops(Dl0) do
                Dl := Dl, copy(Dl0[k]);
            od:
            Dl:= [Dl];

            #print('cand_set_is', Dl , un);

            ## Adding variables for dual element j to all candidates
            un:=[ seq(lv[k], k=1..nops(Dl) )];
            free:= NULL;
            t:= Matrix(n+1,1):
            for i to nops(Dl) do
                r,m:= Dimension(Dl[i]);

                # "free" variables
                if to_polynomial(Dl[i])=0 then
                    un[i]:=w[i];
                    free:= free, w[i];
                fi;

                for k to m do
                    Dl[i][r,k]:= Dl[i][r,k]*un[i];
                od;
                t:= sadd_df(t, Dl[i]);
                #fi;
            od;

            ###### Condition (i)
            #
            #print('cand_set_is', Dl , un);
            #print("Parameters:", un);

            ##  Employ condition (iii) : eliminate variables+add conditions

            R:=NULL;
            NZ:=NULL;
            c:=NULL;

            #print( Dl ) ;
            t1:= expand(add( to_polynomial(Dl[k],var), k=1..nops(Dl) ));
            #print('t1', t1, j);

            #for i from 2 to nops(AA) do
            #for i from 2 to j-v do
            for i from 2 to add(H[k],k=1..u) do
                tt1:= coeffof(AA[i],t1,var);
                tt2:= indets(tt1);

                if nops(tt2)=1 then # get nb of vars/terms of tt1
                    for k to nops(Dl) do
                        if un[k] in tt2 then   # for vv in un intersect tt2 do
                            Dl:=subs(un[k]= delta(i,j) , Dl);
                            t:=subs(un[k]= delta(i,j), t);
                            #print(un[k], "= ", delta(i,j) );
                            un[k] := delta(i,j);
                        fi;
                    od;
                else
                    if nops(tt2) > 0 then
                        # keep condition tt1
                        R:= R, tt1;
                        print('Condition', tt1 );
                    fi;
                fi;
            od; # end i

            ##############
            ##############
            t1:= to_polynomial( BB[j], var);
            t1:= [lstmonof( t1, var)];
            for i to Dimension(t)[2] do
                t2:= mul( var[s]^t[s,i],s=1..n);
                if  not member( t2, t1) then
                    if nops(t[n+1,i])=1 and not is(t[n+1,i],constant) then
                        #print( t[n+1,i], " = ", 0 );
                        un:= subs( t[n+1,i]=0, un);
                        R:= op( subs(t[n+1,i]=0, [R]) );

                        t:= subs( t[n+1,i]=0, t);
                    else
                        R:= R, coeffof(t2, to_polynomial(t,var),var);
                    fi;
                else
                    if nops(t[n+1,i])=1 and not is(t[n+1,i],constant) then
                        NZ:= NZ, t[n+1,i]<>0;
                    fi;
                fi;
            od;


            #print('cand_set_is', to_polynomial(Dl) );
            #print("Reduced parameters:", un, R);
            #print("t=", t );

            t := sremove_zero ( t );
            SS:=  SS, t;


if j-v-1>0 then

    #print(v, "SS ", SS, 1..j-v ) ;
    #print("Closedness on ", [Ev, SS[1..j-v-1]], un, var ) ;
    CC:= [ op(closedness_equations([Ev, SS[1..j-v-1] ], un, var, AA  )), R ];

    #print("NZ: " , NZ) ;

    free:= {free};
    #print("free parameters:", free);
    CC:= eliminate(CC,free)[2];
    #print("Closedness: " , CC) ;

# return conditions instead of solving
#if false then

    CCs:= solve(CC);
    print("values: ",CCs );
    if ( nops([CCs]) > 1 ) then
        print("TROUBLE, found ", nops([CCs]), "solutions :");
        print("Retry with constraints");
        CCs:= solve( [op(CC), NZ] ) ;
        print("new values: ",CCs);
        SS:= op(subs(CCs, [SS])) ;
    else
        if ( nops([CCs]) =0 ) then
            print("TROUBLE, found NO solutions :");
            print("Retry with constraints");
            CCs:= solve( [op(CC), NZ] ) ;
            print("new values: ",CCs);
            SS:= op(subs(CCs, [SS])) ;
        else
            SS:= op(subs(CCs, [SS])) ;
        fi;
    fi;
#fi;
fi;
            #if j=2 then print("got: ", to_polynomial(SS));
            #else
            #print("got: ", to_polynomial( SS[j-1]  )) ; #fi;

        od; # end u ###########################

        #print("====================   degree= ", u-1, " ==> recovered: ", to_polynomial(SS[j-H[u]..j-1]) , "=======================") ;
    od;# end v

SS:= [Ev,SS];
for k to nops(SS) do
    SS[k]:= sremove_zero (SS[k]);
od:
SS;
#SS,CC;
end:



closedness_equations := proc( SS::list, un::list, var::list, BB:= [] )
local sd, j, k, u,p, n, t1, t2, tt1, tt2, c, res;

    n:= nops(var);
    sd:= nops(SS);
    c:=first_comb(n,2);
    res:=NULL;

    #print("n=",n, "sd=", sd , "#un", nops(un) , SS ) ;

    while c <> NULL do
        t1:=[ seq(diff_df(SS[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(SS[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);

        p:=0;
        for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];

        od;

        if BB <> [] then  # improved condition (i)
            p:= convert(
                [seq( BB[u]*coeffof(BB[u],expand(p),var), u=1..nops(BB))],`+` )
        fi;

        #print("ind= ", c , "p= ", p ) ;

        res:= res, lstcoefof(p,var) ;
        c:=next_comb(c,n);
    od;#all combinations

#print("p=", p ) ;

[res];
end:

#
# Modified Newton's Method
#
# f: system, var: variales, z: approximation
# tol: requested accuracy, eps: error bound on z,
# ITER:  max iterations
#
newton_mod := proc( f::list, var::list,z::list, tol:= 0.001, eps:= 0.01, ITER:=100)
    local i,Dx, ZZ, c, DD, ind, S;
    c:=0;
    Dx:= 2*tol;
    ZZ:=z;

    DD := basis_pair ( expand(f) ,var,ZZ, eps )[1] ;
    #DD := mourrain   ( expand(f) ,var,ZZ, eps )[1] ; #Initial basis

    ind := deflate_hint(f,var,ZZ, DD, eps); #Computed once?
    S:= get_system(f,var,DD,ind); # deflated system
    print("Basis:", to_polynomial(DD) );
    print("System:", S , "Solution :", solve(S,var) );

    # Newton-Raphson Method, modified
    while evalf(max(map(abs,Dx)))>tol do
        print("------------- it", c,"----------------------");

        Dx := newton_next(S,var,ZZ,tol);
        #print(Dx);
        ZZ := ZZ - Dx;
        print("Next:", ZZ);
        c:=c+1;
        if c>ITER then
            lprint(ITER,`newton mod: iterations reached.`);
            break;
        fi;

        # Update system
        DD := basis_pair ( expand(f) ,var,ZZ, eps )[1] ;
        #DD := mourrain  ( expand(f) ,var,ZZ, eps )[1] ;# Refine basis
        ind := deflate_hint(f,var,ZZ, DD, eps); #Computed again ...
        S  := get_system(f,var,DD,ind); # Refine system
        print("Next basis:", to_polynomial(DD) );
        print("Next System:", S , seq(D[ind[i][1]]*P[ind[i][2]],i=1..nops(S)) );
        print("S solution :", solve(S,var) );

    od;

    lprint(`newton_mod: iterations:`,c);
    ZZ;
end:

#
# Newton's Method
#
newton := proc( f::list, var::list,z::list, tol:= 0.0001, ITER:=500, minITER:=1)
local allDx := NULL, Dx , ZZ, c, mDx, allRes := NULL;
    #print("Digits:", Digits, UseHardwareFloats);
    c:=0;
    Dx:= 2*tol;
    ZZ:=z;
    while ( mDx>tol or c<minITER ) do # L1 norm
        c:=c+1;
        if c>ITER then
            lprint(ITER,`newton: iterations reached.`);
            break;
        fi;

        #Dx := newton_next(f,var,ZZ,tol);
        Ji:= m_inverse(subs( seq(var[i]=ZZ[i],i=1..nops(var)),
                  VectorCalculus:-Jacobian(f,var)), tol);
        fx:= Matrix( < eval(f, [seq(var[i]=ZZ[i],i=1..nops(z))])>);
        Dx := convert( Ji . fx , list);
        mDx := evalf(max(map(abs,Dx))):
        allDx := allDx, mDx;
        allRes := allRes, MatrixNorm(fx,infinity);
        #print(Dx);
        ZZ := ZZ - Dx;
        print(Dx);
        print("Next:", ZZ, "Residual: ", mDx );
    od;
    allDx := [allDx];
    allRes := [allRes];
    #print(`Residuals:`, allDx);
    print(`Residuals:`, allRes);
    print(`Rate:`, map(ln,allDx[2..c]) /~ map(ln,allDx[1..c-1]) );
    print(`Residual Rate:`, map(ln,allRes[2..c]) /~ map(ln,allRes[1..c-1]) );


lprint(`newton: iterations:`,c);
ZZ;
end:

#
# Newton Operator
#
newton_step := proc( f::list, var::list,z::list, tol:= 0.001)
z - newton_next( f, var, z, tol);
end:

#
# Newton next update
#
newton_next := proc( f::list, var::list,_z::list, tol:= 0.001)
local i,Ji, fx;
    Ji:= m_inverse( # (pseudo-)inverse of Jacobian
        subs( seq(var[i]=_z[i],i=1..nops(var)),
              VectorCalculus:-Jacobian(f,var)), tol);
    fx:= Matrix( < eval(f, [seq(var[i]=_z[i],i=1..nops(_z))])>);
    #fx:= Matrix( < subs(seq(var[i]=_z[i],i=1..nops(_z)), convert(f, 'horner', var)) >) ;

    # Note: check digits and UseHardwareFloats options for correct computations
    #print(Ji);
    #print(_z, convert(fx,list));

convert( Ji . fx , list);
end:

#
#Compute perturbed polynomial system  wrt the elements of A
#
pert_system:= proc( f::list, z::list, var::list,per::list, A::list)
local pp, i, j, all;
    all:=op(var);
    pp:=NULL;
    for i to nops(f) do
            pp:= pp, expand( pert_poly(f[i],z,var,A,per[i])) ;
        for j to nops(A) do
        all:= all, per[i][j];
        od;
    od:
[pp],[all];
end:

#
#Compute perturbed point
#
pert_point:= proc( z::list , e:= 0.005, d::posint:= 2 )
local i,pp;
if e=0.0 then return z; fi;
pp:= RandomTools[Generate]( list( float(range=e..3*e, digits=d), nops(z) ) );
pp:= pp - [seq(2*e,i=1..nops(z)) ] ;
z+pp;
end:


#
# Perturb polynomial wrt the elements of A
#
pert_poly := proc (p, z::list, var::list, A::list, k )
local j,n,i, g;
    #print("pert_poly input", p, z );
    n:=nops(var);
    g:=p;
# add new variables
    for i to  nops(A) do
        #g:= g+ subs(seq(var[j]=var[j],j=1..nops(z)), A[i])* k[i];
        g:= g+ subs(seq(var[j]=var[j]-z[j],j=1..nops(z)), A[i])* k[i];
    od;
    #print("pert_poly output", g );
expand(g);
end:

#
# Add noise to coefficients of a polynomial system
#
add_noise := proc ( f::list, ns:=1e-3 )
local Pt,m,i, g, j;
    g:=f;
    for i to  nops(f) do
        #random numbers
        Pt:=Array(RandomTools:-Generate(
            list(float(range=-0..ns,'method=uniform'),nops(f[i]))),
                  'datatype=float[8]');
        j:=1;

        for m in f[i] do # perturbe f_i
            g[i]:= g[i] +  Pt[j]* m ;
            j:=j+1;
        od;
    od;
g;
end:

#
# Differentiate polynomial  (normalized)
#
diff_poly := proc (p, var::list, df::Matrix   )
 local s,j,i,n, g, res;
    #print("diff_poly_input: ", p, var, df);
    n:=nops(var);
    s:= Dimension(df)[2];

    res:=0;
    for j to s do
        g:=p;
    for i to n do # normalized differentiation
            g:= diff( g, [ var[n-i+1]$df[n-i+1,j] ]) / df[n-i+1,j]! ;
        od;
        res:=res + df[n+1,j]*g; #coeff times g
    od;
res;
end:

#
# Apply (normalized) functionals on system f
#
diff_system := proc ( f::list,var::list,dual_basis::list )
    local i,j,ff ;

    ff:=NULL;
    for j to nops(f) do
        for i to nops(dual_basis) do
            ff:= ff, diff_poly(f[j],var,dual_basis[i])  ;
        od;
    od;

[ff];
end:

#
# Return the indices of n independent rows of an mxn Matrix
#
rmaximal_minor:= proc( M::Matrix, tol:=0)
#print("rmax", M);
cmaximal_minor(Transpose(M), tol );
end:

#
# Returns the indices of n independent columns of an nxm Matrix
#
cmaximal_minor:= proc( M::Matrix, tol:=0)
local RR, i,j,n,m, cc;
    #print("cmaximal_minor_IN:", M );

    n, m:= Dimension(M);

    RR:= QRDecomposition( M , output = ['R'], fullspan=true);
    #print("max_minor: R=", RR, "rank=", Rank(RR), ncorank(RR));
    #RR:= ReducedRowEchelonForm(RR) ;
    #print("max_minor: R=", RR, "rank=", Rank(RR), ncorank(RR));
    #print("QR - rank: ", QRDecomposition(M, output = ['R','rank']));
    #print("redrow: ", ReducedRowEchelonForm(RR));

    #Find principal elements in RR-matrix
    cc:=NULL;
    i:=1;
    j:=1;
    while i<=n and j<=m do
        #print("(",i,j,"): ");
        #print(abs(RR[i,j]), ">", tol );
        if(abs(evalf(RR[i,j]))) > tol then #Caution for errors here!
            cc:= cc, j;
            i:=i+1;
            #else
            #    print( "reject = ", tol );# reject
        fi;
        j:=j+1;
    od;
    #print("cmaximal_minor_out:", cc );
    return [cc];
end:


##############################
# Rump's Test help functions
##############################

# Matrix Multiplication with evalr
mat_prod := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if m1<>n2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m2);
    for i to n1 do
        for j to m2 do
            for k to n2 do
                P[i,j]:= evalr(P[i,j] + evalr(A[i,k]*B[k,j]));
            od;
        od;
    od;
P;
end:

# Matrix Addition with evalr
mat_add := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if n1<>n2 or m1<>m2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m1);
    for i to n1 do
        for j to m1 do
                P[i,j]:= evalr(A[i,j] + B[i,j]);
        od;
    od;
P;
end:

# Matrix Substruction with evalr
mat_sub := proc ( A::Matrix, B::Matrix )
local P,i,j,k,n1,n2,m1,m2;
    n1,m1:= Dimension(A);
    n2,m2:= Dimension(B);

    if n1<>n2 or m1<>m2 then print("Wrong Dim");RETURN(-1); fi;

    P:= Matrix(n1,m1);
    for i to n1 do
        for j to m1 do
                P[i,j]:= evalr(A[i,j] - B[i,j]);
        od;
    od;
P;
end:

# Evaluate Polynomial Matrix on intervals
eval_on_ints:= proc( var::list ,int::list , M::Matrix )
local E, n,m,i,j;

    #print(`Eval_on_ints IN:`, var, int, M );
    n,m:= Dimension(M);
    E:= Matrix(n,m);

    for i to n do
        for j to m do
            E[i,j]:= evalr( subs( seq( var[j]=int[j], j=1..nops(var)) , M[i,j]  ) ) ;
od:
od:
E;
end:

# Compute X+xs with X interval and xs value
X_xs:= proc( X::list, xs::list)
    local i, E;
    E:=X;

    for i to nops(X) do
        E[i]:= evalr( X[i]+ xs[i]);
    od;
E;
end:

#Interval box for use in rump's test
i_box:= proc( bx::list, nvars::integer, tol:=0.01 )
local j,i,zs,n, X,cc ;
    n:= nops(bx);

    zs:= [ seq( (bx[i][1]+bx[i][2])/2, i=1..nops(bx) ),
           seq( 0, i=1..nvars-nops(bx) )     ];

    X:=NULL;
    for i to nops(bx) do
        cc:=bx[i]- [zs[i], zs[i]];
        X:= X, INTERVAL(cc[1]..cc[2]);
    od:
    X:= X, seq( INTERVAL(-tol..tol),j= nops(bx)+1..nops(zs) ) ;

#print(`i_box: `, zs );
zs ,[X] ;
end:

# Make a box around z with certain tolerance
mbox:= proc (z::list, tol:=0.02)
local j;
[seq( [z[j]-tol,z[j]+tol], j=1..nops(z))];
end:


# Return starting value of interval
istart:= proc ( a)
if whattype(a)=function then
RETURN(op( op(a) )[1]);
else
RETURN(a);
fi:
end:

# Return ending value of interval
iend:= proc ( a )
if whattype(a)=function then
RETURN(op( op(a) )[2]);
else
RETURN(a);
fi:
end:

#Checks if a is included in b
inclusion:= proc ( a, b) #a:function or number
    #print(`inclusion IN:`,a,b);
istart(a)>istart(b) and iend(a)<iend(b);
end:

########################################
########################################
## Monomial orderings on differentials
########################################
########################################
#
# Graded lexicographic order
#
lex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
# df1 <lex df2 iff the upmost nonzero entry of df2 − df1 is positive.
local n,i, df;
    df:= df2-df1;
    n:= Dimension(df1);

    if total_deg(df1) < total_deg(df2) then
        return true;
    fi;

    if total_deg(df1) = total_deg(df2) then
        for i from 1 to n-1 do
            if df[i]<>0 then
                if df[i] > 0 then
                    return true;
                else
                    return false;
                fi;
            fi;
        od;
    fi;
false;
end:
lex_df := proc ( ddf1::Matrix, ddf2::Matrix )
lex_c(leading_df(ddf1, lex_c), leading_df(ddf2, lex_c) );
end:

#
# Graded lexicographic order from the end
#
rlex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
# df1 <lex df2 iff the DOWNmost nonzero entry of df2 − df1 is positive.
local n,i, df;
    df:= df2-df1;
    n:= Dimension(df1);


    if total_deg(df1) < total_deg(df2) then
        return true;
    fi;

    if total_deg(df1) = total_deg(df2) then
        for i from n-1 by -1 to 1 do
            if df[i]<>0 then
                if df[i] > 0 then
                    return true;
                else
                    return false;
                fi;
            fi;
        od;
    fi;
false;
end:
rlex_df := proc ( ddf1::Matrix, ddf2::Matrix )
rlex_c(leading_df(ddf1, rlex_c), leading_df(ddf2, rlex_c) );
end:
rlex_min := proc ( p , var::list)
Groebner:-TrailingTerm(p, grlex(op(var) ))[2] ;
end:

#
# Returns the total degree (order) of a differential
#
total_deg := proc(df1::Vector)
local s,i;
    s:=0:
    for i from 1 to Dimension(df1)-1 do
        s:=s+ df1[i];
    od;
    s;
end:

#
# Graded order, not used anymore here.
#
grlex_c := proc ( df1::Vector, df2::Vector )
# df1, df2 are nx1 Matrix
local s1,s2,n,i, df;
    n:= Dimension(df1);

    s1:=0: s2:=0:
    for i from 1 to n-1 do
        s1:=s1+ df1[i];
        s2:=s2+ df2[i];
    od;
    if s1< s2 then
        return true;
    fi;

    # go to rlex
    if s1=s2 then
        return rlex_c(df1,df2);
    fi;
false;
end:
grlex_df := proc ( ddf1::Matrix, ddf2::Matrix )
grlex_c(leading_df(ddf1, grlex_c), leading_df(ddf2, grlex_c) );
end:

#
# leading term of differential wrt an ordering
#
leading_df:= proc( df::Matrix, compare:=rlex_c )
local t,lt,i,n,m;
    n,m:= Dimension(df);
    lt:= Column(df,1);

    for i from 2 to m do
        t:= Column(df,i);
        if not compare(t,lt) then
            lt:=t;
        fi;
    od;
lt;
end:

#
# Trailing term of differential wrt an ordering
#
trailing_df:= proc( df::Matrix, compare:=rlex_c )
local t,lt,i,n,m;
    n,m:= Dimension(df);
    lt:= Column(df,1);

    for i from 2 to m do
        t:= Column(df,i);
        if compare(t,lt) then
            lt:=t;
        fi;
    od;
lt;
end:

#
#Return the coeff. of p in variables var of the monomial m
#(from multires)
coeffof := proc(m,p,vvar)
local i,zs,lm,lc,k;
  lc := [coeffs(p,vvar,'lm')];
  lm := [lm];
  if member(m,lm,'k') then lc[k] else 0 fi;
end:

#
# Return the exponents of a monomial list
#
exp_of := proc(mm::list,var::list)
    local i,j, E , L;
    L:=NULL;
    for j to nops(mm) do
        E:=NULL;
        for i to nops(var) do
            E:= E, degree(mm[j],var[i]);
        od;
        L:= L,[E];
    od;
[L];
end:

#
# List coefficients of polynomial
#
lstcoefof := proc(p,var)
local lm,r,c;
  lm := NULL;
  r := sort(p,var,tdeg);
  while r <> 0 do
     c := tcoeff(r,var,'m');
     lm := lm, c;
     r := expand(r-c*m);
  od;
  lm;
end:

#
#List the monomials of a polynomial p in the variables var:
#(from multires)
lstmonof := proc(p,var:=indets(PP))
local lm,r,c;
  lm := NULL;
  r := sort(p,var,tdeg);
  while r <> 0 do
     c := tcoeff(r,var,'m');
     lm := lm, m;
     r := expand(r-c*m);
  od;
    #ListTools:-MakeUnique([lm]);
op(sort([lm], proc (a, b) options operator, arrow;not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
#, descending
));
end:

#
#List the monomials of a polynomial system in the variables var:
#
lstmonsof := proc(PP::list,var:=indets(PP) )
local lm,p;
    lm := NULL;
    for p in PP do
        lm:= lm, lstmonof(p,var);
    od;
    ListTools:-MakeUnique([lm]);
#sort(%, proc (a, b) options operator, arrow; not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
sort(%, proc (a, b) options operator, arrow; not Groebner:-TestOrder(a, b, tdeg(op(var))) end proc
);
end:

#
# List monomials of a differential
# (not used)
lstterms := proc(df::Matrix )
    local t,n1,i,j,A;
    n1:= Dimension(df)[1];
    A:=NULL;
    #for df in DD do
        for j to Dimension(df)[2] do
            t:=Column(df,j);
            t[n1]:=1;
            A:= A, t;
        od;
    #od;
    #sort(ListTools:-MakeUnique([A]), cat(comp, _c) );
    #sort([A], cat(comp, _c) );
    sort([A], rlex_c );
end:

#
# Check for dublicates in a sorted list
# (not used)
check_list := proc ( l::list )
local i;

    for i to nops(l)-1 do
        if l[i]=l[i+1] then
            lprint(`Warning: Dublicates in the list`);
            return false;
        fi;
    od;
    true;
end:


#
# Return a differential as an operator (to be applied on a polynomial)
#
to_function := overload([
proc( db::Matrix,var::list) option overload;
local n,m;
    #print("to_function_IN:", to_polynomial(db));

    #n is number of variables-1, m number of terms
    n,m:= Dimension(db);

    unassign(`h`);
    unapply( add( db[n,k]* mul(1/factorial(db[i,k]), i=1..n-1) *
             diff(h(op(var)), [seq(var[i]$(db[i,k]), i=1..n-1)]) #diff
                  , k=1..m) #add
                  , h); #unapply
end,

proc( db::list,var::list) option overload;
local t, FF;

    FF:= [];
    for t in db do
        FF:= [op(FF), to_function(t,var) ];
    od;
    FF;
end
]);

#
# Apply Df on function t
#
app_funct := proc( Df, t )
Df( unapply(t) );
end:

#
# Return a differential as a polynomial
#
to_polynomial := overload([
proc( db::Matrix,
var::list :=[seq(d[i],i=1..(Dimension(db)[1]-1))]) option overload;
local t,j,n,m;

    #print("to_polynomial_input:",db,var , Dimension(db[1]));
    n:=nops(var);
    #m= number of terms
    m:= Dimension(db)[2];

    t:=0;
    for j to m do
       t:= t+  db[n+1,j]*mul( var[s]^db[s,j],s=1..n);
    od;
#print("to_polynomial_Output:",t);
t;
end,

proc( db::list,
var::list :=[seq(d[i],i=1..Dimension(db[1])[1]-1)] ) option overload;
local t, FF;

    FF:= NULL;
    for t in db do
        FF:= FF, to_polynomial(t,var);
    od;
    [FF];
end
]);

#
# Return a differential with one terms as a monomial
#
to_monomial := overload([

proc( db::Vector,
var :=[seq(d[i],i=1..(Dimension(db) -1))]) option overload;
local n;
    #print("to_monomial_input:",db,var , Dimension(db));
    n:=nops(var);
    #db[n+1]*
    mul( var[s]^db[s],s=1..n);
end,

proc( db::list,
var::list :=[seq(d[i],i=1..Dimension(db[1])[1]-1)] ) option overload;
local t, FF;

    #print( var);
    FF:= NULL;
    for t in db do
        FF:= FF, to_monomial(t,var);
    od;
    [FF];
end
]);

#
#  Input: coefficient matrix A, indexing diffs NN
#  Output: Differentials induced by A's rows
#
dmatrix2diffs := proc(R::Matrix, NN::list, tol:=0)
local n,p,M, j, i, t ,s ;

    #print("to_diffs_Input:", R, NN );
    n:=nops(NN[1]);
    s:=nops(NN);

    p:=NULL;
    for j to Dimension(R)[2] do
        #M:=NULL;
        M:=Matrix(n+1,1);
        for i to s do
            if abs(R[i,j])>tol then
                #print(i, NN[i], R[i,j]);
                t:= Matrix(<op(NN[i]),R[i,j]>);
                M:=add_df(M,t,tol);
            fi;
        od;
        p:= p, Matrix([M]);
    od;
    #print("to_diffs_Output:", p );
[p];
end:

#
# Create variable list [ x[1],...,x[n] ]
#
get_var := proc (n)
local i;
[seq(x[i],i=1..n)];
end:

sturm02 := proc(n)
  [x^n-y*z,y^n-x*z,z^n-x*y]
end;

#
# Benchmark Systems
#
bench_systems := proc()
local i,k,dd, z0,z1,z2, G,v,p ;

#############################
# Systems
#############################
G:=[seq(0,k=1..14) ];
p:=[seq(0,k=1..14) ];
v:=[seq(0,k=1..14) ];

#1. cbms1:
G[1]:=[
x[1]^3 - x[2]*x[3],
x[2]^3 - x[1]*x[3],
x[3]^3 - x[1]*x[2]
];
p[1]:= [ [0, 0, 0] ,0 ];
v[1]:= get_var(nops(%[1]));

#2. cbms2:
G[2]:=[
x[1]^3 - 3*x[1]^2*x[2] + 3*x[1]*x[2]^2 - x[2]^3 - x[3]^2,
x[3]^3 - 3*x[3]^2*x[1] + 3*x[3]*x[1]^2 - x[1]^3 - x[2]^2,
x[2]^3 - 3*x[2]^2*x[3] + 3*x[2]*x[3]^2 - x[3]^3 - x[1]^2
];
p[2]:= [ [0, 0, 0], 0 ];
v[2]:= get_var(nops(%[1]));

#3. mth191:
G[3]:=[
x[1]^3 + x[2]^2 + x[3]^2 - 1,
x[1]^2 + x[2]^3 + x[3]^2 - 1,
x[1]^2 + x[2]^2 + x[3]^3 - 1
];
p[3]:=[ [0, 1, 0], 0 ];
v[3]:= get_var(nops(%[1]));

#4. decker2:
G[4]:=[
x[1] + x[2]^3,
x[1]^2*x[2] - x[2]^4
];
p[4]:= [ [0, 0], 0 ];
v[4]:= get_var(nops(%[1]));

#5. Ojika2:
G[5]:=[
x[1]^2 + x[2] + x[3] - 1,
x[1] + x[2]^2 + x[3] - 1,
x[1] + x[2] + x[3]^2 - 1
];
p[5]:=[
#[0, 0, 1],  0,
[1, 0, 0]  , 0
];
v[5]:= get_var(nops(%[1]));

#6. Ojika3:
G[6]:=[
x[1] + x[2] + x[3] - 1,
2*x[1]^3 + 5*x[2]^2 - 10*x[3] + 5*x[3]^3 + 5,
2*x[1] + 2*x[2] + x[3]^2 - 1
];
p[6]:=[
[0, 0, 1], 0
#,[-5/2, 5/2, 1], 0
];
v[6]:= get_var(3);

#7. KSS:
G[7]:=[
x[1]^2-2*x[1] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[2]^2-2*x[2] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[3]^2-2*x[3] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[4]^2-2*x[4] + x[1]+x[2]+x[3]+x[4]+x[5]-4,
x[5]^2-2*x[5] + x[1]+x[2]+x[3]+x[4]+x[5]-4
];
p[7]:= [ [1,1,1,1,1] , 0];
v[7]:= get_var(nops(%[1]));

#8. Caprasse:
G[8]:=[
-x[1]^3*x[3] +4*x[1]*x[2]^2*x[3] +4*x[1]^2*x[2]*x[4] +2*x[2]^3*x[4] +4*x[1]^2 -10*x[2]^2 +4*x[1]*x[3] -10*x[2]*x[4] +2,
-x[1]*x[3]^3+4*x[2]*x[3]^2*x[4]+4*x[1]*x[3]*x[4]^2+2*x[2]*x[4]^3+4*x[1]*x[3]+4*x[3]^2- 10*x[2]*x[4]- 10*x[4]^2+ 2,
x[2]^2*x[3] +2*x[1]*x[2]*x[4] -2*x[1] -x[3],
x[1]*x[4]^2 +2*x[2]*x[3]*x[4] -x[1] -2*x[3]
];
p[8]:= [ [ 2, -I*sqrt(3), 2, I*sqrt(3) ] , 0];
v[8]:= get_var(nops(%[1]));

#9. Cyclic nine:
G[9]:= [
x[1]+x[2]+x[3]+x[4]+x[5]+x[6]+x[7]+x[8]+x[9],
x[1]*x[2]+x[2]*x[3]+x[3]*x[4]+x[4]*x[5]+x[5]*x[6]+x[6]*x[7]+x[7]*x[8]+x[8]*x[9]+x[9]*x[1],
x[1]*x[2]*x[3]+x[2]*x[3]*x[4]+x[3]*x[4]*x[5]+x[4]*x[5]*x[6]+x[5]*x[6]*x[7]+x[6]*x[7]*x[8]+x[7]*x[8]*x[9]+x[8]*x[9]*x[1]+x[9]*x[1]*x[2],
x[1]*x[2]*x[3]*x[4]+x[2]*x[3]*x[4]*x[5]+x[3]*x[4]*x[5]*x[6]+x[4]*x[5]*x[6]*x[7]+x[5]*x[6]*x[7]*x[8]+x[6]*x[7]*x[8]*x[9]+x[7]*x[8]*x[9]*x[1]+x[8]*x[9]*x[1]*x[2]+x[9]*x[1]*x[2]*x[3],
x[1]*x[2]*x[3]*x[4]*x[5]+x[2]*x[3]*x[4]*x[5]*x[6]+x[3]*x[4]*x[5]*x[6]*x[7]+x[4]*x[5]*x[6]*x[7]*x[8]+x[5]*x[6]*x[7]*x[8]*x[9]+x[6]*x[7]*x[8]*x[9]*x[1]+x[7]*x[8]*x[9]*x[1]*x[2]+x[8]*x[9]*x[1]*x[2]*x[3]+x[9]*x[1]*x[2]*x[3]*x[4],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6],
x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]+x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]+x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]+x[4]*x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]+x[5]*x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]+x[6]*x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]+x[7]*x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]+x[8]*x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6]+x[9]*x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7],
1-x[1]*x[2]*x[3]*x[4]*x[5]*x[6]*x[7]*x[8]*x[9]
];
z1:=-1/4*(-36-16*I*15^(1/2)-4*(-163+72*I*15^(1/2))^(1/2))^(1/3)-1/4*I*3^(1/2)*(-36-16*I*15^(1/2)-4*(-163+72*I*15^(1/2))^(1/2))^(1/3):
z0:=subs(x1=z1, 6765/2584*x1-1/2584*x1^10):
z2:=3*z0-z1:
dd:= Digits:
Digits:=5:
p[9]:=[
evalf
([z0,z1,z2,z0,-z2,-z1,z0,-z2,-z1]) , 0.0001];
Digits:=dd:
v[9]:= [seq(x[i],i=1..9)];

#10. DZ1:
G[10]:= [
x[1]^4 -x[2]*x[3]*x[4],
x[2]^4 -x[1]*x[3]*x[4],
x[3]^4 -x[1]*x[2]*x[4],
x[4]^4 -x[1]*x[2]*x[3]
];
p[10]:= [ [0, 0, 0, 0] , 0];
v[10]:= get_var(nops(%[1]));

#11. DZ2:
G[11]:= [
x[1]^4,
x[1]^2*x[2] + x[2]^4,
x[3] + x[3]^2 - 7*x[1]^3 - 8*x[1]^2
];
p[11]:= [ [0, 0, -1] , 0];
v[11]:= get_var(nops(%[1]));

#12. DZ3:
G[12]:= [
14*x[1] + 33*x[2] - 3*sqrt(5)* (x[1]^2 + 4*x[1]*x[2] + 4*x[2]^2 + 2) + sqrt(7) + x[1]^3 + 6*x[1]^2*x[2] + 12*x[1]*x[2]^2 + 8*x[2]^3,
41*x[1] - 18*x[2] - sqrt(5) + 8*x[1]^3 - 12*x[1]^2*x[2] + 6*x[1]*x[2]^2 - x[2]^3 + 3*sqrt(7)*(4*x[1]*x[2] - 4*x[1]^2 - x[2]^2 - 2) ];

#13. Sturmfels
G[13]:= [ x^3-3*x^2*y+3*x*y^2-y^3-z^2, z^3-3*z^2*x+3*z*x^2-x^3-y^2, y^3-3*y^2*z+3*y*z^2-z^3-x^2];
p[13]:= [ [0, 0, 0] , 0];
v[13]:= [x,y,z];

#14. Sturmfels, B., 2002. Solving systems of polynomial equations. Number 97 in CBMS Regional Conference Series in Mathematics. American Mathematical Soc.
G[14]:= sturm02(3);
p[14]:= [ [0, 0, 0] , 0];
v[14]:= [x,y,z];

# with coeffcients rounded to 5 digits, at approximate zero
dd:=Digits;
Digits:=5;
#G[12]:= evalf(G[12]);
Digits:=dd;
p[12]:= [  [1.5055, 0.36528] , 0.0005 ];
# Exact Root: [ (2/5)*7^(1/2)+(1/5)*5^(1/2),-(1/5)*7^(1/2)+(2/5)*5^(1/2)];
#p[12]:=[ [ (2/5)*7^(1/2)+(1/5)*5^(1/2),-(1/5)*7^(1/2)+(2/5)*5^(1/2)], 0];

v[12]:= get_var(nops(%[1]));


##
## More instances
##

# Ojika87
#f1 := x[1]^2+x[2] - 3 ;
#f2 := x[1] + 1/8*x[2]^2 -3/2 ;
#z:=[1,2]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

#RumpGr-success
#f1 := x[1]^2 - x[2]^2 ;
#f2 := x[1]   - x[2]^2 ;
#z:=[0,0]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

#RumpGr-fail
#f1 := x[1]^2*x[2] - x[1]*x[2]^2 ;
#f2 := x[1] - x[2]^2 ;
#z:=[0,0]:
#ze := [0.002,0.001]:
#print(`Runing for`,[f1,f2], z+ze );
#DS:=deflate( [f1,f2]  , vars , z + ze , 0.03 );
#rump_test( DS[1], DS[2], i_box( mbox(z+ze,0.02), nops(DS[2]))  ) ;

G,p,v;
end:


#
# Run tests !
#
run_tests := proc(test::integer )
local k, RTA, Db, A, RT, i,j, G,v,p, res, DF, sol;

# Settings
Digits:= 32:
interface(displayprecision = 5):
interface(rtablesize=30):

G,p,v := bench_systems();
#print(G);
#print(v);
#print(p);

#############################
# Compute Dual Basis test
#############################
if test=1 then
#############################

lprint("Running times: macaulay0, macaulay, mourrain0, mourrain, basis_pair");

    res:=NULL;
    RTA := 0;k:=1:
    for i in [10,11,12] do
                print("--- System :",i, " --- ", p[i][1], " --- tol:", p[i][2]);
                RT:=
                [
#                time( ApaTools[MultiplicityStructure](G[i],v[i],p[i][1],p[i][2]) )
#                    time( macaulay0  (G[i],v[i],p[i][1],p[i][2] ) ) ,
#                    time( macaulay   (G[i],v[i],p[i][1],p[i][2] ) ) ,
#                    time( mourrain0  (G[i],v[i],p[i][1],p[i][2] ) ) #,
                    time( mourrain   (G[i],v[i],p[i][1],p[i][2] ) ) #,
#                    time( basis_pair (G[i],v[i],p[i][1],p[i][2] ) )
                ];
                RTA := RTA * (k-1)/k  +  RT / k ;
            print( RTA );
            res:= res, RTA;
        ##od;
    od;
fi;

#############################
# Matrix sizes test
#############################
if test=2 then
#############################

lprint("Deflation");

    res:=NULL;
    for i to nops(G) do
        print("--- System :",i, " --- ", p[i][1], " --- tol:", p[i][2]);

        #Db, A := mourrain (G[i],v[i],p[i][1],p[i][2] );

        DF:= deflate_lin (G[i],v[i],p[i][1], p[i][2]);
        sol:= fsolve(DF[1]);
        #print("Sols:", seq(sol[k][1..nops(v[i])], k=1..nops(sol)) );
        print("Sols:", sol );


    od;
fi;

#############################
# Certify root test
#############################
if test=3 then
#############################
    for i in [9]  do
        for j to nops(p[i]) do
            print("--",i,"--", p[i][j], "--");
            Db, A := mourrain(G[i],v[i],p[i][j]);
            print( nops( Db ) );
            print("Mac_Dim:", mac_dim(nops(G[i]),nops(v[i]), degree(to_polynomial(Db[-1], v[i]))+1 ) );
        od;
    od;
fi;

[res];
end:

#
# Makes Macaulay's matrix block of depth dp
# (not used)
#
macaulay_block := proc(f::list, var::list, z::list, dp::integer:=1 )
    local s,n, r, c, M, ci, mr, ri, i, t;

    n:= nops(var);
    if dp<0 then return [0]; fi;
    if dp=0 then return Matrix([0]); fi;

    r:= nops(f)*binomial(n+dp-2,dp-1);
    c:= binomial(n+dp-1,dp);
    M:= Matrix(r,c);

    r:=0: c:=0:
    ci:= first_mon( dp , n);
    while ci<>NULL do
        c:=c+1;
        mr:=0;
        ri:= first_mon(dp-1, n);
        while ri<>NULL do
            r:=r+1;
            for i to nops(f) do# f_i
                t:=diff_poly( mul(var[s]^ri[s],s=1..n)*f[i],
                              var, Matrix(<op(ci),1>) );
                M[mr + i,c]:=
                eval(t,[seq(var[s]=z[s],s=1..n)]);
            od;
            mr := mr+ i-1;
            ri:= next_mon( ri , dp-1);
        od;
        ci:= next_mon( ci , dp);
    od;
M;
end:

#
# `Integrate` a differential wrt i-th variable
#  (normalized)
#
int_df := proc( df::Matrix, i::integer)
local n,t, m, ci, j, k;

    #print("int_df_input:",df,"var",i);
    t:= copy(df);
    n:= Dimension(t)[1]-1;
    if i>n then
        lprint("Integration out of range");
        return df; fi;
    m:=Dimension(t)[2];

    for j to m do # Integrate
        t[i,j]:= t[i,j]+1;
    od;
    #print("int_df_output:",t);
t;
end:

#
# Remove terms with near-to-zero coefficient
# from a differential
#
remove_zero :=proc (df::Matrix, tol:=0 )
    local dd, n1,m,i,c ;
    #print("Remove zero IN:", df);

    dd:= copy(df);
    n1,m:= Dimension(dd);
    c:= NULL;

    for i to m do

        if abs(evalf(dd[n1,i]))<=tol then
            c:=c,i;
        fi;
#        if evalf(abs( Im(dd[n1,i])))<=tol then
#            dd[n1,i]:= Re(df[n1,i]);
#        fi;
#        if evalf(abs( Re(dd[n1,i])))<=tol then
#            dd[n1,i]:= Im(df[n1,i]);
#        fi;
    od;
    if nops([c])=0 then return dd; fi;
    if nops([c])=m then return Matrix(n1,1); fi;

DeleteColumn(dd,[c]);
end:

#
# Remove terms with EXACT zero coef
# from a differential
#
sremove_zero :=proc (df::Matrix )
    local dd, n1,m,i,c ;
    #print("Remove zero IN:", df);

    dd:= copy(df);
    n1,m:= Dimension(dd);
    c:= NULL;

    for i to m do

        if dd[n1,i]=0 then
            c:=c,i;
        fi;
#        if evalf(abs( Im(dd[n1,i])))<=tol then
#            dd[n1,i]:= Re(df[n1,i]);
#        fi;
#        if evalf(abs( Re(dd[n1,i])))<=tol then
#            dd[n1,i]:= Im(df[n1,i]);
#        fi;
    od;
    if nops([c])=0 then return dd; fi;
    if nops([c])=m then return Matrix(n1,1); fi;

DeleteColumn(dd,[c]);
end:


#
# Add two differentials, df1 + df2
#
add_df := proc (df1::Matrix, df2::Matrix, tol:=0)
    local ex, flag, t,n,i,j;
    #print(" add_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df1,Matrix(n+1,1)) then return copy(df2); fi;
    if Equal(df2,Matrix(n+1,1)) then return copy(df1); fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( t[ex,j],df2[ex,i] );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] + df2[n+1,i];
                if abs(evalf(t[n+1,j]))<=tol*.1 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([t,Column(df2,i)]);
            fi;
    od;
    #print(" add_df_Output",t);
#t;
remove_zero(t,tol); # zeros are not removed without this
end:

#
#  Add two differentials, df1 + df2 with symbolic coefficients
#
sadd_df := proc (df1::Matrix, df2::Matrix)
    local ex, flag, t,n,i,j;
    #print(" add_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df1,Matrix(n+1,1)) then return copy(df2); fi;
    if Equal(df2,Matrix(n+1,1)) then return copy(df1); fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( t[ex,j],df2[ex,i] );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] + df2[n+1,i];
                if abs(evalf(t[n+1,j]))=0 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([t,Column(df2,i)]);
            fi;
    od;
    #print(" add_df_Output",t);
t;
end:

#
# Add two differentials, df1 - df2
#
# BUG: sub_df(A,A);
sub_df := proc (df1::Matrix, df2::Matrix, tol:=0)
    local ex, flag, t,n,i,j;
    #print(" sub_df_input",df1,df2);

    n:= Dimension(df1)[1]-1;
    if Equal(df2,Matrix(n+1,1)) then return df1; fi;
    t:=copy(df1);

    ex:= 1..n;
    for i to Dimension(df2)[2] do
        flag:=false;
        j:=1;
        while j<= Dimension(t)[2] do
            #print( i,j );
            if Equal(t[ex,j],df2[ex,i]) then
                t[n+1,j]:= t[n+1,j] - df2[n+1,i];
                if abs(t[n+1,j])<=tol*.1 then
                    t:=DeleteColumn(t,j);j:=j-1;
                fi;
                flag:=true;
            fi;
            j:=j+1;
        od;
            if flag=false then
                t:=Matrix([Column(df2,i),t]);
                t[n+1,1]:= - t[n+1,1];
            fi;
    od;
    #print(" sub_df_Output",t);
t;
end:

#
# Multiply a differential by a scalar value
#
scalar_df := proc(df::Matrix, s )
    local n1,k, t;
    n1:= Dimension(df)[1];
    t:=df;
    for k to Dimension(df)[2] do
        t[n1,k]:= s * t[n1,k];
    od;
t;
end:

#
# Set coeff of dual(AA[i]) in DD[i] equal to 1
#
unify_coef := proc( DD::list, AA::list, var::list )
local Dp, res, i;
Dp:= to_polynomial(DD, var);

res:=NULL;
for i to nops(DD) do
    res:= res, scalar_df( DD[i], 1/coeffof(AA[i], Dp[i], var) );
od:

[res];
end:

#
# `Differentiate` a differential wrt variable i
#
diff_df := proc( df::Matrix, i::integer)
local n,t, m, ci, j, k;

    #print("diff_df_input:",df, to_polynomial(df), i);
    t:= copy(df);
    n:= Dimension(t)[1]-1;
    if i>n then
        lprint("Differentiation out of range");
        return df; fi;
    m:=Dimension(t)[2];

    # nullify terms of deg=0 wrt i
    ci:=NULL;
    for j to m do
        if t[i,j]=0 then
            ci:= ci, j;
        fi;
    od;#nullif
    t:=DeleteColumn(t,[ci]);
    m:=Dimension(t)[2];
    if m=0 then return Matrix(n+1,1); fi;

    for j to m do # Differentiate
        t[i,j]:= t[i,j]-1;
    od;
#    print("diff_df_output:",df,i);
t;
end:

#
# Check of the leading term of df appears as a term in LT.
# (not used)
has_term:= proc( df, LT::list)
    local s,d, i, m;
    #print("has_term_Input:", df, LT );
    d:= Dimension(df);

    for m to d[2] do
        for i in LT do
            if convert([seq(i[s]=df[s,m],s=1..(d[1]-1))], `and` )
            then
                return true; fi;
        od;
    od;
    #print("has_term_Output:", false);
    false;
end:

#
# Produce candidate set for the Integration Method
#
cand_set:= proc( DD::list )
local n, df, t, m, ci,i, j, k, L ;

    n:= Dimension(DD[1])[1]-1;
    #print(" cand_set In:", Matrix(<to_polynomial(DD)>));

    L:=NULL;

    for df in DD do
        for i to n do

            t:= copy(df);
            m:=Dimension(df)[2];
            #print(`next integration: `, d[i]);
            ci:=NULL;
            # for k from i+1 to n do # set i+1..n diffs to zero
            for k from 1 to i-1 do # set 1..i-1 diffs to zero
                for j to m do
                    if t[k,j]>0 then
                        ci:= ci, j;
                    fi;
                od;
            od;#set

            ci:=ListTools:-MakeUnique([ci]);
            if nops(ci)=m then
                t:=Matrix(n+1,1);
            else
                t:=DeleteColumn(t,ci);
            fi;

            L:= L, int_df(t,i);
            #II:= int_df(t,i);
            #if to_polynomial(II)<> 0 then L:= L, II; fi;
        od:
    od;
    #print(" cand_set In:", Matrix(<to_polynomial(DD)>),
    #      "Out:", Matrix(<to_polynomial([L])>));
[L];
end:

#
# Compute corank by SVD
#
ncorank := proc( M::Matrix, tol:=0)
    local r, i,m,n, Sv, K;
    #print("ncorank_input:", M );

    return min(Dimension(M))-LinearAlgebra:-Rank(M);

##########
    if tol=0 then # Exact computation
        return min(Dimension(M)) - Rank(M);
    fi;

    Sv:= SingularValues(evalf(M), output = [':-S'] );
    n,m:= Dimension(M);

    K:=0;
    for i to min(n,m) do

        if abs(Sv[i])<=tol then
            K:= K+1;
        fi;
    od;

    if min(n,m) < m then
        K:= K +  m - min(n,m)+1;
    fi;

    return min(n,m)-K;
end:


# PSEUDO-inverse..
#Ax=b
#x= A^-1 b


##
## Compute Matrix (pseudo-)inverse by SVD
##
m_inverse := proc(M::Matrix, tol:=1e-3)
    local m,n,U,Sv,Vt ;

    m,n := Dimension(M);

    # does both inverse or pseudo-inverse
    return LinearAlgebra:-MatrixInverse(M); #, method = 'LU', 'pseudo');

    #methodoptions=[tolerance=tol]

    U,Sv,Vt:= SingularValues(evalf(M), output = [':-U',':-S',':-Vt'] );

Transpose(Vt) .MatrixInverse(Matrix(Sv, shape=diagonal)[1..m,1..n]) . Transpose(U) ;
end:

##
## Compute Numerical Kernel using SVD
##
nkernel := proc(M::Matrix, tol:=0)
    local m,n,U,Sv,V,K,i,j;
    #print("nkernel_Input:", Dimension(M), tol );

    if tol=0 then # Exact computation
        return NullSpace(M);
    fi;

    U,Sv,V:= SingularValues(evalf(M), output = [':-U',':-S',':-Vt'] );
    V:= Transpose(V);
    n,m:= Dimension(M);

    #print("Singular values:", Sv);

    K:=NULL;
    for i to min(n,m) do

        if abs(Sv[i])<=tol then
            K:= K, V[..,i];
        fi;
    od;

    if min(n,m) < m then
        for i from min(n,m)+1 to m do
            K:= K, V[..,i]:
        od;
    fi;

    if nops([K])=0 then return {}; fi;
    #print("nkernel_Output:",nops([K]) );
    #print("nkernel_Output:", K );
[K];
end:

#####################################################################

#
# Macaulay's matrix dimension for s eq in n vars in depth dp
#
mac_dim:= proc(s::integer,n::integer,dp::integer )
    s*binomial(dp-1+n,dp-1), binomial(dp+n,dp);
end:

#
# Bound on integration method matrix dimension for s eq in n vars in depth dp
#
int_dim:= proc(s::integer,n::integer,dp::integer, mult::integer )
    #binomial(n,2)*binomial(dp-2+n,dp-2)+s, mult*(n-1)+1;
    mult*binomial(n,2)+s, mult*(n-1)+1;
end:


#
# Step in depth dp of Macaulay's method for the dual basis
#
macaulay_step := proc(f::list, var::list, z::list, dp::integer, tol:=0, BB:=[])
local s,E, n,NN,R,p,row, r, c, M, mc, j, ci, mr, k, ri, i, t;

    n:= nops(var);
    if dp<0 then return [0]; fi;
    if dp=0 then return [Matrix(<seq(0,s=1..n),1>)]; fi;

    r:= nops(f)*binomial(dp-1+n,dp-1);
    c:= binomial(dp+n,dp);
    NN:=[seq(0,s=1..n)];
    mc:=1;
    if BB<>[] then #MM2011
        c:= c-nops(BB);
        mc:=0;
        NN:=NULL;
    fi;

    M:= Matrix(r,c);
    E:= exp_of(BB,var);
    for j to dp do#depth
        ci:= first_mon( j , n);
        c:=0:
        while ci<>NULL do #order of diff(column)
            if BB<>[] and member(ci,E) ## MM2011
            then
                ci:= next_mon( ci , j);
                next;
            fi;
            c:=c+1;
            NN:=NN,ci;# keep column indices
            mr:=0;
            for  k to j do#multiplier degree+1
                ri:= first_mon(k-1, n);
                r:=0:
                while ri<>NULL do#multiplier monomials
                    r:=r+1;
                    for i to nops(f) do# f_i
                        t:=diff_poly(
                            mul((var[s]-z[s])^ri[s],s=1..n)*f[i],
                            var, Matrix(<op(ci),1>) );
                        #print(`at`,mr + i,mc + c);
                        M[mr + i,mc + c]:=
                        eval(t,[seq(var[s]=z[s],s=1..n)]);
                    od;
                    mr := mr+ i-1;
                    ri:= next_mon( ri , k-1);
                od;
            od;
            ci:= next_mon( ci , j);
        od;
        mc:= mc + c; #loop ends in c-value Ok
    od;
    c:= Dimension(M)[2];

## Condition (iii) MM2011
    c:=NULL;
    if BB <> [] then
        R:=NULL;
        c:=NULL;
    fi;

    #print("Mac. Dimension:",Dimension(M));
    R:= nkernel( M , tol);

    p:=NULL;
    for row in R do
        #M:=NULL;
        M:=Matrix(n+1,1);

        for i to nops([NN]) do
            if tol=0 or abs(evalf(row[i]))>tol then
                t:= Matrix(<op(NN[i]),row[i]>);
                #M:=M, t;
                M:=add_df(M,t, tol);
            fi;
        od;
        p:= p, Matrix([M]);
    od;
#sort([p], proc (a, b) options operator, arrow;not Groebner:-TestOrder(a, b, grlex(op(var))) end proc);
# sort([p], rlex_df ); # sorting spoils primal-dual pairs
[p];
end:

#
# Step of the Integration Method given partial dual basis DD
# and (optionally) partial standard basis BB of the quotient
#
mourrain_step := proc( f::list, var::list, z::list,DD::list, tol:=0, BB:=[])
local u,sd,un,c,t1,t2,tt1,tt2,p, k, row,R,rows,rr,n, M, NN, DIF, s, ro, i,j;
    n:= nops(var);
    sd:=nops(DD);
    #print(" mourrain_step_Input",DD);

    # Vector Lambda
    NN:= cand_set(  DD );
    #print("Cand_set:", ([to_polynomial(NN)]) );

    #print("NN=", NN);
    s:=nops(NN);

###### Condition (i)
    ro:=0;# number of rows added
    M:=Matrix(nops(f),s);

    un:=[cat(a,1..s)];
    #cnt:=0;

    c:=first_comb(n,2);
    while c <> NULL do
        #cnt:=cnt+1;

        t1:=[ seq(diff_df(DD[j], c[2]),j=1..sd)];
        t2:=[ seq(diff_df(DD[j], c[1]),j=1..sd)];
        tt1:= to_polynomial(t1,var);
        tt2:= to_polynomial(t2,var);
        #print( Matrix(<tt1>),Matrix(<tt2>) );
        #print("OK", s, d);
        p:=0;
        #for k to sd do
            #print("--", k, p);
            #p:= p + un[(c[1]-1)*sd + k] * tt1[k]
            #       - un[(c[2]-1)*sd + k] * tt2[k];
         for k to sd do
            p:= p + un[ (k-1)*n + c[1] ] * tt1[k]
                  - un[ (k-1)*n + c[2] ] * tt2[k];

#            if not has_term(t1[k] , LT) then
#            p:= p + un[(c[1]-1)*d + k] * tt1[k];
#            fi;
#            if not has_term(t2[k] , LT) then
#            p:= p - un[(c[2]-1)*d + k] * tt2[k];
#            fi;
        od;

#        if p<>0 then

        if BB <> [] then  # improved condition (i)
            p:= convert(
            [seq( BB[u]*coeffof(BB[u],expand(p),var), u=1..nops(BB))],`+` )
        fi;

        #print(collect(p,var));  # Print Constraints (i)
        #print("Closedness on ", DD, un, var ) ;
        #print("Closedness eqs:", closedness_equations(DD, un, var ) ) ;
        #print("Closedness:", lstcoefof(p,var) );

        rows:= Array([lstcoefof(p,var)]);
        #print(rows);
#        fi;
        #print(rows);
        #print("cond i: ", nops([lstcoefof(p,var)]) );
        R:=NULL;
        for row in rows do
            #rr:= [seq(0,u=1..s)];
            rr:= Array([seq(0,u=1..s)]); #lists don't work for big dimension
            for i to s do
#                rr[i]:= coeffof(cat(a,i),row,un); ###
                rr[i]:= coeffof(un[i],row,un); ###
                #rr:=subsop(rr[i]=coeffof(cat(a,i),row,un),rr);
            od;
            #R:=R,rr;
            R:=R, convert(rr,`list`);
        od;

        if R<>NULL then
            M:= Matrix(<Matrix([R]), M> );
            ro:= ro + nops([R]);
            #print("M=",Matrix([R]));
        fi;
    c:=next_comb(c,n);
    od;#all combinations

##### Condition (ii), nops(f) constraints
    DIF:= to_function(NN,var);
    for i to nops(f) do # f[i]
        for j to s do
            M[ro+i,j]:=
            eval( app_funct( DIF[j], f[i]) ,
            #eval( app_funct( DIF[j], f[i]) ,
                 [seq(var[k]=z[k],k=1..n)]);
        od;
    od;
    #print("Matrix:", M );

##### Condition (iii), MM2011
    # ADD CONDITION: DUALS OF BB MUST VANISH, nops(DD)-1 constaints
    c:=NULL;
    if BB <> [] then
        R:=NULL;
        c:=NULL;
        t1:= expand(add( un[k]*to_polynomial(NN[k],var), k=1..s));
        #print(t1);

        for i from 2 to nops(BB) do
            tt1:= coeffof(BB[i],t1,var);
            tt2:= indets(tt1);

            #print(tt2, nops(tt2));
            if nops(tt2)=1 then # get nb of vars/terms of tt1
                for j to s do
                    #if un[j]=tt1 then
                    if un[j] in tt2 then
                        c:=c, j;
                        break;
                    fi;
                od;
            else
                rr:= Array([seq(0,u=1..s)]);
                for j to s do
                    rr[j]:= coeffof(un[j],tt1,un);
                od;
                R:=R,convert(rr,`list`);
            fi;
        od;

        #print("delete ",c);
        if R<>NULL then
            M:= Matrix(<Matrix([R]), M> );
            print("Condition III added", nops([R]),"rows" );
        fi;
        if c<>NULL then
            c:= [c];
            M:= DeleteColumn(M,c);
            NN:=subsop(seq(c[k]=NULL,k=1..nops(c)),NN);
            #print("Condition III removed",nops(c),"cols" );
        fi;

    fi;
    #print("Columns:", to_polynomial(NN) );
    #print("Matrix:", M );
    #print("Int. Dimension:",Dimension(M));
    R:= nkernel( M, tol );
    #print(`Found`, nops(R). `vectors`);
    #print(`sol= `, R );

#### Computing new elements

    p:=NULL;
    for row in R do
        M:=Matrix(n+1,1);
        for i to nops(NN) do
#            if tol>0 then
                if tol=0 or abs(evalf(row[i]))>tol then
                    t1:= copy(NN[i]);
                    for j to Dimension(t1)[2] do
                        t1[n+1,j]:= t1[n+1,j]*row[i];
                    od;
                    M:=add_df(M,t1,tol);
                fi;
#            else
#                M:=add_df(M,t1,tol);
#            fi;
        od;
        p:= p, remove_zero(M, tol);
        #p:= p, M;
    od;

    #print("Unk:", un, R);
    #Return parameters if requested
    if _nresults = 1 or _nresults = undefined then
         [p];
    else
        [p], R;
    end if
end:

#
# Macaulay' s 1916 algorithm to compute dual basis
#
macaulay0:= proc( f::list, var::list, z::list, tol:=0  )
    local  mu, DD,t,ind, n,j,i, flag;
    n:= nops(var);
    DD:= [ ];
    i:=0;
    mu:=0;
    while true do
        t:= macaulay_step(f,var,z,i, tol);
        #print(mu,nops(t), "step=",t);
        if mu=nops(t) then
            #print("Yes!", mu,nops(DD)- 1 );
            break;
        else
            DD:= [ op(t) ];
            mu:=nops(t);
            i:=i+1;
            #print("Mac. Mult. is now", mu );
        fi;
    od;
sort( DD, rlex_df );
end:

#
# Macaulay's 1916 Algorithm with MM11 improvement,
# Returns triangular basis
# Output is the primal-dual structure
#
macaulay:= proc( f::list, var::list, z::list, tol:=0, upto:=infinity  )
    local  mu, BB, DD,t, t1, n,i, c ;
    n:= nops(var);
    DD:= [ ];
    BB:= [];
    i:=0;
    mu:=0;
    while true and i<upto+1 do
        t:= macaulay_step(f,var,z,i, tol, BB);
        #print(mu,nops(t), "step=",t);
        if 0=nops(t) then
            break;
        else
            t:= coefmatrix(t,var);
            t1:= cmaximal_minor( t[1], tol );#indices
            BB:= [ op(BB), op(t[2][t1]) ];

            # Orthogonalize current elements
            t[1]:= ReducedRowEchelonForm(
                Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));

            ## Update dual basis
            DD:= [ op(DD), op( matrix2diffs( t[1], t[2],var, tol) ) ];

            i:=i+1;
            #print("Mac. Added:", nops(t1) );
        fi;
    od;
DD,BB;
end:

#
# Primal-Dual structure by Mourrain's 97 algorithm, with MM11 improvement
# Returns triangular basis
#
mourrain := proc( f::list, var::list, z::list, tol:=0, upto:=infinity )
local j,BB, DD,t,t1, n, c;

    n:= nops(var);
    c:=1;
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    DD:= [ DD ];
    BB:= [1];
    while true and c<upto+1 do
        t:= mourrain_step(f,var,z,DD, tol, BB);
        #print(mu,nops(t));
        #print("step=",t);
        if 0=nops(t) then
            break;
        else
            #print("deg=",c,"#D=",nops(t) );
            c:=c+1;

            t:= coefmatrix(t,var);
            #print("coef_matrix:", t);
            t1:= cmaximal_minor( t[1], tol );#indices

            #print("max_minor=", t1 );
            #print("Update partial quotient basis");
            ## Update Partial quotient Basis
            BB:= [ op(BB), op(t[2][t1]) ];
            #print("basis:", BB);

            #print("Orthogonalize current elements");
            # Orthogonalize current elements
           t[2]:= [op(t[2][t1]),op(subsop(seq( t1[j]=NULL,j=1..nops(t1)),t[2]))];
           t[1]:= ReducedRowEchelonForm(
              Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));
            #print("Update dual basis");
            ## Update dual basis
            DD:= [ op(DD), op( matrix2diffs( t[1], t[2],var, tol) ) ];
        fi;
    od;
DD, BB;
end:



#
# Primal-Dual structure by Mourrain's 97 algorithm, with MM11 improvement
# Returns primal-dual basis and approximate dual parameter values
#
mourrain_parametric := proc( f::list, var::list, z::list, tol:=0, upto:=infinity )
local j,BB, DD,t,t1, n, c, vv;

    n:= nops(var);
    c:=1;
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    DD:= [ DD ];
    BB:= [1];
    while true and c<upto+1 do
        t, vv:= mourrain_step(f,var,z,DD, tol, BB);
        #print(mu,nops(t));
        #print("step=",t, vv);
        if 0=nops(t) then
            break;
        else
            #print("deg=",c,"#D=",nops(t) );
            c:=c+1;

            t:= coefmatrix(t,var);
            #print("coef_matrix:", t);
            t1:= cmaximal_minor( t[1], tol );#indices

            #print("max_minor=", t1 );
            #print("Update partial quotient basis");
            ## Update Partial quotient Basis
            BB:= [ op(BB), op(t[2][t1]) ];
            #print("basis:", BB);

            #print("Orthogonalize current elements");
            # Orthogonalize current elements
           t[2]:= [op(t[2][t1]),op(subsop(seq( t1[j]=NULL,j=1..nops(t1)),t[2]))];
           t[1]:= ReducedRowEchelonForm(
              Matrix([ t[1][..,t1],  DeleteColumn(t[1],t1)]));
            #print("Update dual basis");
            ## Update dual basis
            DD:= [ op(DD), op( matrix2diffs( t[1], t[2],var, tol) ) ];
        fi;
    od;
DD, BB;
end:


#
# Compute Hilbert Function
# input: a dual basis
#

hilbert_func := proc( BB::list )
local H, t, cd, c, e;

#print("hilbert_func_IN:", BB );
if (whattype(BB[1])=Matrix) then
    H:= NULL;
    cd := 0;
    c  := 0;
    for e in BB do
        t :=  degree( to_polynomial(e) );
        if t=cd then
            c:= c+1;
        else
            H:= H, c;
            cd:= cd+1;
            c:= 1;
        fi;
    od:
    # last value
    H:= H, c;
else
    H:= NULL;
    cd := 0;
    c  := 0;
    for e in BB do
        t :=  degree( e );
        if t=cd then
            c:= c+1;
        else
            H:= H, c;
            cd:= cd+1;
            c:= 1;
        fi;
    od:
    # last value
    H:= H, c;
fi;

[H];
end:


#
# Dual basis by classic Mourrain's '97 `Integration Method`
#
mourrain0 := proc( f::list, var::list, z::list, tol:=0 )
local mu, DD,t, n ;

    n:= nops(var);
    DD:=Matrix(n+1,1);
    DD[n+1,1]:=1;
    DD:= [ DD ];
    mu:=0;
    while true do
        t:= mourrain_step(f,var,z,DD, tol);
        #print(mu,nops(t));
        #print("step=",t);
        if mu=nops(t) then
            #print("Yes!", mu,nops(DD)- 1 );
            break;
        else
            DD:= [DD[1],   op(t) ];
            mu:=nops(t);
            #print("Int. Mult. is now:", mu );
        fi;
        #cnt:=cnt+1;if cnt>3 then break; fi;
    od;
#sort(DD, cat(comp,_df) );
sort(DD, rlex_df );
end:

########################################################
########################################################
#### Applications
########################################################
########################################################

#
# Computes Normal form of p, given the primal-dual pair (BB,AA)
#
normal_form := proc ( p, var::list, z::list, BB::list, AA::list)
    local k,Sb, nf, i, m, dfs;
    m:=nops(BB);
    nf:=0;
    Sb:= seq(var[k]=z[k], k=1..nops(z));

    for i to m do
        nf:= nf +
        eval( app_funct( to_function( BB[i],var ) , p ), [Sb])
        * AA[i] ;
    od;
nf;
end:

#
# Computes the matrix of multiplication in R/Q_z
#
mult_table := proc ( f::list, var::list, z::list)
    local BB,AA, m, MM,j,i ;

    BB, AA := basis_pair(f,var,z);
    m:= nops(BB);
    MM:= Matrix(m);

    for i to m do
        for j to m do
            MM[i,j]:=
            normal_form( AA[i]*AA[j], var, z, BB,AA );
        od;
    od;
MM;
end:

#
# Computes the matrix of multiplication by a polynomial S in R/Q_z
#
mult_mat := proc (f::list, var::list, z::list, S)
local NF, BB,AA, m, MM,j,i ;

    BB, AA := basis_pair(f,var,z);
    m:= nops(BB);
    MM:= Matrix(m);


    for i to m do
        NF := normal_form( S*AA[i], var, z, BB,AA );
        for j to m do
            MM[i,j]:=
            coeffof( AA[j], NF, var );
        od;
    od;
    MM;
end:

#
# Computes the matrix of multiplication in R/Q_z
#
parametric_mult_table := proc (sdual::list, BB::list, var::list)
    local AA, m, MM,j,i ;

MM;
end:


#
# Return sign of number
#
sign_of  := proc (k)
if k=0 then return 0; fi;
sign(k);
end:

#
# Return the number of half-branches of real curve f=0 at point z
#
curve_branches := proc ( f::list, var::list, z::list )
    local k, n, Sb,m,i,MM,j,JJ, ff, BB, AA, ev, Phi;
    n:= nops(var);
    Sb:= [seq(var[k]=z[k],k=1..n)];
    ff:= [ op(f),
           Determinant(VectorCalculus:-Jacobian([op(f),add((var[k]-z[k])^2,k=1..n)] , var         ))];
    #print(`Map is ff= `, ff);
    BB, AA := basis_pair(ff,var,z );
    m:= nops(BB);

    #print(to_polynomial(BB) );

    JJ:= Determinant ( VectorCalculus:-Jacobian( ff , var ) );
    #print(`J= `, JJ);

    # find positive quad form
    for i to m do
        ev:= eval( app_funct( to_function( BB[i],var ), JJ ), Sb) ;
        if ev<>0 then
           if ev>0 then
               Phi:= BB[i];
           else
               print(`negative`);
           fi;
               break;
        fi;
    od;

    print(`Phi=`, to_polynomial(Phi) ) ;
    # Compute Matrix representation of quadratic form Phi
    Phi:= to_function(Phi,var);
    MM:= Matrix(m);
    for i to m do
        for j to m do
            MM[i,j]:=
            eval( app_funct( Phi ,
                             AA[i]*AA[j]
                             #normal_form( AA[i]*AA[j], var, z, BB,AA )
                           ), Sb );
        od;
    od;

    #print(MM);

    #Compute signature
    MM:=Eigenvalues( evalf(MM) );
    #print(`Eigenvalues=`, MM);
    2*add( sign_of(MM[i]), i=1..m );
end:

#
# Compute topological degree of mapping ff at point z
#
topological_degree := proc ( ff::list, var::list, z::list, tol:=0)
    local k,n, Sb,m,i,MM,j,JJ, BB, AA, ev, Phi;
    n:= nops(var);
    Sb:= [seq(var[k]=z[k],k=1..n)];

    BB, AA := basis_pair(ff,var,z, tol );
    m:= nops(BB);

    JJ:= Determinant ( VectorCalculus:-Jacobian( ff , var ) );

    # find positive quad form
    for i to m do
        ev:= eval( app_funct( to_function( BB[i],var ), JJ ), Sb) ;
        if abs(ev)> tol then
            Phi:= BB[i];
            break;
        fi;
    od;

    print(`got Phi=`, to_polynomial(Phi) ) ;
    # Compute Matrix representation of quadratic form Phi
    Phi:= to_function(Phi,var);
    MM:= Matrix(m);
    for i to m do
        for j to m do
            MM[i,j]:=
            eval( app_funct( Phi ,
                             #normal_form( AA[i]*AA[j], var, z, BB,AA)
                             AA[i]*AA[j]
                           ), Sb );
        od;
    od;

    #print(MM);
    #Compute signature and take absolute value
    Eigenvalues( evalf(MM) );
    abs( add( sign_of(MM[i]), i=1..m ) );
end:

#
# Create coefficient matrix of differentials BB
#
coefmatrix := proc (BB,v:=[] )
    local s,SBB,i,j,A,c,n,var;

    n:=Dimension(BB[1])[1]-1;
    if v=[] then
        var:=[seq(d[s],s=1..n)];
    else
        var:=v;
    fi;
    c:=to_polynomial( BB,var);
    #print("coefmat",c);
    SBB:= lstmonsof(c, var):
    A:= Matrix(nops(BB), nops(SBB) ) :
    for i to nops(c) do
        for j to nops(SBB) do
            A[i,j]:= coeffof(SBB[j],c[i], var ):
        od:
    od:
    [ A, SBB ] ;
end:

#
#  Input: coefficient matrix A, indexing polys SBB
#  Output: Polynomials induced by A's rows
#
matrix2polys:= proc ( A, SBB )
    local u,v,i,j,t,L;
    u,v := Dimension(A);

    L:=NULL;
    for i to u do
        t:=0;
        for j to v do
            t:= t + A[i,j]* SBB[j];
        od;
        L:=L, t;
    od;
[L];
end:

#
#  Input: coefficient matrix A, indexing polys SBB
#  Output: Differentials induced by A's rows
#
matrix2diffs:= proc ( A::Matrix, SBB::list, var::list, tol:=0 )
    local n,k,df,u,v,i,j,t,L;
    #print("matrix2diffs_IN:", A, SBB, var);
    u,v := Dimension(A);
    n:=nops(var);

    L:=NULL;
    t:=Matrix(n+1,1);
    for k to u do
        df:= Matrix(n+1,1);
        for i to v do
            if  tol=0 or abs(evalf(A[k,i])) > tol then
                t[n+1,1]:=A[k,i];
                for j to n do
                    t[j,1] := degree (SBB[i], var[j]);
                od;
                df:= add_df(df,t,tol);
            fi;
        od;
        L:=L, copy(df);
    od;
    #print("matrix2diffs_OUT:", L );
[L];
end:

#
# Compute a primal-dual orthogonal pair
#
basis_pair:= proc( f::list, var::list, z::list, tol:=0, upto:=infinity )
    local j,Db,A,i,C,ind;

    #for a suitable ordering (reverse to degree) we get already a good
    # basis
##    return mourrain(f,var,z, tol, upto);

    Db,A:= mourrain(f,var,z, tol, upto); # Get triangular basis


    C:= coefmatrix( Db, var );

    ind:=NULL;
    for i to nops(A) do
       ind:=ind, ListTools:-Search(A[i], C[2] ) ;
    od;
    ind:=[ind];

    # Orthogonalize basis
    #print("Got basis, eliminating upp. triang. part");
    C[1]:= ReducedRowEchelonForm(
        Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]));
    A:=C[2][ind];
    C[2]:=[op(A),op(subsop(seq( ind[j]=NULL,j=1..nops(ind)),C[2]))];

matrix2diffs( C[1], C[2], var, tol), A;
end:

#
# Given dual basis BB, find AA.  (under constuction)
#
make_basis_pair:= proc( BB::list, var::list)
    local j,Db,A,B,i,C,ind;

    C:= coefmatrix( BB, var );

    ind:=NULL;
    for i to nops(A) do
       ind:=ind, ListTools:-Search(A[i], C[2] ) ;
    od;
    ind:=[ind];

    #print(  Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]) );
    C[1]:= ReducedRowEchelonForm(
        Matrix([ C[1][..,ind],  DeleteColumn(C[1],ind) ]));
    A:=C[2][ind];
    C[2]:=[op(A),op(subsop(seq( ind[j]=NULL,j=1..nops(ind)),C[2]))];

    #print(C[2]);
    #print(C[1]);

#matrix2polys( ReducedRowEchelonForm(C[1]), subs(seq(var[k]=d[k],k=1..nops(var)), C[2])),
matrix2diffs( C[1], C[2],var, tol),
A;
end:


####################################################
####################################################
### Auxiliary functions
#######s#############################################
####################################################

#
# Computes the `Cyclic-n` polynmial system in variables x[1]..x[n]
#
cyclicn := proc( n )
local k,m,i,j, t, CN;

CN:=NULL;
m:=n-1;
for i from 0 to m-1 do # t=f_i
    t:=0;
    for j from 0 to m do # sum
        t:= t+ mul( x[(k mod n)+1], k= j..(i+j));
    od;
    CN:= CN, t;
od;
CN:= CN, 1-  mul( x[k], k=1..n);

[CN];
end:

#
# Computes a system with zero mult 2^n at x=0
#
expmultn := proc( n )
local S, i;

S:=NULL;
for i from 1 to n-1 do # t=f_i
    S:= S,  x[i]^3 + x[i]^2 - x[i+1];
od;
#S:=
[S, x[n]^2];
end:

#Benchmark system by Kobayashi et al.
kssn := proc( n )
local i,j,s;
lprint("Solution is", [seq(1,i=1..n)]);
s:=add(x[j],j=1..n) - n + 1;
[seq( x[i]^2 - 2*x[i]+ s, i=1..n)];
end:


#
# Next r-combination of [1..n] after c in lex-order
# nops(c)=r
#
next_comb := proc( c::list, n::integer)
	  local nc,r,i,j;

	  r:= nops(c);
	  if c=[seq(n-r+1..n)] then return NULL; fi; #finished
	  nc:=c;

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
    #print(`Warning: r>n combination requested`,r,n);
    return NULL;
fi;
end:

#
# RevLex-first degree r monomial in n variables
#
first_mon:= proc(r::integer,n::integer)
    local k;
    return [r,seq(0,k=1..n-1)];
end:

#
# RevLex-Next degree r monomial in n variables after c
#
next_mon := proc( c::list, r::integer)
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




#####################################
end use;

lprint(`Multiple Roots package`);
end:

# Settings
#UseHardwareFloats := true: #Using hardware floats
#Digits:= 32:


##
## procedure analyzer
##
mmint := proc( f,
  {level::posint:=2},
  {toggle::list(posint):=[]},
  {header::truefalse:=false},
  {extras::string:=""} )
local x,fname,k,oldiface,executable;
   fname := cat(kernelopts('homedir'),kernelopts('dirsep'),"minttemp.txt");
   #fname := "/tmp/minttemp.txt"; # or some other temp location
   oldiface := interface('verboseproc');
   interface('verboseproc'=3);
   writeto(fname);
   printf("%a := %a:\n", f, eval(f));
   writeto(terminal):
   fclose(fname);
   interface('verboseproc'=oldiface);
   executable:=`if`(kernelopts('platform')="windows",
      cat("\"",kernelopts('bindir'),"\\mint","\""),
      cat(kernelopts('mapledir'),kernelopts('dirsep'),"bin/mint"));
   k:=ssystem(cat(executable, cat(" -i ",min(level,4)," "),
                  seq(cat(" -t ",x," "), x in remove(t->t>32,toggle)),
                  `if`(not(header)," -q ",NULL),
                  " ",extras," ","\"",fname,"\""));
   if k[1]>=0 then printf("%s",k[2]); end if;
   NULL;
end proc:
