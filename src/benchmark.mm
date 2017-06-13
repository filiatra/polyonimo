##########################################################################
##########################################################################
##                                                                      ##
##  polyonimo:-benchmark                                                ##
##                                                                      ##
##  This Source Code Form is subject to the terms of the Mozilla Public ##
##  License, v. 2.0. If a copy of the MPL was not distributed with this ##
##  file, You can obtain one at http://mozilla.org/MPL/2.0/.            ##
##                                                                      ##
##  Author: Angelos Mantzaflaris, 2017                                  ##
##                                                                      ##
##########################################################################
##########################################################################

benchmark := module()

description "Polyonimo benchmark Module";

option package;

export 
minrankSystem,
makeRandomSystem;


#########################################################################
# Minrank system
#########################################################################
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


### Make random system
    makeRandomSystem:= proc(nis::Vector, dis::Matrix, var, sz:=1..100)
    local _c_list, rlist, roll, sf, i, sys:= NULL;
        randomize();
        unassign('c');
        roll := rand(sz);
        
        for i to ColumnDimension(dis) do
            sf := makePoly(nis,dis[..,i],c,var);
            _c_list := [coeffs(sf,allvars(l,var))];
            rlist := [seq(_c_list[k]=roll(),k=1..nops(_c_list))];
            sys := sys, subs(op(rlist), sf); #, rlist;
        od:
        return [sys];
    end:

end:#end benchmark
