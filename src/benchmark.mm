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
minrankSystem;


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


end:#end benchmark

