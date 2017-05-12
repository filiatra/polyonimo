##########################################################################
##########################################################################
##                                                                      ##
##  polyonimo                                                           ##
##                                                                      ##
##  This Source Code Form is subject to the terms of the Mozilla Public ##
##  License, v. 2.0. If a copy of the MPL was not distributed with this ##
##  file, You can obtain one at http://mozilla.org/MPL/2.0/.            ##
##                                                                      ##
##  Author: Angelos Mantzaflaris, 2017                                  ##
##                                                                      ##
##########################################################################
##########################################################################

polyonimo := module()

description "Polyonimo Maple packages";

option package;

export resultant, benchmark, utility;

local devel, ModuleLoad;

$include "src/utility.mm"

$include "src/resultant.mm"

$include "src/benchmark.mm"

ModuleLoad:= proc()

    # Weyman cohomology group type
    # H^{g_1+g_2+..+g_d} (mvc - deg_{i_1} - .. - deg_{i_p} =
    # H^q(mdeg) = H^{g_1}(mdeg_1) x .. x H^{g_d}(mdeg_d)
    #
    # exp::set
    # fis::set
    # mdeg::Vector
    # dim::integer
    TypeTools[AddType]( WCOH, 'record(exp::set, fis::set, mdeg::Vector, dim::integer)' ); 

    # Weyman component type K_{p,q}, v=p-q
    #
    # list(WCOH)
    TypeTools[AddType]( WCOMP, 'list(WCOH)' );
    # is "exp" constant?

    # Weyman term type K_v
    #
    # Array(WCOMP) indexed by p = 0..n+1
    TypeTools[AddType]( WTERM, 'Array(Or(WCOMP,integer))' ); # array requires to store integer 0

    # Weyman complex type K_{*}
    #
    # nv::integer
    # ng::integer
    # grp::Vector
    # deg::Matrix
    # mvc::Vector
    # K::Array(WTERM) indexed by v = -n..n+1
    TypeTools[AddType]( WCOMPLEX, 'record(nv::integer, ng::integer, grp::Vector,deg::Matrix,mvc::Vector, K::Array )'); # ::Array(WTERM)
    
lprint(`Polyonimo Maple Modules, Angelos Mantzaflaris, 2017`);
end:
# Explicitly call ModuleLoad here so the type is registered when this
# code is cut&pasted in.  ModuleLoad gets called when the module is
# read from the repository, but the code used to define a module
# (like the command below) is not called at library read time.
ModuleLoad();

end:#end polyonimo

# Codes under development
$include "src/devel.mm"
