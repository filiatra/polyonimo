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

export resultant;

local devel, ModuleLoad;

$include "src/resultant.mm"


#########################################################################
# Code under development
#########################################################################
devel := module()

option package;

description "Polyonimo development package";



end:#end polyonimo-devel


ModuleLoad:= proc()
lprint(`Polyonimo Maple Modules, Angelos Mantzaflaris, 2017`);
end:
# Explicitly call ModuleLoad here so the type is registered when this
# code is cut&pasted in.  ModuleLoad gets called when the module is
# read from the repository, but the code used to define a module
# (like the command below) is not called at library read time.
ModuleLoad();

end:#end polyonimo
