##########################################################################
##########################################################################
##                                                                      ##
##  polyonimo:-devel                                                    ##
##                                                                      ##
##  This Source Code Form is subject to the terms of the Mozilla Public ##
##  License, v. 2.0. If a copy of the MPL was not distributed with this ##
##  file, You can obtain one at http://mozilla.org/MPL/2.0/.            ##
##                                                                      ##
##  Author: Angelos Mantzaflaris, 2017                                  ##
##                                                                      ##
##########################################################################
##########################################################################

devel := module()

description "Polyonimo development package";
option package;

isWcomplex := proc(kk:=anything)

return false;
end:

#TypeTools:-AddType(wcomplex, isWcomplex);



end:#end polyonimo-devel
