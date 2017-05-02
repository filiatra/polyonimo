mv := version():
if (mv<991181) then
makehelp("polyonimo", "doc/polyonimo.mw", "lib/polyonimo.hdb"):
makehelp("polyonimo[resultant]", "doc/resultant.mw", "lib/polyonimo.hdb"):
makehelp("polyonimo[resultant][mDegree]", "doc/resultant_mDegree.mw", "lib/polyonimo.hdb"):
else
fremove("lib/polyonimo.help");
makehelp("polyonimo", "doc/polyonimo.mw", "lib/polyonimo.help"):
makehelp("polyonimo[resultant]", "doc/resultant.mw", "lib/polyonimo.help"):
makehelp("polyonimo[resultant][mDegree]", "doc/resultant_mDegree.mw", "lib/polyonimo.help"):
fi:
done
