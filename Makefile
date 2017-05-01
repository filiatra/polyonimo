#
# Makefile to build and install polyonimo
#

# Maple tty executable
maple := maple

MAPLE_ROOT := $(shell $(maple) -q -c 'printf("%A\n",kernelopts(mapledir))' -cdone)
MAPLE_BIN  := $(shell $(maple) -q -c 'printf("%A\n",kernelopts(bindir))' -cdone)

BIN_SYS := $(notdir $(MAPLE_BIN))


default: polyonimo.mla polyonimo.hdb

install_dir := ${HOME}/maple/toolbox/polyonimo
installed_mla := $(install_dir)/lib/polyonimo.mla

install: $(installed_mla)

polyonimo.mla: make/savelib.mpl
#	$(RM) $@
	$(maple) -q $+

polyonimo.hdb: make/makehelp.mpl
#	$(RM) $@
	$(maple) -q $+

$(installed_mla): polyonimo.mla
	install -d $(dir $@)
	install -t $(dir $@) $+

# Clean up
clean:
	$(RM) $(installed_mla)

uninstall: clean
	 $(RM) -r $(install_dir)

.phony: clean default install uninstall
