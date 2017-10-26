##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2016                                               #
#    INRIA (Institut National de Recherche en Informatique et en         #
#           Automatique)                                                 #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file licenses/LGPLv2.1).            #
#                                                                        #
##########################################################################

FRAMAC ?= frama-c

# Do not use ?= to initialize both below variables
# (fixed efficiency issue, see GNU Make manual, Section 8.11)
ifndef FRAMAC_SHARE
FRAMAC_SHARE  :=$(shell $(FRAMAC) -journal-disable -print-path)
endif
ifndef FRAMAC_LIBDIR
FRAMAC_LIBDIR :=$(shell $(FRAMAC) -journal-disable -print-libpath)
endif

PLUGIN_DIR      ?= .

INCLUDES:=-I $(FRAMAC_LIBDIR)/plugins

PLUGIN_NAME:=Crude_slicer
PLUGIN_CMO:= version options common flag bv data info fixpoint analyze region transform function_pointers summaries slice register
PLUGIN_HAS_MLI:=yes
PLUGIN_DEPENDENCIES:=
PLUGIN_BFLAGS:=$(INCLUDES) -w +a -safe-string -short-paths -strict-formats -no-alias-deps
PLUGIN_OFLAGS:=$(INCLUDES) -w +a -safe-string -short-paths -strict-formats -no-alias-deps

ifeq ($(FRAMAC_MAKE),yes)
unexport $(FRAMAC_MAKE)
endif

version.ml:
	$(eval COMMIT:=$(shell git show-ref master | head -n 1 | cut -d ' ' -f 1))
	$(eval DATE:=$(shell date -R))
	@printf "let commit = \"$(COMMIT)\"" >> $@
	@printf "let date = \"$(DATE)\"" >> $@

$(PLUGIN_DIR)/%.cmo:

$(PLUGIN_DIR)/%.cmi:

$(PLUGIN_DIR)/%.cmx:

install::
	$(MKDIR) $(FRAMAC_DATADIR)/crude_slicer

uninstall::
	$(RM) -r $(FRAMAC_DATADIR)/crude_slicer

include $(FRAMAC_SHARE)/Makefile.dynamic
