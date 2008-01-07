# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2008 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use ExtUtils::MakeMaker;
use Config;

sub MY::postamble {
    my $out;
    #print Config::myconfig();
    $out .= "LD = g++\n";	# Always as we're making exe
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= '
CC = g++
LEX = flex
FLEXFIX = ./flexfix

#CFLAGS += -DFLEX_DEBUG
#LEXFLAGS += -d -L

VPATH += src

all:: example

example: example.o VPreproc.o VFileLine.o VPreprocLex.o
	$(LD) $(LDFLAGS) -o $@ $^ $(LIBS)

VPreprocLex.o:	VPreprocLex.h VPreproc.h VFileLine.h
VPreproc.o:	VPreprocLex.h VPreproc.h VFileLine.h
VFileLine.o:	                         VFileLine.h

VPreprocLex_prefix.cpp: VPreprocLex.l
	$(LEX) $(LEXFLAGS) -o$@ $<

VPreprocLex.cpp: $(FLEXFIX) VPreprocLex_prefix.cpp
	$(PERL) $(FLEXFIX) < VPreprocLex_prefix.cpp > $@

clean::
	-rm -rf test *.d *.o VPreprocLex*.cpp *.output example example.exe
';
    return $out;
}

WriteMakefile(
              NAME => "Verilog::Preproc::lib",
	      SKIP => [qw(all static static_lib dynamic dynamic_lib)],
	      );
