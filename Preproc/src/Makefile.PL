# $Revision: 1.9 $$Date: 2004/12/04 20:13:28 $$Author: wsnyder $
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2004 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use ExtUtils::MakeMaker;
use Config;

sub MY::postamble {
    my $out;
    #print Config::myconfig();
    $out .= "LD = g++\n";	# Always as we're making exe
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    $out .= '
CC = g++
LEX = flex

#CFLAGS += -DFLEX_DEBUG
#LEXFLAGS += -d -L

VPATH += src

example: example.o VPreproc.o VFileLine.o VPreprocLex.o
	$(LD) $(LDFLAGS) -o $@ $^ $(LIBS)

VPreprocLex.o:	VPreprocLex.h VPreproc.h VFileLine.h
VPreproc.o:	VPreprocLex.h VPreproc.h VFileLine.h
VFileLine.o:	VPreprocLex.h VPreproc.h VFileLine.h

VPreprocLex.cpp: VPreprocLex.l
	$(LEX) $(LEXFLAGS) -o$@ $<

clean::
	-rm -rf test *.d *.o VPreprocLex.cpp *.output example example.exe
';
    return $out;
}

WriteMakefile(
              NAME => "Verilog::Preproc::lib",
	      SKIP => [qw(all static static_lib dynamic dynamic_lib)],
	      );
