# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use ExtUtils::MakeMaker;
use Config;

sub MY::postamble {
    my $out;
    #print Config::myconfig();
    if ($Config{osname} !~ /cygwin/i && $Config{archname} !~ /cygwin/i
	&& $Config{osname} !~ /darwin/i && $Config{archname} !~ /darwin/i) {
	# Cygwin: Don't change LD, it breaks
	# Sun: Requires g++ LD
	# Linux: Either way
	$out .= "LD = g++\n";
    }
    if ($Config{osname} =~ /cygwin/i || $Config{archname} =~ /cygwin/i) {
	# Cygwin ExtUtils::MakeMaker ignores our LIBS declaration and says
	# "No library found for -lstdc++".  Force it.
	$out .= "LDLOADLIBS += -lstdc++\n";
    }
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    #$out .= "CCFLAGS += -O0 -ggdb\n" if $ENV{VERILATOR_AUTHOR_SITE};  print "%Warning: -O0 --gdb on, also FLEX -d on";
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= '
CC = g++
LEX = flex
PPSRC = ../Preproc/src
FLEXFIX = $(PPSRC)/flexfix
YFLAGS = -d -v

CCFLAGS += -I$(PPSRC)
#CFLAGS += -DFLEX_DEBUG
LEXFLAGS += -d

VPATH += . $(PPSRC)

VParseLex.o:		VParseLex.cpp     VParseLex.h VParseGrammar.h VParse.h VFileLine.h VParseBison.h
VParseGrammar.o:	VParseGrammar.cpp VParseLex.h VParseGrammar.h VParse.h VFileLine.h VParseBison.h
VParse.o:		VParse.cpp        VParseLex.h VParseGrammar.h VParse.h VFileLine.h VParseBison.h
VFileLine.o:	        VFileLine.cpp     VFileLine.h

VFileLine.o: $(PPSRC)/VFileLine.cpp
	$(CCCMD) $(CCCDLFLAGS) "-I$(PERL_INC)" $(PASTHRU_DEFINE) $(DEFINE) $<

VParseLex_prefix.cpp: VParseLex.l
	$(LEX) $(LEXFLAGS) -o$@ $<

VParseLex.cpp: $(FLEXFIX) VParseLex_prefix.cpp
	$(PERL) $(FLEXFIX) < VParseLex_prefix.cpp > $@

VParseBison.cpp VParseBison.h:	VParseBison.y
	-rm -rf VParseBison.c VParseBison.cpp
	${YACC} ${YFLAGS} --debug --verbose -d -k $< -pVParseBison -o VParseBison.c
	-(grep conflicts VParseBison.output || mv VParseBison.c VParseBison.cpp )
	-rm -rf VParseBison.c

clean::
	-rm -rf test *.d *.o *.output
	-rm -rf VParseLex*.cpp VParseBison.h VParseBison.cpp
';
    return $out;
}

WriteMakefile(
              NAME => "Verilog::Parser",
	      LIBS => '-lstdc++',
	      VERSION_FROM  => 'Parser.pm',
	      XSOPT => '-C++',
    	      OBJECT   => 'VFileLine.o VParseLex.o VParse.o VParseBison.o',
	      MYEXTLIB => 'Parser.o',
	      INC => (" -I. -Isrc"),
	      );
