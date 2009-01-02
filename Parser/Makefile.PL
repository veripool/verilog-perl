# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
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
    # Note OPTIMIZE is passed from upper makefile, so this code needed there too.
    if ($Config{osname} =~ /cygwin/i || $Config{archname} =~ /cygwin/i) {
	# Cygwin ExtUtils::MakeMaker ignores our LIBS declaration and says
	# "No library found for -lstdc++".  Force it.
	$out .= "LDLOADLIBS += -lstdc++\n";
	# Cygwin: High optimization causes g++ "out of memory"
	$out .= "OPTIMIZE += -O\n";
    }
    $out .= "CCFLAGS  += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    #$out .= "CCFLAGS += -O0 -ggdb\n" if $ENV{VERILATOR_AUTHOR_SITE};  print "%Warning: -O0 --gdb on, also FLEX -d on";
    $out .= "CCFLAGS  += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= "OPTIMIZE += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= '
ifeq ($(OBJCACHE_HOSTS_DETERMINANT),)
OBJCACHE :=
else
OBJCACHE := objcache --read --write
endif

CC = $(OBJCACHE) g++
LEX = flex
YACC = bison
PPSRC = ../Preproc
FLEXFIX = $(PPSRC)/flexfix
XSUBPPFIX = $(PPSRC)/xsubppfix

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

VParseBison.h: VParseBison.cpp

VParseBison.cpp:	VParseBison.y bisonpre
	-$(RM_RF) VParseBison.c VParseBison.cpp
	@echo "If the next command fails, you probably need to install Bison 1.875 or newer"
	$(PERL) bisonpre --yacc ${YACC} --debug --verbose --d -k VParseBison.y -p VParseBison -o VParseBison.c
	mv VParseBison.c VParseBison.cpp

Parser_cleaned.c: Parser.c
	$(PERL) $(XSUBPPFIX) < Parser.c > Parser_cleaned.c

clean::
	-$(RM_RF) test *.d *.o *.output *.pre.*
	-$(RM_RF) VParseLex*.cpp VParseBison.h VParseBison.cpp Parser_cleaned.c
';
    return $out;
}

# Grr; some flags cause warnings in g++
(my $ccflags = $Config{ccflags}) =~ s/ *-Wdeclaration-after-statement//;

WriteMakefile(
              NAME => "Verilog::Parser",
	      LIBS => '-lstdc++',
	      VERSION_FROM  => 'Parser.pm',
	      XSOPT => '-C++',
	      CCFLAGS	=> $ccflags,
	      OBJECT   => 'VFileLine.o VParseLex.o VParse.o VParseBison.o',
	      MYEXTLIB => 'Parser_cleaned.o',
	      );
