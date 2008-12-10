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
#LEXFLAGS += -d

VPATH += . $(PPSRC)

VPreprocLex.o:	VPreprocLex.h VPreproc.h VFileLine.h
VPreproc.o:	VPreprocLex.h VPreproc.h VFileLine.h
VFileLine.o:	                         VFileLine.h

VPreprocLex_prefix.cpp: VPreprocLex.l
	$(LEX) $(LEXFLAGS) -o$@ $<

VPreprocLex.cpp: $(FLEXFIX) VPreprocLex_prefix.cpp
	$(PERL) $(FLEXFIX) < VPreprocLex_prefix.cpp > $@

Preproc_cleaned.c: Preproc.c
	$(PERL) $(XSUBPPFIX) < Preproc.c > Preproc_cleaned.c

clean::
	-$(RM_RF) test *.d *.o *.output
	-$(RM_RF) VPreprocLex*.cpp Preproc_cleaned.c
';
    return $out;
}

# Grr; some flags cause warnings in g++
(my $ccflags = $Config{ccflags}) =~ s/ *-Wdeclaration-after-statement//;

WriteMakefile(
              NAME => "Verilog::Preproc",
	      LIBS => '-lstdc++',
	      VERSION_FROM  => 'Preproc.pm',
	      XSOPT => '-C++',
	      CCFLAGS	=> $ccflags,
	      OBJECT   => 'VFileLine.o VPreproc.o VPreprocLex.o',
	      MYEXTLIB => 'Preproc_cleaned.o',
	      );
