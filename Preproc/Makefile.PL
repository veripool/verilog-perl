# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2024 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

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
    my $optimize = $Config{optimize};  $optimize =~ s/(^| )-O2( |$)/\1-O\2/g;
    # pass hardening flags
    $optimize .= " $ENV{CFLAGS} $ENV{CPPFLAGS}";
    $out .= "OPTIMIZE = $optimize\n";
    if ($Config{osname} =~ /cygwin/i || $Config{archname} =~ /cygwin/i) {
	# Cygwin ExtUtils::MakeMaker ignores our LIBS declaration and says
	# "No library found for -lstdc++".  Force it.
	$out .= "LDLOADLIBS += -lstdc++\n";
	# Cygwin: High optimization causes g++ "out of memory"
	$out .= "OPTIMIZE += -O\n";
    }
    if ($Config{osname} =~ /darwin/i || $Config{archname} =~ /darwin/i) {
	# MakeMaker wants to create bundles on MacOSX rather than dylibs. We override DLEXT and LDDLFLAGS generated by MakeMaker in this case
	$out .= "DLEXT = dylib\n";
	if ($^V eq '5.12.4') {
	    $out .= sprintf("LDDLFLAGS = -dynamiclib -lstdc++ -L/System/Library/Perl/5.12/%s/CORE -lperl -L/usr/local/lib\n",$Config{archname});
	} elsif ($^V eq '5.18.2') {
	    $out .= sprintf("LDDLFLAGS = -dynamiclib -lstdc++ -L/System/Library/Perl/5.18/%s/CORE -lperl -L/usr/local/lib\n",$Config{archname});
	} elsif ($^V < 'v5.26.3') {
	    $out .= sprintf("LDDLFLAGS = -dynamiclib -lstdc++ -L/System/Library/Perl/%vd/%s/CORE -lperl -lgcc_eh -L/usr/local/lib\n",$^V,$Config{archname});
	}
    }
    $out .= "CCFLAGS  += -Wall -Wno-unused -Wno-sign-compare -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    #$out .= "CCFLAGS += -O0 -ggdb\n" if $ENV{VERILATOR_AUTHOR_SITE};  print "%Warning: -O0 --gdb on, also FLEX -d on";
    $out .= "CCFLAGS  += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= "OPTIMIZE += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= "CCFLAGS += -I\$(PPSRC)\n";
    my $cmt = $ENV{VERILOGPERL_FLEX_DEBUG} ? "" : "#";
    $out .= "${cmt}CFLAGS += -DFLEX_DEBUG\n";
    $out .= "${cmt}LEXFLAGS += -d\n";
    $out .= '
CC = $(OBJCACHE) g++
LEX = flex
YACC = bison
PPSRC = ../Preproc
FLEXFIX = $(PPSRC)/flexfix
TOOLHASH = $(PPSRC)/toolhash
XSUBPPFIX = $(PPSRC)/xsubppfix

VPATH += . $(PPSRC)

VPreLex.o:	VPreLex.h VPreProc.h VFileLine.h
VPreProc.o:	VPreLex.h VPreProc.h VFileLine.h
VFileLine.o:	                         VFileLine.h

VPreLex_pretmp.cpp: VPreLex.l
	-$(LEX) --version
	$(PERL) $(TOOLHASH) --verbose --in $< --out $@ --cmd $(LEX) $(LEXFLAGS) -o$@ $<

VPreLex.cpp: $(FLEXFIX) VPreLex_pretmp.cpp
	$(PERL) $(FLEXFIX) VPreLex < VPreLex_pretmp.cpp > $@

Preproc_cleaned.cpp: Preproc.c
	$(PERL) $(XSUBPPFIX) < Preproc.c > Preproc_cleaned.cpp

clean::
	-$(RM_RF) test *.d *.o *.output
	-$(RM_RF) VPreLex*.cpp Preproc_cleaned.*
	-$(RM_RF) VPreprocLex*
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
	      OBJECT   => 'VFileLine.o VPreProc.o VPreLex.o',
	      MYEXTLIB => 'Preproc_cleaned.o',
	      );
