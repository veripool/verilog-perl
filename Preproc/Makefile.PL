# $Revision: 1.11 $$Date: 2004/12/08 22:21:06 $$Author: wsnyder $
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
    if ($Config{osname} !~ /cygwin/i && $Config{archname} !~ /cygwin/i
	&& $Config{osname} !~ /darwin/i && $Config{archname} !~ /darwin/i) {
	# Cygwin: Don't change LD, it breaks
	# Sun: Requires g++ LD
	# Linux: Either way
	$out .= "LD = g++\n";
    }
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    $out .= '
CC = g++
LEX = flex

#CFLAGS += -DFLEX_DEBUG
#LEXFLAGS += -d -L

VPATH += src

.PHONY: src/VFileLine.o src/VPreproc.o src/VPreprocLex.o

src/VFileLine.o src/VPreproc.o src/VPreprocLex.o:
	cd src && $(MAKE) $(PASSTHRU) example

clean::
	-rm -rf test *.o VPreprocLex.cpp *.output
';
    return $out;
}

WriteMakefile(
              NAME => "Verilog::Preproc",
	      LIBS => '-lstdc++',
	      VERSION_FROM  => 'Preproc.pm',
	      XSOPT => '-C++',
    	      OBJECT => '$(O_FILES)',
	      # Included in .xs, as had problems
	      #MYEXTLIB => 'src/PreprocSrc.o',
	      MYEXTLIB => 'src/VFileLine.o src/VPreproc.o src/VPreprocLex.o',
	      #MYEXTLIB => 'VFileLine.o VPreproc.o VPreprocLex.o',
	      INC => (" -I. -Isrc"),
	      );
