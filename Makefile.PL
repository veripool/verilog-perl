# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

require 5.005;
use ExtUtils::MakeMaker;
use Carp;

$DOLLAR = '$$';	# Quoted properly for make
sub MY::postamble {
    my $out="";
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= "
README: readme.texi
	-rm -rf \$@
	makeinfo \$< --output \$@ --no-headers --no-validate

clean::
	-rm -rf simv .vpm test_dir

dist: maintainer-copy distcheck README

## Maintainer use:
preexist:
	test ! -r \$(HOME)/src/kits/\$(DISTVNAME).tar.gz

tag:
	svnorcvs tag  \$(DISTNAME)_\$(VERSION_SYM)

maintainer-diff:
	svnorcvs diff \$(DISTNAME)_\$(VERSION_SYM) 

maintainer-dist: preexist dist tag
	cp \$(DISTVNAME).tar.gz \$(HOME)/src/kits
	mv \$(DISTVNAME).tar.gz \$(HOME)/backpack

maintainer-copy:

maintainer-clean: distclean
	-rm -rf README Makefile

";
    return $out;
}

local $! = undef;
`flex --version`; ($?==0) or die "\n%Error: 'flex' must be installed to build\n";
`g++ --version`; ($?==0) or die "\n%Error: 'gcc/g++' must be installed to build\n";

WriteMakefile(
	      DISTNAME  => 'Verilog-Perl',
	      NAME      => 'Verilog::Language',
	      AUTHOR	=> 'Wilson Snyder <wsnyder@wsnyder.org>',
	      ABSTRACT  => 'Verilog language utilities and parsing',
	      VERSION_FROM  => 'Language.pm',
	      NO_META	=> 1,
	      #OPTIMIZE	=> '-ggdb',
	      PMLIBDIRS => ['lib', 'Verilog', 'Netlist',],
	      EXE_FILES => [qw( vrename vpm vppp vhier )],
	      'clean'	=> {FILES => qw (test_dir signals.vrename .vpm simv ),},
	      'dist'    => {COMPRESS => 'gzip -9f',
			    SUFFIX   => '.gz', 
			    DIST_DEFAULT => 'README all tardist',
			},
	      );

