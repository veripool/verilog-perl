# $Revision: 1.32 $$Date: 2004/09/01 20:21:10 $$Author: wsnyder $
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2004 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

require 5.005;
use ExtUtils::MakeMaker;
use Carp;

$DOLLAR = '$$';	# Quoted properly for make
sub MY::postamble {
"
README: readme.texi
	-rm \$@
	makeinfo \$< --output \$@ --no-headers --no-validate

clean::
	-rm -rf simv .vpm test_dir

dist: maintainer-copy distcheck README

## Maintainer use:
preexist:
	test ! -r \$(HOME)/src/kits/\$(DISTVNAME).tar.gz

tag:
	c4 label -d     \$(DISTNAME)_\$(VERSION_SYM) || true
	c4 label        \$(DISTNAME)_\$(VERSION_SYM)
	c4 labelsync -l \$(DISTNAME)_\$(VERSION_SYM) ...
#	cvs tag -F      \$(DISTNAME)_\$(VERSION_SYM) .

maintainer-diff:
	c4 diff     ...@\$(DISTNAME)_\$(VERSION_SYM) 

maintainer-dist: preexist dist tag
	cp \$(DISTVNAME).tar.gz \$(HOME)/src/kits
	mv \$(DISTVNAME).tar.gz \$(HOME)/backpack

maintainer-copy:

maintainer-clean: distclean
	-rm README Makefile

";
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
	      #OPTIMIZE	=> '-ggdb',
	      PMLIBDIRS => ['lib', 'Verilog', 'Netlist',],
	      EXE_FILES => [qw( vrename vpm vppp )],
	      'clean'	=> {FILES => qw (test_dir signals.vrename .vpm simv ),},
	      'dist'    => {COMPRESS => 'gzip -9f',
			    SUFFIX   => '.gz', 
			    DIST_DEFAULT => 'README all tardist',
			},
	      );

