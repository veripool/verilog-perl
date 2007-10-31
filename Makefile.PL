# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'perl Makefile.PL' to create a Makefile for this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

require 5.005;
use ExtUtils::MakeMaker;
use Carp;
use Config;

sub MY::postamble {
    my $out="";
    # Note OPTIMIZE is passed from upper makefile, so this code needed there too.
    if ($Config{osname} =~ /cygwin/i || $Config{archname} =~ /cygwin/i) {
	# Cygwin ExtUtils::MakeMaker ignores our LIBS declaration and says
	# "No library found for -lstdc++".  Force it.
	$out .= "LDLOADLIBS += -lstdc++\n";
	# Cygwin: High optimization causes g++ "out of memory"
	$out .= "OPTIMIZE += -O\n";
    }
    $out .= "CCFLAGS += -Wall -Wno-unused -Werror\n" if $ENV{VERILATOR_AUTHOR_SITE};
    $out .= "CCFLAGS  += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= "OPTIMIZE += -Wno-unused\n" if $ENV{VERILATOR_AUTHOR_SITE};  # Makefile has another -Wall
    $out .= "OPTIMIZE += $ENV{VERILOGPERL_CCFLAGS}\n" if defined $ENV{VERILOGPERL_CCFLAGS};
    $out .= "
README: Verilog-Perl.pod
	-rm -rf \$@
	pod2text --loose \$< > \$@

clean::
	-rm -rf simv .vpm test_dir *.tmp

dist: maintainer-copy distcheck README

## Maintainer use:
preexist:
	test ! -r \$(HOME)/src/kits/\$(DISTVNAME).tar.gz
	test -s README

tag:
	svnorcvs tag  \$(DISTNAME)_\$(VERSION_SYM)

maintainer-diff:
	svnorcvs diff \$(DISTNAME)_\$(VERSION_SYM) 

maintainer-dist: preexist dist tag
	cp \$(DISTVNAME).tar.gz \$(HOME)/src/kits
	mv \$(DISTVNAME).tar.gz \$(HOME)/backpack

maintainer-copy:

maintainer-clean: distclean
	-rm -rf README Makefile MANIFEST.bak \$(MAKEFILE_OLD)
";
    return $out;
}

local $! = undef;
`flex --version`; ($?==0) or die "\n%Error: 'flex' must be installed to build\n";
`bison --version`; ($?==0) or die "\n%Error: 'bison' must be installed to build\n";
`g++ --version`; ($?==0) or die "\n%Error: 'gcc/g++' must be installed to build\n";

WriteMakefile(
	      DISTNAME  => 'Verilog-Perl',
	      NAME      => 'Verilog::Language',
	      AUTHOR	=> 'Wilson Snyder <wsnyder@wsnyder.org>',
	      ABSTRACT  => 'Verilog language utilities and parsing',
	      VERSION_FROM  => 'Language.pm',
	      NO_META	=> 1,
	      #OPTIMIZE	=> '-ggdb',
	      PREREQ_PM => {'Pod::Usage' => 0,
			},
	      PMLIBDIRS => ['lib', 'Verilog', 'Netlist',],
	      EXE_FILES => [qw( vrename vpm vppp vhier vsplitmodule )],
	      'clean'	=> {FILES => qw (test_dir signals.vrename .vpm simv ),},
	      'dist'    => {COMPRESS => 'gzip -9f',
			    SUFFIX   => '.gz', 
			    DIST_DEFAULT => 'README all tardist',
			},
	      );

