#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2007-2017 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { require "./t/test_utils.pl"; }
my @execs = glob ("blib/script/[a-z]*");
plan tests => (3 * ($#execs+1));

foreach my $exe (@execs) {
    print "Doc test of: $exe\n";
    ok (-e $exe, "exe exists: $exe");
  SKIP: {
      skip("vsplitmodule is only example (harmless)",2)
	  if ($exe =~ /vsplitmodule/);

      my $cmd = "$PERL $exe --help 2>&1";
      my $help = `$cmd`;
      like ($help, qr/--version/, "help result for: $cmd");

      $cmd = "$PERL $exe --version 2>&1";
      $help = `$cmd`;
      like ($help, qr/Version.*[0-9]/, "version result for: $cmd");
    }
}
