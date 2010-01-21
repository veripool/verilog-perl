#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vppreproc...\n";

vppreproc ("t/80_vppreproc_none.out",   "test_dir/vppreproc_none.v",	"");
vppreproc ("t/80_vppreproc_cmped.out",  "test_dir/vppreproc_cmped.v",	"--nocomment --pedantic");
vppreproc ("t/80_vppreproc_simple.out", "test_dir/vppreproc_simple.v", "--simple");

sub vppreproc {
    my $checkname = shift;
    my $out = shift;
    my $flags = shift;

    run_system ("${PERL} vppreproc ${flags} -y verilog inc2.v > $out");
    ok(-r $out);
    ok(files_identical ($out, $checkname));
}
