#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2008 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vperlpp...\n";

vperlpp ("t/80_vperlpp_none.out",   "test_dir/vperlpp_none.v",	"");
vperlpp ("t/80_vperlpp_cmped.out",  "test_dir/vperlpp_cmped.v",	"--nocomment --pedantic");
vperlpp ("t/80_vperlpp_simple.out", "test_dir/vperlpp_simple.v", "--simple");

sub vperlpp {
    my $checkname = shift;
    my $out = shift;
    my $flags = shift;

    run_system ("${PERL} vperlpp ${flags} -y verilog inc2.v > $out");
    ok(-r $out);
    ok(files_identical ($out, $checkname));
}
