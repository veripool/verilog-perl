#!/usr/bin/perl -w
# $Revision: 1.3 $$Date$$Author$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2005 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vppp...\n";

vppp ("t/80_vppp_none.out",   "");
vppp ("t/80_vppp_cmped.out", "--nocomment --pedantic");
vppp ("t/80_vppp_simple.out", "--simple");

sub vppp {
    my $checkname = shift;
    my $flags = shift;

    my $out = "test_dir/vppp.v";
    run_system ("${PERL} vppp ${flags} -y verilog inc2.v > $out");
    ok(-r $out);
    ok(files_identical ($checkname, $out));
}
