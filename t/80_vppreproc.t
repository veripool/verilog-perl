#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2012 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 8 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vppreproc...\n";

vppreproc ("t/80_vppreproc_none.out",   "test_dir/vppreproc_none.v",	"");
vppreproc ("t/80_vppreproc_cmped.out",  "test_dir/vppreproc_cmped.v",	"--nocomment --pedantic");
vppreproc ("t/80_vppreproc_simple.out", "test_dir/vppreproc_simple.v", "--simple");
vppreproc ("t/80_vppreproc_defines.out", "test_dir/vppreproc_defines.v", "--dump-defines");

sub vppreproc {
    my $checkname = shift;
    my $out = shift;
    my $flags = shift;

    my $cmd = "${PERL} ./vppreproc ${flags} -y verilog inc2.v > $out";
    run_system ($cmd);
    ok(-r $out, "vppreproc output from: $cmd");
    ok(files_identical ($out, $checkname), "diff");
}
