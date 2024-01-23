#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2024 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { plan tests => 6 }
BEGIN { require "./t/test_utils.pl"; }

print "Checking vrename...\n";
{
    # -List
    my $changefile = "test_dir/signals.vrename";
    unlink $changefile;
    my $cmd = "${PERL} ./vrename -changefile=$changefile -list -xref verilog/test.v";
    run_system ($cmd);
    ok(1, "vrename list");
    ok(files_identical($changefile, "t/50_vrename.out"), "diff");
    unlink $changefile;
}
{
    # Try renaming
    mkdir 'test_dir/verilog', 0777;
    my $cmd = ("${PERL} ./vrename -change --changefile verilog/test.vrename"
	       ." -o test_dir verilog/test.v");
    run_system ($cmd);
    ok(1, "vrename change");
    ok(-r 'test_dir/verilog/test.v', "diff");
}

{
    # Crypt
    my $changefile = "test_dir/signals.vrename";
    my $cmd = ("${PERL} ./vrename -changefile=$changefile -list --crypt"
	       ." -o test_dir verilog/test.v");
    run_system ($cmd);
    $cmd = ("${PERL} ./vrename -changefile=$changefile -change --crypt"
	    ." -o test_dir verilog/test.v");
    run_system ($cmd);
    ok(1, "vrename crypt");
    ok(-r 'test_dir/verilog/test.v', "output exists");
}
