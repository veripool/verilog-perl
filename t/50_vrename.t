#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

print "Checking vrename...\n";
{
    # -List
    my $changefile = "test_dir/signals.vrename";
    unlink $changefile;
    run_system ("${PERL} ./vrename -changefile=$changefile -list -xref verilog/test.v");
    ok(1);
    ok(files_identical($changefile, "t/50_vrename.out"));
    unlink $changefile;
}
{
    # Try renaming
    mkdir 'test_dir/verilog', 0777;
    run_system ("${PERL} ./vrename -change --changefile verilog/test.vrename"
		." -o test_dir verilog/test.v");
    ok(1);
    ok(-r 'test_dir/verilog/test.v');
}

{
    # Crypt
    my $changefile = "test_dir/signals.vrename";
    run_system ("${PERL} ./vrename -changefile=$changefile -list --crypt"
		." -o test_dir verilog/test.v");
    run_system ("${PERL} ./vrename -changefile=$changefile -change --crypt"
		." -o test_dir verilog/test.v");
    ok(1);
    ok(-r 'test_dir/verilog/test.v');
}
