#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;

BEGIN { plan tests => 2 }
BEGIN { require "t/test_utils.pl"; }

$ENV{HARNESS_ACTIVE} = 1;  # vsplitmodule checks this and doesn't die

print "Checking vsplitmodule...\n";
{
    # -List
    my $out = "test_dir/a.v";
    unlink $out;
    run_system ("${PERL} ./vsplitmodule");
    ok(1);
    ok(-r $out);
    unlink $out;
}
