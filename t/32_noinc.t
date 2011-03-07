#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2011 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 7 }
BEGIN { require "t/test_utils.pl"; }

#######################################################################

use Verilog::Getopt;
use Verilog::Preproc;
ok(1, "use");

# Check we get error
eval {
    check();
};
like ($@, qr/32_noinc.v:\d+: Cannot open notfound/);
check(include_open_nonfatal=>1);
ok (1);

# Check no error

sub check {
    my @opts = (@_);

    my $opt = new Verilog::Getopt;

    my $pp = new Verilog::Preproc (options=>$opt,
				   @opts);
    ok(1, "new");

    #$pp->debug(9);
    $pp->open("t/32_noinc.v");
    ok(1, "open");

    while (defined(my $line = $pp->getline())) {
	#print "LINE: $line";
    }
}
