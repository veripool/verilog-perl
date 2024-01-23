#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2024 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 4 }
BEGIN { require "./t/test_utils.pl"; }

#######################################################################

use Verilog::Getopt;
use Verilog::Preproc;
ok(1, "use");

# Check we get error
SKIP: {
    if (`which gzip` !~ m!^/!
	|| `which gunzip` !~ m!^/!) {
	skip("no gzip installed (harmless)",3);
    }
    system("gzip t/32_noinc.v -c > test_dir/33_gzip.v.gz");
    ok (-r "test_dir/33_gzip.v.gz", "gzip test creation");

    my $opt = new Verilog::Getopt;
    my $pp = new Verilog::Preproc (options=>$opt,
				   include_open_nonfatal=>1,);
    $pp->open("test_dir/33_gzip.v.gz");
    ok(1, "open");

    my $hit;
    while (defined(my $line = $pp->getline())) {
	#print "TEXT $line";
	$hit = 1 if $line =~ /text/;
    }
    ok ($hit, "decompress found text");
}
