#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2017 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

BEGIN { require "./t/test_utils.pl"; }

use strict;
use Test;
use warnings;

$SIG{__WARN__} = sub {};

eval "use Storable;";
if ($@) {
    plan tests => 1;
    skip("Storable not installed so ignoring check (harmless)",1);
} else {
    plan tests => 4;
    eval "use Verilog::Netlist;";
    ok(1);
    if (1) {
	my $nl = new Verilog::Netlist;
	$nl->read_file(filename=>"verilog/v_hier_subsub.v");
	ok(1);
	Storable::store($nl, "test_dir/netlist.db");
	ok(1);
    }
    if (1) {
	my $nl = retrieve("test_dir/netlist.db");
	ok(1);
    }
}
