#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2013 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { plan tests => 2 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::Netlist::Debug = 1;
use Verilog::Netlist;
use Verilog::Getopt;
ok(1, "use");
{
    # Setup options so files can be found
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );

    # Prepare netlist
    my $nl = new Verilog::Netlist (options => $opt,
				   );
    foreach my $file ('verilog/v_gate.v') {
	$nl->read_file (filename=>$file);
    }
    # Read in any sub-modules
    $nl->read_libraries();
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();

    print "Dump\n";
    $nl->dump;
}

ok(1, "done");
