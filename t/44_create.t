#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2016 by Wilson Snyder.  This program is free software;
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
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );

    # Prepare netlist
    my $nl = new Verilog::Netlist (options => $opt,
				   link_read_nonfatal=>1,
				   );

    my @fl = (filename=>'44_create.t', lineno=>0);

    my $moda = $nl->new_module (name=>'a', @fl);
    {
	my $x = $moda->new_port (name=>'x', @fl, direction=>'input',  data_type=>'[2:0]',);
	my $y = $moda->new_port (name=>'y', @fl, direction=>'output', data_type=>'[2:0]',);
	my $b = $moda->new_cell (name=>'i_b', submodname=>'b', @fl);
	{
	    $b->new_pin(name=>'z', portname=>'z', pinnamed=>1, netname=>'x', @fl);
	    $b->new_pin(name=>'w', portname=>'w', pinnamed=>1, netname=>'y', @fl);
	}
    }

    #$nl->link;
    print $nl->verilog_text;
}

ok(1, "done");
