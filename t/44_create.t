#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 2 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::Netlist::Debug = 1;
use Verilog::Netlist;
use Verilog::Getopt;
ok(1);
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
	my $x = $moda->new_net (name=>'x', @fl, type=>'input', msb=>2, lsb=>0,);
	my $y = $moda->new_net (name=>'y', @fl, type=>'output', msb=>2, lsb=>0,);
	my $b = $moda->new_cell (name=>'i_b', submodname=>'b', @fl);
	{
	    $b->new_pin(name=>'z', portname=>'z', pinnamed=>1, netname=>'x', @fl);
	    $b->new_pin(name=>'w', portname=>'w', pinnamed=>1, netname=>'y', @fl);
	}
    }

    #$nl->link;
    print $nl->verilog_text;
}

ok(1);
