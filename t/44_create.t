#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2021 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { plan tests => 3 }
BEGIN { require "./t/test_utils.pl"; }

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
	    $b->new_pin(name=>'w', portname=>'w', pinnamed=>1, pinselects=>[{netname=>'y', msb=>2, lsb=>0}], @fl);
	}
    }

    $nl->link;
    my $fh = IO::File->new('test_dir/44_create.dmp', "w") or die "%Error: $! creating dump file,";
    print $fh $nl->verilog_text;
    $fh->close;
    ok(files_identical("test_dir/44_create.dmp", "t/44_create.out"));
}

ok(1, "done");
