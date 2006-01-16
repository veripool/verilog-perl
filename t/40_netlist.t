#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 2 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::Netlist::Debug = 1;
use Verilog::Netlist;
ok(1);
{
    print "Checking example in Netlist.pm\n";

  use Verilog::Netlist;

    # Setup options so files can be found
    use Verilog::Getopt;
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );

    # Prepare netlist
    my $nl = new Verilog::Netlist (options => $opt,
				   link_read_nonfatal=>1,
				   );
    foreach my $file ('verilog/v_hier_top.v', 'verilog/v_hier_top2.v') {
	$nl->read_file (filename=>$file);
    }
    # Read in any sub-modules
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();

    foreach my $mod ($nl->top_modules_sorted) {
	show_hier ($mod, "  ", "","");
    }

    sub show_hier {
	my $mod = shift;
	my $indent = shift;
	my $hier = shift;
	my $cellname = shift;
	if (!$cellname) {$hier = $mod->name;} #top modules get the design name
	else {$hier .= ".$cellname";} #append the cellname
	printf ("%-45s %s\n", $indent."Module ".$mod->name,$hier);
	foreach my $sig ($mod->ports_sorted) {
	    printf ($indent."	  %sput %s\n", $sig->direction, $sig->name);
	}
	foreach my $cell ($mod->cells_sorted) {
	    printf ($indent. "    Cell %s\n", $cell->name);
	    foreach my $pin ($cell->pins_sorted) {
		printf ($indent."     .%s(%s)\n", $pin->name, $pin->netname);
	    }
	    show_hier ($cell->submod, $indent."	 ", $hier, $cell->name) if $cell->submod;
	}
    }

    print "Dump\n";
    $nl->dump;
}


ok(1);
