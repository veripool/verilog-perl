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
ok(1, "use");
{
    local *STDOUT;
    open(STDOUT, ">", "test_dir/41_example.dmp");

    print "Checking example in Netlist.pm\n";

    use Verilog::Netlist;

    # Setup options so files can be found
    use Verilog::Getopt;
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );

    # Prepare netlist
    my $nl = new Verilog::Netlist(options => $opt,
				  link_read_nonfatal=>1,
	);
    foreach my $file ('verilog/v_hier_top.v', 'verilog/v_hier_top2.v') {
	$nl->read_file(filename=>$file);
    }
    # Read in any sub-modules
    $nl->link();
    #$nl->lint();  # Optional, see docs; probably not wanted
    $nl->exit_if_error();

    my %recursing;  # Prevent recursion; not in example
    foreach my $mod ($nl->top_modules_sorted) {
	show_hier($mod, "  ", "", "");
    }

    sub show_hier {
	my $mod = shift;
	my $indent = shift;
	my $hier = shift;
	my $cellname = shift;
	return if $recursing{$mod->name}++;  # Not in example
	if (!$cellname) {$hier = $mod->name;} #top modules get the design name
	else {$hier .= ".$cellname";} #append the cellname
	printf ("%-45s %s\n", $indent."Module ".$mod->name,$hier);
	foreach my $sig ($mod->ports_sorted) {
	    printf ($indent."	  %sput %s\n", $sig->direction, $sig->name);
	}
	foreach my $cell ($mod->cells_sorted) {
	    printf ($indent. "    Cell %s\n", $cell->name);
	    foreach my $pin ($cell->pins_sorted) {
		printf($indent."     .%s(%s)\n", $pin->name, $pin->netname);
	    }
	    show_hier($cell->submod, $indent."	 ", $hier, $cell->name) if $cell->submod;
	}
	--$recursing{$mod->name};  # Not in example
    }

    print "Dump\n";
    $nl->dump;
}

ok(files_identical("test_dir/41_example.dmp", "t/41_example.out"));

ok(1, "done");
