#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2015 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;

BEGIN { plan tests => 19 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::Netlist::Debug = 1;
use Verilog::Netlist;
ok(1, "use");

##*** See also 41_example.t

# Setup options so files can be found
use Verilog::Getopt;
my $opt = new Verilog::Getopt;
$opt->parameter( "+incdir+verilog",
		 "-y","verilog",
    );

# Prepare netlist
my $nl = new Verilog::Netlist (options => $opt,
			       keep_comments => 1,
			       link_read_nonfatal=>1,
    );
foreach my $file ('verilog/v_hier_top.v',
		  'verilog/v_hier_top2.v',
		  'verilog/v_sv_mod.v'
    ) {
    $nl->read_file (filename=>$file);
}
# Read in any sub-modules
$nl->link();
$nl->lint();  # Optional, see docs; probably not wanted
$nl->exit_if_error();

print "Level tests\n";
is($nl->find_module("v_hier_top")->level, 3);
is($nl->find_module("v_hier_sub")->level, 2);
is($nl->find_module("v_hier_subsub")->level, 1);

my @mods = map {$_->name} $nl->modules_sorted_level;
is_deeply (\@mods, ['$root',
		    'v_hier_noport',
		    'v_hier_subsub',
		    'v_sv_pgm',
		    'v_hier_sub',
		    'v_hier_top2',
		    'v_recursive',
		    'v_hier_top',
		    'v_sv_mod']);

# Width checks
{
    my $mod = $nl->find_module("v_hier_top");
    is (_width_of($mod,"WC_w1"), 1);
    is (_width_of($mod,"WC_w1b"), 1);
    is (_width_of($mod,"WC_w3"), 3);
    is (_width_of($mod,"WC_w4"), 4);
    is (_width_of($mod,"WC_p32"), 32);
    is (_width_of($mod,"WC_p1"), 1);
    is (_width_of($mod,"WC_p3"), 3);
    is (_width_of($mod,"WC_p4"), 4);
    is (_width_of($mod,"WC_pint"), 32);
}

# Port accessors
{
    my $mod = $nl->find_module("v_hier_sub");

    my @o = $mod->ports_sorted;
    ok ($#o == 2 && $o[0]->name eq 'avec');

    @o = $mod->ports_ordered;
    ok ($#o == 2 && $o[0]->name eq 'clk');
}

# Comments
{
    my $mod = $nl->find_module("v_hier_top2");

    my $net = $mod->find_net("iosig");
    ok($net);
    # Someday ->comment should include stuff before the ; also
    is($net->comment, "/* synthesis aftersemi*/\n// NetListName=F12_IO");
}

ok(1);

sub _width_of {
    my $mod = shift;
    my $name = shift;
    if (!$mod) {
	warn "%Warning: No module found,";
	return;
    }
    my $sig = $mod->find_net($name);
    if (!$sig) {
	warn "%Warning: No signal '$name' found,";
	return;
    }
    return $sig->width;
}
