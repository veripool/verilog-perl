#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 19 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::Netlist::Debug = 1;
use Verilog::Netlist;
ok(1);

##*** See also 41_example.t

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

print "Level tests\n";
ok($nl->find_module("v_hier_top")->level, 3);
ok($nl->find_module("v_hier_sub")->level, 2);
ok($nl->find_module("v_hier_subsub")->level, 1);

my @mods = map {$_->name} $nl->modules_sorted_level;
ok ($mods[0], 'v_hier_noport');
ok ($mods[1], 'v_hier_subsub');
ok ($mods[2], 'v_hier_sub');
ok ($mods[3], 'v_hier_top2');
ok ($mods[4], 'v_hier_top');

# Width checks
{
    my $mod = $nl->find_module("v_hier_top");
    ok (_width_of($mod,"WC_w1"), 1);
    ok (_width_of($mod,"WC_w1b"), 1);
    ok (_width_of($mod,"WC_w3"), 3);
    ok (_width_of($mod,"WC_w4"), 4);
    ok (_width_of($mod,"WC_p32"), 32);
    ok (_width_of($mod,"WC_p1"), 1);
    ok (_width_of($mod,"WC_p3"), 3);
    ok (_width_of($mod,"WC_p4"), 4);
    ok (_width_of($mod,"WC_pint"), 32);
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
