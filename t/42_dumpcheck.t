#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;

BEGIN { plan tests => 12 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::SigParser::Debug = $Verilog::Parser::Debug = 1;
use Verilog::Netlist;
ok(1);

check ('test_dir/42.dmp', ['verilog/v_hier_top.v', 'verilog/v_hier_top2.v', 'verilog/v_comments.v'],
       [link_read_nonfatal=>1, keep_comments => 1,]);
ok(1);
ok(files_identical("test_dir/42.dmp", "t/42_dumpcheck_1.out"));

my $n2 = check ('test_dir/42_n2.dmp', ['verilog/pinorder.v'],
		[link_read_nonfatal=>1, keep_comments => 1,]);
ok(1);
ok(files_identical("test_dir/42_n2.dmp", "t/42_dumpcheck_2.out"));
ok(files_identical("test_dir/42_n2.dmp.v", "t/42_dumpcheck_2v.out"));

check ('test_dir/42_v2k.dmp', ['verilog/v_v2k.v'],
       [link_read_nonfatal=>1, keep_comments => 1,]);
ok(1);
ok(files_identical("test_dir/42_v2k.dmp", "t/42_dumpcheck_v2k.out"));

print "Edit tests\n";
$n2->find_module("pinorder4")->find_cell("foo3")->delete;
$n2->find_module("pinorder4")->find_cell("foo1")->find_pin("x")->delete;
$n2->find_module("pinorder4")->find_cell("foo1")->find_pin("def")->delete;
$n2->find_module("pinorder4")->find_net("IPCD_const")->delete;
$n2->find_module("foo2")->delete;
vwrite($n2, "test_dir/42.ed.v");
ok(1);
ok(files_identical("test_dir/42.ed.v", "t/42_dumpcheck_2e.out"));

check ('test_dir/42_sv.dmp', ['verilog/v_sv_mod.v'],
       [link_read_nonfatal=>0, keep_comments => 1,]);
ok(1);
ok(files_identical("test_dir/42_sv.dmp", "t/42_dumpcheck_sv.out"));

sub check {
    my $outfilename = shift;
    my $files = shift;
    my $nl_opts = shift;
    # Setup options so files can be found
    use Verilog::Getopt;
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );
    my $nl = new Verilog::Netlist (options => $opt,
				   link_read_nonfatal=>1,
				   keep_comments => 1,
				   @{$nl_opts});
    foreach my $file (@{$files}) {
	$nl->read_file (filename=>$file);
    }
    # Read in any sub-modules
    $nl->link();
    $nl->lint();
    $nl->exit_if_error();

    print "Dump\n";
    {
	open (SAVEOUT, ">&STDOUT") or die "%Error: Can't dup stdout,";
	if (0) { print SAVEOUT "To prevent used only once"; }
	open (STDOUT, ">$outfilename") or die "%Error: $! $outfilename,";
	$nl->dump;
	close(STDOUT);
	open (STDOUT, ">&SAVEOUT");
    }

    vwrite($nl, $outfilename.".v");
    return $nl;
}

sub vwrite {
    my $nl = shift;
    my $filename = shift;
    my $fh = IO::File->new($filename,"w") or die "%Error: $! writing $filename,";
    print $fh $nl->verilog_text;
    $fh->close;
}
