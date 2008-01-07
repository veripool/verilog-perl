#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2008 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 10 }
BEGIN { require "t/test_utils.pl"; }

#$Verilog::SigParser::Debug = $Verilog::Parser::Debug = 1;
use Verilog::Netlist;
ok(1);

check ('test_dir/42.dmp', 'verilog/v_hier_top.v', 'verilog/v_hier_top2.v', 'verilog/v_comments.v');
ok(1);
ok(files_identical("test_dir/42.dmp", "t/42_dumpcheck_1.out"));

my $n2 = check ('test_dir/42_n2.dmp', 'verilog/pinorder.v');
ok(1);
ok(files_identical("test_dir/42_n2.dmp", "t/42_dumpcheck_2.out"));
ok(files_identical("test_dir/42_n2.dmp.v", "t/42_dumpcheck_2v.out"));

check ('test_dir/42_v2k.dmp', 'verilog/v_v2k.v', );
ok(1);
ok(files_identical("test_dir/42_v2k.dmp", "t/42_dumpcheck_v2k.out"));

print "Edit tests\n";
$n2->find_module("pinorder4")->find_cell("foo3")->delete;
$n2->find_module("pinorder4")->find_cell("foo1")->find_pin("x")->delete;
vwrite($n2, "test_dir/42.ed.v");
ok(1);
ok(files_identical("test_dir/42.ed.v", "t/42_dumpcheck_2e.out"));

sub check {
    my $outfilename = shift;
    my @files = @_;
    # Setup options so files can be found
    use Verilog::Getopt;
    my $opt = new Verilog::Getopt;
    $opt->parameter( "+incdir+verilog",
		     "-y","verilog",
		     );
    my $nl = new Verilog::Netlist (options => $opt,
				   link_read_nonfatal=>1,
				   keep_comments => 1,
				   );
    foreach my $file (@files) {
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
