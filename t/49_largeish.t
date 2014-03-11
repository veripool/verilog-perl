#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2014 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;
use Time::HiRes qw(gettimeofday tv_interval);
use Data::Dumper; $Data::Dumper::Indent = 1;

BEGIN { plan tests => 4 }
BEGIN { require "t/test_utils.pl"; }

use Verilog::SigParser;
use Verilog::Preproc;
use Verilog::Getopt;
use Verilog::Netlist;
use POSIX qw();

######################################################################

our $nets = 10*1000;
our $Opt_Sym_Size = 30;
our $Opt_Spaced_Out = 0;   # Lots of stuff that preprocessor can rip out
our $Opt_Dir = $ENV{HARNESS_TEST_DIR}||"test_dir";  # Move to scratch disk for very large tests

prep("${Opt_Dir}/largeish_1.v",1);
prep("${Opt_Dir}/largeish_2.v",1+($nets/10));
prep("${Opt_Dir}/largeish_3.v",1+$nets);

per_net_test('sigparser', 100000);
per_net_test('netlist', 100000);

unlink(glob("${Opt_Dir}/largeish_*"));   # Fat, so don't keep around

######################################################################

sub prep {
    my $filename = shift;
    my $count = shift;

    my $fh = IO::File->new(">$filename");
    print $fh "module largeish;\n";
    my $wirefmt = " wire n%0".($Opt_Sym_Size-1)."d;\n";  # Each net is constant sized
    for (my $i=0; $i<$count; $i++) {
	printf $fh $wirefmt, $i;
	print $fh " "x1023,"\n" if $Opt_Spaced_Out;
    }
    print $fh "endmodule\n";

    printf "Wrote $filename: %6.3f MB\n", (-s $filename)/1024/1024;
}

sub per_net_test {
    my $pack = shift;
    my $limit = shift;

    my (@mem, @time, @size, @names, @secPerB);
    $names[1] = "${Opt_Dir}/largeish_1.v";
    $names[2] = "${Opt_Dir}/largeish_2.v";
    $names[3] = "${Opt_Dir}/largeish_3.v";

    $mem[0]  = get_memory_usage();
    $time[0] = [gettimeofday];

    for (my $i=1; $i<4; $i++) {
	read_test($pack, $names[$i]);
	$size[$i] = -s $names[$i];
	$mem[$i]  = get_memory_usage();
	$time[$i] = [gettimeofday];
    }

    for (my $i=2; $i<4; $i++) {
	my $deltamem = $mem[$i]-$mem[0];
	my $deltatime = tv_interval($time[$i-1],$time[$i]);
	my $mpn = $deltamem / $size[$i];
	$secPerB[$i] = $deltatime / ($size[$i]/1024/1024);
	printf "For $pack $names[$i]: File %1.3f MB, %1.3f s, %1.3f MB, Alloced %1.3f MB, %1.1f Alloc/FileB %1.1f s/MB\n"
	 , $size[$i]/1024/1024, $deltatime, $mem[$i]/1024/1024, $deltamem/1024/1024, $mpn, $secPerB[$i];
    }

    ok(1, "run complete");

    my $slope = $secPerB[3] / ($secPerB[2]||1);
  SKIP: {
      if ($slope > 0.5 && $slope < 2) {
	  ok(1, "complexity");
      } else {
	  if (!$ENV{VERILATOR_AUTHOR_SITE} || $ENV{HARNESS_FAST}) {
	      # It's somewhat sensitive unless there's a lot of loops,
	      # and lots of loops is too slow for users to deal with.
	      skip("waived, author only test",1);
	  } else {
	      warn "%Warning: ",$slope," non O(n) based on input file size, slope=$slope\n";
	      ok(0, "complexity");
	  }
	}
    }
}

sub read_test {
    my $pack = shift;
    my $filename = shift;

    if ($pack eq 'sigparser') {
	my $go = Verilog::Getopt->new();
	my $pp = Verilog::Preproc->new(keep_comments=>1);
	my $parser = Verilog::SigParser->new();
	#my $parser = Verilog::Parser->new();
	#$pp->debug(99);
	$pp->open($filename);
	##Preproc_Only_Test:  while (defined($pp->getline())) {}
	$parser->parse_preproc_file($pp);

	$pp->open($filename);
	while (defined($pp->getline())) {}

    }
    elsif ($pack eq 'netlist') {
	my $nl = Verilog::Netlist->new();
	$nl->read_file(filename=>$filename);
	$nl->delete;
    }
    else { die; }
}
