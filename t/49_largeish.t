#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;
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
prep("test_dir/smallish.v",1);
prep("test_dir/largeish.v",1+$nets);

per_net_test('sigparser', 100000);
per_net_test('netlist', 100000);

######################################################################

sub prep {
    my $filename = shift;
    my $count = shift;

    my $fh = IO::File->new(">$filename");
    print $fh "module largeish;\n";
    for (my $i=0; $i<$count; $i++) {
	print $fh " wire ",sprintf("n%010d",$i),";\n";  # Keep size of each net constant
    }
    print $fh "endmodule\n";

    printf "$filename: %6.3f MB\n", (-s $filename)/1024/1024;
}

sub per_net_test {
    my $pack = shift;
    my $limit = shift;

    my $mem = get_memory_usage();
    my $time = time();
    read_test($pack,"test_dir/smallish.v");
    my $smallmem = get_memory_usage();
    my $smalltime = time();
    read_test($pack,"test_dir/largeish.v");
    my $largemem = get_memory_usage();
    my $largetime = time();
    my $delta = $largemem-$smallmem;
    my $deltatime = $largetime-$smalltime;
    my $mpn = $delta / $nets;
    printf "For $pack: Time %d s, Memory %1.3f MB  Alloced %1.3f MB  Mem/net %d\n"
	, $deltatime, $largemem/1024/1024, $delta/1024/1024, $mpn;

    ok(1);
    if ($mpn == 0) {
	skip("get_memory_usage isn't supported",1);
    } elsif ($mpn < $limit) {
	ok(1);
    } else {
	warn "%Warning: ",$mpn," bytes per signal\n";
	if (!$ENV{VERILATOR_AUTHOR_SITE} || $ENV{HARNESS_FAST}) {
	    # It's somewhat sensitive unless there's a lot of loops,
	    # and lots of loops is too slow for users to deal with.
	    skip("fat, but author only test",1);
	} else {
	    ok(0);
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
