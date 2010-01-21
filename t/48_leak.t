#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;
use Data::Dumper; $Data::Dumper::Indent = 1;
BEGIN { eval "use Devel::Leak;"; }  # Optional

BEGIN { plan tests => 2 }
BEGIN { require "t/test_utils.pl"; }

use Verilog::SigParser;
use Verilog::Preproc;
use Verilog::Getopt;
use Verilog::Netlist;
use POSIX qw();

######################################################################

my $mem = get_memory_usage();
my $loops = 50;  # At least 10
my $mem_end; my $mem_mid;
my $handle;
for (my $i=0; $i<$loops; $i++) {
    test();
    my $newmem = get_memory_usage();
    my $delta = $newmem - $mem;
    print "$i: Memory $newmem kb  Alloced $delta kb\n" if $delta;
    $mem_mid = $newmem if $i==int($loops/2)-1;
    $mem_end = $newmem if $i==$loops-1;

    # The Devel checks must complete before $mem_mid is sampled, as they use memory
    if (0 && $Devel::Leak::VERSION) {
	Devel::Leak::NoteSV($handle)  if $i==int($loops/2)-4;
	Devel::Leak::CheckSV($handle) if $i==int($loops/2)-3;
	#warn "EXITING" if $i==int($loops/2)-3;
	#POSIX::_exit(10) if $i==int($loops/2)-3;
    }

    $mem = $newmem;
}
ok(1);
if ($mem == 0) {
    skip("get_memory_usage isn't supported",1);
} elsif ($mem_end <= $mem_mid) {
    ok(1);
} else {
    warn "%Warning: Leaked ",int(1024*($mem_end-$mem_mid)/($loops/2))," bytes per parse\n";
    if (!$ENV{VERILATOR_AUTHOR_SITE}) {
	# It's somewhat sensitive unless there's a lot of loops,
	# and lots of loops is too slow for users to deal with.
	skip("leaked, but author only test",1);
    } else {
	ok(0);
    }
}

######################################################################

sub test {
    read_test("verilog/v_hier_sub.v");
    read_test("verilog/parser_bugs.v");
    read_test("verilog/pinorder.v");
    read_test("verilog/parser_sv.v");
}

sub read_test {
    my $filename = shift;

    my $go = Verilog::Getopt->new();
    my $pp = Verilog::Preproc->new(keep_comments=>1);
    my $parser = Verilog::SigParser->new();
    #my $parser = Verilog::Parser->new();
    $pp->open($filename);
    ##Preproc_Only_Test:  while (defined($pp->getline())) {}

    $parser->parse_preproc_file($pp);

    my $nl = Verilog::Netlist->new();
    $nl->read_file(filename=>"verilog/v_hier_sub.v");
    $nl->delete;
    #print Dumper($nl); use Devel::Peek;  print "\nPEEK: \n";Dump(\$nl);
}
