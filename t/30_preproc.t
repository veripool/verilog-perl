#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2006 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 8 }
BEGIN { require "t/test_utils.pl"; }

#######################################################################
package MyPreproc;
use Verilog::Preproc;
use vars qw (@ISA);
@ISA = qw(Verilog::Preproc);
sub comment { print $::OUTTO "COMMENT: $_[1]\n";
	      $_[0]->unreadback(' /*CMT*/ '); }
package main;
#######################################################################

sub prep {
    my $opt = new Verilog::Getopt;
    $opt->parameter (qw(
			+incdir+verilog
			));
    return $opt;
}

use Verilog::Getopt;
ok(1);

use Verilog::Preproc;
ok(1);

{
    my $opt = prep();
    my $pp = new Verilog::Preproc (options=>$opt);
    ok(1);

    #$pp->debug(9);
    $pp->open("inc1.v");
    $pp->open("inc2.v");
    ok(1);

    my $fhout = IO::File->new(">test_dir/inc.out");

    my $ln = 1;
    while (defined(my $line = $pp->getline())) {
	print "LINE: $line";
	print $fhout $pp->filename.":".$pp->lineno.": ".$line;
	die if ++$ln > 2000;
    }
    ok(1);

    $fhout->close();
    ok(files_identical("test_dir/inc.out", "t/30_preproc.out"));
}

{
    my $opt = prep();
    my $pp = new MyPreproc (options=>$opt, keep_comments=>'sub',);
    $pp->open("inc1.v");
    $pp->open("inc2.v");

    my $fhout = IO::File->new(">test_dir/inc2.out");
    $::OUTTO = $fhout;
    while (defined(my $line = $pp->getline())) {
	print $fhout $pp->filename.":".$pp->lineno.": ".$line;
    }
    $fhout->close();
    ok(1);

    ok(files_identical("test_dir/inc2.out", "t/30_preproc2.out"));
}

