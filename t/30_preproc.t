#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test;

BEGIN { plan tests => 14 }
BEGIN { require "t/test_utils.pl"; }

#######################################################################
package MyPreproc;
use Verilog::Preproc;
use base qw(Verilog::Preproc);

sub comment { print $::OUTTO "COMMENT: $_[1]\n";
	      $_[0]->unreadback(' /*CMT*/ '); }

sub def_substitute {
    my ($self,$out) = @_;
    # Only do this for some tests, as it makes the output look strange
    if ($self->{_test_def_substitute}
	&& $out !~ /^".*"$/) {  # And don't corrupt `include test
	return "DS<".$out.">";
    } else {
	return $out;
    }
}

package main;
#######################################################################

sub prep {
    my $opt = new Verilog::Getopt;
    $opt->parameter (qw(
			+incdir+verilog
			+define+PREDEF_COMMAND_LINE
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
	#print "LINE: $line";
	print $fhout $pp->filename.":".$pp->lineno.": ".$line;
	die if ++$ln > 2000;
    }
    ok(1);

    $fhout->close();
    ok(files_identical("test_dir/inc.out", "t/30_preproc.out"));
}

test ('_sub', keep_comments=>'sub', _test_def_substitute=>1);
test ('_on',  keep_comments=>1,);
test ('_nows', keep_comments=>0, keep_whitespace=>0,);
test_getall ();

sub test {
    my $id = shift;
    my @args = @_;

    my $opt = prep();
    my $pp = new MyPreproc (options=>$opt, @args);
    $pp->open("inc1.v");
    $pp->open("inc2.v");
    $pp->open("inc_ifdef.v");

    my $fhout = IO::File->new(">test_dir/inc${id}.out");
    $::OUTTO = $fhout;
    while (defined(my $line = $pp->getline())) {
	print $fhout $pp->filename.":".$pp->lineno.": ".$line;
    }
    $fhout->close();
    ok(1);

    ok(files_identical("test_dir/inc${id}.out", "t/30_preproc${id}.out"));
}

sub test_getall {
    my $id = shift;
    my @args = @_;

    my $a;
    my $acalls = 0;
    {
	my $pp = new MyPreproc (options=>prep(), @args);
	$pp->open("inc1.v");
	while (defined(my $line = $pp->getline)) {
	    $a .= $line;
	    $acalls++;
	}
    }
    my $b;
    my $bcalls = 0;
    {
	my $pp = new MyPreproc (options=>prep(), @args);
	$pp->open("inc1.v");
	while (defined(my $all = $pp->getall)) {
	    $b .= $all;
	    $bcalls++;
	}
    }

    ok($a eq $b);
    ok($acalls > $bcalls);
}

