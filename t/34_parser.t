#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License or the Perl Artistic License.

use strict;
use Test;
use Data::Dumper; $Data::Dumper::Indent = 1; #Debug

BEGIN { plan tests => 6 }
BEGIN { require "t/test_utils.pl"; }

our %_TestCoverage;

######################################################################

package MyParser;
use Verilog::Parser;
use strict;
use base qw(Verilog::Parser);

BEGIN {
    # Make functions like this:
    #  sub attribute {	$_[0]->_common('attribute', @_); }
    foreach my $cb (Verilog::Parser::callback_names()) {
	my $func = ' sub __CB__ { $_[0]->_common("__CB__", @_); } ';
	$func =~ s/__CB__/$cb/g;
	eval($func);
    }
}

sub _common {
    my $self = shift;
    my $what = shift;
    my $call_self = shift;
    my $text = shift;
    my $urb = $self->unreadback;

    $_TestCoverage{$what}++;
    if ($urb &&  $urb ne '') {
	$self->{dump_fh}->printf("%s:%03d: unreadback '%s'\n",
				 $self->filename, $self->lineno,
				 $urb);
	$self->unreadback('');
    }
    $self->{dump_fh}->printf("%s:%03d: %s '%s'\n",
			     $self->filename, $self->lineno,
			     uc $what, $text);
}

######################################################################

package main;

use Verilog::Parser;
use Verilog::Preproc;
ok(1);

# Use our class and dump to a file
my $dump_fh = new IO::File(">test_dir/34.dmp") or die "%Error: $! test_dir/34.dmp,";

my $p = new Verilog::Parser;
ok($p);
$p->lineno(100);
$p->filename("XXX");
ok($p->lineno == 100);

read_test("verilog/v_hier_subprim.v", $dump_fh);
read_test("verilog/v_hier_sub.v", $dump_fh);
read_test("verilog/example.v", $dump_fh);
ok(1);
$dump_fh->close();

# Did we read the right stuff?
ok(files_identical("test_dir/34.dmp", "t/34_parser.out"));

# Did we cover everything?
my $err;
foreach my $cb (Verilog::Parser::callback_names()) {
    if (!$_TestCoverage{$cb}) {
	$err=1;
	warn "%Warning: No test coverage for callback: $cb\n";
    }
}
ok (!$err);

######################################################################

sub read_test {
    my $filename = shift;
    my $dump_fh = shift;

    my $pp = Verilog::Preproc->new(keep_comments=>0,);

    my $parser = new MyParser (dump_fh => $dump_fh);

    # Preprocess
    $pp->open($filename);
    $parser->parse_preproc_file($pp);
}
