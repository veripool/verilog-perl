#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

use strict;
use Test;
use Data::Dumper; $Data::Dumper::Indent = 1; #Debug

BEGIN { plan tests => 3 }
BEGIN { require "t/test_utils.pl"; }

######################################################################

package MyParser;
use Verilog::Parser;
use strict;
use base qw(Verilog::Parser);

sub _common {
    my $self = shift;
    my $what = shift;
    my $call_self = shift;
    my $text = shift;
    if (defined $self->unreadback && $self->unreadback ne '') {
	$self->{dump_fh}->printf("%s:%03d: unreadback '%s'\n",
				 $self->filename, $self->lineno,
				 $self->unreadback);
	$self->unreadback('');
    }
    $self->{dump_fh}->printf("%s:%03d: %s '%s'\n",
			     $self->filename, $self->lineno,
			     uc $what, $text);
}

sub comment {	$_[0]->_common('comment', @_); }
sub string {	$_[0]->_common('string', @_); }
sub keyword {	$_[0]->_common('keyword', @_); }
sub symbol {	$_[0]->_common('symbol', @_); }
sub operator {	$_[0]->_common('operator', @_); }
sub number {	$_[0]->_common('number', @_); }

######################################################################

package main;

use Verilog::Parser;
use Verilog::Preproc;
ok(1);

# Use our class and dump to a file
my $dump_fh = new IO::File(">test_dir/34.dmp") or die "%Error: $! test_dir/34.dmp,";

read_test("verilog/v_hier_subprim.v", $dump_fh);
read_test("verilog/v_hier_sub.v", $dump_fh);
ok(1);
$dump_fh->close();

# Did we read the right stuff?
ok(files_identical("test_dir/34.dmp", "t/34_parser.out"));

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
