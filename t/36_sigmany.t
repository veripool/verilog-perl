#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
######################################################################
#  (delete-matching-lines "^#\\|^ok \\|^1\\.\\.\\|^not ok")

use strict;
use Test;

BEGIN { plan tests => 3 }
BEGIN { require "t/test_utils.pl"; }

our $Any_Error;

######################################################################

package MyParser;
use Verilog::SigParser;
use strict;
use vars qw(@ISA);
@ISA = qw(Verilog::SigParser);

sub _common {
}

sub error {
    my ($self,$text,$token)=@_;
    my $fileline = $self->filename.":".$self->lineno;
    if ($text !~ /\`math/) {
	warn ("%Warning: $fileline: $text\n");
	$self->{_errored} = 1;
	$::Any_Error = 1;
    }
}

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
ok(1);

my @files;
if (!$ENV{VERILOG_TEST_FILES}) {
    skip("VERILOG_TEST_FILES not set (harmless)",1);
    # export VERILOG_TEST_FILES="$V4/test_regress/t/t_case*.v"
    @files = ("verilog/*.v");
} else {
    ok(1);
    @files = split(/:/,$ENV{VERILOG_TEST_FILES});
}
check_series(map {glob $_} @files);

######################################################################

sub check_series {
    my @files = @_;
    $Any_Error = 0;
    foreach my $file (@files) {
	next if $file =~ m!/inc!;
	read_test($file);
    }
    ok(!$Any_Error);
}

sub read_test {
    my $filename = shift;
    my $parser = one_parse($filename, 0);
    if ($ENV{VERILOG_TEST_DEBUG} && $parser->{_errored}) {
	print "======== REPARSING w/debug\n";
	one_parse($filename, 9);
    }
}

sub one_parse {
    my $filename = shift;
    my $debug = shift;

    print "="x70,"\n";
    print "read $filename\n";
    my $pp = Verilog::Preproc->new(keep_comments=>0,
				   include_open_nonfatal=>1);

    my $parser = new MyParser();
    $parser->debug($debug);
    $pp->open($filename);
    $parser->parse_preproc_file($pp);
    return $parser;
}
