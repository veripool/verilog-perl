#!/usr/bin/perl -w
# $Id$
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.

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
    warn ("%Warning: $fileline: $text\n");
    $self->{_errored} = 1;
    $::Any_Error = 1;
}

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
ok(1);

check_series(glob("verilog/*.v"));

if (!$ENV{VERILOG_TEST_DIRS}) {
    skip("VERILOG_TEST_DIRS not set (harmless)",1);
} else {
    check_series(map {glob $_} split(/:/,$ENV{VERILOG_TEST_DIRS}));
}

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

    print "-"x70,"\n";
    print "read $filename\n";
    my $pp = Verilog::Preproc->new(keep_comments=>0,
				   include_open_nonfatal=>1);

    my $parser = new MyParser();
    $pp->open($filename);
    $parser->parse_preproc_file($pp);

    #if ($parser->{_errored})
}
