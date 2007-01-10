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

######################################################################

package MyParser;
use Verilog::SigParser;
use strict;
use vars qw(@ISA);
@ISA = qw(Verilog::SigParser);

sub module {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    $self->{dump_fh}->print("module $keyword $name\n");
}

sub task {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    $self->{dump_fh}->print("task $keyword $name\n");
}

sub function {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    $self->{dump_fh}->print("function $keyword $name\n");
}

sub signal_decl {
    my $self = shift;
    my $keyword = shift;
    my $name = shift;
    my $vector = shift||"";
    my $mem = shift||"";
    my $signed = shift||"";
    $self->{dump_fh}->print("signal_decl $keyword $name $vector $mem $signed\n");
}

sub instant {
    my $self = shift;
    my $module = shift;
    my $cell = shift;
    $self->{dump_fh}->print("instant $module $cell\n");
}

sub pin {
    my $self = shift;
    my $name = shift;
    my $conn = shift||"";
    my $number = shift||"";
    $self->{dump_fh}->print("pin $name $conn $number\n");
}

sub port {
    my $self = shift;
    my $name = shift;
    $self->{dump_fh}->print("port $name\n");
}

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
ok(1);

# Use our class and dump to a file
my $dump_fh = new IO::File("test_dir/35.dmp","w")
    or die "%Error: $! test_dir/35.dmp,";

read_test("verilog/v_hier_subprim.v", $dump_fh);
read_test("verilog/v_hier_sub.v", $dump_fh);
ok(1);
$dump_fh->close();

# Did we read the right stuff?
ok(files_identical("test_dir/35.dmp", "t/35_sigparser.out"));

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
