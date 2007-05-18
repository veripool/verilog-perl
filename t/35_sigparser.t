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

sub _common {
    my $self = shift;
    my $what = shift;
    my $call_self = shift;
    my @args = @_;

    my $args="";
    foreach (@args) { $args .= defined $_ ? " '$_'" : " undef"; }
    my $urb = $self->unreadback;
    $self->{dump_fh}->printf("%s:%03d: %s %s\n",
			     $self->filename, $self->lineno,
			     uc $what,
			     $args);
}

sub error {
    my ($self,$text,$token)=@_;
    my $fileline = $self->filename.":".$self->lineno;
    warn ("%Warning: $fileline: $text\n");
}

sub attribute {	$_[0]->_common('attribute', @_); }
sub function {	$_[0]->_common('function', @_); }
sub instant {	$_[0]->_common('instant', @_); }
sub module {	$_[0]->_common('module', @_); }
sub pin {	$_[0]->_common('pin', @_); }
sub port {	$_[0]->_common('port', @_); }
sub signal_decl { $_[0]->_common('signal_decl', @_); }
sub task {	$_[0]->_common('task', @_); }

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
ok(1);

# Use our class and dump to a file
my $dump_fh = new IO::File("test_dir/35.dmp","w")
    or die "%Error: $! test_dir/35.dmp,";

read_test("/dev/null", $dump_fh);  # Empty files should be ok
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
    #$parser->debug(9);

    # Preprocess
    $pp->open($filename);
    $parser->parse_preproc_file($pp);
}
