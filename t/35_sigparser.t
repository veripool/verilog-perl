#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2009 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License or the Perl Artistic License.

use strict;
use Test;

BEGIN { plan tests => 3 }
BEGIN { require "t/test_utils.pl"; }

######################################################################

package MyParser;
use Verilog::SigParser;
use strict;
use base qw(Verilog::SigParser);

sub _common {
    my $self = shift;
    my $what = shift;
    my $call_self = shift;
    my @args = @_;

    my $args="";
    foreach (@args) { $args .= defined $_ ? " '$_'" : " undef"; }
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
sub endcell    { $_[0]->_common('endcell', @_); }
sub endinterface { $_[0]->_common('endinterface', @_); }
sub endtaskfunc{ $_[0]->_common('endtaskfunc', @_); }
sub endmodule  { $_[0]->_common('endmodule', @_); }
sub endpackage { $_[0]->_common('endpackage', @_); }
sub funcsignal { $_[0]->_common('funcsignal', @_); }
sub function {	$_[0]->_common('function', @_); }
sub import {	$_[0]->_common('import', @_); }
sub instant {	$_[0]->_common('instant', @_); }
sub interface { $_[0]->_common('interface', @_); }
sub module {	$_[0]->_common('module', @_); }
sub package {	$_[0]->_common('package', @_); }
sub parampin {	$_[0]->_common('parampin', @_); }
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
read_test("verilog/parser_bugs.v", $dump_fh);
read_test("verilog/pinorder.v", $dump_fh);
read_test("verilog/parser_sv.v", $dump_fh);
ok(1);
$dump_fh->close();

# Did we read the right stuff?
ok(files_identical("test_dir/35.dmp", "t/35_sigparser.out"));

######################################################################

sub read_test {
    my $filename = shift;
    my $dump_fh = shift;

    my $pp = Verilog::Preproc->new(keep_comments=>1,);

    my $parser = new MyParser (dump_fh => $dump_fh,
			       metacomment=>{synopsys=>1},);
    #$parser->debug(9);

    # Preprocess
    $pp->open($filename);
    $parser->parse_preproc_file($pp);
}
