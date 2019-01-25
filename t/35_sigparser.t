#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2019 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test::More;
use Data::Dumper; $Data::Dumper::Indent = 1;

BEGIN { plan tests => 6 }
BEGIN { require "./t/test_utils.pl"; }

our %_TestCoverage;
our %_TestCallbacks;

######################################################################

package MyParser;
use Verilog::SigParser;
use strict;
use base qw(Verilog::SigParser);

BEGIN {
    # Make functions like this:
    #  sub attribute {	$_[0]->_common('module', @_); }
    foreach my $cb (Verilog::SigParser::callback_names(),
		    'comment') {
	$_TestCallbacks{$cb} = 1;
	my $func = ' sub __CB__ { $_[0]->_common("__CB__", @_); } ';
	$func =~ s/__CB__/$cb/g;
	eval($func);
    }
}

sub _serialize {
    my $in = shift;
    if (ref($in)) {
	my $dd = Data::Dumper->new([$in], [qw(in)]);
	$dd->Reset->Indent(0)->Terse(1)->Sortkeys(1);
	return $dd->Dump;
    } else {
	return $in;
    }
}

sub _common {
    my $self = shift;
    my $what = shift;
    my $call_self = shift;
    my @args = @_;

    $_TestCoverage{$what}++;
    my $args="";
    foreach (@args) {
	if (defined $_) {
	    $args .= " \'"._serialize($_)."\'";
	} else {
	    $args .= " undef";
	}
    }
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

######################################################################

package main;

use Verilog::SigParser;
use Verilog::Preproc;
ok(1, "use");

read_tests("test_dir/35.dmp",
	   []);
ok(1, "read");
# Did we read the right stuff?
ok(files_identical("test_dir/35.dmp", "t/35_sigparser.out"), "diff");

read_tests("test_dir/35_ps.dmp",
	   [use_pinselects => 1]);
ok(1, "read-pinselects");
# Did we read the right stuff?
ok(files_identical("test_dir/35_ps.dmp", "t/35_sigparser_ps.out"), "diff");

# Did we cover everything?
my $err;
foreach my $cb (sort keys %_TestCallbacks) {
    if (!$_TestCoverage{$cb}) {
	$err=1;
	warn "%Warning: No test coverage for callback: $cb\n";
    }
}
ok (!$err, "coverage");


######################################################################

# Use our class and dump to a file
sub read_tests {
    my $dump_filename = shift;
    my $option_ref = shift;

    my $dump_fh = new IO::File($dump_filename,"w")
	or die "%Error: $! $dump_filename,";
    read_test($dump_fh, $option_ref, "/dev/null");  # Empty files should be ok
    read_test($dump_fh, $option_ref, "verilog/v_hier_subprim.v");
    read_test($dump_fh, $option_ref, "verilog/v_hier_sub.v");
    read_test($dump_fh, $option_ref, "verilog/parser_bugs.v");
    read_test($dump_fh, $option_ref, "verilog/pinorder.v");
    read_test($dump_fh, $option_ref, "verilog/parser_sv.v");
    read_test($dump_fh, $option_ref, "verilog/parser_sv09.v");
    read_test($dump_fh, $option_ref, "verilog/parser_sv17.v");
    read_test($dump_fh, $option_ref, "verilog/parser_vectors.v");
    $dump_fh->close();
}

sub read_test {
    my $dump_fh = shift;
    my $option_ref = shift;
    my $filename = shift;

    my $pp = Verilog::Preproc->new(keep_comments=>1,);

    my $parser = new MyParser (dump_fh => $dump_fh,
			       metacomment=>{synopsys=>1},
			       @$option_ref);

    if ($ENV{VERILOG_TEST_DEBUG}) {  # For example, VERILOG_TEST_DEBUG=9
	$parser->debug($ENV{VERILOG_TEST_DEBUG});
    }

    # Preprocess
    $pp->open($filename);
    $parser->parse_preproc_file($pp);

    print Dumper($parser->{symbol_table}) if ($parser->debug());
}
