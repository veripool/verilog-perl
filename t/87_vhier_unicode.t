#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2024 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use IO::File;
use strict;
use Test::More;

BEGIN { plan tests => 3 }
BEGIN { require "./t/test_utils.pl"; }

{
    my $fh = IO::File->new(">test_dir/unicode.v");
    $fh->print(chr(0xEF).chr(0xBB).chr(0xBF));  # BOM
    $fh->print("// Bom\n");
    $fh->print("module t;\n");
    $fh->print("   // Chinese "
               .chr(0xe8).chr(0xaf).chr(0x84).chr(0xe8).chr(0xae).chr(0xba)  # Comment
               ."\n");
    $fh->print("   initial begin\n");
    $fh->print("      \$write(\"Hello "
               .chr(0xe4).chr(0xb8).chr(0x96).chr(0xe7).chr(0x95).chr(0x8c)  # World
               ."\\n\");\n");
    $fh->print("      \$write(\"*-* All Finished *-*\\n\");\n");
    $fh->print("   end\n");
    $fh->print("endmodule\n");
    $fh->close;
}
ok(1);

{
    my $out = "test_dir/unicode_vppreproc.out";
    my $cmd = "${PERL} ./vppreproc -y verilog test_dir/unicode.v > $out";
    run_system($cmd);
    ok(-r $out, "vppreproc outputted from: $cmd");
}
{
    my $out = "test_dir/unicode_vhier.out";
    my $cmd = "${PERL} ./vhier --input-files --nomissing -y verilog test_dir/unicode.v -o $out";
    run_system($cmd);
    ok(-r $out, "vhier outputted from: $cmd");
}

