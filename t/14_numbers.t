#!/usr/bin/perl -w
# DESCRIPTION: Perl ExtUtils: Type 'make test' to test this package
#
# Copyright 2000-2010 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

use strict;
use Test;

BEGIN { plan tests => 22 }
BEGIN { require "t/test_utils.pl"; }

use Verilog::Language;
ok(1);

ok (Verilog::Language::number_value("5'h13")==19);
ok (Verilog::Language::number_value("5'd13")==13);
ok (Verilog::Language::number_value("5'o13")==11);
ok (Verilog::Language::number_value("5'B11")==3);
ok (Verilog::Language::number_value("5 'B 11")==3);
ok (Verilog::Language::number_value("'b10")==2);
ok (Verilog::Language::number_value("2'sb10")==2);
ok (Verilog::Language::number_bits("8'b10")==8);
ok (Verilog::Language::number_bits("8 'b 10")==8);
ok (Verilog::Language::number_signed("8 'sb 1")==1);
ok (!defined Verilog::Language::number_bits("'b10"));

print "  Bit::Vector\n";
eval "use Bit::Vector";
if ($@) {
    skip("Bit::Vector not installed (harmless)",1);
    skip("Bit::Vector not installed (harmless)",1);
    skip("Bit::Vector not installed (harmless)",1);
    skip("Bit::Vector not installed (harmless)",1);
    skip("Bit::Vector not installed (harmless)",1);
} else {
    try_bitvector("5823", 32, "000016bf");
    try_bitvector("80'h47cb_40d7_b50f_0147_1a85", 80, "47cb40d7b50f01471a85");
    try_bitvector("83'o227525534413441101057616251", 83, "097aad721721208bf1ca9");
    try_bitvector("70'b1011010111111001010111111111111001110000011000101110010100110101101101", 70, "2d7e57ff9c18b94d6d");
    try_bitvector("90'd46548__4046747316__6145438700", 90, "003d9b368496d10ab0043ec");
}

print "  Math::BigInt\n";
eval "use Math::BigInt";
if ($@) {
    skip("Math::BigInt not installed (harmless)",1);
    skip("Math::BigInt not installed (harmless)",1);
    skip("Math::BigInt not installed (harmless)",1);
    skip("Math::BigInt not installed (harmless)",1);
    skip("Math::BigInt not installed (harmless)",1);
} else {
    try_bigint("5823", 4, "0x16bf");
    try_bigint("80'h47cb_40d7_b50f_0147_1a85", 24, "0x47cb40d7b50f01471a85");
    try_bigint("83'o227525534413441101057616251", 24, "0x97aad721721208bf1ca9");
    try_bigint("70'b1011010111111001010111111111111001110000011000101110010100110101101101", 21, "0x2d7e57ff9c18b94d6d");
    try_bigint("90'd46548__4046747316__6145438700", 25, "0x3d9b368496d10ab0043ec");
}


sub try_bitvector {
    my $text = shift;
    my $expbits = shift;
    my $expvalue = shift;

    my $got = Verilog::Language::number_bitvector($text);
    my $gotbits = $got->Size;
    my $gotvalue = lc $got->to_Hex;
    print "   $text -> got $gotbits $gotvalue =? exp $expbits exp $expvalue\n";
    ok ($gotbits eq $expbits && $gotvalue eq $expvalue);
}

sub try_bigint {
    my $text = shift;
    my $expbits = shift;
    my $expvalue = shift;

    my $got = Verilog::Language::number_bigint($text);
    my $gotbits = $got->length;
    my $gotvalue = lc $got->as_hex;
    print "   $text -> got $gotbits $gotvalue =? exp $expbits exp $expvalue\n";
    ok ($gotbits eq $expbits && $gotvalue eq $expvalue);
}
