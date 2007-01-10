# Verilog::Language.pm -- Verilog language keywords, etc
# $Id$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2007 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

=pod

=head1 NAME

Verilog::Language - Verilog language utilities

=head1 SYNOPSIS

  use Verilog::Language;

  $result = Verilog::Language::is_keyword ("wire");  # true
  $result = Verilog::Language::is_compdirect ("`notundef");  # false
  $result = Verilog::Language::number_value ("4'b111");  # 8
  $result = Verilog::Language::number_bits  ("32'h1b");  # 32
  $result = Verilog::Language::number_signed ("1'sh1");  # 1
  @vec    = Verilog::Language::split_bus ("[31,5:4]"); # 31, 5, 4
  @vec    = Verilog::Language::split_bus_nocomma ("[31:29]"); # 31, 30, 29
  $result = Verilog::Language::strip_comments ("a/*b*/c");  # ac

=head1 DESCRIPTION

This package provides useful utilities for general use with the
Verilog Language.  General functions will be added as needed.

=over 4

=item Verilog::Language::is_keyword ($symbol_string)

Return true if the given symbol string is a Verilog reserved keyword.
Value indicates the language standard, 1995, 2001, or sv31 for
SystemVerilog 3.1.

=item Verilog::Language::is_compdirect ($symbol_string)

Return true if the given symbol string is a Verilog compiler directive.

=item Verilog::Language::language_standard ($year)

Sets the language standard to indicate what are keywords.  If undef, all
standards apply.  1995 sets only Verilog 1995, 2001 sets Verilog 2001, and
'sv31' sets SystemVerilog 3.1.

=item Verilog::Language::number_bits ($number_string)

Return the number of bits in a value string, or undef if incorrectly
formed, _or_ not specified.

=item Verilog::Language::number_signed ($number_string)

Return true if the Verilog value is signed, else undef.

=item Verilog::Language::number_value ($number_string)

Return the numeric value of a Verilog value, or undef if incorrectly
formed.  It ignores any signed Verilog attributes, but is is returned as a
perl signed integer, so it may fail for over 31 bit values.

=item Verilog::Language::split_bus ($bus)

Return a list of expanded arrays.  When passed a string like
"foo[5:1:2,10:9]", it will return a array with ("foo[5]", "foo[3]", ...).
It correctly handles connectivity expansion also, so that "x[1:0] = y[3:0]"
will get intuitive results.

=item Verilog::Language::split_bus_nocomma ($bus)

As with split_bus, but faster.  Only supports simple decimal colon
separated array specifications, such as "foo[3:0]".

=item Verilog::Language::strip_comments ($text)

Return text with any // or /**/ comments stripped, correctly handing quoted
strings.  Newlines will be preserved in this process.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.com/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2007 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Parser>, 
L<Verilog::ParseSig>, 
L<Verilog::Getopt>

And the L<http://www.veripool.com/verilog-mode.html>Verilog-Mode package for Emacs.

=cut
######################################################################

package Verilog::Language;
require 5.000;
require Exporter;

use strict;
use vars qw($VERSION %Keyword %Keywords %Compdirect $Standard);
use Carp;

######################################################################
#### Configuration Section

$VERSION = '2.370';

######################################################################
#### Internal Variables

foreach my $kwd (qw(
		    always and assign begin buf bufif0 bufif1 case
		    casex casez cmos deassign default defparam
		    disable else end endcase endfunction endmodule
		    endprimitive endspecify endtable endtask event
		    for force forever fork function highz0
		    highz1 if initial inout input integer join large
		    macromodule medium module nand negedge
		    nmos nor not notif0 notif1 or output parameter
		    pmos posedge primitive pull0 pull1 pulldown
		    pullup rcmos real realtime reg release repeat
		    rnmos rpmos rtran rtranif0 rtranif1 scalared
		    signed small specify strength strong0 strong1
		    supply0 supply1 table task time tran tranif0
		    tranif1 tri tri0 tri1 triand trior trireg
		    vectored wait wand weak0 weak1 while wire wor
		    xnor xor
		    )) { $Keywords{1995}{$kwd} = 1995; }

foreach my $kwd (qw(
		    automatic cell config design edge endconfig endgenerate
		    generate genvar ifnone instance liblist localparam
		    noshowcancelled pulsestyle_ondetect pulsestyle_onevent
		    showcancelled signed specparam unsigned use
		    )) { $Keywords{2001}{$kwd} = 2001; }

foreach my $kwd (qw(
		    alias always_comb always_ff always_latch assert
		    assert_strobe before bind bit break byte chandle class
		    clocking const constraint context continue cover dist
		    do endcass endclocking endinterface endprogram
		    endproperty endsequence enum export extends extern
		    final first_match forkjoin iff import inside int
		    interface intersect join_any join_none local logic
		    longint modport new null packed priority program
		    property protexted pure rand randc ref sequence
		    shortint shortreal solve static string struct super
		    this throughout timeprecision timeunit type typedef
		    union unique var virtual void wait_order with within
		    )) { $Keywords{sv31}{$kwd} = 'sv31'; }

foreach my $kwd (
		 "`celldefine", "`default_nettype", "`define", "`else",
		 "`endcelldefine", "`endif", "`ifdef", "`include",
		 "`nounconnected_drive", "`resetall", "`timescale",
		 "`unconnected_drive", "`undef",
		 # Commercial Extensions
		 "`protected", "`endprotected",
		 ) { $Keywords{$kwd}{1995} = $Compdirect{$kwd} = 1995; }

foreach my $kwd (
		 "`default_nettype", "`elsif", "`undef", "`ifndef",
		 "`file", "`line",
		 ) { $Keywords{$kwd}{2001} = $Compdirect{$kwd} = 2001; }

language_standard ('sv31');  # Default standard

######################################################################
#### Keyword utilities

sub language_standard {
    my $standard = shift;
    if (defined $standard) {
	my @subsets;
	if ($standard eq '1995') {
	    $Standard = $standard;
	    @subsets = qw(1995);
	} elsif ($standard eq '2001') {
	    $Standard = $standard;
	    @subsets = qw(1995 2001);
	} elsif ($standard eq 'sv31') {
	    $Standard = $standard;
	    @subsets = qw(1995 2001 sv31);
	} else {
	    croak "%Error: Verilog::Language::language_standard passed bad value: $standard,";
	}
	# Update keyword list to present language
	# (We presume the language_standard rarely changes, so it's faster to compute the list.)
	%Keyword = ();
	foreach my $ss (@subsets) {
	    foreach my $kwd (%{$Keywords{$ss}}) {
		$Keyword{$kwd} = $ss;
	    }
	}
    }
    return $Standard;
}

sub is_keyword {
    my $symbol = shift;
    return ($Keyword{$symbol});
}

sub is_compdirect {
    my $symbol = shift;
    return ($Compdirect{$symbol});
}

######################################################################
#### String utilities

sub strip_comments {
    return $_[0] if $_[0] !~ m!/!s;  # Fast path
    my $text = shift;
    # Spec says that // has no special meaning inside /**/
    my $quote; my $olcmt; my $cmt;
    my $out = "";
    while ($text =~ m!(.*?)(//|/\*|\*/|\n|\"|$)!sg) {
	$out .= $1 if !$olcmt && !$cmt;
	my $t = $2;
	if ($2 eq '"') {
	    $out .= $t;
	    $quote = ! $quote;
	} elsif (!$quote && !$olcmt && $t eq '/*') {
	    $cmt = 1;
	} elsif (!$quote && !$cmt && $t eq '//') {
	    $olcmt = 1;
	} elsif ($cmt && $t eq '*/') {
	    $cmt = 0;
	} elsif ($t eq "\n") {
	    $olcmt = 0;
	    $out .= $t;
	} else {
	    $out .= $t if !$olcmt && !$cmt;
	}
    }
    return $out;
}

######################################################################
#### Numeric utilities

sub number_bits {
    my $number = shift;
    if ($number =~ /^\s*([0-9]+)\s*\'/i) {
	return $1;
    }
    return undef;
}

sub number_signed {
    my $number = shift;
    if ($number =~ /\'\s*s/i) {
	return 1;
    }
    return undef;
}

sub number_value {
    my $number = shift;
    $number =~ s/[_ ]//g;
    if ($number =~ /\'s?h([0-9a-f]+)$/i) {
	return (hex ($1));
    }
    elsif ($number =~ /\'s?o([0-9a-f]+)$/i) {
	return (oct ($1));
    }
    elsif ($number =~ /\'s?b([0-1]+)$/i) {
	my $val = 0;
	my $bit;
	$number = $1;
	foreach $bit (split(//, $number)) {
	    $val = ($val<<1) | ($bit=='1'?1:0);
	}
	return ($val);
    }
    elsif ($number =~ /\'s?d?([0-9]+)$/i
	   || $number =~ /^([0-9]+)$/i) {
	return ($1);
    }
    return undef;
}

######################################################################
#### Signal utilities

sub split_bus {
    my $bus = shift;
    if ($bus !~ /\[/) {
	# Fast case: No bussing
	return $bus;
    } elsif ($bus =~ /^([^\[]+\[)([0-9]+):([0-9]+)(\][^\]]*)$/) {
	# Middle speed case: Simple max:min
	my $bit;
	my @vec = ();
	if ($2 >= $3) {
	    for ($bit = $2; $bit >= $3; $bit --) {
		push @vec, $1 . $bit . $4;
	    }
	} else {
	    for ($bit = $2; $bit <= $3; $bit ++) {
		push @vec, $1 . $bit . $4;
	    }
	}
	return @vec;
    } else {
	# Complex case: x:y:z,p,...	etc
	# Do full parsing
	my @pretext = ();	# [brnum]
	my @expanded = ();	# [brnum][bitoccurance]
	my $inbra = 0;
	my $brnum = 0;
	my ($beg,$end,$step);
	foreach (split (/([:\]\[,])/, $bus)) {
	    if (/^\[/) {
		$inbra = 1;
		$pretext[$brnum] .= $_;
	    } 
	    if (!$inbra) {
		# Not in bracket, just remember text
		$pretext[$brnum] .= $_;
		next;
	    }
	    if (/[\],]/) {
		if (defined $beg) {
		    # End of bus piece
		    #print "Got seg $beg $end $step\n";
		    my $bit;
		    if ($beg >= $end) {
			for ($bit = $beg; $bit >= $end; $bit -= $step) {
			    push @{$expanded[$brnum]}, $bit;
			}
		    } else {
			for ($bit = $beg; $bit <= $end; $bit += $step) {
			    push @{$expanded[$brnum]}, $bit;
			}
		    }
		}
		$beg = undef;
		# Now what?
		if (/^\]/) {
		    $inbra = 0;
		    $brnum++;
		    $pretext[$brnum] .= $_;
		}
		elsif (/,/) {
		    $inbra = 1;
		}
	    } elsif (/:/) {
		$inbra++;
	    }
	    else {
		if ($inbra == 1) {	# Begin value
		    $beg = $end = number_value ($_);	# [2'b11:2'b00] is legal
		    $step = 1;
		} elsif ($inbra == 2) {	# End value
		    $end = number_value ($_);		# [2'b11:2'b00] is legal
		} elsif ($inbra == 3) {	# Middle value
		    $step = number_value ($_);		# [2'b11:2'b00] is legal
		}
		# Else ignore extra colons
	    }
	}

	# Determine max size of any bracket expansion array
	my $br;
	my $max_size = $#{$expanded[0]};
	for ($br=1; $br<$brnum; $br++) {
	    my $len = $#{$expanded[$br]};
	    if ($len < 0) {
		push @{$expanded[$br]}, "";
		$len = 0;
	    }
	    $max_size = $len if $max_size < $len;
	}

	my $i;
	my @vec = ();
	for ($i=0; $i<=$max_size; $i++) {
	    $bus = "";
	    for ($br=0; $br<$brnum; $br++) {
		#print "i $i  br $br >", $pretext[$br],"<\n";
		$bus .= $pretext[$br] . $expanded[$br][$i % (1+$#{$expanded[$br]})];
	    }
	    $bus .= $pretext[$br];	# Trailing stuff
	    push @vec, $bus;
	}
	return @vec;
    }
}

sub split_bus_nocomma {
    # Faster version of split_bus
    my $bus = shift;
    if ($bus !~ /:/) {
	# Fast case: No bussing
	return $bus;
    } elsif ($bus =~ /^([^\[]+\[)([0-9]+):([0-9]+)(\][^\]]*)$/) {
	# Middle speed case: Simple max:min
	my $bit;
	my @vec = ();
	if ($2 >= $3) {
	    for ($bit = $2; $bit >= $3; $bit --) {
		push @vec, $1 . $bit . $4;
	    }
	} else {
	    for ($bit = $2; $bit <= $3; $bit ++) {
		push @vec, $1 . $bit . $4;
	    }
	}
	return @vec;
    } else {
	# Complex case: x:y	etc
	# Do full parsing
	my @pretext = ();	# [brnum]
	my @expanded = ();	# [brnum][bitoccurance]
	my $inbra = 0;
	my $brnum = 0;
	my ($beg,$end);
	foreach (split (/([:\]\[])/, $bus)) {
	    if (/^\[/) {
		$inbra = 1;
		$pretext[$brnum] .= $_;
	    } 
	    if (!$inbra) {
		# Not in bracket, just remember text
		$pretext[$brnum] .= $_;
		next;
	    }
	    if (/[\]]/) {
		if (defined $beg) {
		    # End of bus piece
		    #print "Got seg $beg $end\n";
		    my $bit;
		    if ($beg >= $end) {
			for ($bit = $beg; $bit >= $end; $bit--) {
			    push @{$expanded[$brnum]}, $bit;
			}
		    } else {
			for ($bit = $beg; $bit <= $end; $bit++) {
			    push @{$expanded[$brnum]}, $bit;
			}
		    }
		}
		$beg = undef;
		# Now what?
		if (/^\]/) {
		    $inbra = 0;
		    $brnum++;
		    $pretext[$brnum] .= $_;
		}
	    } elsif (/:/) {
		$inbra++;
	    }
	    else {
		if ($inbra == 1) {	# Begin value
		    $beg = $end = $_;
		} elsif ($inbra == 2) {	# End value
		    $end = $_;
		}
		# Else ignore extra colons
	    }
	}

	# Determine max size of any bracket expansion array
	my $br;
	my $max_size = $#{$expanded[0]};
	for ($br=1; $br<$brnum; $br++) {
	    my $len = $#{$expanded[$br]};
	    if ($len < 0) {
		push @{$expanded[$br]}, "";
		$len = 0;
	    }
	    $max_size = $len if $max_size < $len;
	}

	my $i;
	my @vec = ();
	for ($i=0; $i<=$max_size; $i++) {
	    $bus = "";
	    for ($br=0; $br<$brnum; $br++) {
		#print "i $i  br $br >", $pretext[$br],"<\n";
		$bus .= $pretext[$br] . $expanded[$br][$i % (1+$#{$expanded[$br]})];
	    }
	    $bus .= $pretext[$br];	# Trailing stuff
	    push @vec, $bus;
	}
	return @vec;
    }
}

######################################################################
#### Package return
1;
