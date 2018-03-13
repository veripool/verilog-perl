# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Net;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
use vars qw ($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Net::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.450';

my %_Type_Widths = (
    'bit'	=> 1,
    'byte'	=> 8,
    'genvar'	=> 32,
    'integer'	=> 32,
    'localparam'=> 32,
    'logic'	=> 1,
    'longint'	=> 64,
    'parameter'	=> 32,
    'reg'	=> 1,
    'shortint'	=> 16,
    'supply0'	=> 1,
    'supply1'	=> 1,
    'tri'	=> 1,
    'tri0'	=> 1,
    'tri1'	=> 1,
    'triand'	=> 1,
    'trior'	=> 1,
    'trireg'	=> 1,
    'wand'	=> 1,
    'wire'	=> 1,
    'wor'	=> 1,
    );

my %_Type_Accessors = (
    'genvar'	=> 'decl_type',
    'localparam'=> 'decl_type',
    'parameter'	=> 'decl_type',
    'var'	=> 'decl_type',		# Not in old version, but for completeness
    #'port'	=> 'decl_type',		# Internals - Look at Port (input/output/inout/ref)
    #'net'	=> 'decl_type',		# Internals - Look at net_type (wire/tri/...)
    #
    'supply0' 	=> 'net_type',
    'supply1'	=> 'net_type',
    'tri'	=> 'net_type',
    'tri0'	=> 'net_type',
    'tri1'	=> 'net_type',
    'triand'	=> 'net_type',
    'trior'	=> 'net_type',
    'trireg'	=> 'net_type',
    'wand'	=> 'net_type',
    'wire'	=> 'net_type',
    'wor'	=> 'net_type',
    #
    'bit'	=> 'data_type',
    'byte'	=> 'data_type',
    'chandle'	=> 'data_type',
    'event'	=> 'data_type',
    'int'	=> 'data_type',
    'integer'	=> 'data_type',
    'logic'	=> 'data_type',
    'longint'	=> 'data_type',
    'real'	=> 'data_type',
    'realtime'	=> 'data_type',
    'reg'	=> 'data_type',
    'shortint'	=> 'data_type',
    'shortreal'	=> 'data_type',
    'string'	=> 'data_type',
    'time'	=> 'data_type',
    );

######################################################################

structs('_new_base',
	'Verilog::Netlist::Net::Struct'
	=>[name     	=> '$', #'	# Name of the net
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   data_type 	=> '$', #'	# SystemVerilog Type (logic/integer/reg [3:0] etc)
	   decl_type 	=> '$', #'	# Declaration type (parameter/genvar/port/net etc)
	   net_type 	=> '$', #'	# Net type (wire/tri/supply0 etc)
	   comment	=> '$', #'	# Comment provided by user
	   array	=> '$', #'	# Vector
	   module	=> '$', #'	# Module, Program or Interface entity belongs to
	   signed	=> '$', #'	# True if signed
	   value	=> '$', #'	# For parameters, the value of the parameter
	   # below only after links()
	   port		=> '$', #'	# Reference to port connected to
	   msb		=> '$', #'	# MSB of signal (if known)
	   lsb		=> '$', #'	# LSB of signal (if known)
	   stored_lsb	=> '$', #'	# Bit number of signal stored in bit 0  (generally lsb)
	   _used_in	=> '$', #'	# Driver count onto signal
	   _used_out	=> '$', #'	# Receiver count on signal
	   _used_inout	=> '$', #'	# Bidirect count on signal
	   # SystemPerl only: below only after autos()
	   simple_type	=> '$', #'	# True if is uint (as opposed to sc_signal)
	   sp_traced	=> '$', #'	# Created by SP_TRACED
	   sp_autocreated	=> '$', #'	# Created by /*AUTOSIGNAL*/
	   ]);

sub new {
    my $class = shift;
    my %params = @_;
    my $self = $class->_new_base (%params);
    $self->type($params{type}) if $params{type};  # Backward compatibility
    return $self;
}

sub delete {
    my $self = shift;
    my $h = $self->module->_nets;
    delete $h->{$self->name};
    return undef;
}

######################################################################

sub logger {
    return $_[0]->netlist->logger;
}
sub netlist {
    return $_[0]->module->netlist;
}

sub _used_in_inc { $_[0]->_used_in(1+($_[0]->_used_in()||0)); }
sub _used_out_inc { $_[0]->_used_out(1+($_[0]->_used_out()||0)); }
sub _used_inout_inc { $_[0]->_used_inout(1+($_[0]->_used_inout()||0)); }
sub _used_in_dec {
    return if !$_[0]->_used_in();
    $_[0]->_used_in(-1+$_[0]->_used_in());
}
sub _used_out_dec {
    return if !$_[0]->_used_out();
    $_[0]->_used_out(-1+$_[0]->_used_out());
}
sub _used_inout_dec {
    return if !$_[0]->_used_inout();
    $_[0]->_used_inout(-1+$_[0]->_used_inout());
}

sub stored_lsb { defined $_[0]->SUPER::stored_lsb ? $_[0]->SUPER::stored_lsb : $_[0]->lsb; }

sub width {
    my $self = shift;
    # Return bit width (if known)
    my $dt = $self->data_type; $dt="" if $dt eq "signed";
    if (defined $self->msb && defined $self->lsb) {
	return (abs($self->msb - $self->lsb) + 1);
    } elsif (my $width = $_Type_Widths{$dt || $self->net_type || $self->decl_type}) {
	return $width;
    }
    return undef;
}

sub type {
    my $self = shift;
    my $flag = shift;
    if (defined $flag) {
	if (my $acc = $_Type_Accessors{$flag}) {
	    if ($acc eq 'decl_type') { $self->decl_type($flag); }
	    elsif ($acc eq 'net_type') { $self->net_type($flag); }
	    else { $self->data_type($flag); }
	} else {
	    $self->data_type($flag);
	}
    }
    my $dt = $self->data_type; $dt="" if $dt && $dt eq "signed";
    return $dt || $self->net_type || $self->decl_type;
}

######################################################################

sub _link {}

sub lint {
    my $self = shift;
    # Sequential logic may gen/use a signal, so we have to be a little sloppy
    if (0&&$self->_used_inout() && $self->_used_out()
	&& !$self->array()) {   # if an array, different outputs might hit different bits
	$self->warn("Signal is used as both a inout and output: ",$self->name(), "\n");
	$self->dump_drivers(8);
    }
    elsif ($self->_used_out()) {
	if ($self->_used_out()>1
	    # if an array, different outputs might hit different bits
	    && !$self->array()
	    # if vector, warn only if # of usages is higher than # of bits in vector
	    && (abs($self->msb() - $self->lsb()) + 1) < $self->_used_out()) {
	    $self->warn("Signal has multiple drivers (",
			$self->_used_out(),"): ",$self->name(), "\n");
	    $self->dump_drivers(8);
	}
    }
    if (0&&$self->_used_in() && !$self->_used_out()) {
	$self->warn("Signal has no drivers: ",$self->name(), "\n");
    }
    if (0&&$self->_used_out() && !$self->_used_in()
	&& $self->name() !~ /unused/) {
	$self->dump(5);
	$self->port->dump(10) if $self->port;
	$self->warn("Signal is not used (or needs signal declaration): ",$self->name(), "\n");
	flush STDOUT;
	flush STDERR;
    }
}

######################################################################
## Outputters

sub _decls {
    my $self = shift;
    my $out = $self->net_type || $self->decl_type;
    if ($self->port) {
	$out = "input" if $self->port->direction eq "in";
	$out = "output" if $self->port->direction eq "out";
	$out = "inout" if $self->port->direction eq "inout";
    }
    return $out;
}

sub verilog_text {
    my $self = shift;
    my @out;
    foreach my $decl ($self->_decls) {
	push @out, $decl;
	push @out, " ".$self->data_type if $self->data_type;
	push @out, " ".$self->name;
	push @out, " ".$self->array if $self->array;
        push @out, " = ".$self->value if defined $self->value && $self->value ne '';
	push @out, ";";
	push @out, " ".$self->comment if defined $self->comment && $self->comment ne '';
    }
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Net:",$self->name()
	,"  ",($self->_used_in() ? "I":""),($self->_used_out() ? "O":""),
	,"  DeclT:",$self->decl_type||''
	,"  NetT:",$self->net_type||''
	,"  DataT:",$self->data_type||''
	,"  Array:",$self->array()||'';
    print "  ",($self->msb).":".($self->lsb) if defined $self->msb;
    print "  Value:",$self->value if defined $self->value && $self->value ne '';
    print "\n";
}

sub dump_drivers {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Net:",$self->name,"\n";
    if (my $port = $self->port) {
	print " "x$indent,"  Port: ",$port->name,"  ",$port->direction,"\n";
    }
    foreach my $cell ($self->module->cells_sorted) {
	foreach my $pin ($cell->pins_sorted) {
	    foreach my $net ($pin->nets) {
		next unless defined $net->{net};
		if ($pin->port && $net->{net} == $self) {
		    print " "x$indent,"  Pin:  ",$cell->name,".",$pin->name
			,"  ",$pin->port->direction,"\n";
		}
		elsif ($self->name eq $net->{net}->name) {
		    warn "%Warning: Internal net name duplicate: ".$cell->name."  ".$self->name."\n"
			.$self->comment."  ".$net->{net}->comment."\n"
			."$self  ".$net->{net}->name."\n";
		}
	    }
	}
    }
    flush STDERR;
    flush STDOUT;
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Net - Net for a Verilog Module

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $net = $module->find_net ('signalname');
  print $net->name;

=head1 DESCRIPTION

A Verilog::Netlist::Net object is created by Verilog::Netlist::Module for
every signal and input/output declaration, and parameter in the current
module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->array

Any array (vector) declaration for the net.  This is for Verilog 2001
multidimensional signals; for the width of a signal, use msb/lsb/width. For
newer applications use data_type() as it supports SystemVerilog types.

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->data_type

The data type of the net.  This may be a data type keyword ("integer",
"logic", etc), user defined type from a type def, a range ("[11:0]",
"signed [1:0]" or "" for an implicit wire.

=item $self->decl_type

How the net was declared.  A declaration keyword ("genvar", "localparam",
"parameter", "var") or "port" if only as a port - and see the port method,
or "net" - and see the net_type method.

=item $self->module

Reference to the Verilog::Netlist::Module or Verilog::Netlist::Interface
the net is under.

=item $self->lsb

The least significant bit number of the net.

=item $self->msb

The most significant bit number of the net.

=item $self->name

The name of the net.

=item $self->net_type

The net type, if one applies.  Always a net type keyword ('supply0',
'supply1', 'tri', 'tri0', 'tri1', 'triand', 'trior', 'trireg', 'wand',
'wire', 'wor').

=item $self->type

The type function is provided for backward compatibility to Verilog-Perl
versions before 3.200. Applications should change to use data_type() and/or
decl_type() instead.

The type function returns an agglomeration of data_type, net_type and
decl_type that worked ok in Verilog, but does not work with SystemVerilog.
Calls to type() will be converted to calls to data_type, decl_type or
net_type in a way that attempts to maintain backward compatibility, however
compatibility is not always possible.

=item $self->value

If the net's type is 'parameter', the value from the parameter's
declaration.

=item $self->width

The width of the net in bits.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->lint

Checks the net for errors.  Normally called by Verilog::Netlist::lint.

=item $self->dump

Prints debugging information for this net.

=item $self->dump_drivers

Prints debugging information for this net, and all pins driving the net.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2018 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
