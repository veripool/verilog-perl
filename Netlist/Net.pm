# Verilog - Verilog Perl Interface
# $Revision: 1.39 $$Date$$Author$
# Author: Wilson Snyder <wsnyder@wsnyder.org>
######################################################################
#
# Copyright 2000-2005 by Wilson Snyder.  This program is free software;
# you can redistribute it and/or modify it under the terms of either the GNU
# General Public License or the Perl Artistic License.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
# 
######################################################################

package Verilog::Netlist::Net;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Subclass;
@ISA = qw(Verilog::Netlist::Net::Struct
	Verilog::Netlist::Subclass);
$VERSION = '2.310';
use strict;

######################################################################

structs('new',
	'Verilog::Netlist::Net::Struct'
	=>[name     	=> '$', #'	# Name of the net
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   #
	   type	 	=> '$', #'	# C++ Type (bool/int)
	   comment	=> '$', #'	# Comment provided by user
	   array	=> '$', #'	# Vector
	   module	=> '$', #'	# Module entity belongs to
	   # below only after links()
	   port		=> '$', #'	# Reference to port connected to
	   msb		=> '$', #'	# MSB of signal (if known)
	   lsb		=> '$', #'	# LSB of signal (if known)
	   _used_in	=> '$', #'	# Driver count onto signal
	   _used_out	=> '$', #'	# Receiver count on signal
	   _used_inout	=> '$', #'	# Bidirect count on signal
	   # SystemPerl only: below only after autos()
	   simple_type	=> '$', #'	# True if is uint (as opposed to sc_signal)
	   sp_traced	=> '$', #'	# Created by SP_TRACED
	   sp_autocreated	=> '$', #'	# Created by /*AUTOSIGNAL*/
	   ]);

######################################################################

sub _used_in_inc { $_[0]->_used_in(1+($_[0]->_used_in()||0)); }
sub _used_out_inc { $_[0]->_used_out(1+($_[0]->_used_out()||0)); }
sub _used_inout_inc { $_[0]->_used_inout(1+($_[0]->_used_inout()||0)); }
sub width {
    my $self = shift;
    # Return bit width (if known)
    if (defined $self->msb && defined $self->lsb) {
	return ($self->msb - $self->lsb + 1);
    }
    return undef;
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
	    && !$self->array()) {   # if an array, different outputs might hit different bits
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

sub _decls {
    my $self = shift;
    if ($self->port) {
	return "input" if $self->port->direction eq "in";
	return "output" if $self->port->direction eq "out";
	return "inout" if $self->port->direction eq "inout";
    }
    return $self->type;
}

sub verilog_text {
    my $self = shift;
    my @out;
    foreach my $decl ($self->_decls) {
	push @out, $decl;
	push @out, " [".$self->msb.":".$self->lsb."]" if defined $self->msb;
	push @out, " ".$self->name;
	push @out, " ".$self->array if $self->array;
	push @out, ";";
    }
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Net:",$self->name()
	,"  ",($self->_used_in() ? "I":""),($self->_used_out() ? "O":""),
	,"  Type:",$self->type(),"  Array:",$self->array()||"";
    print "  ",($self->msb).":".($self->lsb) if defined $self->msb;
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
	    if ($pin->port && $pin->net && $pin->net == $self) {
		print " "x$indent,"  Pin:  ",$cell->name,".",$pin->name
		    ,"  ",$pin->port->direction,"\n";
	    }
	    elsif ($pin->net && $self->name eq $pin->net->name) {
		warn "%Warning: Internal net name duplicate: ".$cell->name."  ".$self->name."\n"
		    .$self->comment."  ".$pin->net->comment."\n"
		    ."$self  ".$pin->net->name."\n";
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

Verilog::Netlist creates a net for every sc_signal declaration in the
current module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->array

Any array (vector) declaration for the net.  This is for multidimensional
signals, for the width of a signal, use msb/lsb/width.

=item $self->comment

Any comment the user placed on the same line as the net.

=item $self->module

Reference to the Verilog::Netlist::Module the net is in.

=item $self->lsb

The least significant bit number of the net.

=item $self->msb

The most significant bit number of the net.

=item $self->name

The name of the net.

=item $self->type

The C++ type of the net.

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

The latest version is available from CPAN and from
L<http://www.veripool.com/verilog-perl.html>.

Copyright 2000-2005 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License or the Perl Artistic License.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
