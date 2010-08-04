# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Pin;

use Verilog::Netlist;
use Verilog::Netlist::Port;
use Verilog::Netlist::Net;
use Verilog::Netlist::Cell;
use Verilog::Netlist::Module;
use Verilog::Netlist::Pin;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Pin::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.301';

structs('new',
	'Verilog::Netlist::Pin::Struct'
	=>[name     	=> '$', #'	# Pin connection
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   comment	=> '$', #'	# Comment provided by user
	   netname	=> '$', #'	# Net connection
	   portname 	=> '$', #'	# Port connection name
	   portnumber   => '$', #'	# Position of name in call
	   pinnamed 	=> '$', #'	# True if name assigned
	   cell     	=> '$', #'	# Cell reference
	   # below only after link()
	   net		=> '$', #'	# Net connection reference
	   port		=> '$', #'	# Port connection reference
	   # SystemPerl: below only after autos()
	   sp_autocreated => '$', #'	# Created by auto()
	   # below by accessor computation
	   #module
	   #submod
	   ]);

sub delete {
    my $self = shift;
    my $h = $self->cell->_pins;
    delete $h->{$self->name};
    return undef;
}

######################################################################
#### Methods

sub logger {
    return $_[0]->netlist->logger;
}
sub module {
    return $_[0]->cell->module;
}
sub submod {
    return $_[0]->cell->submod;
}
sub netlist {
    return $_[0]->cell->module->netlist;
}

sub _link {
    my $self = shift;
    # Note this routine is HOT
    my $change;
    if (!$self->net) {
	if (my $netname = $self->netname) {
	    $self->net($self->module->find_net($netname));
	    $change = 1;
	}
    }
    if (!$self->port) {
	if (my $submod = $self->submod) {
	    my $portname = $self->portname;
	    if ($portname && !$self->cell->byorder ) {
		$self->port($submod->find_port($portname));
		$change = 1;
	    }
	    else {
		$self->port($submod->find_port_by_index($self->portnumber));
		# changing name from pin# to actual port name
		$self->name($self->port->name) if $self->port;
		$change = 1;
	    }
	}
    }
    if ($change && $self->net && $self->port) {
	my $dir = $self->port->direction;
	if    ($dir eq 'in')    { $self->net->_used_in_inc(); }
	elsif ($dir eq 'out')   { $self->net->_used_out_inc(); }
	elsif ($dir eq 'inout') { $self->net->_used_inout_inc(); }
    }
}

sub type_match {
    my $self = shift;
    # We could check for specific types being OK, but nearly everything,
    # reg/trireg/wire/wand etc/tri/ supply0|1 etc
    # is allowed to connect with everything else, and we're not a lint tool...
    # So, not: return $self->net->data_type eq $self->port->data_type;
    return 1;
}

sub lint {
    my $self = shift;
    if (!$self->net && !$self->netlist->{implicit_wires_ok}) {
        $self->error ("Pin's net declaration not found: ",$self->netname,"\n");
    }
    if (!$self->port && $self->submod) {
        $self->error ($self,"Port not found in ",$self->submod->keyword," ",$self->submod->name,": ",$self->portname,"\n");
    }
    if ($self->port && $self->net) {
	if (!$self->type_match) {
	    my $nettype = $self->net->data_type;
	    my $porttype = $self->port->data_type;
	    $self->error("Port pin data type '$porttype' != Net data type '$nettype': "
			 ,$self->name,"\n");
	}
	my $netdir = "net";
	$netdir = $self->net->port->direction if $self->net->port;
	my $portdir = $self->port->direction;
	if (($netdir eq "in" && $portdir eq "out")
	    #Legal: ($netdir eq "in" && $portdir eq "inout")
	    #Legal: ($netdir eq "out" && $portdir eq "inout")
	    ) {
	    $self->error("Port is ${portdir}put from submodule, but ${netdir}put from this module: "
			 ,$self->name,"\n");
	    #$self->cell->module->netlist->dump;
	}
    }
}

sub verilog_text {
    my $self = shift;
    if ($self->port) {  # Even if it was by position, after linking we can write it as if it's by name.
	return ".".$self->port->name."(".$self->netname.")";
    } elsif ($self->pinnamed) {
	return ".".$self->name."(".$self->netname.")";
    } else { # not by name, and unlinked
	return $self->netname;
    }
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    print " "x$indent,"Pin:",$self->name,"  Net:",$self->netname,"\n";
    if ($self->port) {
	$self->port->dump($indent+10, 'norecurse');
    }
    if ($self->net) {
	$self->net->dump($indent+10, 'norecurse');
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Pin - Pin on a Verilog Cell

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $pin = $cell->find_pin ('pinname');
  print $pin->name;

=head1 DESCRIPTION

A Verilog::Netlist::Pin object is created by Verilog::Netlist::Cell for for
each pin connection on a cell.  A Pin connects a net in the current design
to a port on the instantiated cell's module.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->cell

Reference to the Verilog::Netlist::Cell the pin is under.

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->delete

Delete the pin from the cell it's under.

=item $self->module

Reference to the Verilog::Netlist::Module the pin is in.

=item $self->name

The name of the pin.  May have extra characters to make vectors connect,
generally portname is a more readable version.  There may be multiple pins
with the same portname, only one pin has a given name.

=item $self->net

Reference to the Verilog::Netlist::Net the pin connects to.  Only valid after a link.

=item $self->netlist

Reference to the Verilog::Netlist the pin is in.

=item $self->netname

The net name the pin connects to.

=item $self->portname

The name of the port connected to.

=item $self->port

Reference to the Verilog::Netlist::Port the pin connects to.  Only valid after a link.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->lint

Checks the pin for errors.  Normally called by Verilog::Netlist::lint.

=item $self->dump

Prints debugging information for this pin.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2010 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
