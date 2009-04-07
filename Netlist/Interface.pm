# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Interface;
use Class::Struct;

use Verilog::Netlist;
use Verilog::Netlist::Net;
use Verilog::Netlist::Subclass;
use vars qw($VERSION @ISA);
use strict;
@ISA = qw(Verilog::Netlist::Interface::Struct
	Verilog::Netlist::Subclass);

$VERSION = '3.200';

structs('new',
	'Verilog::Netlist::Interface::Struct'
	=>[name     	=> '$', #'	# Name of the module
	   filename 	=> '$', #'	# Filename this came from
	   lineno	=> '$', #'	# Linenumber this came from
	   netlist	=> '$', #'	# Netlist is a member of
	   userdata	=> '%',		# User information
	   attributes	=> '%', #'	# Misc attributes for systemperl or other processors
	   #
	   comment	=> '$', #'	# Comment provided by user
	   _nets	=> '%',		# hash of Verilog::Netlist::Nets
	   ]);

sub delete {
    my $self = shift;
    foreach my $oref ($self->nets) {
	$oref->delete;
    }
    my $h = $self->netlist->{_interfaces};
    delete $h->{$self->name};
    return undef;
}

######################################################################

sub is_top {}  # Ignored, for module compatibility

sub logger {
    return $_[0]->netlist->logger;
}

sub find_net {
    my $self = shift;
    my $search = shift;
    my $rtn = $self->_nets->{$search}||"";
    #print "FINDNET ",$self->name, " SS $search  $rtn\n";
    return $self->_nets->{$search} || $self->_nets->{"\\".$search." "};
}

sub attrs_sorted {
    return (sort {$a cmp $b} @{$_[0]->attrs});
}
sub nets {
    return (values %{$_[0]->_nets});
}
sub nets_sorted {
    return (sort {$a->name() cmp $b->name()} (values %{$_[0]->_nets}));
}
sub nets_and_ports_sorted {
    my $self = shift;
    return $self->nets_sorted(@_);
}

sub new_net {
    my $self = shift;
    # @_ params
    # Create a new net under this interface
    my $netref = new Verilog::Netlist::Net (direction=>'net', data_type=>'wire',
					    @_,
					    interface=>$self, );
    $self->_nets ($netref->name(), $netref);
    return $netref;
}

sub new_attr {
    my $self = shift;
    my $clean_text = shift;
    push @{$self->attrs}, $clean_text;
}

sub link {
    my $self = shift;
    # Ports create nets, so link ports before nets
    foreach my $netref ($self->nets) {
	$netref->_link();
    }
}

sub lint {
    my $self = shift;
    if (!$self->netlist->{skip_pin_interconnect}) {
	foreach my $netref ($self->nets) {
	    $netref->lint();
	}
    }
}

sub verilog_text {
    my $self = shift;
    my @out = "interface ".$self->name." (\n";
    my $indent = "   ";
    # Signal list
    foreach my $netref ($self->nets_sorted) {
	push @out, $indent, $netref->verilog_text, "\n";
    }

    push @out, "endinterface\n";
    return (wantarray ? @out : join('',@out));
}

sub dump {
    my $self = shift;
    my $indent = shift||0;
    my $norecurse = shift;
    print " "x$indent,"Interface:",$self->name(),"  File:",$self->filename(),"\n";
    if (!$norecurse) {
	foreach my $netref ($self->nets_sorted) {
	    $netref->dump($indent+2);
	}
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Interface - Interface within a Verilog Netlist

=head1 SYNOPSIS

  use Verilog::Netlist;

  ...
  my $interface = $netlist->find_interface('name');
  my $cell = $self->find_cell('name')
  my $port =  $self->find_port('name')
  my $net =  $self->find_net('name')

=head1 DESCRIPTION

A Verilog::Netlist::Interface object is created by Verilog::Netlist for
every interface in the design.

=head1 ACCESSORS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->comment

Returns any comments following the definition.  keep_comments=>1 must be
passed to Verilog::Netlist::new for comments to be retained.

=item $self->find_port_by_index

Returns the port name associated with the given index.

=item $self->name

The name of the interface.

=item $self->netlist

Reference to the Verilog::Netlist the interface is under.

=item $self->nets

Returns list of references to Verilog::Netlist::Net in the interface.

=item $self->nets_sorted

Returns list of name sorted references to Verilog::Netlist::Net in the interface.

=item $self->nets_and_ports_sorted

Returns list of name sorted references to Verilog::Netlist::Net and
Verilog::Netlist::Port in the interface.

=back

=head1 MEMBER FUNCTIONS

See also Verilog::Netlist::Subclass for additional accessors and methods.

=over 4

=item $self->autos

Updates the AUTOs for the interface.

=item $self->find_net(I<name>)

Returns Verilog::Netlist::Net matching given name.

=item $self->lint

Checks the interface for errors.

=item $self->link

Creates interconnections between this interface and other interfaces.

=item $self->new_net

Creates a new Verilog::Netlist::Net.

=item $self->dump

Prints debugging information for this interface.

=item $self->verilog_text

Returns verilog code which represents this interface.  Returned as an array
that must be joined together to form the final text string.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<http://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<http://www.veripool.org/verilog-perl>.

Copyright 2000-2009 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License
Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist::Subclass>
L<Verilog::Netlist>

=cut
