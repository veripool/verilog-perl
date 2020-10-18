# Verilog - Verilog Perl Interface
# See copyright, etc in below POD section.
######################################################################

package Verilog::Netlist::Subclass;
use Scalar::Util qw(weaken);
use Carp;

use Verilog::Netlist::Logger;
require Exporter;
use base qw(Exporter);
use vars qw($VERSION @EXPORT);
use strict;

$VERSION = '3.473';
@EXPORT = qw(structs);

# Maybe in the future.  For now all users of this must do it themselves
#struct ('Verilog::Netlist::Subclass'
#	 =>[name     	=> '$', #'	# Name of the element
#	    filename 	=> '$', #'	# Filename this came from
#	    lineno	=> '$', #'	# Linenumber this came from
#	    logger	=> '%',		# Logger object, or undef
#	    userdata	=> '%',		# User information
#	    ]);

######################################################################
#### Member functions

sub fileline {
    my $self = shift;
    return ($self->filename||"").":".($self->lineno||"");
}

######################################################################
#### Error Handling

our $_Subclass_Logger_Warned;

sub logger {
    my $self = shift;
    # This provides forward compatibility to derived classes written before
    # Verilog-Perl 3.041.  At some point this function will be removed; all
    # new derived classes should provide an override for this function.
    if (!$_Subclass_Logger_Warned) {
	warn "-Info: Object class missing logger method, update the package?: ".ref($self)."\n";
	$_Subclass_Logger_Warned = Verilog::Netlist::Logger->new();
    }
    return $_Subclass_Logger_Warned;
}

sub errors {
    my $self = shift;
    return $self->logger->errors;
}
sub warnings {
    my $self = shift;
    return $self->logger->warnings;
}

# Methods
sub info {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->info($objref,@_);
}

sub warn {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->warn($objref,@_);
}

sub error {
    my $self = shift;
    my $objref = $self; $objref = shift if ref $_[0];	# Optional reference to object
    $self->logger->error($objref,@_);
}

sub exit_if_error {
    my $self = shift;
    return $self->logger->exit_if_error(@_);
}

sub unlink_if_error {
    my $self = shift;
    # Not documented; Depreciated in Verilog-Perl 3.041.
    # Applications should call the logger object's unlink_if_error directly.
    return $self->logger->unlink_if_error(@_);
}

######################################################################
######################################################################
######################################################################
#
# Prior to perl 5.6, Class::Struct's new didn't bless the arguments,
# or allow parameter initialization!  Later versions didn't support weak
# references.
# This code is thus from Class::Struct, copyright under the Artistic license

sub structs {
    my $func = shift;
    my $baseclass = $_[0];

    # Determine parameter list structure, one of:
    #	struct (class => [ element-list ])

    my ($class, @decls);
    my $base_type = ref $_[1];
    if	($base_type eq 'ARRAY')	 {
	$class = shift;
	@decls = @{shift()};
	confess "structs usage error" if @_;
    }
    else {
	confess "structs usage error";
    }
    confess "structs usage error" if @decls % 2 == 1;

    # Create constructor.
    croak "function 'new' already defined in package $class"
	if do { no strict 'refs'; defined &{$class . "::new"} };

    my @methods = ();
    my %refs = ();
    my %arrays = ();
    my %hashes = ();
    my %types;
    my $got_class = 0;
    my $out = '';

    $out .= "{\n  package $class;\n  use Carp;\n";
    $out .= "  use Scalar::Util qw(weaken);\n\n";
    $out .= "  sub new {\n";
    $out .= "    my (\$class, \%init) = \@_;\n";
    $out .= "    \$class = __PACKAGE__ unless \@_;\n";

    my $cnt = 0;
    my ($cmt, $elem);

    if ($base_type eq 'ARRAY') {
	$out .= "    my(\$r) = [];\n";
    }
    for (my $idx=0; $idx < @decls; $idx+=2) {
	my $name = $decls[$idx];
	my $type = $decls[$idx+1];
	$types{$name} = $type;
	push (@methods, $name);
	if ($base_type eq 'ARRAY') {
	    $elem = "[$cnt]";
	    ++$cnt;
	    $cmt = " # $name";
	}
	if ($type =~ /^\*(.)/) {
	    $refs{$name}++;
	    $type = $1;
	}
	my $init = "defined(\$init{'$name'}) ? \$init{'$name'} :";
	if ($type eq '@') {
	    $out .= "    croak 'Initializer for $name must be array reference'\n";
	    $out .= "      if defined(\$init{'$name'}) && ref(\$init{'$name'}) ne 'ARRAY';\n";
	    $out .= "    \$r->$elem = $init [];$cmt\n";
	    $arrays{$name}++;
	}
	elsif ($type eq '%') {
	    $out .= "    croak 'Initializer for $name must be hash reference'\n";
	    $out .= "      if defined(\$init{'$name'}) && ref(\$init{'$name'}) ne 'HASH';\n";
	    $out .= "    \$r->$elem = $init {};$cmt\n";
	    $hashes{$name}++;
	}
	elsif ($type eq '$') {
	    $out .= "    \$r->$elem = $init undef;$cmt\n";
	}
	else{
	    croak "'$type' is not a valid struct element type";
	}
    }
    $out .= "     bless \$r, \$class;\n	}\n";

    # Create accessor methods.

    my ($pre, $pst, $sel);
    $cnt = 0;
    foreach my $name (@methods) {
	my $type = $types{$name};
	if  (do { no strict 'refs'; defined &{$class . "::$name"} }) {
	    warnings::warnif("function '$name' already defined, overrides struct accessor method");
	}
	else {
	    $pre = $pst = $cmt = $sel = '';
	    if (defined $refs{$name}) {
		$pre = "\\(";
		$pst = ")";
		$cmt = " # returns ref";
	    }
	    $out .= "  sub $name {$cmt\n    my \$r = shift;\n";
	    if ($base_type eq 'ARRAY') {
		$elem = "[$cnt]";
		++$cnt;
	    }
	    if (defined $arrays{$name}) {
		$out .= "    my \$i;\n";
		$out .= "    \@_ ? (\$i = shift) : return \$r->$elem;\n";
		$out .= "    if (ref(\$i) eq 'ARRAY' && !\@_) { \$r->$elem = \$i; return \$r }\n";
		$sel = "->[\$i]";
	    }
	    elsif (defined $hashes{$name}) {
		$out .= "    my \$i;\n";
		$out .= "    \@_ ? (\$i = shift) : return \$r->$elem;\n";
		$out .= "    if (ref(\$i) eq 'HASH' && !\@_) { \$r->$elem = \$i; return \$r }\n";
		$sel = "->{\$i}";
	    }
	    $out .= "    croak 'Too many args to $name' if \@_ > 1;\n";
	    $out .= "    \@_ ? ($pre\$r->$elem$sel = shift$pst) : $pre\$r->$elem$sel$pst;\n";
	    $out .= "  }\n";
	}
    }

    #print $out;
    $out .= "}\n1;\n";
    my $result = eval $out;
    carp $@ if $@;

    # Create top class
    (my $overclass = $baseclass) =~ s/::Struct$//;
    {
	#print \"NEW \",join(' ',\@_),\"\\n\";
	eval "
	    package $overclass;
	    sub ${func} {
		my \$class = shift;
		my \$self = new $baseclass(\@_);
		bless \$self, \$class;
	    }";
    }
}

######################################################################
#### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Netlist::Subclass - Common routines for all classes

=head1 SYNOPSIS

  package Verilog::Netlist::Something;
  use Verilog::Netlist::Subclass;
  use base qw(Verilog::Netlist::Subclass);

  ...

  $self->info("We're here\n");
  $self->warn("Things look bad\n");
  $self->error("Things are even worse\n");
  $self->exit_if_error();

=head1 DESCRIPTION

The Verilog::Netlist::Subclass is used as a base class for all
Verilog::Netlist::* structures.  It is mainly used so that $self->warn()
and $self->error() will produce consistent results.

=head1 MEMBER FUNCTIONS

=over 4

=item $self->error(I<Text...>)

Print an error in a standard format.

=item $self->errors()

Return number of errors detected.

=item $self->exit_if_error()

Exits the program if any errors were detected.

=item $self->filename()

The filename number the entity was created in.

=item $self->info(I<Text...>)

Print a informational in a standard format.

=item $self->lineno()

The line number the entity was created on.

=item $self->logger()

The class to report errors using, generally a Verilog::Netlist::Logger
object.

=item $self->userdata(I<key>)
=item $self->userdata(I<key>, I<data>)

Sets (with two arguments) or retrieves the specified key from an opaque
hash.  This may be used to store application data on the specified node.

=item $self->warn(I<Text...>)

Print a warning in a standard format.

=item $self->warnings()

Return number of warnings detected.

=back

=head1 DISTRIBUTION

Verilog-Perl is part of the L<https://www.veripool.org/> free Verilog EDA
software tool suite.  The latest version is available from CPAN and from
L<https://www.veripool.org/verilog-perl>.

Copyright 2000-2020 by Wilson Snyder.  This package is free software; you
can redistribute it and/or modify it under the terms of either the GNU
Lesser General Public License Version 3 or the Perl Artistic License Version 2.0.

=head1 AUTHORS

Wilson Snyder <wsnyder@wsnyder.org>

=head1 SEE ALSO

L<Verilog-Perl>,
L<Verilog::Netlist>

=cut
