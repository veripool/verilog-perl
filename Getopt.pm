# Verilog::Getopt.pm -- Verilog command line parsing
# $Revision: 1.57 $$Date$$Author$
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

package Verilog::Getopt;
require 5.000;
require Exporter;

use strict;
use vars qw($VERSION $Debug);
use Carp;
use IO::File;
use File::Basename;
use File::Spec;
use Cwd;

######################################################################
#### Configuration Section

$VERSION = '2.311';

#######################################################################
#######################################################################
#######################################################################

sub new {
    @_ >= 1 or croak 'usage: Verilog::Getopt->new ({options})';
    my $class = shift;		# Class (Getopt Element)
    $class ||= "Verilog::Getopt";

    my $self = {defines => {},
		incdir => ['.', ],
		module_dir => ['.', ],
		libext => ['.v', ],
		library => [ ],
		gcc_style => 1,
		vcs_style => 1,
		fileline => 'Command_Line',
		unparsed => [],
		@_
		};
    bless $self, $class;
    return $self;
}

#######################################################################
# Option parsing

sub parameter_file {
    my $self = shift;
    my $filename = shift;

    print "*parameter_file $filename\n" if $Debug;
    my $fh = IO::File->new($filename) or die "%Error: ".$self->fileline().": $! $filename\n";
    my $hold_fileline = $self->fileline();
    while (my $line = $fh->getline()) {
	chomp $line;
	$line =~ s/\/\/.*$//;
	next if $line =~ /^\s*$/;
	$self->fileline ("$filename:$.");
	my @p = (split /\s+/,"$line ");
	$self->_parameter_parse(@p);
    }
    $fh->close();
    $self->fileline($hold_fileline);
}

sub parameter {
    my $self = shift;
    # Parse VCS like parameters, and perform standard setup based on it
    # Return list of leftover parameters
    @{$self->{unparsed}} = ();
    $self->_parameter_parse(@_);
    return @{$self->{unparsed}};
}

sub _parameter_parse {
    my $self = shift;
    # Internal: Parse list of VCS like parameters, and perform standard setup based on it
    foreach my $param (@_) {
	next if ($param =~ /^\s*$/);
	print " parameter($param)\n" if $Debug;

	### GCC & VCS style
	if ($param eq '-f') {
	    $self->{_parameter_next} = $param;
	}

	### VCS style
	elsif (($param eq '-v'
		|| $param eq '-y') && $self->{vcs_style}) {
	    $self->{_parameter_next} = $param;
	}
	elsif ($param =~ /^\+libext\+(.*)$/ && $self->{vcs_style}) {
	    my $ext = $1;
	    foreach (split /\+/, $ext) {
		$self->libext($_);
	    }
	}
	elsif ($param =~ /^\+incdir\+(.*)$/ && $self->{vcs_style}) {
	    $self->incdir($1);
	}
	elsif (($param =~ /^\+define\+([^+=]*)[+=](.*)$/
		|| $param =~ /^\+define\+(.*?)()$/) && $self->{vcs_style}) {
	    $self->define ($1, $2);
	}
	# Ignored
	elsif ($param =~ /^\+librescan$/ && $self->{vcs_style}) {
	}

	### GCC style
	elsif (($param =~ /^-D([^=]*)=(.*)$/
		|| $param =~ /^-D([^=]*)()$/) && $self->{gcc_style}) {
	    $self->define($1,$2);
	}
	elsif (($param =~ /^-U([^=]*)$/) && $self->{gcc_style}) {
	    $self->undef($1);
	}
	elsif ($param =~ /^-I(.*)$/ && $self->{gcc_style}) {
	    $self->incdir($1);
	}

	# Second parameters
	elsif ($self->{_parameter_next}) {
	    my $pn = $self->{_parameter_next};
	    $self->{_parameter_next} = undef;
	    if ($pn eq '-f') {
		$self->parameter_file ($param);
	    }
	    elsif ($pn eq '-v') {
		$self->library ($param);
	    }
	    elsif ($pn eq '-y') {
		$self->module_dir ($param);
	    }
	    else {
		die "%Error: ".$self->fileline().": Bad internal next param ".$pn;
	    }
	}

	else { # Unknown
	    push @{$self->{unparsed}}, $param;
	}
    }
}

#######################################################################
# Accessors

sub fileline {
    my $self = shift;
    if (@_) { $self->{fileline} = shift; }
    return ($self->{fileline});
}
sub incdir {
    my $self = shift;
    if (@_) {
	my $token = shift;
	print "incdir $token\n" if $Debug;
	if (ref $token) {
	    @{$self->{incdir}} = @{$token};
	} else {
	    push @{$self->{incdir}}, $self->file_abs($token);
	}
	$self->file_path_cache_flush();
    }
    return (wantarray ? @{$self->{incdir}} : $self->{incdir});
}
sub libext {
    my $self = shift;
    if (@_) {
	my $token = shift;
	print "libext $token\n" if $Debug;
	if (ref $token) {
	    @{$self->{libext}} = @{$token};
	} else {
	    push @{$self->{libext}}, $token;
	}
	$self->file_path_cache_flush();
    }
    return (wantarray ? @{$self->{libext}} : $self->{libext});
}
sub library {
    my $self = shift;
    if (@_) {
	my $token = shift;
	print "library $token\n" if $Debug;
	if (ref $token) {
	    @{$self->{library}} = @{$token};
	} else {
	    push @{$self->{library}}, $self->file_abs($token);
	}
    }
    return (wantarray ? @{$self->{library}} : $self->{library});
}
sub module_dir {
    my $self = shift;
    if (@_) {
	my $token = shift;
	print "module_dir $token\n" if $Debug;
	if (ref $token) {
	    @{$self->{module_dir}} = @{$token};
	} else {
	    push @{$self->{module_dir}}, $self->file_abs($token);
	}
	$self->file_path_cache_flush();
    }
    return (wantarray ? @{$self->{module_dir}} : $self->{module_dir});
}
sub depend_files {
    my $self = shift;
    if (@_) {
	if (ref $_[0]) {
	    $self->{depend_files} = {};
	    foreach my $fn (@{$_[0]}) {
		$self->{depend_files}{$fn} = 1;
	    }
	} else {
	    foreach my $fn (@_) {
		print "depend_files $fn\n" if $Debug;
		$self->{depend_files}{$fn} = 1;
	    }
	}
    }
    my @list = (sort (keys %{$self->{depend_files}}));
    return (wantarray ? @list : \@list);
}

sub get_parameters {
    my $self = shift;
    # Defines
    my @params = ();
    foreach my $def (sort (keys %{$self->{defines}})) {
	my $defvalue = $self->defvalue($def);
	$defvalue = "=".($defvalue||"") if (defined $defvalue && $defvalue ne "");
	if ($self->{gcc_style}) {
	    push @params, "-D${def}${defvalue}";
	} else {
	    push @params, "+define+${def}${defvalue}";
	}
    }
    # Put all libexts on one line, else NC-Verilog will bitch
    my $exts="";
    foreach my $ext ($self->libext()) {
	$exts = "+libext" if !$exts;
	$exts .= "+$ext";
    }
    push @params, $exts if $exts;
    # Includes...
    foreach my $dir ($self->incdir()) {
	if ($self->{gcc_style}) {
	    push @params, "-I${dir}";
	} else {
	    push @params, "+incdir+${dir}";
	}
    }
    foreach my $dir ($self->module_dir()) {
	push @params, "-y", $dir;
    }
    foreach my $dir ($self->library()) {
	push @params, "-v", $dir;
    }
    return (@params);
}

#######################################################################
# Utility functions

sub remove_duplicates {
    my $self = shift if ref $_[0];
    # return list in same order, with any duplicates removed
    my @rtn;
    my %hit;
    foreach (@_) { push @rtn, $_ unless $hit{$_}++; }
    return @rtn;
}

sub file_abs {
    my $self = shift;
    my $filename = shift;
    # return absolute filename
    # If the user doesn't want this absolutification, they can just
    # make their own derived class and override this function.
    #
    # We don't absolutify files that don't have any path,
    # as file_path() will probably be used to resolve them.
    return $filename;
    return $filename if ("" eq dirname($filename));
    return $filename if File::Spec->file_name_is_absolute($filename);
    # Cwd::abspath() requires files to exist.  Too annoying...
    $filename = File::Spec->canonpath(File::Spec->catdir(Cwd::getcwd(),$filename));
    return $filename;
}

sub file_path_cache_flush {
    my $self = shift;
    # Clear out a file_path cache, needed if the incdir/module_dirs change
    $self->{_file_path_cache} = {};
}

sub file_path {
    my $self = shift;
    my $filename = shift;
    # return path to given filename using library directories & files, or undef
    # locations are cached, because -r can be a very slow operation

    defined $filename or carp "%Error: Undefined filename,";
    return $self->{_file_path_cache}{$filename} if defined $self->{_file_path_cache}{$filename};
    if (-r $filename && !-d $filename) {
	$self->{_file_path_cache}{$filename} = $filename;
	$self->depend_files($filename);
	return $filename;
    }
    # Check each search path
    # We use both the incdir and moduledir.  This isn't strictly correct,
    # but it's fairly silly to have to specify both all of the time.
    my %checked = ();
    foreach my $dir (@{$self->incdir()}, @{$self->module_dir()}) {
	next if $checked{$dir}; $checked{$dir}=1;  # -r can be quite slow
	# Check each postfix added to the file
	foreach my $postfix ("", @{$self->{libext}}) {
	    my $found = "$dir/$filename$postfix";
	    next if $checked{$found}; $checked{$found}=1;  # -r can be quite slow
	    if (-r $found && !-d $filename) {
		$self->{_file_path_cache}{$filename} = $found;
		$self->depend_files($found);
		return $found;
	    }
	}
    }
    
    return $filename;	# Let whoever needs it discover it doesn't exist
}

sub libext_matches {
    my $self = shift;
    my $filename = shift;
    return undef if !$filename;
    foreach my $postfix (@{$self->{libext}}) {
	my $re = quotemeta($postfix) . "\$";
	return $filename if ($filename =~ /$re/);
    }
    return undef;
}

#######################################################################
# Getopt functions

sub defparams {
    my $self = shift;
    my $token = shift;
    my $val = $self->{defines}{$token};
    if (!defined $val) {
	return undef;
    } elsif (ref $val) {
	return $val->[1];  # Has parameters, return param list
    } else {
	return 0;
    }
}
sub defvalue {
    my $self = shift;
    my $token = shift;
    my $val = $self->{defines}{$token};
    (defined $val) or carp "%Warning: ".$self->fileline().": No definition for $token,";
    if (ref $val) {
	return $val->[0];  # Has parameters, return just value
    } else {
	return $val;
    }
}
sub defvalue_nowarn {
    my $self = shift;
    my $token = shift;
    my $val = $self->{defines}{$token};
    if (ref $val) {
	return $val->[0];  # Has parameters, return just value
    } else {
	return $val;
    }
}
sub define {
    my $self = shift;
    if (@_) {
	my $token = shift;
	my $value = shift;
	my $params = shift||"";
	print "Define $token $params= $value\n" if $Debug;
	my $oldval = $self->{defines}{$token};
	(!defined $oldval or ($oldval eq $value)) or warn "%Warning: ".$self->fileline().": Redefining `$token\n";
	if ($params) {
	    $self->{defines}{$token} = [$value, $params];
	} else {
	    $self->{defines}{$token} = $value;
	}
    }
}
sub undef {
    my $self = shift;
    my $token = shift;
    my $oldval = $self->{defines}{$token};
    (defined $oldval) or carp "%Warning: ".$self->fileline().": No definition to undef for $token,";
    delete $self->{defines}{$token};
}

######################################################################
### Package return
1;
__END__

=pod

=head1 NAME

Verilog::Getopt - Get Verilog command line options

=head1 SYNOPSIS

  use Verilog::Getopt;

  my $opt = new Verilog::Getopt;
  $opt->parameter (qw( +incdir+standard_include_directory ));

  @ARGV = $opt->parameter (@ARGV);
  ...
  print "Path to foo.v is ", $opt->file_path('foo.v');

=head1 DESCRIPTION

The L<Verilog::Getopt> package provides standardized handling of options similar
to Verilog/VCS and cc/GCC.

=over 4

=item $opt = Verilog::Getopt->new ( I<opts> )

Create a new Getopt.  If gcc_style=>0 is passed as a parameter, parsing of
GCC-like parameters is disabled.  If vcs_style=>0 is passed as a parameter,
parsing of VCS-like parameters is disabled.

=item $self->file_path ( I<filename> )

Returns a new path to the filename, using the library directories and
search paths to resolve the file.

=item $self->get_parameters ( )

Returns a list of parameters that when passed through $self->parameter()
should result in the same state.  Often this is used to form command lines
for downstream programs that also use Verilog::Getopt.

=item $self->parameter ( \@params )

Parses any recognized parameters in the referenced array, removing the
standard parameters and returning a array with all unparsed parameters.

The below list shows the VCS-like parameters that are supported, and the
functions that are called:

    +libext+I<ext>+I<ext>...	libext (I<ext>)
    +incdir+I<dir>		incdir (I<dir>)
    +define+I<var>[+=]I<value>	define (I<var>,I<value>)
    +define+I<var>		define (I<var>,undef)
    +librescan		Ignored
    -f I<file>		Parse parameters in file
    -v I<file>		library (I<file>)
    -y I<dir>		module_dir (I<dir>)
    all others		Put in returned list

The below list shows the GCC-like parameters that are supported, and the
functions that are called:

    -DI<var>=I<value>		define (I<var>,I<value>)
    -DI<var>		define (I<var>,undef)
    -UI<var>		undefine (I<var>)
    -II<dir>		incdir (I<dir>)
    -f I<file>		Parse parameters in file
    all others		Put in returned list

=back

=head1 ACCESSORS

=over 4

=item $self->define ( $token, $value )

This method is called when a define is recognized.  The default behavior
loads a hash that is used to fulfill define references.  This function may
also be called outside parsing to predefine values.

=item $self->defparams ( $token )

This method returns the parameter list of the define.  This will be defined,
but false, if the define does not have arguments.

=item $self->defvalue ( $token )

This method returns the value of a given define, or prints a warning.

=item $self->defvalue_nowarn ( $token )

This method returns the value of a given define, or undef.

=item $self->depend_files ()

Returns reference to list of filenames referenced with file_path, useful
for creating dependency lists.  With argument, adds that file.  With list
reference argument, sets the list to the argument.

=item $self->file_abs ( $filename )

Using the incdir and libext lists, convert the specified module or filename
("foo") to a absolute filename ("include/dir/foo.v").

=item $self->incdir ()

Returns reference to list of include directories.  With argument, adds that
directory.

=item $self->libext ()

Returns reference to list of library extensions.  With argument, adds that
extension.

=item $self->libext_matches (I<filename>)

Returns true if the passed filename matches the libext.

=item $self->library ()

Returns reference to list of libraries.  With argument, adds that library.

=item $self->module_dir ()

Returns reference to list of module directories.  With argument, adds that
directory.

=item $self->undef ( $token )

Deletes a hash element that is used to fulfill define references.  This
function may also be called outside parsing to erase a predefined value.

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

L<Verilog::Language>

=cut
