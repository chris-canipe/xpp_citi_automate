package XPP::CITI::Automate;

use strict;
use warnings FATAL => qw(all);
use feature qw(switch state);

use Moose;
use MooseX::StrictConstructor;
use Moose::Util::TypeConstraints;

use Carp;
use File::Copy;
use File::Temp;
use Path::Class;
use Regexp::Assemble;
use Set::IntSpan;
use Unicode::Normalize;

#=========#
# Signals #
#=========#

### Make dies showy because they can easily disappear in the flood of CITI output.
$SIG{__DIE__} = sub {
	my $msg = shift;
	print "\n\n";
	print +('X' x 30, "\n") x 3;
	print "\n$msg\n";
	print +('X' x 30, "\n") x 3;
	print "\n\n";
	exit 1;
};

#=============#
# Verify Args #
#=============#

### There should only be two arguments when called by CITI: the in and out files.
croak "Incorrect usage. Are you calling this from CITI?\n" if 2 != grep { -f } @ARGV;

#=======#
# Files #
#=======#

#--------#
# In/Out #
#--------#

my ($in_file, $out_file) = @ARGV;
open my $IN, '<:utf8', $in_file or die $!;
### The out_file is not opened here, but overwritten later on.
our $in;
our $out;

#-------#
# Temps #
#-------#

my $tmp_dir;
my @tmp_files = ([$in_file, $IN]);

#===========#
# Variables #
#===========#

### p1-p6 with an optional <ri> print-style and prefix.
our $page_format_re = qr/
	\A
	(p[1-6])
	:?
	([ar]n|RN|ABC|abc|anss?|anzz?|aio|AIO|0)?
	:?
	(.+)?
	\z
/x;

### RE's for CITI formats.
our $rsv_re = qr{
	(?<rsv>
		<
		(?:\?xpp\x20)? ### XML only
		rsv;
		(?:
			### These are present if rsv is set to "full"
			(?<nr0>\d+);(?<nr1>\d+);(?<nr2>\d+);(?<nr3>\d+);(?<nr4>\d+);
			(?<nr5>\d+);(?<nr6>\d+);(?<nr7>\d+);(?<nr8>\d+);(?<nr9>\d+);
			(?<nr10>\d+);(?<nr11>\d+);(?<nr12>\d+);(?<nr13>\d+);(?<nr14>\d+);
			(?<nr15>\d+);(?<nr16>\d+);(?<nr17>\d+);(?<nr18>\d+);(?<nr19>\d+);
		)?
		### These are present if rsv is "full" or "page"
		(?<page_position>\d+);
		(?<relative_page>\d+);
		(?<p1>\d+);
		(?<p2>\d+);
		(?<p3>\d+);
		(?<p4>\d+);
		(?<p5>\d+);
		(?<p6>\d+)
		\?? ### XML only
		>
	)
}x ;

our $entry_re = qr{
	\A
	(?:
		(?:$rsv_re)? ### Optional rsv, although it should exist for the last level.
		(?<begin_string>[^\x1f]*) ### Optional "Insert String"
		\x1f ### Separator
		(?!$rsv_re) ### If there's another rsv the file probably isn't deduped properly.
		(?<content_and_end_string>.*?) ### Optional content and "Insert at End"
		% ### CITI always adds a pgraf at the end.
		(\x1f|\z) ### Either another level after this one, or nothing.
	)+
}x;

our $dd_entry_re = qr{
	\A
	$rsv_re ### rsv: These always exist for dedupes.
	### Begin strings do not exist for dedupes.
	\x1f ### Separator
	### Content and "Insert at End" do not exist for dedupes.
	% ### No need to check for escapes; this is placed by XPP and will never have a percent sign.
	\z
}x;

#============#
# Attributes #
#============#

#-------#
# Bools #
#-------#

has 'debug' => (
	is => 'rw',
	isa => 'Bool',
	default => 0,
	trigger => sub {
		my ($self, $debug) = @_;
		$File::Temp::KEEP_ALL = 1 if $debug;
	}
);

has 'strip_eb_ep' => (
	is => 'rw',
	isa => 'Bool',
	default => 1,
);

has 'strip_keeps' => (
	is => 'rw',
	isa => 'Bool',
	default => 1,
);

has 'strip_pgrafs' => (
	is => 'rw',
	isa => 'Bool',
	default => 1,
);

has 'initial_case_sensitive' => (
	is => 'rw',
	isa => 'Bool',
	default => 0,
);

has 'initial_ignore_diacritics' => (
	is => 'rw',
	isa => 'Bool',
	default => 1,
);

has 'move_uninitialized_to_top' => (
	is => 'rw',
	isa => 'Bool',
	default => 1,
);

#--------------#
# Initializing #
#--------------#

has 'initial_prefix' => (
	is => 'rw',
	isa => 'Str',
	predicate => 'has_initial_prefix',
);

has 'initial_re' => (
	is => 'rw',
	isa => 'Str',
	predicate => 'has_initial_re',
);

has '_initial_re' => (
	is => 'ro',
	isa => 'RegexpRef',
	lazy => 1,
	default => sub {
		my $self = shift;
		### By default match anything up to the x1f.
		my $candidate_re = $self->has_initial_candidates ?
			$self->_initial_candidates_re->re :
			'[^\x1f]+';
		### By default match any one letter or digit.
		my $initial_re = $self->has_initial_re ?
			$self->initial_re :
			'([\p{L}\p{N}])' ;
		qr/^($candidate_re\x1f$initial_re)/m
	},
);

### Controls which strings (tags, macros) get initialized.
has 'initial_candidates' => (
	is => 'rw',
	isa => 'ArrayRef[Str]',
	predicate => 'has_initial_candidates',
	trigger => sub {
		my ($self, $array_ref) = @_;
		die "Initial candidates cannot be empty" unless @$array_ref;
		for (@$array_ref) {
			### Make the string regex-safe then revert escaped *'s.
			$_ = quotemeta $_;
			s/\\\*/.*?/g;
			$self->_initial_candidates_re->add($_);
		}
	}
);

has '_initial_candidates_re' => (
	is => 'ro',
	isa => 'Regexp::Assemble',
	default => sub { Regexp::Assemble->new },
	handles => [qw(add re)]
);

#------------#
# Page Stuff # 
#------------#

subtype 'PageNumber'
	=> as 'Str'
	=> where { $_ =~ $page_format_re }
	=> message { "$_ is invalid." };

has 'pages' => (
	traits => ['Array'],
	is => 'rw',
	isa => 'ArrayRef[PageNumber]',
	default => sub { ['p4:an:{p4}'] },
	handles => {
		_page_elements => 'elements',
	},
);

has '_page_part' => (
	traits  => ['Array'],
	is      => 'ro',
	isa     => 'ArrayRef[Str]',
	default => sub { [] },
	handles => {
		_page_part_elements => 'elements',
		_page_part_count => 'count',
		_set_page_part => 'push',
		_get_page_part => 'get',
	},
);

has '_page_format' => (
	traits  => ['Hash'],
	is      => 'ro',
	isa     => 'HashRef[Str]',
	default => sub { {} },
	handles => {
	  _set_page_format => 'set',
	  _get_page_format => 'get',
	},
);

has '_page_prefix' => (
	traits  => ['Hash'],
	is      => 'ro',
	isa     => 'HashRef[Str]',
	default => sub { {} },
	handles => {
	  _set_page_prefix => 'set',
  	  _get_page_prefix => 'get',
	},
);

#------#
# Misc #
#------#

has 'modifier' => (
	is => 'rw',
	isa => 'CodeRef',
	predicate => 'has_modifier',
);

has 'tmp_dir' => (
	is => 'rw',
	isa => 'Str',
	default => '/tmp',
	trigger => sub {
		my ($self, $path) = @_;
		die "Path specified in tmp_dir does not exist.\n" if ! -e $path;
		die "Path specified in tmp_dir is not writable.\n" if ! -w $path;
	}
);

#=========#
# Methods #
#=========#

sub process {
	
	my $self = shift;

	$tmp_dir = File::Temp->newdir($ENV{USER} . '-ci-XXXX', DIR => $self->tmp_dir);
	print STDERR "\nUsing temporary directory: $tmp_dir\n\n" if $self->debug;
		
	### Parse the formats and prefixes out of the page numbers;
	### default to arabic numerals and self-describing tags.
	for ($self->_page_elements) {
		m/$page_format_re/;
		$self->_set_page_part($1);
		$self->_set_page_format($1, $2 || 'an');
		$self->_set_page_prefix($1, $3 || "{$1}");
	}

	### Loop through the file, append deduped lines to entry lines by a record
	### separator (0x1e, seen via "less" as "^^"), apply any content modifiers,
	### and output to a temporary file.
	$self->_create_tmp_file('basic_reformat');
	($in, $out) = $self->_get_in_out_files;
	while (<$in>) {
		s/\s+\z//;
		if ($_ =~ $dd_entry_re) {
			### Remove the 0x1f's and pgrafs. 0x1e will be the sole separator for these.
			s/[\x1f%]//g;
			print $out "\x{1e}$_";
		}
		else {
			print $out "\n" unless $. == 1;
			print $out $_;
		}
	}
	
	### Loop through the temporary file, convert to classic, and build/output page structs.
	$self->_create_tmp_file('page_reformat');
	($in, $out) = $self->_get_in_out_files;
	while (<$in>) {
		s/\s+\z//;
		### Separate the entry from the deduped data.
		my ($entry, @deduped) = split /\x1e/, $_;
		### Convert XML macros to the "Classic" XPP format.
		s/<\?xpp\s+(.+?)\s*\?>/<$1>/g;
		### Validate the entry, matching any number of levels, but only
		### saving the last (because it will be the extent of the dedupe).
		die "Invalid CITI format!" unless $entry =~ $entry_re;
		### Add the last level's rsv to the dedupes (if any).
		### These will be processed as one.
		my $last_level = \%+;
		unshift @deduped, $last_level->{rsv} ||
			die "No <rsv> macros are available to parse. Please check the CI spec.";
		### Strip the rsv's from the entry.
		$entry =~ s/$rsv_re//g;
		### Break mutli-level entries onto their own line.
		$entry =~ s/(?<!\\)%\x1f/\n/g;
		### Strips.
		$entry =~ s/(?<!\\)%//g if $self->strip_pgrafs;
		$entry =~ s/<e[bp][^<>]*>//g if $self->strip_eb_ep;
		$entry =~ s/<(?:k[se]|vk)[^<>]*>//g if $self->strip_keeps;
		### Output the entry.
		print $out $entry;
		### Place the page data into a structure based on the user-specified pages.
		### Multiple levels use a hash ref; single levels an array ref.
		my $page_nos = $self->_page_part_count == 1 ? [] : {} ;
		for my $rsv (@deduped) {
			$rsv =~ $rsv_re or die $!;
			### When multiple page parts are present create a multilevel hash where all
			### page part numbers are keys, except for the last--it's arrayed in the last key.
			my @page_parts = $self->_page_part_elements;
			if ($self->_page_part_count > 1) {
				my $last_page_part = pop @page_parts;
				_create_page_no_hash(
					$page_nos,
					[ @+{@page_parts} ],
					$+{$last_page_part},
				);
			}
			### When only one page number is present use an array.
			else {
				my $page_no = shift @page_parts;
				push @$page_nos, $+{$page_no};
			}
		}
		$self->_output_pages($page_nos);
		print $out "\n";
	}
	
	### Modifiers and initializing.
	$self->_apply_modifier(
		$self->has_initial_prefix ? ('modifier_pre', 0) : ('modifier', 1)
	) if $self->has_modifier;
	
	if ($self->has_initial_prefix) {
		$self->_apply_initialization;
		$self->_apply_modifier('modifier_post', 1) if $self->has_modifier;
	}
	
	### Copy the final file to CITI's expected output.
	my $final = pop @tmp_files;
	if ($self->debug) {
		print STDERR "Writing result.\n";
		print STDERR 'Using input file : ', $final->[0], "\n";
		print STDERR 'Using output file: ', $out_file, "\n\n";
	}
	close $final->[1] or die $!;
	copy($final->[0], $out_file) or die $!;
}

sub _apply_initialization {
	my $self = shift;
	$self->_create_tmp_file('initial');
	my ($in, $out) = $self->_get_in_out_files;
	### Place content in $_ for the RE to use.
	local $_ = do { undef $/; <$in>; };
	### Perform initializing and prefix each line with an acknowledgement (x6).
	my $re = $self->_initial_re;
	my $prefix = $self->initial_prefix;
	my $last_initial = q{};
	s{$re}{
		my ($full_match, $initial) = ($1, $2);
		### Diacritics.
		if ($self->initial_ignore_diacritics) {
			$initial = NFD($initial);
			$initial =~ s/\p{M}+//g ;
		}
		### Case.
		my $initial_cmp = $self->initial_case_sensitive ? $initial : uc $initial ;
		### Only add the initialization if it changed.
		my $return = $last_initial eq $initial_cmp ?
			chr(6) . $full_match :
			chr(6) . "$prefix$initial\n" . chr(6) . $full_match ;
		$last_initial = $initial_cmp;
		$return;
	}gme;
	### Array the lines that weren't initialized (acknowledged with x6), remove
	### them, remove the acknowledgements, and prepend the non-initialized.
	if ($self->move_uninitialized_to_top) {
		my @non_i;
		push @non_i, $1 while m/^(?!\x06)(.+)/mg;
		s/^(?!\x06).+\n//mg;
		$_ = join "\n" => @non_i, $_;
	}
	s/^\x06//mg;
	print $out $_;
}

sub _create_tmp_file {
	my $self = shift;
	my $desc = shift || '';
	my $file = file($tmp_dir, scalar @tmp_files . ($desc ? "-$desc" : ''))->stringify;
	print STDERR "Created new temporary file: $file\n" if $self->debug;
	open my $fh, '+>:utf8', $file or die $!;
	push @tmp_files, [ $file, $fh ];
}

### The last index is being written to and the last index - 1 is being read.
sub _get_in_out_files {
	my $self = shift;
	my ($in, $out) = @tmp_files[$#tmp_files-1, $#tmp_files];
	if ($self->debug) {
		print STDERR 'Using input file : ', $in->[0], "\n";
		print STDERR 'Using output file: ', $out->[0], "\n\n";
	}
	seek($in->[1], 0, 0) or die $!;
	return ($in->[1], $out->[1]);
}

sub _apply_modifier {
	my ($self, $desc, $final) = @_;
	$self->_create_tmp_file($desc);
	my ($in, $out) = $self->_get_in_out_files;
	### Place content in $_ for the modifier to use.
	local $_ = do { undef $/; <$in>; };
	$self->modifier->($final || 0);
	print $out $_;
}

### Code from http://perlmonks.org/?node_id=535551
sub _create_page_no_hash {
	my ($hash, $keys, $value) = @_;
	my @keys = @$keys;
	while (@keys && defined $hash) {
		my $key = shift @keys;
		if (@keys) {
			$hash->{$key} = {} if ! exists $hash->{$key};
			$hash = $hash->{$key};
		} else {
			$hash->{$key} = [] if ! exists $hash->{$key};
			push @{$hash->{$key}}, $value if defined $value;
			return \$hash->{$key};
		}
	}
}

sub _output_pages {
	my $self = shift;
	my $ref = shift;
	return unless ref $ref;
	
	my $lvl = shift // -1;
	++$lvl;
	
	my $page_type = $self->_get_page_part($lvl);
	my $sep = $self->_get_page_prefix($page_type);
	my $format = $self->_get_page_format($page_type);	

	given (ref $ref) {
		when ('HASH') {
			for (keys %$ref) {
				printf $out '%s<ri;%s;%s>', $sep, $_, $format;
				### Recurse.
				$self->_output_pages($ref->{$_}, $lvl);
			}
		}
		when ('ARRAY') {
			my $ranger = Set::IntSpan->new(@$ref);
			print $out $sep, map {
				s/(?<=,)/ /g;
				s/(\d+)/<ri;$1;$format>/g;
				$_;
			} $ranger->run_list;
		}
	}
}

no Moose;
__PACKAGE__->meta->make_immutable;

__END__

=head1 NAME

XPP::CITI::Automate -- Automates the formatting and parsing of CITI extracts.

=head1 SYNOPSIS

In its simplest form:

  #!/usr/local/bin/perl
  use warnings;
  use strict;
  use lib '/usr/local/lib/perl_aps';
  use XPP::CITI::Automate;

  XPP::CITI::Automate->new->process;
	
In its verbose (if not sane) form:
	
  #!/usr/local/bin/perl
  use warnings;
  use strict;
  use lib '/usr/local/lib/perl_aps';
  use XPP::CITI::Automate;

  XPP::CITI::Automate->new(
  	pages => [qw(p3:ABC:{section} p4:rn:{page})],
	initial_case_sensitive => 0,
	initial_ignore_diacritics => 0,
  	initial_prefix => '{idx_initial}',
  	initial_re => '(Mc|[\p{L}\p{N}])',
	initial_candidates => [qw(
		{tag*}
		<macro>
	)],
  	modifier => sub {
  		 my $final = shift;
  		if ($final) {
  			### Modify the data at the very end of the process.
  		}
  		else {
  			### Modify the data prior to initializing.
  		}
  	},
	move_uninitialized_to_top => 1,
	strip_eb_ep => 1,
	strip_keeps => 1,
	strip_pgafs => 1,
	tmp_dir => '/tmp',
  	debug => 1,
)->process;

=head1 DESCRIPTION

C<XPP::CITI::Automate> parses and reformats CITI extracts.

It:

=over 4

=item 1

Can be used for jobs that are set in "Classic" or XML; however, it only outputs "Classic" XPP codes.

=item 2

Is set up in a Perl script and called as one of CITI's processes.

=item 3

Is Unicode-friendly.

=item 4

Handles the transformation of C<< <rsv> >> macros into friendlier formats. The user can control which multi-part page numbers are used (p1-p6), what print-style (format) they're output as (arabic numeral, roman numeral, alpha character, etc.), and what they're prefixed by (generally a tag). Page numbers are automatically separated by a comma and a space (1, 3, 5), ranged (1-5), or a mix of the two (1, 3-5).

=item 5

Handles initial letteringE<mdash>putting "A" above the A's, "B" above the B's, etc. The user can control if it's executed or not, which candidates (tags or macros) are initialized, which characters are used for initializing (it can be letters and digits, I<any> character, or even multiple characters), and what the initial is prefixed by (again, generally a tag).

=item 6

Strips elements that are generally of no import to indexing, such as pgrafs, keeps (C<< <ks> >>, C<< <ke> >>, C<< <vk> >>) and breaks (C<< <eb> >>, C<< <ep> >>).

=item 7

Allows global modifications to be made.

=back

=head1 TERMINOLOGY

candidates

=over 4

By default all prefixes are included in the initializing process. When more than one level is present in the extract you can control which are initialized and this is done by specifying candidates. For example, if your tags are C<{level_one}> and C<{level_two}>, you can restrict the initializing to C<{level_one}> by specifying it as a candidate:

  initial_candidates => [qw(
	{level_one}
  )]

Similar to CITI's functionality, you may use an asterisk to include tags or macros that have attributes:

  initial_candidates => [qw(
  	{level_one*}
  )]

Lastly, multiple candidates are valid:

  initial_candidates => [qw(
  	{level_one*}
	<level_one*>
  )]
  
=back

initializing; initial lettering

=over 4

The process of generating initials from strings; e.g., "A" is the initial of "Apple", "B" the initial of "Banana", "1" the intial of "123", etc. This is customizable and not restricted to one character or alpha characters. Also, any candidates that were not initialized (because they didn't match the patternE<mdash>punctuation, for instance) will be placed at the beginning of the file. This is done to prevent erroneous intermixing and it can be disabled if needed.

=back

prefix

=over 4

This is synonymous to CITI's "Insert String" fieldZ<>E<mdash>Z<>the content (generally a tag, possibly a macro) that is inserted before the extracted data.

=back

print-style

=over 4

These are described under C<< <ri> >> in the XyMacro documentation.

=back

=head1 SETUP

Four things must be done to use this module:

=over 4

=item 1

A Perl script must be created that uses this module.

=item 2

The Language field in the CITI spec must be populated. This enables XPP's Unicode libraries (ICU), converts the incoming data to UTF-8, and informs the sort process (if any) that it needs to use Unicode collation.

=item 3

The highest level that you extract must have an RSV Macro Form that is not "C<none>" as C<< <rsv> >> macros are required for parsing. If for some reason you do not need to display page numbers simply suppress them within the XPP styles or remove them using the C<modifier> feature.

=item 4

The Perl script must be called from one of the Process Name slots in the CITI spec. It should appear prior to  C<toxsf> and C<compose> and come after any sort and/or dedupe processes.

=begin html

<br><br><img src="images/setup.jpg">

=end html

=back

=head1 DEFAULTS

By default the module does the following:

=over 4

=item 1

Extracts the p4 multi-part page number from the C<< <rsv> >> macros, prefixes them with a C<{p4}> tag, and outputs them as arabic numerals.

=item 2

Strips pgrafs, keeps, and breaks.

=item 3

Creates intermediate files in C</tmp> and removes them automatically.

=back

When initial lettering is activated it has the following defaults:

=over 4

=item 1

Only the first letter or digit of any entry (because there are no candidates) is initialized.

=item 2

Case is ignored.

=item 3

Diacritics are ignored.

=item 4

Any entries that are not initialized are moved to the top of the file.

=back

=head1 METHODS

=over 4

=item new

Creates the object and defines its parameters:

=over 4

=item debug

A boolean that controls debugging. When enabled the script outputs the name of the temporary files that are created and does not remove them automatically. Do B<not> leave this option on after debugging as it will retain a slew of unecessary files. This defaults to 0.

=item initial_candidates

This is supplied as an array reference and each element specifies a candidate. See "candidates" under L</TERMINOLOGY>.

=item initial_case_sensitive

A boolean that makes initializing case sensitive, e.g., "A" and "a" will be not grouped together under "A", but separately under "A" and "a". This defaults to 0.

=item initial_ignore_diacritics

A boolean that makes initializaing ignore diacritical marks, e.g., "A", "E<Aacute>", "E<Agrave>", and "E<Aring>" will all be grouped under the base character of "A". This defaults to 1.

=item initial_prefix

A string (generally a tag, possibly a macro) used to prefix the initials. When this is set it causes the module to perform initial lettering. By default this is not set and initial lettering is not performed.

=item initial_re

A string used to override the default regular expressionZ<>E<mdash>Z<>C<([\p{L}\p{N}])>Z<>E<mdash>Z<>that controls initializing. The default matches any one character that is classified as a letter or digit, but you may change this as you wish. Be sure to enclose the part you want initialized in capturing parenthesis: C<()>.

For example, if you want last names that start with "Mc" to have their own initial and also perform the default initializing, use:

  (Mc|[\p{L}\p{N}])

You can also initial I<any> character by using:

  (\X)

Lastly, keep in mind that initializing is not restricted to one character; you can do any number:

  (\X{2})
  
For more information see the Regular Expression Unicode Properties L<here|http://www.regular-expressions.info/unicode.html> and Perl's regular expression docs L<here|http://perldoc.perl.org/perlre.html>.
  
=item modifier

A user-defined subroutine that modifies the entire data set (stored in C<$_>). It is called after all other processes have completed; however, it will also be called before the initializing process when it is ran. An argument is passed to this routine that indicates where in the process flow it has been called: if 0, it is being called prior to initial lettering; if 1, it is being called after the entire set of processes. This can be used to perform different sets of modification like so:

  modifier => sub {
 	my $final = shift;
 	if ($final) {
 		### Modify the data at the very end of the process.
 	}
 	else {
 		### Modify the data prior to initializing.
 	}
  }

=item move_uninitialized_to_top

This prevents candidates that did not meet the initializing criteria from being moved to the top. This is useful when working with hierarchical data that should not be moved. This defaults to 1.
  
=item pages

This is supplied as an array reference and each element specifies the following separated by colons:

=over 4

=item 1

The multi-part page number (p1-p6) to extract from the C<< <rsv> >> macros.

=item 2

The print-style for the page number.

=item 3

The prefix for the page number.

=back

This defaults to C<[qw( p4:an:{p4} )]> which uses the actual page number (I<p4>), displays it as an arabic numeral (I<an>), and prefixes it with a C< {p4} > tag (I<{p4}>). Thus, an entry on the first page would be followed by: C<{p4}1>.

When pages are specified their print-styles and prefixes default to "C<an>" and "C<{pX}>" respectively, where I<X> is the multi-part page number (1-6). Thus, C<[qw( p3 )]> is the same as C<[qw( p3:an:{p3} )]>.

What if you need a p3 that prints in uppercase letters followed by an arabic numeral p4 (A1, A2, ..., B1, etc.)? Use C<[qw( p3:ABC p4 )]> to get output like C<{p3}A{p4}1>.

=item strip_eb_ep

A boolean that determines if C<< <eb> >> and C<< <ep> >> macros (with or without arguments) are stripped from the file. This defaults to 1.

=item strip_keeps

A boolean that determines if keep macros are stripped from the file. This will remove the following macros (with or without arguments): C<< <ks> >>, C<< <ke> >>, C<< <vk> >>. This defaults to 1.

=item strip_pgrafs

A boolean that determines if pgrafs (unescaped percent signs) are stripped from the file. This defaults to 1.

=item tmp_dir

Allows the user to change the directory where temporary files are created. This defaults to C</tmp>.

=back

=item process

Executes the processes defined above.

=back

=head1 ERROR REPORTING

Because CITI's output runs together and is often verbose errors are made obvious as seen below:

=begin html

<img src="images/error.jpg" style="margin-left:1em;">

=end html

=head1 SORTING

=over 4

=item *

Use the "sort-a" CITI process to ignore accents during sorting.

=item *

For more information see "Sorting the Unicode Character Set" in the CITI manual and the L<Collation section of the ICU user guide|http://userguide.icu-project.org/collation>.

=back

=head1 EXAMPLES

=head2 Single-Level

=head3 Before

=begin html

<img src="images/single_default_before.jpg" style="margin-left:1em;">

=end html

=head3 After (with defaults)

  XPP::CITI::Automate->new->process;

=begin html

<img src="images/single_default_after.jpg" style="margin-left:1em;">

=end html

=head3 After (with initial lettering)
 
  XPP::CITI::Automate->new(
    initial_prefix => '{i}'
  )->process;
 
=begin html

<img src="images/single_default_after_initial.jpg" style="margin-left:1em;">

=end html

=head3 After (with custom initial letteringE<mdash>2 leading letters or digits)
 
  XPP::CITI::Automate->new(
    initial_prefix => '{i}',
    initial_re => '([\p{L}\p{N}]{2})',
  )->process;

=begin html

<img src="images/single_default_after_initial2.jpg" style="margin-left:1em;">

=end html

=head3 After (with initial lettering and modifiers to initial cap and group numerics)

  XPP::CITI::Automate->new(
    initial_prefix => '{i}',
    modifier => sub {
        my $final = shift;
        if ($final) {
            ### Group all numbers under "Numerics"
            s/^\{i\}\p{N}+\n/{i}Numerics/m;
            s/^\{i\}\p{N}+\n//gm;
        }
        else {
            ### Initial cap entries prior to initializing
            s/(?<=\{e\}\x1f)(\p{L})/uc $1/eg;
        }
    },
  )->process;


=begin html

<img src="images/single_default_after_num_mod.jpg" style="margin-left:1em;">

=end html

=head2 Single-Level using 2 mult-part page numbers (p3 and p4)

=head3 Before

=begin html

<img src="images/single_multi_pp_before.jpg" style="margin-left:1em;">

=end html

=head3 After (with a differently formatted p3 and initial lettering)

  XPP::CITI::Automate->new(
    pages => [qw(p3:ABC p4)],
    initial_prefix => '{i}',
  )->process;

=begin html

<img src="images/single_multi_pp_after_initial.jpg" style="margin-left:1em;">

=end html
  

=head2 Multi-Level

=head3 Before

=begin html

<img src="images/multi_default_before.jpg" style="margin-left:1em;">

=end html

=head3 After (with defaults)

  XPP::CITI::Automate->new->process;

=begin html

<img src="images/multi_default_after.jpg" style="margin-left:1em;">

=end html

=head3 After (with selective initial lettering)


  XPP::CITI::Automate->new(
    initial_prefix => '{i}',
    initial_candidates => ['{e l="1"}'],
    move_uninitialized_to_top => 0,
  )->process;

=begin html

<img src="images/multi_initial_after.jpg" style="margin-left:1em;">

=end html

=head1 HISTORY

This module supercedes C<XPP::CITI::Modify>. It includes a number of updates, design improvements (Moose), has increased flexibility, and it can handle multi-level extracts. This is not backward-compatible with C<XPP::CITI::Modify>.

=head1 AUTHOR

Chris Canipe <chris.canipe@gmail.com>

