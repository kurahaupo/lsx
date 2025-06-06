#!/usr/bin/perl

use 5.006;
use warnings;
use strict;

use Carp 'croak';
use Fcntl ':mode';
use Getopt::Long;
use POSIX qw(
                S_ISDIR
                S_ISREG
                floor
                log10
                strftime
            );

use FindBin qw(                  $RealBin  $Bin );
use lib map { "$_/../lib/perl" } $RealBin, $Bin, $ENV{HOME};

use Time::Nanosecond 'strftime', 'localtime', 'gmtime';
use Linux::Syscalls qw(
                :AT_
                :O_
                :timeres_
                fstatat
            );

use constant { TIMEFMT_SHORT => -1 };

use constant {
    INDICATOR_NONE      => 0,
    INDICATOR_SLASH     => 1,   # -p; only add
    INDICATOR_FILE_TYPE => 2,   # --file-type
    INDICATOR_CLASSIFY  => 3,   # -C --classify; same as --file-type but also with ‘*’ for executable plain files
};

my (    $all, $almost_all,
        $long_mode, $hide_owner, $hide_group,
        $indicator_style,
        $in_columns,
        $use_colour, $colour_map,
        $sorter_needs_stat,
        $sort_by, $reverse,
        $dont_expand, $find_mode, $recurse, $show_symlink,
        $show_numeric,
        $show_qmark,
        $show_inum,
        $show_blocks,
        $hide_mode,
        $hide_nlinks,
        $hide_size,
        $show_mtime, $show_ctime, $show_atime,
        $show_xattr, $show_selinux_security_context,
        $show_heading,
        $human_readable,
        $use_utc,
        $max_prec,
        $trace_symlink_paths,
        $dereference,
    );
my $debug_colourizer = 0;
my $link_loop_limit = 32;
my $time_precision = undef;

$colour_map ||= do { my $e = $ENV{LS_COLORS}; $e ? [ split /:/, $e ] : () }
             || [ qw{
                   no=0 fi=0 di=34;1 ln=36;1 pi=40;33 so=35;1 do=35;1 bd=40;33;1 cd=40;33;1
                   or=40;31;9 ex=32;1
                   ud=35;1
                   hl=7
                   *.tar=31;1  *.tgz=31;1  *.arj=31;1  *.taz=31;1  *.lzh=31;1
                   *.zip=31;1    *.z=31;1    *.Z=31;1   *.gz=31;1  *.bz2=31;1
                   *.deb=31;1  *.rpm=31;1  *.jpg=35;1  *.png=35;1  *.gif=35;1
                   *.bmp=35;1  *.ppm=35;1  *.tga=35;1  *.xbm=35;1  *.xpm=35;1
                   *.tif=35;1  *.png=35;1  *.mpg=35;1  *.avi=35;1  *.fli=35;1
                    *.gl=35;1   *.dl=35;1
                 }];
$use_colour = 'auto';
$max_prec = 1;

my $block_size = $ENV{POSIXLY_CORRECT} ? 512 : 1024;

sub format_date_heading($) {
    my ( $head ) = @_;
    $head .= ' (UTC)' if $use_utc;
    my $w = $time_precision == TIMEFMT_SHORT
                ? 12
                : 20 + $time_precision - !$time_precision + 6 * !$use_utc;
    #                                    no decimal point   «␠±hhmm»
    return sprintf "%-*s ", $w, $head;
}

sub format_date($) {
    my $time = shift;
    return strftime( $time_precision == TIMEFMT_SHORT
                        ? $time > $^T - 15552000
                            ? "%b %d %H:%M" # newer than six months
                            : "%b %d  %Y"   # older than six months
                        : $use_utc
                            ? "%F %T%.${time_precision}N"
                            : "%F %T%.${time_precision}N %z",
                     $use_utc ? gmtime $time
                              : localtime $time
                     ).' ';
}

sub format_long_heading() {
    my $line = "";

    $line .= sprintf "%8s ", "inode" if $show_inum;

    $line .= sprintf "%8s ", "blocks" if $show_blocks;

    $line .= sprintf "%-10s ", "mode" unless $hide_mode;

    $line .= sprintf "%4s ", "link" unless $hide_nlinks;

    $line .= sprintf "%-8s ", "user" unless $hide_owner;

    $line .= sprintf "%-8s ", "group" unless $hide_group;

    $line .= sprintf "%8s ", "size" unless $hide_size;

    $line .= format_date_heading "ctime" if $show_ctime;

    $line .= format_date_heading "mtime" if $show_mtime;

    $line .= ' ' if !$show_ctime != !$show_mtime;

    $line .= format_date_heading "atime" if $show_atime;

    $line .= "name";

    $line .= "#" if $indicator_style;

    return $line;
}

my @si_prefix = qw( 0 k M G T P );      # Metric
my @hr_prefix = qw( 0 Ki Mi Gi Ti Pi ); # 1024, 1048576 etc
my $l10 = log(10);

sub human_format($$) {
    my ( $val, $width ) = @_;
    return sprintf "%${width}s ", $val unless $human_readable && $val;

    my $hrp = $human_readable == 1000 ? \@si_prefix
                                      : \@hr_prefix;

    my $power = int(log(abs($val)) / log($human_readable));
    $power = $#$hrp if $power > $#$hrp;
    $val /= $human_readable ** $power;

    my $hr = $hrp->[$power] || '';      # use blank instead of 0

    $width -= length $hr;
    if ( $power > 0 && $max_prec > 0 ) {
        # using rounded value...
        my $p2 = int(log($val) / $l10); # digits to left of decimal point
        my $digits = $width - 1;        # space available for digits
        my $prec = $width - 1 - $p2;    # digits to right of decimal point
        $prec = $max_prec if $prec > $max_prec;
        while ( $prec > 0 ) {
            my $result = sprintf "%${width}.${prec}f", $val;
            if ( length($result) <= $width ) {
                return "$result$hr ";
            }
            # rounding increased the number of digits to the left of the
            # decimal point (eg: sprintf("%3.1f", 9.96) eq '10.0'), so try
            # again with fewer digits to the right
            --$prec;
        }
    }
    return sprintf "%${width}.0f$hr ", $val;
}

# smode & 0170000 => (smode >> 12 & 0x0f) =>
#   000: deleted
#   001: IFIFO
#   002: IFCHR
#   003:
#   004: IFDIR
#   005:
#   006: IFBLK
#   007:
#   010: IFREG
#   011:
#   012: IFLNK
#   013:
#   014: IFSOCK
#   015:
#   016:
#   017:

# LS_COLORS='no=0:fi=0:di=1;34:ln=1;36:pi=40;33:so=1;35:do=1;35:bd=40;33;1:cd=40;33;1:or=40;31;1:ex=1;32'
#
# where:
#  no=0         ⇒ 0        NOne (missing)
#  fi=0         ⇒ S_IFREG  regular FIle
#  di=34;1      ⇒ S_IFDIR  DIrectory
#  ln=36;1      ⇒ S_IFLNK  symLiNk
#  pi=40;33     ⇒ S_IFIFO  PIpe/fifo
#  so=35;1      ⇒ S_IFSOCK SOcket
#  do=35;1      ⇒ S_IFDOOR DOor (Solaris only)
#  bd=40;33;1   ⇒ S_IFBLK  Block Device (hd)
#  cd=40;33;1   ⇒ S_IFCHR  Char Device (tty)
#
#  or=40;31;1   ⇒ "ORphan" (dangling) symlink, encoded as 16
#  ex=32;1      ⇒ EXecutable
#  ud=35;1      # Unscannable Directory
#
#  hl=7         # Heading Line (inverse video)

my @mchar = qw( ? p c ? d X b ? - ? l ? S ? ? ? );
my @mkind = qw( 0 pi cd 0 di X bd 0 no 0 ln 0 so 0 0 0 or );
my @xchar = qw( 0 0 0 0 / 0 0 0 0 0 @ 0 = 0 0 0 );
my @zchar = qw( x t s ? s ? ? ? );
my @Zchar = qw( - T l ? S ? ? ? );

sub indicator($) {
    if (! $indicator_style) { return '' }
    my ($mode) = $_[0];
    if ($indicator_style == INDICATOR_SLASH) {
        return S_ISDIR($mode) ? '/' : ''
    }
    return ! defined $mode && '?'
        || $xchar[$mode >> 12 & 15]
        || $mode & 0111 && $indicator_style == INDICATOR_CLASSIFY && '*'
        || '';
}

sub file_match($$) {
    my ( $name, $shell_pattern ) = @_;
    $shell_pattern =~ s/[\\.]/\\$&/go;
    $shell_pattern =~ s/\*/.*/go;
    $shell_pattern =~ s/\?/./go;
    return $name =~ $shell_pattern;
}

{
my $colour_kinds;
my ($colour_match_glob,   $colour_match_glob_re,
    $colour_match_suffix, $colour_match_suffix_re,
    $colour_match_prefix, $colour_match_prefix_re);

sub colour_init() {
    $colour_map || return;

    # Translate C<$colour_map> string to 'kind' and 'regex' and 'glob'
    # maps, and then remove the C<$colour_map> string so that this only
    # happens once.
    for my $c ( @$colour_map ) {
        my ( $p, $x ) = split /=/, $c, 2;
        if ( $p =~ m{ ^\*\*\w+$ }x ) {
            # Allow extensions to be encoded with a leading '**' to avoid
            # complaints from 'normal' ls.
            $colour_kinds->{substr $p, 2} = $x;
        }
        elsif ( $p =~ m{ ^\*$
                       | .\*.
                       | \?
                       }x ) {
            # If pattern consists *entirely* of '*', or has '?' anywhere,
            # or has '*' that's neither initial nor final, then treat this
            # as a full glob, which means we need to scan it to find the
            # match.
            $colour_match_glob->{$p} = $x;
        }
        elsif ( $p =~ /^\*/ ) {
            # If it starts with '*' (and contains no other wildcard chars)
            # then treat as a suffix match
            $colour_match_suffix->{$'} = $x;
        }
        elsif ( $p =~ /\*$/ ) {
            # If it ends with '*' (and contains no other wildcard chars)
            # then treat as a prefix match
            $colour_match_prefix->{$`} = $x;
        } else {
            $colour_kinds->{$p} = $x;
        }
    }
    undef $colour_map;  # only create map once or if changed
    for my $cx ( [ \$colour_match_suffix, \$colour_match_suffix_re, '^', '' ],
                 [ \$colour_match_prefix, \$colour_match_prefix_re, '', '$' ] ) {
        my ($mr, $rr, $s, $e) = @$cx;
        $$mr || next;
        my @k = sort { length($b) <=> length($a) } keys %$$mr;
        my $q = join '|', map { quotemeta $_ } @k;
        $q = "$s($q)$e";
        $q = qr/$q/;
        $$rr = $q;
    }
    if ($colour_match_glob) {
        my @k = sort { length($b) <=> length($a) } keys %$colour_match_glob;
        my $q = join '|',
                    map {
                        s{
                            [*?\\.^\[\]\$]
                        }{
                            $& eq '*' ? '.*' :
                            $& eq '?' ? '.'  :
                            '\\'.$&
                        }egrx
                    } @k;
        $q = "^($q)\$";
        $colour_match_glob_re = qr/$q/;
    }
}

sub colourize_heading($) {
    my ( $line ) = @_;
    return $line unless $use_colour;
    colour_init;
    my $cx = $colour_kinds->{hl} // '7;33';	# Use inverse if unspecified

    printf STDERR "Colourizing header cx=[%s] [%s]\n", $cx || '(none)', $line if $debug_colourizer;

    $line = "\033[${cx}m$line\033[0m" if $cx;
    return $line;
}

sub colourize_name($$) {
    my ( $name, $mode ) = @_;
    return $name unless $use_colour;
    colour_init;
    printf STDERR "Match Glob=%s\n", $colour_match_glob_re // '(undef)' if $debug_colourizer;
    my $cx = "";
    MATCH: {
        if ( $colour_match_suffix_re && $name =~ $colour_match_suffix_re ) {
            $cx = $colour_match_suffix->{$&};
            printf STDERR "Colourizing %s -> suffix %s -> %s\n", $name, $&, $cx if $debug_colourizer;
            last MATCH;
        }
        if ( $colour_match_prefix_re && $name =~ $colour_match_prefix_re ) {
            $cx = $colour_match_prefix->{$&};
            printf STDERR "Colourizing %s -> prefix %s -> %s\n", $name, $&, $cx if $debug_colourizer;
            last MATCH;
        }
        if ($colour_match_glob_re && $name =~ $$colour_match_glob_re) {
            for my $c ( keys %$colour_match_glob ) {
                if ( file_match $name, $c ) {
                    $cx = $colour_match_glob->{$c};
                    printf STDERR "Colourizing %s -> glob %s -> %s\n", $name, $&, $cx if $debug_colourizer;
                    last MATCH;
                }
            }
            printf STDERR "Colourizing %s -> glob %s -> %s\n", $name, $&, $cx if $debug_colourizer;
        }
        if ( S_ISDIR($mode) && !( $mode & 0111 ) ) {
            # Unscannable directory
            $cx = $colour_kinds->{ud} and
            last MATCH;
            # Fall back to "normal" directory
        }
        if ( my $cxx = $mkind[ $mode >> 12 || 16 ] ) {
            $cx = $colour_kinds->{$cxx};
            printf STDERR "Colourizing %s -> mkind %s -> %s\n", $name, $cxx, $cx // '(undef)' if $debug_colourizer;
            $cx //= '';
            last MATCH;
        }
        if ( S_ISREG($mode) && $mode & 0111 ) {
            # Executable
            $cx = $colour_kinds->{ex};
            last MATCH;
        }
        $cx = $colour_kinds->{no};
    }
    $name = "\033[${cx}m$name\033[0m" if $cx;
    return $name;
}
}

sub append_path(\$$) {
    my ($t,$x) = @_;
    $x =~ m</> and croak "'/' not allowed";
    return if $x eq '.';
    if ( $x eq '..' && $$t !~ m<(?:^|/)\.\./$> ) {
        return if $$t eq '/';
        $$t =~ s</?[^/]+$><>;
        return;
    }
    $$t .= "/" if $$t ne "" && $$t !~ m</$>;
    $$t .= $x;
}

sub trace_symlinks($$$);
sub trace_symlinks($$$) {
    my ($prefix, $path, $limit) = @_;
    $path =~ s<//+></>g;
    #1 while $path =~ s</\./></>g;
    #$path =~ s<^\./><>;
    return $prefix if $path eq '';

    my $result = "";
    $path =~ s<^/><> and $result = $prefix = "/";

    my @parts = split m</>, $path;
    PARTS: while (@parts) {
        my $part = shift @parts;
        my $newpref = "$prefix$part";

        if ( $part ne '.' && $part ne '..' and my $l = readlink $newpref ) {
            $limit && --$limit or do {
                $result .= "$part -> [...]";
                last PARTS;
            };
            $l = trace_symlinks($prefix, $l, $limit);
            $part .= " -> $l";
            $part = "[$part]" if @parts;
        }
        $result .= $part;

        $result .= "/" if @parts;
        $prefix = $newpref;
        $prefix .= "/" if @parts;
    }
    return $result;
}

sub format_long($) {
    my $ref = $_[0];
    my $name = $ref->{name};
    my $file = $ref->{file} ||= $name;
    my $stat = $ref->{stat} ||= fstatat undef, $file, $dereference ? undef : AT_SYMLINK_NOFOLLOW;

    @$stat or do {
        warn "Couldn't stat $file: $!\n";
        return
    };

    my ( $dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
        $atime,$mtime,$ctime,$blksize,$blocks ) = @$stat;

    my $line = "";

    $line .= sprintf "%8d ", $ino if $show_inum;

    my $block_unit = 512;
    $line .= sprintf "%8s ",
                     human_format $blocks * ( ! $human_readable && $block_unit / $block_size || 1 ),
                                  4
        if $show_blocks;

    $line .= sprintf "%10.10s ",
                    join '',
                    $mchar[$mode >> 12],
                    map {
                        ( $_ & 0444 ? "r" : "-" ).
                        ( $_ & 0222 ? "w" : "-" ).
                        (( $_ & 0111 ? $zchar[ $_ >> 9 ]
                                     : $Zchar[ $_ >> 9 ] ) || "?" )
                    } $mode & 04700, $mode & 02070, $mode & 01007
        unless $hide_mode;

    $line .= human_format $nlink, 4
        unless $hide_nlinks;

    $line .= sprintf "%-8s ", ! $show_numeric && getpwuid( $uid ) || $uid
        unless $hide_owner;

    $line .= sprintf "%-8s ", ! $show_numeric && getgrgid( $gid ) || $gid
        unless $hide_group;

    $line .= human_format $size, 8
        unless $hide_size;

    if ( $show_ctime || $show_mtime || $show_atime ) {
        if ($show_ctime) {
            $line .= format_date $ctime;
            if ($show_mtime) {
                # Show both
                $line .= format_date $mtime;
            } else {
                $line =~ s/ $//;
                $line .= $ctime <= $mtime ? '  ' : '> ';
            }
        }
        elsif ($show_mtime) {
            $line .= format_date $mtime;
            $line =~ s/ $//;
            $line .= $ctime <= $mtime ? '  ' : '< ';
        }

        $line =~ s/ ([<>] )$/$1/;

        $line .= format_date $atime if $show_atime;
    }

    my $link_ptr = "";

    if ( $trace_symlink_paths ) {
        $name = trace_symlinks "", $name, $link_loop_limit;
    } elsif ( S_ISLNK($mode) ) {
        my $link = $ref->{link} ||= readlink( $file ) || "<can't read link>";
        $mode = (stat $file)[2];
        $link_ptr = " -> $link";
    }

    my $indicator = "";
    $indicator = indicator $mode if $indicator_style;
    $name = $file if $find_mode;

    my $length = length($line) + length($name) + length($link_ptr) + length($indicator);

    $name = colourize_name $name, $mode if $use_colour;

    $line .= $name;
    $line .= $link_ptr;
    $line .= $indicator;

    return ( $line, $length );
}

sub format_short_heading() {
    my $line = "name";

    $line = sprintf "%8s %s", "blocks", $line if $show_blocks;

    $line = sprintf "%8s %s", "inode", $line if $show_inum;

    $line .= '#' if $indicator_style;

    return $line;
}

sub format_short($) {
    my $ref = $_[0];
    my $name = $ref->{name};

    my $file = $ref->{file} ||= $name;
    my $stat;

    my $line = $name;
    my $length = length $line;

    if ( $indicator_style || $show_blocks || $show_inum || $use_colour ) {
        $stat = $ref->{stat} ||= fstatat undef, $file, $dereference ? undef : AT_SYMLINK_NOFOLLOW;

        my ( $dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
            $atime,$mtime,$ctime,$blksize,$blocks ) = @$stat;

        my $start = "";
        my $end = "";

        $start .= sprintf "%8d ", $blocks if $show_blocks;

        $start .= sprintf "%8d ", $ino if $show_inum;

        $end .= indicator $mode if $indicator_style;

        $line = colourize_name $line, $mode if $use_colour;

        $line = "$start$line$end";
        $length += length($start)+length($end);
    }

    return ( $line, $length );
}

sub get_dir($) {
    my $dir = $_[0];
    opendir my $dh, $dir or die "Can't read $_[0]; $!\n";
    return readdir $dh;
}

sub load_dir($) {
    my $dir = $_[0];
    $dir = $dir->{file} if ref $dir;
    return map { +{ name => $_, file => "$dir/$_" } }
            grep { $all
                  || $almost_all && $_ ne '.' && $_ ne '..'
                  || ! m/^\./o
                }
            get_dir $dir;
}

sub max(@) { my $r = shift; for(@_){ $r = $_ if $_ > $r } return $r }
sub min(@) { my $r = shift; for(@_){ $r = $_ if $_ < $r } return $r }
sub sum(@) { my $r = shift; for(@_){ $r += $_ } return $r }

my $tc = 0;

sub ls_list(@) {
    my @l = @_;
    my $heading;
    if ( $long_mode ) {
        $heading = format_long_heading if $show_heading;
        for (@l) { ( $_->{fmt}, $_->{fmt_width} ) = format_long $_ }
    } else {
        $heading = format_short_heading if $show_heading;
        for (@l) { ( $_->{fmt}, $_->{fmt_width} ) = format_short $_ }
    }
    $show_heading = 0 if $find_mode;  # Only print heading first time
    @l = grep { $_->{fmt} } @l;
    @l or return;
    @l = sort $sort_by @l if $sort_by;
    @l = reverse @l if $reverse;
    if ( $show_qmark ) { for (@l) { $_->{name} =~ s/[^ -~]/?/go } }

    if ( $in_columns ) {
        use integer;
        $tc ||= $ENV{COLUMNS}
            || do {
                    my $S = qx{ exec /bin/stty size };
                    my @S = split /\s+/,$S;
                    $S[1];
                }
            || 80;

        my $heading_width = length($heading||"");

        $heading = colourize_heading $heading if $use_colour;

        my $mean_width = ( sum map { max $heading_width, $_->{fmt_width} } @l )
                         / scalar(@l)
                         || 1;

        WIDTH: for my $cols ( reverse 2 .. $tc / $mean_width  ) {
            my $rows = (@l-1)/$cols+1;
            my @col_widths =   map {
                                    my $col = $_;
                                    my $cp = $col * $rows;
                                    max $heading_width, map { $l[$_]->{fmt_width} } $cp .. min $#l, $cp+$rows-1;
                                } 0 .. $cols-1;
            my $need_width = ($cols - 1)*2 + sum @col_widths;

            next WIDTH unless $need_width <= $tc;

            if ( $heading ) {
                my $h2 = $heading . (' ' x ( $col_widths[$_] + 2 - $heading_width));
                print $h2 x ($cols - 1), $heading, "\n";
            }

            for my $r ( 0 .. $rows-1 ) {
                for my $c ( 0 .. $cols - 1 ) {
                    my $i = $r+$c*$rows;
                    my $z = $l[$i] || die "Shouldn't get here";
                    if ( $i > $#l - $rows ) {
                        print $z->{fmt}, "\n";
                        last;
                    } else {
                        print $z->{fmt}, " " x ( $col_widths[$c] + 2 - $z->{fmt_width} );
                    }
                }
            }
            return;
        }
    }

    # If we either didn't ask for columns, or can't fit into columns, then use
    # single-column mode.

    if ( $heading ) {
        $heading = colourize_heading $heading if $use_colour;

        print $heading, "\n";
    }
    for (@l) {
        print $_->{fmt}, "\n";
    }
}

#
# Options which need manipulation to be useful
#

my %sorter = (
        file  => sub { $a->{file}       cmp $b->{file}       },
        name  => sub { $a->{name}       cmp $b->{name}       },
        mode  => sub { $b->{stat}->[2]  <=> $a->{stat}->[2]  },
        mtime => sub { $b->{stat}->[9]  <=> $a->{stat}->[9]  },
        ctime => sub { $b->{stat}->[10] <=> $a->{stat}->[10] },
        atime => sub { $b->{stat}->[8]  <=> $a->{stat}->[8]  },
        size  => sub { $b->{stat}->[7]  <=> $a->{stat}->[7]  },
    );
$sorter{perms} = $sorter{mode};

my %sorter_needs_stat = (
        atime => 1,
        ctime => 1,
        mtime => 1,
        time  => 1,
        mode  => 1,
        perms => 1,
    );

my ( $hide_time,
     $time_display,
     $use_time,
     $use_double_time,
     $use_triple_time,
    );

sub set_sort_by($) {
    my $k = $_[-1];
    if ($k eq 'none' || $k eq 'raw') {
        $sorter_needs_stat = 0;
        $sort_by = undef;
    } elsif ($k eq 'time') {
        $sort_by = $k;
    } else {
        $sorter_needs_stat = $sorter_needs_stat{$k};
        $sort_by = $sorter{$k} || die "No way to sort on '$k'\n";
    }
}

# Default sorting order...
set_sort_by 'name';

sub set_show_all($$) {
    $hide_time =
    $hide_group =
    $hide_mode =
    $hide_nlinks =
    $hide_owner =
    $hide_owner =
    $hide_size =
    $hide_time = ! $_[1];
    $show_xattr =
    $show_selinux_security_context = $_[1];
    $long_mode = 1;
}

sub set_time_res {
    my $res = pop @_;

    if (! defined $res) {
        $time_precision = TIMEFMT_SHORT;
        return;
    }

    $res = TIMERES_NANOSECOND if $res eq '';  # different from literal '0'

    # Accepts number of digits
    if ( $res =~ /^\d+$/ && $res <= 9 ) { $time_precision = $res; return }

    # Accepts decimal fraction indicating precision
    if ( $res =~ /^0\.\d+$/ ) { $time_precision = -floor(log10($res)); return }

    use feature 'state';

    state $resmap = {

        'brief'         => TIMEFMT_SHORT,       'short' => TIMEFMT_SHORT,
        'full'          => TIMERES_NANOSECOND,

        'none'          => TIMERES_SECOND,      'no'    => TIMERES_SECOND,
        ''              => TIMERES_SECOND,      '-'     => TIMERES_SECOND,

        'seconds'       => TIMERES_SECOND,      's'     => TIMERES_SECOND,
        'deciseconds'   => TIMERES_DECISECOND,  'ds'    => TIMERES_DECISECOND,
        'centiseconds'  => TIMERES_CENTISECOND, 'cs'    => TIMERES_CENTISECOND,
        'milliseconds'  => TIMERES_MILLISECOND, 'ms'    => TIMERES_MILLISECOND,
        'microseconds'  => TIMERES_MICROSECOND, 'us'    => TIMERES_MICROSECOND,
                                                'µs'    => TIMERES_MICROSECOND,
                                                'μs'    => TIMERES_MICROSECOND,
        'nanoseconds'   => TIMERES_NANOSECOND,  'ns'    => TIMERES_NANOSECOND,
#       'picoseconds'   => TIMERES_PICOSECOND,  'ps'    => TIMERES_PICOSECOND,

    };

    for ( $res, $res =~ s/s(e(c(o(nd?)?)?s?)?)?$/seconds/r, $res.'s' ) {
        $time_precision = $resmap->{$_} // next;
        return
    }
    die "Invalid time resolution $res\n";
}

{
my %indicator_names = (
    classify    => INDICATOR_CLASSIFY,  # -C --classify
    file_type   => INDICATOR_FILE_TYPE, # --file-type
    'file-type' => INDICATOR_FILE_TYPE, # --file-type
    none        => INDICATOR_NONE,
    slash       => INDICATOR_SLASH,
    slash       => INDICATOR_SLASH,     # -p
);
sub indicator_n2i {
    my $name = pop;
    return $indicator_names{$name} // die "Invalid indicator type ‘$name’\n";
}
}

sub N($) { my $r = \$_[0]; $$r && ref $$r eq 'CODE' ? sub { $_[-1] = !$_[-1]; goto &$$r } : sub { $$r = !$_[-1] } }
sub S($$) { my $r = \$_[0]; my $v = $_[1]; sub { $$r = $v } }
Getopt::Long::config(qw( no_ignore_case bundling require_order ));
GetOptions
    '1'             => S($in_columns, 0),
    '2'             => \$use_double_time,
    '3'             => \$use_triple_time,
    'A'             => \$almost_all,
    'C'             => \$in_columns,
    'E'             => \$show_xattr,
    'F|classify'    => S($indicator_style, INDICATOR_CLASSIFY),
    'H|si'          => S($human_readable, 1000),
    'L|dereference' => \$dereference,
    'R|recurse'     => \$recurse,
    'S'             => sub { set_sort_by 'size' },
    'T'             => sub { print "Usage error: -T TABSIZE is unsupported, and '--trace' is now '-e'\n"; exit 64 },
    'U|unsorted|no-sort|no-sort-by|sort-by-none|sort-by-raw'
                    => sub { set_sort_by 'none' },
    'Z'             => \$show_selinux_security_context,
    'a'             => \$all,
    'blocksize=i'   => \$block_size,
    'colour|color:s'=> \$use_colour,
    'c|use-ctime'   => S($use_time,'ctime'),
    'd'             => \$dont_expand,
    'debug!'        => \$debug_colourizer,
    'e|trace'       => \$trace_symlink_paths,
    'find'          => \$find_mode,
    'full-time'     => S($time_precision, TIMERES_NANOSECOND),
    'time-precision=s'
                    => \&set_time_res,
 'no-full-time|short-time|brief-time'
                    => S($time_precision, -1),
    'heading!'      => \$show_heading,
    'hide-all!'     => N \&set_show_all,
    'hide-blocks!'  => N$show_blocks,
    'hide-date!'    => \$hide_time,
    'o|hide-group!' => \$hide_group,
    'hide-inode!'   => N$show_inum,
    'hide-mode!'    => \$hide_mode,
    'hide-num-links!'
                    => \$hide_nlinks,
    'g|hide-owner!' => \$hide_owner,
    'hide-size!'    => \$hide_size,
    'hide-time!'    => \$hide_time,
    'h|human-readable'
                    => S($human_readable, 1024),
    'i|inode|show-inode'
                    => \$show_inum,
    'indicator-style=s'
                    => \&indicator_n2i,
 'no-indicator'     => S($indicator_style, INDICATOR_NONE),
    'l|long-mode'   => \$long_mode,
    'localtime!'    => N$use_utc,
    'max-precision=i'
                    => \&max_prec,
    'n'             => \$show_numeric,
    'file-type'     => S($indicator_style, INDICATOR_FILE_TYPE),
    'p'             => S($indicator_style, INDICATOR_SLASH),
    'q'             => \$show_qmark,
    'r'             => \$reverse,
    'show-all!'     => \&set_show_all,
    'show-atime!'   => \$show_atime,
    'show-context|context!'
                    => \$show_selinux_security_context,
    'show-ctime!'   => \$show_ctime,
    'show-date!'    => N$hide_time,
    'show-group!'   => N$hide_group,
    'show-mode!'    => N$hide_mode,
    'show-mtime!'   => \$show_mtime,
    'show-num-links!'
                    => N$hide_nlinks,
    'show-owner!'   => N$hide_owner,
    'show-size!'    => N$hide_size,
    'show-time!'    => N$hide_time,
    'show-xattr!'   => \$show_xattr,
    'sort-by-time!' => sub { set_sort_by( $_[-1] ? 'time' : 'none' ) },
    'sort-by=s'     => \&set_sort_by,
    's|show-blocks' => \$show_blocks,
    't'             => sub { set_sort_by 'time' },
    'utc!'          => \$use_utc,
    'u|use-atime'   => S($use_time,'atime'),
    (map { my $x = $_;
    "sort-by-$x"    => sub { set_sort_by $x } } keys %sorter),
   #'sort-by-name'  => sub { set_sort_by 'name' },
    'help'          => sub { print <<EOF; exit 0 } or die "Try \"lsx --help\" for more information.\n";

$0 [options]... [files]...

Options to select files:
    -A                  all except "." and ".."
    -R                  recurse
    -a                  all
    -d                  don't expand directories
    --find              work like "find -ls"

Options to select layout:
    -1                  single-column
    -C                  multi-column
    -F                  put symbol after filename to denote type
    --colo[u]r          change colour depending on filetype
    -l --long-mode      use classic "long mode"
    -L --derefence      show info about what symlink point to rather than itself
    -e --trace          show part-by-part redirection of symlinks (only with -l)

Options to control which timestamp fields are used and/or presented
    -c                  show ctime rather than mtime in "long mode"
    -u                  show atime rather than mtime in "long mode"

Options to control sorting
    --sort-by {atime,ctime,file,mode,mtime,name}
    -t, --sort-by-time  sort by whichever time field is displayed in long mode
    -U, --unsorted      display in order returned by filesystem

Options to control how information is formatted
    --short-time        display time(s) as month, day, and either time-of-day
                        (if within the last 180 days) or year (otherwise)
    --full-time[=PREC]  display time(s) as year, month, day, hour, minute & second
                        display fractional seconds to PREC-digit precision
    --localtime         display time(s) relative to current locale (\$TZ)
    --utc               display time(s) relative to GMT

    --si|-H             display sizes using k, M, G, etc (powers of 1000)
    --human-readable|-h display sizes using Ki, Mi, Gi etc (powers of 1024)

Options to include specific information:
    --show-all
    --hide-all

    --show-atime
    --show-ctime
    --show-mtime
    -2                  show ctime and mtime (imples "-l")
    -3                  show atime, ctime and mtime (imples "-l")

    --blocksize
    -g                  hide owner (only with "-l")
    -o                  hide group (only with "-l")

    --heading           show_heading
    --{show,hide}-{date,time}
    --{hide,show}-group
    --{hide,show}-inode
    --{hide,show}-mode
    --{hide,show}-num-links
    --{hide,show}-owner
    --{hide,show}-size
    -i                  --show-inode
    -n                  show_numeric
    -q                  show_qmark
    -r                  reverse
    -s                  show_blocks
EOF

#
# Patch up for root usage
#

$almost_all = 1 if ! $< || ! $>;

#
# Patch up for colour usage
#

$use_colour = {qw{
                    al 1 alw 1 alwa 1 alway 1 always 1
                    n 0 no 0 ne 0 nev 0 neve 0 never 0
                    y 1 ye 1 yes 1
               }}->{$use_colour || 'never'};

$use_colour = -t STDOUT if ! defined $use_colour;

#
# Convert short options to equivalent long option bundles
# (Short options use the same flags to control both the selection of time
# field to display, and the selection of field to sort by.)
#

$long_mode ||= $hide_owner;
$long_mode ||= $hide_group;
$use_time  ||= 'mtime';

if ( !$hide_time && !$show_mtime && !$show_ctime && !$show_atime ) {
    if ( $use_double_time || $use_triple_time ) {
        $time_precision //= TIMERES_NANOSECOND;
        $long_mode = 1;
        $show_atime = 1 if $use_triple_time;
        $show_ctime = 1;
        $show_mtime = 1;
        $sort_by = $sorter{ctime} if $sort_by eq 'time';
    } elsif ( $use_time eq 'ctime' ) {
        $show_ctime = 1;
    } elsif ( $use_time eq 'atime' ) {
        $show_atime = 1;
    } else {
        $show_mtime = 1;
    }
}

$time_precision //= -1;
$time_precision >= -1 && $time_precision <= TIMERES_NANOSECOND
    or die "Time precision $time_precision not supported\n";

#
# Options '-c' and '-u' change '-t' from meaning "sort by mtime" into "sort by
# ctime" and "sort by atime" respectively.
#

if ( ! ref $sort_by && $sort_by eq 'time' ) {
    $sort_by = $sorter{$use_time};
    $sorter_needs_stat = 1;
}

$recurse ||= $find_mode;

my $errs;

if ( ! @ARGV && ! $dont_expand && ! $recurse ) {
    ls_list load_dir ".";
} else {
    @ARGV = "." unless @ARGV;
    my @X = map { { name => $_ } } @ARGV;
    if ( $dont_expand ) {
        ls_list @X;
    } else {
        my $ls;
        $ls = sub {
            my $lim = shift;
            my (@F, @D);
            for ( @_ ) {
                $_->{file} ||= $_->{name};
                my @S = fstatat undef, $_->{file}, AT_SYMLINK_NOFOLLOW;
                @S or do { warn "$_->{file}: $!\n"; ++$errs; next };
                $_->{stat} = \@S;
                if ( S_ISDIR($S[2]) && $lim ) {
                    push @D, $_ if ! $recurse || $_ ne '.' && $_ ne '..';
                    push @F, $_ if $recurse;
                } else {
                    push @F, $_
                }
            }
            ls_list @F;
            for my $d (@D) {
                print "$d->{file}:\n" unless $find_mode;
                my @X = eval { load_dir $d };
                $ls->( $recurse, @X ) if @X;
            }
        };
        $ls->(1,@X);
    }
}

exit !! $errs;
