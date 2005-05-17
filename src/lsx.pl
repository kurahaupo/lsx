#!/usr/bin/perl -w

use 5.006;
use warnings;
use strict;

use POSIX 'strftime', 'S_ISDIR';
use Getopt::Long;
use Fcntl ':mode';

my (    $all, $almost_all,
        $long_mode, $hide_owner, $hide_group,
        $with_flag, $in_columns,
        $use_colour, $colour_map, $colour_kinds, $colour_match,
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
        $show_mtime, $show_ctime, $show_atime, $full_time,
        $show_heading,
        $human_readable,
        $use_utc,
        $max_prec,
    );

$colour_map ||= do { my $e = $ENV{LS_COLORS}; $e ? [ split /:/, $e ] : () }
             || [ qw{
                   no=00 fi=00 di=01;34 ln=01;36 pi=40;33 so=01;35 do=01;35
                   bd=40;33;01 cd=40;33;01 or=40;31;01 ex=01;32
                   *.tar=01;31 *.tgz=01;31 *.arj=01;31 *.taz=01;31 *.lzh=01;31
                   *.zip=01;31 *.z=01;31 *.Z=01;31 *.gz=01;31 *.bz2=01;31
                   *.deb=01;31 *.rpm=01;31 *.jpg=01;35 *.png=01;35 *.gif=01;35
                   *.bmp=01;35 *.ppm=01;35 *.tga=01;35 *.xbm=01;35 *.xpm=01;35
                   *.tif=01;35 *.png=01;35 *.mpg=01;35 *.avi=01;35 *.fli=01;35
                   *.gl=01;35 *.dl=01;35
                 }];
$use_colour = 'never';
$max_prec = 1;

my $block_size = $ENV{POSIXLY_CORRECT} ? 512 : 1024;

sub format_date_heading($) {
    my ( $head ) = @_;
    $head .= ' (UTC)' if $use_utc;
    return sprintf $full_time ? "%-19s " : "%-12s ", $head;
}

sub format_date($) {
    my $time = shift;
    return strftime( +(
                        $full_time ? "%Y-%m-%d,%H:%M:%S " :
                        $time > $^T - 15552000  # less than six months old?
                            ? "%b %d %H:%M "
                            : "%b %d  %Y "
                       ),
                       $use_utc ? gmtime $time
                                : localtime $time
                     )
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

    #$line .= " " if $show_ctime || $show_mtime || $show_atime;

    $line .= format_date_heading "ctime" if $show_ctime;

    $line .= format_date_heading "mtime" if $show_mtime;

    $line .= format_date_heading "atime" if $show_atime;

    $line .= "name";

    $line .= "#" if $with_flag;

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
# LS_COLORS='no=00:fi=00:di=01;34:ln=01;36:pi=40;33:so=01;35:do=01;35:bd=40;33;01:cd=40;33;01:or=40;31;01:ex=01;32'
#
my @mchar = qw( ? p c ? d X b ? - ? l ? S ? ? ? );
my @mkind = qw( 0 pi cd 0 di X bd 0 no 0 ln 0 so 0 0 0 );
my @xchar = qw( 0 0 0 0 / 0 0 0 0 0 @ 0 = 0 0 0 );
my @zchar = qw( x t s ? s ? ? ? );
my @Zchar = qw( - T l ? S ? ? ? );

sub mode_flag($) {
    my $mode = $_[0];
    return ! defined $mode && "@?"
        || $xchar[$mode >> 12 & 15]
        || $mode & 0111 && "*"
        || "";
}

sub file_match($$) {
    my ( $name, $shell_pattern ) = @_;
    $shell_pattern =~ s/[\\.]/\\$&/go;
    $shell_pattern =~ s/\*/.*/go;
    $shell_pattern =~ s/\?/./go;
    return $name =~ $shell_pattern;
}

sub colourize($$) {
    my ( $name, $mode ) = @_;
    if ( ! $colour_kinds && ! $colour_match ) {
        for my $c ( @$colour_map ) {
            my ( $p, $x ) = split /=/, $c, 2;
            if ( $p =~ /[*?]/ ) {
                $colour_match->{$p} = $x;
            } else {
                $colour_kinds->{$p} = $x;
            }
        }
    }

    my $cx = "";
    MATCH: {
        for my $c ( keys %$colour_match ) {
            if ( file_match $name, $c ) {
                $cx = $colour_match->{$c};
                last MATCH;
            }
        }
        if ( my $cxx = $mkind[ $mode >> 12 ] ) {
            $cx = $colour_kinds->{$cxx};
            last MATCH;
        }
        $cx = $colour_kinds->{no};
    }
    $name = "\033[${cx}m$name\033[0m" if $cx;
    $name;
}

sub format_long($) {
    my $ref = $_[0];
    my $name = $ref->{name};
    my $file = $ref->{file} ||= $name;
    my $stat = $ref->{stat} ||= [ lstat $file ];

    @$stat or do {
        warn "Couldn't stat $file: $!\n";
        return
    };

    my ( $dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
        $atime,$mtime,$ctime,$blksize,$blocks ) = @$stat;

    my $line = "";

    $line .= sprintf "%8d ", $ino if $show_inum;

    $line .= human_format $blocks * 512 # $blksize
                                  / ( ! $human_readable && $block_size || 1 ), 4
        if $show_blocks;

    $line .= sprintf "%10.10s ",
                    join '',
                    $mchar[$mode >> 12],
                    map {
                        ( $_ & 0444 ? "r" : "-" ).
                        ( $_ & 0222 ? "w" : "-" ).
                        (( $_ & 0111 ? $zchar[ $_ >> 9 & 7 ]
                                     : $Zchar[ $_ >> 9 & 7 ] ) || "?" )
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
        $mtime >= $ctime or $line =~ s/ ?$/*/o;

        $line .= format_date $ctime if $show_ctime;

        $line .= format_date $mtime if $show_mtime;

        $line .= format_date $atime if $show_atime;
    }
    my $link_ptr = "";
    my $mode_flag = "";

    if ( S_ISLNK($mode) ) {
        my $link = $ref->{link} ||= readlink( $file ) || "<can't read link>";
        $mode = (stat $file)[2];
        $link_ptr = " -> $link";
    }

    $mode_flag = mode_flag $mode if $with_flag;
    $name = $file if $find_mode;

    my $length = length($line) + length($name) + length($link_ptr) + length($mode_flag);

    if ( $use_colour ) {
        $name = colourize $name, $mode;
    }

    $line .= $name;
    $line .= $link_ptr;
    $line .= $mode_flag;

    return ( $line, $length );
}

sub format_short_heading() {
    my $line = "name";

    $line = sprintf "%8s %s", "blocks", $line if $show_blocks;

    $line = sprintf "%8s %s", "inode", $line if $show_inum;

    $line .= "#" if $with_flag;

    return $line;
}

sub format_short($) {
    my $ref = $_[0];
    my $name = $ref->{name};

    my $file = $ref->{file} ||= $name;
    my $stat;

    my $line = $name;
    my $length = length $line;

    if ( $with_flag || $show_blocks || $show_inum || $use_colour ) {
        $stat = $ref->{stat} ||= [ lstat $file ];

        my ( $dev,$ino,$mode,$nlink,$uid,$gid,$rdev,$size,
            $atime,$mtime,$ctime,$blksize,$blocks ) = @$stat;

        my $start = "";
        my $end = "";

        $start .= sprintf "%8d ", $blocks if $show_blocks;

        $start .= sprintf "%8d ", $ino if $show_inum;

        $end .= mode_flag $mode if $with_flag;

        $line = colourize $line, $mode if $use_colour;

        $line = "$start$line$end";
        $length += length($start)+length($end);
    }

    return ( $line, $length );
}

sub get_dir($) {
    my $dir = $_[0];
    local *DIR;
    opendir DIR, $dir or die "Can't read $_[0]; $!\n";
    return readdir DIR;
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
    @l = sort { &$sort_by } @l if $sort_by;
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
                print( ( map {
                                ( $heading, " " x ( $col_widths[$_] + 2 - $heading_width) )
                            } 0 .. $cols - 2 ),
                       $heading, "\n" );
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

my %sorter_needs_stat = (
        atime => 1,
        ctime => 1,
        mtime => 1,
        mode  => 1,
    );

my ( $hide_time,
     $sort_by_time,
     $time_display,
     $unsorted,
     $use_atime,
     $use_ctime,
     $use_double_time,
     $use_triple_time,
    );

sub set_sort_by($) {
    $sorter_needs_stat = $sorter_needs_stat{$_[0]};
    $sort_by = $sorter{$_[0]} || die "No way to sort on $_[0]\n";
}

Getopt::Long::config(qw( no_ignore_case bundling require_order ));
GetOptions(
    '1'             => sub { $in_columns = 0 },
    '2'             => \$use_double_time,
    '3'             => \$use_triple_time,
    'A'             => \$almost_all,
    'C'             => \$in_columns,
    'F'             => \$with_flag,
    'H|si'          => sub { $human_readable = 1000 },
    'R'             => \$recurse,
    'S'             => sub { $sort_by = $sorter{size} },
    'U'             => \$unsorted,
    'a'             => \$all,
    'blocksize=i'   => \$block_size,
    'colour|color:s'=> \$use_colour,
    'c|use-ctime'   => \$use_ctime,
    'd'             => \$dont_expand,
    'find'          => \$find_mode,
    'full-time!'    => \$full_time,
    'g'             => \$hide_owner,
    'heading!'      => \$show_heading,
    'hide-all!'     => sub { $hide_time   = $hide_group  = $hide_mode   = $hide_nlinks = $hide_owner  = $hide_owner  = $hide_size   = $hide_time   = $_[1]; $long_mode = 1; },
    'hide-date!'    => \$hide_time,
    'hide-group!'   => \$hide_group,
    'hide-links!'   => \$hide_nlinks,
    'hide-mode!'    => \$hide_mode,
    'hide-num-links!' => \$hide_nlinks,
    'hide-owner!'   => \$hide_owner,
    'hide-size!'    => \$hide_size,
    'hide-time!'    => \$hide_time,
    'h|human-readable' => sub { $human_readable = 1024 },
    'i'             => \$show_inum,
    'l'             => \$long_mode,
    'localtime!'    => sub { $use_utc = ! $_[1] },
    'n'             => \$show_numeric,
    'o'             => \$hide_group,
    'q'             => \$show_qmark,
    'r'             => \$reverse,
    's'             => \$show_blocks,
    'short-time!'   => sub { $full_time = ! $_[1] },
    'show-all!'     => sub { $hide_time   = $hide_group  = $hide_mode   = $hide_nlinks = $hide_owner  = $hide_owner  = $hide_size   = $hide_time   = ! $_[1]; $long_mode = 1; },
    'show-atime!'   => \$show_atime,
    'show-ctime!'   => \$show_ctime,
    'show-date!'    => sub { $hide_time = ! $_[1] },
    'show-group!'   => sub { $hide_group = ! $_[1] },
    'show-mode!'    => sub { $hide_mode = ! $_[1] },
    'show-mtime!'   => \$show_mtime,
    'show-num-links!' => sub { $hide_nlinks = ! $_[1] },
    'show-owner!'   => sub { $hide_owner = ! $_[1] },
    'show-size!'    => sub { $hide_size = ! $_[1] },
    'show-time!'    => sub { $hide_time = ! $_[1] },
    'sort-by-time!' => \$sort_by_time,
    'sort-by=s'     => sub { set_sort_by $_[1] },
    't'             => \$sort_by_time,
    'unsorted'      => \$unsorted,
    'utc!'          => \$use_utc,
    'u|use-atime'   => \$use_atime,
    'max-precision=i' => \&max_prec,
    'help'          => sub { print <<EOF; exit 0 } ) or die "Try \"lsx --help\" for more information.\n";

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
    -l                  use classic "long-mode"

Options to control which timestamp fields are used and/or presented
    -c                  use ctime
    -u                  use atime

Options to control sorting
    --sort-by {atime,ctime,file,mode,mtime,name}
    --sort-by-time      sort_by_time
    -t                  sort_by_time
    -U                  unsorted
    --unsorted          unsorted

Options to control how information is formatted
    --short-time        display time(s) as month, day, and either time-of-day
                        (if within the last 180 days) or year (otherwise)
    --full-time         display time(s) as year, month, day, hour, minute & second
    --localtime         display time(s) relative to current locale (\$TZ)
    --utc               display time(s) relative to GMT

    --si|-H             display sizes using k, M, G, etc (powers of 1000)
    --human-readable|-h display sizes using Ki, Mi, Gi etc (powers of 1024)

Options to include specific information:
    --show-all
    --hide-all

    --show-{date,time}
    --hide-{date,time}
    --show-atime
    --show-ctime
    --show-mtime
    -2                  show ctime and mtime
    -3                  show atime, ctime and mtime

    --blocksize
    -g                  hide owner (only with "-l")
    -o                  hide group (only with "-l")

    --heading           show_heading
    --hide-group        hide_group
    --hide-links        hide_nlinks
    --hide-mode         hide_mode
    --hide-num-links    hide_nlinks
    --hide-owner        hide_owner
    --hide-size         hide_size
    -i                  show_inum
    -n                  show_numeric
    -q                  show_qmark
    -r                  reverse
    -s                  show_blocks
    --show-group        hide_group
    --show-mode         hide_mode
    --show-num-links    hide_nlinks
    --show-owner        hide_owner
    --show-size         hide_size
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

if ( !$hide_time && !$show_mtime && !$show_ctime && !$show_atime ) {
    if ( $use_double_time || $use_triple_time ) {
        $full_time = 1;
        $long_mode = 1;
        $show_atime = 1 if $use_triple_time;
        $show_ctime = 1;
        $show_mtime = 1;
        $sort_by = $sorter{ctime};
    } elsif ( $use_ctime ) {
        $show_ctime = 1;
    } elsif ( $use_atime ) {
        $show_atime = 1;
    } else {
        $show_mtime = 1;
    }
}

if ( $unsorted ) {
    $sort_by = undef;
} elsif ( !$sort_by ) {
    if ( !$sort_by_time ) {
        $sort_by = $sorter{name};
    } elsif ( $use_ctime ) {
        $sort_by = $sorter{ctime};
    } elsif ( $use_atime ) {
        $sort_by = $sorter{atime};
    } else {
        $sort_by = $sorter{mtime};
    }
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
                my @S = lstat $_->{file};
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
