#!/usr/bin/perl

use 5.006;
use warnings;
use strict;

use Carp 'croak';
use POSIX 'strftime', 'S_ISDIR';
use Getopt::Long;
use Fcntl ':mode';

use lib $ENV{HOME}.'/lib/perl';
use Linux::Syscalls 'lstat', ':o_';

my (    $all, $almost_all,
        $long_mode, $hide_owner, $hide_group,
        $with_flag, $in_columns,
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
        $show_mtime, $show_ctime, $show_atime, $full_time,
        $show_xattr, $show_selinux_security_context,
        $show_heading,
        $human_readable,
        $use_utc,
        $max_prec,
        $trace_symlink_paths,
        $dereference,
    );
my $link_loop_limit = 32;

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
$use_colour = 'auto';
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
my @mkind = qw( 0 pi cd 0 di X bd 0 no 0 ln 0 so 0 0 0 or );
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

{
my $colour_kinds;
my $colour_match;
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
        if ( my $cxx = $mkind[ $mode >> 12 || 16 ] ) {
            $cx = $colour_kinds->{$cxx};
            last MATCH;
        }
        $cx = $colour_kinds->{no};
    }
    $name = "\033[${cx}m$name\033[0m" if $cx;
    $name;
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
    my $stat = $ref->{stat} ||= [ $dereference ? stat $file : lstat $file ];

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
        $mtime >= $ctime or $line =~ s/ ?$/*/o;

        $line .= format_date $ctime if $show_ctime;

        $line .= format_date $mtime if $show_mtime;

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

    my $mode_flag = "";
    $mode_flag = mode_flag $mode if $with_flag;
    $name = $file if $find_mode;

    my $length = length($line) + length($name) + length($link_ptr) + length($mode_flag);

    $name = colourize $name, $mode if $use_colour;

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
        $stat = $ref->{stat} ||= [ $dereference ? stat $file : lstat $file ];

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
$sorter{perms} = $sorter{mode};

my %sorter_needs_stat = (
        atime => 1,
        ctime => 1,
        mtime => 1,
        mode  => 1,
        perms => 1,
    );

my ( $hide_time,
     $sort_by_time,
     $time_display,
     $use_time,
     $use_double_time,
     $use_triple_time,
    );

sub set_sort_by($) {
    my $k = $_[-1];
    if ($k eq 'none') {
        $sort_by_time = 0;
        $sorter_needs_stat = 0;
        $sort_by = undef;
    } elsif ($k eq 'time') {
        $sort_by_time = 1;
        $sorter_needs_stat = 0;
        $sort_by = undef;
    } else {
        $sort_by_time = 0;
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
    'F'             => \$with_flag,
    'H|si'          => S($human_readable, 1000),
    'L|dereference' => \$dereference,
    'R|recurse'     => \$recurse,
    'S'             => sub { set_sort_by 'size' },
    'T'             => sub { print "Usage error: -T TABSIZE is unsupported, and '--trace' is now '-e'\n"; exit 64 },
    'U|unsorted|no-sort-by' => sub { set_sort_by 'none' },
    'Z'             => \$show_selinux_security_context,
    'a'             => \$all,
    'blocksize=i'   => \$block_size,
    'colour|color:s'=> \$use_colour,
    'c|use-ctime'   => S($use_time,'ctime'),
    'd'             => \$dont_expand,
    'e|trace'       => \$trace_symlink_paths,
    'find'          => \$find_mode,
    'full-time!'    => \$full_time,
    'g'             => \$hide_owner,
    'heading!'      => \$show_heading,
    'hide-all!'     => N \&set_show_all,
    'hide-blocks!'  => N$show_blocks,
    'hide-date!'    => \$hide_time,
    'hide-group!'   => \$hide_group,
    'hide-inode!'   => N$show_inum,
    'hide-mode!'    => \$hide_mode,
    'hide-num-links!' => \$hide_nlinks,
    'hide-owner!'   => \$hide_owner,
    'hide-size!'    => \$hide_size,
    'hide-time!'    => \$hide_time,
    'h|human-readable' => sub { $human_readable = 1024 },
    'i|show-inode'  => \$show_inum,
    'l|long-mode'   => \$long_mode,
    'localtime!'    => N$use_utc,
    'max-precision=i' => \&max_prec,
    'n'             => \$show_numeric,
    'o'             => \$hide_group,
    'q'             => \$show_qmark,
    'r'             => \$reverse,
    'short-time!'   => N$full_time,
    'show-all!'     => \&set_show_all,
    'show-atime!'   => \$show_atime,
    'show-context|context!' => \$show_selinux_security_context,
    'show-ctime!'   => \$show_ctime,
    'show-date!'    => N$hide_time,
    'show-group!'   => N$hide_group,
    'show-mode!'    => N$hide_mode,
    'show-mtime!'   => \$show_mtime,
    'show-num-links!' => N$hide_nlinks,
    'show-owner!'   => N$hide_owner,
    'show-size!'    => N$hide_size,
    'show-time!'    => N$hide_time,
    'show-xattr!'   => \$show_xattr,
    'sort-by-time!' => sub { set_sort_by $_[-1] ? 'time' : 'none' },
    'sort-by=s'     => \&set_sort_by,
    's|show-blocks' => \$show_blocks,
    't'             => sub { set_sort_by 'time' },
    'utc!'          => \$use_utc,
    'u|use-atime'   => S($use_time,'atime'),
    (map { my $x = $_; "sort-by-$x" => sub { set_sort_by $x } } keys %sorter),
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
    --full-time         display time(s) as year, month, day, hour, minute & second
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
        $full_time = 1;
        $long_mode = 1;
        $show_atime = 1 if $use_triple_time;
        $show_ctime = 1;
        $show_mtime = 1;
        $sort_by = $sorter{ctime};
    } elsif ( $use_time eq 'ctime' ) {
        $show_ctime = 1;
    } elsif ( $use_time eq 'atime' ) {
        $show_atime = 1;
    } else {
        $show_mtime = 1;
    }
}

#
# Options '-c' and '-u' change '-t' from meaning "sort by mtime" into "sort by
# ctime" and "sort by atime" respectively.
#

if ( $sort_by_time ) {
    $sort_by = $sorter{$use_time};
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
