#!/usr/bin/perl

use File::Find;

use POSIX qw/strftime/;
use Time::HiRes qw( time );

#print strftime('%D %T',localtime);
$start = strftime('%D %T',localtime);

my $files;
find(\&wanted, 'benchmarks');
$n = 1;
#open(TIMEOUTFILE, ">timeout_aalta") or die "cannot open the file!";
#open(TIMEOUTFILE, ">error") or die "cannot open the file!";
foreach(@content)
{
  if(-f $_)
  {
    #print "$_\n";
    if($_ =~ /.*\.alaska/)
    {
      open(INFILE, "$_") or die "cannot open the input file!";
      open(OUTFILE, ">output/$_") or die "cannot open the file!";
      #open(TIMEOUTFILE, ">>output/timeout_aalta") or die "cannot open the file!";
      $line = <INFILE>;
      
      while ($line ne "")
      {
        eval
        {
	   local $SIG{ALRM} = sub { die "timeout\n" };
	   alarm(60);
           $t0 = time();
           #print "checking\ $_ ...\n";
	   $output = `./aalta -fn "$line"`;
	   print OUTFILE "$output\n";
	   
           $n = $n + 1;
	   alarm(0);
	};
	if($@)
	{
	  #print TIMEOUTFILE ("$_\n");
          $output = `killall -9 aalta`;
          print OUTFILE "timeout\n";
	  $n = $n + 1;
	  sleep 1;		 
	}
	$line = <INFILE>;
      }
      close(INFILE);
      #close(OUTFILE);
    }
  }
}
close(TIMEOUTFILE);

$end = strftime('%D %T',localtime);
open(TIMEFILE, ">timeinfo") or die "cannot open the file!";
print TIMEFILE ("start time:  $start\n");
print TIMEFILE ("end time:  $end\n");
close(TIMEFILE);

exit;

sub wanted
{
  push @content, $File::Find::name;
  return;
}



