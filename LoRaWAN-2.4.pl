#!/usr/bin/perl -w

###################################################################################
#      Event-based simulator for (un)confirmed LoRaWAN 2.4GHz transmissions       #
#                                    v2024.1.7                                    #
#                                                                                 #
# Features:                                                                       #
# -- Multiple half-duplex gateways (3 x uplink, 1 x downlink transceivers)        #
# -- Acks with two receive windows (RX1, RX2)                                     #
# -- Non-orthogonal SF transmissions                                              #
# -- Periodic or non-periodic (exponential) transmission rate                     #
# -- Percentage of nodes required confirmed transmissions                         #
# -- Capture effect                                                               #
# -- Path-loss signal attenuation model (uplink+downlink)                         #
# -- Multiple channels                                                            #
# -- Collision handling for both uplink and downlink transmissions                #
# -- Energy consumption calculation (uplink+downlink)                             #
# -- Network server policies (downlink packet & gw selection)                     #
#                                                                                 #
# author: Dr. Dimitrios Zorbas                                                    #
# email: dimzorbas@ieee.org                                                       #
# distributed under GNUv2 General Public Licence                                  #
###################################################################################

use strict;
use POSIX;
use List::Util qw(min max sum);
use Time::HiRes qw(time);
use Math::Random qw(random_uniform random_exponential random_normal);
use Term::ProgressBar 2.00;
use GD::SVG;
use Statistics::Basic qw(:all);

# Give 3 or 4 arguments (if 4 arguments are given, the terrain file format is different than the usual one)
die "usage: ./LoRaWAN-2.4.pl <packets_per_hour> <simulation_time(secs)> <terrain_file> <gw_settings_file_(optional)>\n" unless (scalar @ARGV > 2);

die "Packet rate must be higher than or equal to 1pkt per hour\n" if ($ARGV[0] < 1);
die "Simulation time must be longer than or equal to 1h\n" if ($ARGV[1] < 3600);

# node attributes
my %ncoords = (); # node coordinates
my %nconsumption = (); # consumption
my %nretransmissions = (); # retransmissions per node (per packet)
my %surpressed = ();
my %nreachablegws = (); # reachable gws
my %nptx = (); # transmit power index
my %nresponse = (); # 0/1 (1 = ADR response will be sent)
my %nconfirmed = (); # confirmed transmissions or not
my %nunique = (); # unique transmissions per node (equivalent to FCntUp)
my %nacked = (); # unique acked packets (for confirmed transmissions) or just delivered (for non-confirmed transmissions)
my %nperiod = (); 
my %npkt = (); # packet size per node
my %ntotretr = (); # number of retransmissions per node (total)
my %nsf = (); # SF of each ED
my %nch = (); # Channel of each ED

# gw attributes
my %gcoords = (); # gw coordinates
my %gunavailability = (); # unavailable gw time due to downlink or locked to another transmission
my %gresponses = (); # acks carried out per gw
my %gdest = (); # contains downlink information [node, sf, RX1/2, channel]
my %gwsf = (); # SF per gw transceiver
my %gwch = (); # Channel per gw transceiver
my %gw_mode = (); # GW mode (uplink/downlink)

# LoRa PHY and LoRaWAN parameters
my @sensis = ([7,-112,-106], [8,-115,-109], [9,-117,-111], [10,-120,-114], [11,-123,-117], [12,-126,-120]); # sensitivities [SF, BW812, BW1625]
my @thresholds = ([1,-8,-9,-9,-9,-9], [-11,1,-11,-12,-13,-13], [-15,-13,1,-13,-14,-15], [-19,-18,-17,1,-17,-18], [-22,-22,-21,-20,1,-20], [-25,-25,-25,-24,-23,1]); # capture effect power thresholds per SF[SF] for non-orthogonal transmissions
my $var = 3.57; # variance
my ($dref, $Lpld0, $gamma) = (40, 100, 2.3); # attenuation model parameters
my $max_retr = 8; # max number of retransmissions per packet (default value = 1)
my $bw = 812500; # channel bandwidth
my $cr = 1; # Coding Rate
my @Ptx_l = (0, 10, 12.5); # dBm
my @Ptx_w = (40*3.3, 58*3.3, 70*3.3); # Ptx cons. for 0, 10, 12.5 dBm (mW)
my $Prx_w = 40 * 3.3;
my $Pidle_w = 30 * 3.3; # this is actually the consumption of the microcontroller in idle mode
my @channels = (2403000000, 2425000000, 2479000000); # 3 uplink channels for the 3 available uplink transceivers
my $rx2sf = 12; # SF used for RX2 
my $rx2ch = 2450000000; # channel used for RX2
my @avail_sfs = (8, 10, 12); # SF8, 10, and 12 for the 3 uplink transceivers, respectively (unless a custom settings file is used)

# packet specific parameters
my $fpl = 242; # max uplink frame payload (bytes)
my $preamble = 12; # in symbols
my $H = 0; # header 0/1
my $hcrc = 0; # HCRC bytes
my $CRC = 1; # 0/1
my $mhdr = 1; # MAC header (bytes)
my $mic = 4; # MIC bytes
my $fhdr = 7; # frame header without fopts
my $adr = 4; # Fopts option for the ADR (4 Bytes)
my $txdc = 1; # Fopts option for the TX duty cycle (1 Byte)
my $fport_u = 1; # 1B for FPort for uplink
my $fport_d = 0; # 0B for FPort for downlink (commands are included in Fopts, acks have no payload)
my $overhead_u = $mhdr+$mic+$fhdr+$fport_u+$hcrc; # LoRa+LoRaWAN uplink overhead
my $overhead_d = $mhdr+$mic+$fhdr+$fport_d+$hcrc; # LoRa+LoRaWAN downlink overhead
my %overlaps = (); # handles special packet overlaps 

# simulation parameters
my $confirmed_perc = 0; # percentage of nodes that require confirmed transmissions (1=all)
my $full_collision = 1; # take into account non-orthogonal SF transmissions or not
my $period = 3600/$ARGV[0]; # time period between transmissions
my $sim_time = $ARGV[1]; # given simulation time
my $debug = 1; # enable debug mode
my $sim_end = 0;
my ($terrain, $norm_x, $norm_y) = (0, 0, 0); # terrain side, normalised terrain side
my $start_time = time; # just for statistics
my $successful = 0; # number of delivered packets (not necessarily acked)
my $dropped = 0; # number of dropped packets (for confirmed traffic)
my $dropped_unc = 0; # number of dropped packets (for unconfirmed traffic)
my $total_trans = 0; # number of transm. packets
my $total_retrans = 0; # number of re-transm packets
my $no_rx1 = 0; # no gw was available in RX1
my $no_rx2 = 0; # no gw was available in RX1 or RX2
my $picture = 0; # generate an energy consumption map
my $fixed_packet_rate = 1; # send packets periodically with a fixed rate (=1) or at random (=0)
my $total_down_time = 0; # total downlink time
my $progress_bar = 0; # activate progress bar (slower!)
my $avg_sf = 0;
my @sf_distr = (0, 0, 0, 0, 0, 0);
my $fixed_packet_size = 1; # all nodes have the same packet size defined in @fpl (=1) or a randomly selected (=0)
my $packet_size = 16; # default packet size if fixed_packet_size=1 or avg packet size if fixed_packet_size=0 (Bytes)
my $packet_size_distr = "normal"; # uniform / normal (applicable if fixed_packet_size=0)
my $avg_pkt = 0; # actual average packet size
my %sorted_t = (); # keys = channels, values = list of nodes
my @recents = ();
my $auto_simtime = 0; # 1 = the simulation will automatically stop (useful when sim_time>>10000)
my %sf_retrans = (); # number of retransmissions per SF

# application server
my $policy = 2; # gateway selection policy for downlink traffic
my %prev_seq = ();
my %appacked = (); # counts the number of acked packets per node
my %appsuccess = (); # counts the number of packets that received from at least one gw per node
my %nogwavail = (); # counts how many time no gw was available (keys = nodes)

my $progress;
if ($progress_bar == 1){
	$progress = Term::ProgressBar->new({
		count => $sim_time,
		ETA   => 'linear',
		remove => 1
	});
	$progress->minor(0);
	$progress->max_update_rate(1);
}
my $next_update = 0;

if (scalar @ARGV == 3){
	read_data();
	foreach my $n (keys %ncoords){
		$nsf{$n} = min_sf($n);
	}
}else{
	read_data_custom();
}

# first transmission
my @init_trans = ();
foreach my $n (keys %ncoords){
	my $start = random_uniform(1, 0, $period);
	$avg_sf += $nsf{$n};
	$avg_pkt += $npkt{$n};
	my $airt = airtime($nsf{$n}, $npkt{$n});
	my $stop = $start + $airt;
	print "# $n will transmit from $start to $stop (SF$nsf{$n})\n" if ($debug == 1);
	$nunique{$n} = 1;
	push (@init_trans, [$n, $start, $stop, $nch{$n}, $nsf{$n}, $nunique{$n}]);
	$nconsumption{$n} += $airt * $Ptx_w[$nptx{$n}] + ($airt+1) * $Pidle_w; # +1sec for sensing
	$total_trans += 1;
}

# sort transmissions in ascending order
foreach my $t (sort { $a->[1] <=> $b->[1] } @init_trans){
	my ($n, $sta, $end, $ch, $sf, $nuni) = @$t;
	push (@{$sorted_t{$channels[$ch]}}, $t);
}
undef @init_trans;

# main loop
while (1){
	print "-------------------------------\n" if ($debug == 1);
	foreach my $ch (keys %sorted_t){
		if (exists $sorted_t{$ch}){
			delete $sorted_t{$ch} if (scalar @{$sorted_t{$ch}} == 0);
		}
	}
	# select the channel with earliest transmission among all first transmissions
	my @earliest = (sort {$sorted_t{$a}[0][1] <=> $sorted_t{$b}[0][1]} keys %sorted_t);
	my $min_ch = shift(@earliest);
	my $cardi = scalar @earliest;
	my ($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $sel_seq) = @{shift(@{$sorted_t{$min_ch}})};
	while (!defined $sel){
		print "# Channel $min_ch has no transmissions in the queue!\n" if ($debug == 1);
		delete $sorted_t{$min_ch} if (scalar @{$sorted_t{$min_ch}} == 0);
		$min_ch = shift(@earliest);
		($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $sel_seq) = @{shift(@{$sorted_t{$min_ch}})};
	}
	$next_update = $progress->update($sel_end) if ($progress_bar == 1);
	if ($sel_sta > $sim_time){
		if ($progress_bar == 1){
			$next_update = $progress->update($sim_time);
			$progress->update($sim_time);
		}
		last;
	}
	print "# grabbed $sel, transmission from $sel_sta -> $sel_end (CH=$channels[$sel_ch])\n" if ($debug == 1);
	$sim_end = $sel_end;
	if ($auto_simtime == 1){
		my $nu = (sum values %nunique);
		$nu = 1 if ($nu == 0);
		if (scalar @recents < 50){
			push(@recents, (sum values %nacked)/$nu);
			#printf "stddev = %.5f\n", stddev(\@recents);
		}else{
			if (stddev(\@recents) < 0.00001){
				print "### Continuing the simulation will not considerably affect the result! ###\n";
				last;
			}
			shift(@recents);
		}
	}
	
	if ($sel =~ /^[0-9]/){ # if the packet is an uplink transmission
		
		my $gw_rc = node_col($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf); # check for collisions and return a list of gws that received the uplink pkt
		my $rwindow = 0;
		my $failed = 0;
		if ((scalar @$gw_rc > 0) && ($nconfirmed{$sel} == 1)){ # if at least one gateway received the pkt -> successful transmission
			$successful += 1;
			$appsuccess{$sel} += 1 if ($sel_seq > $prev_seq{$sel});
			printf "# $sel 's transmission received by %d gateway(s) (channel $channels[$sel_ch])\n", scalar @$gw_rc if ($debug == 1);
			# now we have to find which gateway (if any) can transmit an ack in RX1 or RX2
			
			# check RX1
			my ($sel_gw, $sel_p) = gs_policy($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $gw_rc, 1);
			if (defined $sel_gw){
				$sel_gw = $sel_gw.4; # switch to the downlink transceiver
				my ($ack_sta, $ack_end) = ($sel_end+1, $sel_end+1+airtime($sel_sf, $overhead_d));
				$total_down_time += airtime($sel_sf, $overhead_d);
				$rwindow = 1;
				$gresponses{$sel_gw} += 1;
				push (@{$gunavailability{$sel_gw}}, [$ack_sta, $ack_end, $sel_ch, $sel_sf, "d"]);
				my $new_name = $sel_gw."_".$gresponses{$sel_gw}; # e.g. A4_1
				# place new transmission at the correct position
				my $i = 0;
				foreach my $el (@{$sorted_t{$channels[$sel_ch]}}){
					my ($n, $sta, $end, $ch, $sf, $seq) = @$el;
					last if ($sta > $ack_sta);
					$i += 1;
				}
				$appacked{$sel} += 1 if ($sel_seq > $prev_seq{$sel});
				splice(@{$sorted_t{$channels[$sel_ch]}}, $i, 0, [$new_name, $ack_sta, $ack_end, $sel_ch, $sel_sf, $appacked{$sel}]);
				push (@{$gdest{$sel_gw}}, [$sel, $sel_end+$rwindow, $sel_sf, $rwindow, $sel_ch, -1]);
				print "# gw $sel_gw will transmit an ack to $sel ($new_name, RX$rwindow, channel $channels[$sel_ch])\n" if ($debug == 1);
			}else{
				# check RX2
				$no_rx1 += 1;
				($sel_gw, $sel_p) = gs_policy($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $gw_rc, 2);
				if (defined $sel_gw){
					$sel_gw = $sel_gw.4; # switch to the downlink transceiver
					my ($ack_sta, $ack_end) = ($sel_end+2, $sel_end+2+airtime($rx2sf, $overhead_d));
					$total_down_time += airtime($rx2sf, $overhead_d);
					$rwindow = 2;
					$gresponses{$sel_gw} += 1;
					push (@{$gunavailability{$sel_gw}}, [$ack_sta, $ack_end, 0, $rx2sf, "d"]);
					my $new_name = $sel_gw."_".$gresponses{$sel_gw};
					my $i = 0;
					foreach my $el (@{$sorted_t{$rx2ch}}){
						my ($n, $sta, $end, $ch, $sf, $seq) = @$el;
						last if ($sta > $ack_sta);
						$i += 1;
					}
					$appacked{$sel} += 1 if ($sel_seq > $prev_seq{$sel});
					splice(@{$sorted_t{$rx2ch}}, $i, 0, [$new_name, $ack_sta, $ack_end, 0, $rx2sf, $appacked{$sel}]);
					push (@{$gdest{$sel_gw}}, [$sel, $sel_end+$rwindow, $sel_sf, $rwindow, 0, -1]);
					print "# gw $sel_gw will transmit an ack to $sel ($new_name, RX$rwindow, channel $rx2ch)\n" if ($debug == 1);
				}else{
					$no_rx2 += 1;
					print "# no gateway is available\n" if ($debug == 1);
					$nogwavail{$sel} += 1;
					$failed = 1;
				}
			}
			$prev_seq{$sel} = $sel_seq;
# 			if (defined $sel_gw){
# 				# ADR: the SF is already adjusted in min_sf; here only the transmit power is adjusted
# 				my $gap = $sel_p - $sensis[$sel_sf-7][bwconv($bw)];
# 				my $new_ptx = undef;
# 				my $new_index = -1;
# 				foreach my $p (sort {$a<=>$b} @Ptx_l){
# 					$new_index += 1;
# 					next if ($p >= $Ptx_l[$nptx{$sel}]); # we can only decrease power at the moment
# 					if ($gap-$Ptx_l[$nptx{$sel}]+$p >= 12){
# 						$new_ptx = $p;
# 						last;
# 					}
# 				}
# 				if (defined $new_ptx){
# 					$gdest{$sel_gw}[-1][5] = $new_index;
# 					print "# it will be suggested that $sel changes tx power to $Ptx_l[$new_index]\n" if ($debug == 1);
# 				}
# 			}
		}elsif ((scalar @$gw_rc > 0) && ($nconfirmed{$sel} == 0)){ # successful transmission but no ack is required
			$successful += 1;
			$nacked{$sel} += 1;
			printf "# $sel 's transmission received by %d gateway(s) (channel $channels[$sel_ch])\n", scalar @$gw_rc if ($debug == 1);
			
			# remove the examined tuple of gw unavailability
			foreach my $gwpr (@$gw_rc){
				my ($gw, $pr) = @$gwpr;
				my $index = 0;
				foreach my $tuple (@{$gunavailability{$gw}}){
					my ($sta, $end, $ch, $sf, $m) = @$tuple;
					splice @{$gunavailability{$gw}}, $index, 1 if (($end == $sel_end) && ($ch == $sel_ch) && ($sf == $sel_sf) && ($m eq "u"));
					last;
				}
			}
			
			my $at = airtime($sel_sf, $npkt{$sel});
			$sel_sta = $sel_end + $nperiod{$sel} + rand(1);
			$sel_end = $sel_sta + $at;
			# place the new transmission at the correct position
			my $i = 0;
			foreach my $el (@{$sorted_t{$channels[$sel_ch]}}){
				my ($n, $sta, $end, $ch_, $sf_, $seq) = @$el;
				last if ($sta > $sel_sta);
				$i += 1;
			}
			$nunique{$sel} += 1 if ($sel_sta < $sim_time); # do not count transmissions that exceed the simulation time;
			splice(@{$sorted_t{$channels[$sel_ch]}}, $i, 0, [$sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $nunique{$sel}]);
			$total_trans += 1 if ($sel_sta < $sim_time); 
			print "# $sel, new transmission at $sel_sta -> $sel_end\n" if ($debug == 1);
			$nconsumption{$sel} += $at * $Ptx_w[$nptx{$sel}] + (airtime($sel_sf, $npkt{$sel})+1) * $Pidle_w;
		}else{ # non-successful transmission
			$failed = 1;
		}
		if ($failed == 1){
			my $at = 0;
			my $new_trans = 0;
			if ($nconfirmed{$sel} == 1){
				if ($nretransmissions{$sel} < $max_retr){
					$nretransmissions{$sel} += 1;
					$sf_retrans{$sel_sf} += 1;
				}else{
					$dropped += 1;
					$ntotretr{$sel} += $nretransmissions{$sel};
					$nretransmissions{$sel} = 0;
					$new_trans = 1;
					print "# $sel 's packet lost!\n" if ($debug == 1);
				}
				# the node stays on only for the duration of the preamble for both receive windows
				$nconsumption{$sel} += $preamble*(2**$sel_sf)/($bw*1000) * ($Prx_w + $Pidle_w); ### check this
				$nconsumption{$sel} += $preamble*(2**$rx2sf)/($bw*1000) * ($Prx_w + $Pidle_w);
				# plan the next transmission as soon as the duty cycle permits that
				$at = airtime($sel_sf, $npkt{$sel});
				if ($new_trans == 0){
					$sel_sta = $sel_end + 2 + rand(3); # just some randomness
				}else{
					$sel_sta = $sel_end + 2 + $nperiod{$sel} + rand(1);
				}
			}else{
				$dropped_unc += 1;
				$prev_seq{$sel} = $sel_seq;
				$new_trans = 1;
				print "# $sel 's packet lost!\n" if ($debug == 1);
				$at = airtime($sel_sf, $npkt{$sel});
				$sel_sta = $sel_end + $nperiod{$sel} + rand(1);
			}
			$sel_end = $sel_sta+$at;
			# place the new transmission at the correct position
			my $i = 0;
			foreach my $el (@{$sorted_t{$channels[$sel_ch]}}){
				my ($n, $sta, $end, $ch_, $bw, $sf_, $seq) = @$el;
				last if ($sta > $sel_sta);
				$i += 1;
			}
			$nunique{$sel} += 1 if (($new_trans == 1) && ($sel_sta < $sim_time)); # do not count transmissions that exceed the simulation time
			splice(@{$sorted_t{$channels[$sel_ch]}}, $i, 0, [$sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $nunique{$sel}]);
			$total_trans += 1 if ($sel_sta < $sim_time);
			$total_retrans += 1 if (($nconfirmed{$sel} == 1) && ($sel_sta < $sim_time));
			print "# $sel, new transmission at $sel_sta -> $sel_end\n" if ($debug == 1);
			$nconsumption{$sel} += $at * $Ptx_w[$nptx{$sel}] + (airtime($sel_sf, $npkt{$sel})+1) * $Pidle_w;
		}
		foreach my $g (keys %gcoords){
			$surpressed{$sel}{$g} = 0;
		}
		
		
	}else{ # if the packet is a gw transmission
		
		$sel =~ s/_[0-9]+//; # keep only the gw id
		print "$sel \n";
		# remove the unnecessary tuples from gw unavailability
		my @indices = ();
		my $index = 0;
		foreach my $tuple (@{$gunavailability{$sel}}){
			my ($sta, $end, $ch, $sf, $m) = @$tuple;
			push (@indices, $index) if ($end < $sel_sta);
			$index += 1;
		}
		for (sort {$b<=>$a} @indices){
			splice @{$gunavailability{$sel}}, $_, 1;
		}
		
		# look for the examined transmission in gdest, get some info, and then remove it 
		my $failed = 0;
		$index = 0;
		# ($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $sel_seq) information we already have
		# sel_sf = SF of the downlink, sf = SF of the corresponding uplink in gdest
		my ($dest, $st, $sf, $rwindow, $ch, $pow); # we also need dest, rwindow, and pow (the others should be the same)
		foreach my $tup (@{$gdest{$sel}}){
			my ($dest_, $st_, $sf_, $rwindow_, $ch_, $p_) = @$tup;
			if (($st_ == $sel_sta) && ($ch_ == $sel_ch)){
				($dest, $st, $sf, $rwindow, $ch, $pow) = ($dest_, $st_, $sf_, $rwindow_, $ch_, $p_);
				last;
			}
			$index += 1;
		}
		splice @{$gdest{$sel}}, $index, 1;
		# check if the transmission can reach the node
		my $G = random_normal(1, 0, 1);
		my $d = distance($gcoords{$sel}[0], $ncoords{$dest}[0], $gcoords{$sel}[1], $ncoords{$dest}[1]);
		my $prx = 12.5 - ($Lpld0 + 10*$gamma * log10($d/$dref) + $G*$var);
		if ($prx < $sensis[$sel_sf-7][2]){
			print "# ack didn't reach node $dest\n" if ($debug == 1);
			$failed = 1;
		}
		# check if transmission time overlaps with other transmissions
		foreach my $tr (@{$sorted_t{$channels[$ch]}}){
			my ($n, $sta, $end, $ch_, $sf_, $seq) = @$tr;
			last if ($sta > $sel_end);
			$n =~ s/_[0-9]+// if ($n =~ /^[A-Z]/);
			next if (($n eq $sel) || ($end < $sel_sta) || ($ch_ != $ch)); # skip non-overlapping transmissions or different channels
			
			if ( (($sel_sta >= $sta) && ($sel_sta <= $end)) || (($sel_end <= $end) && ($sel_end >= $sta)) || (($sel_sta == $sta) && ($sel_end == $end)) ){
				push(@{$overlaps{$sel}}, [$n, $G, $sf_]); # put in here all overlapping transmissions
				push(@{$overlaps{$n}}, [$sel, $G, $sel_sf]); # check future possible collisions with those transmissions
			}
		}
		my %examined = ();
		foreach my $ng (@{$overlaps{$sel}}){
			my ($n, $G_, $sf_) = @$ng;
			next if (exists $examined{$n});
			$examined{$n} = 1;
			my $overlap = 1;
			# SF
			if ($sf_ == $sel_sf){
				$overlap += 2;
			}
			# power 
			my $d_ = 0;
			my $p = 0;
			if ($n =~ /^[0-9]/){
				$d_ = distance($ncoords{$dest}[0], $ncoords{$n}[0], $ncoords{$dest}[1], $ncoords{$n}[1]);
				$p = $Ptx_l[$nptx{$n}];
			}else{
				$d_ = distance($ncoords{$dest}[0], $gcoords{$n}[0], $ncoords{$dest}[1], $gcoords{$n}[1]);
				$p = 12.5;
			}
			my $prx_ = $p - ($Lpld0 + 10*$gamma * log10($d_/$dref) + $G_*$var);
			if ($overlap == 3){
				if ((abs($prx - $prx_) <= $thresholds[$sel_sf-7][$sf_-7]) ){ # both collide
					$failed = 1;
					print "# ack collided together with $n at node $sel\n" if ($debug == 1);
				}
				if (($prx_ - $prx) > $thresholds[$sel_sf-7][$sf_-7]){ # n suppressed sel
					$failed = 1;
					print "# ack surpressed by $n at node $dest\n" if ($debug == 1);
				}
				if (($prx - $prx_) > $thresholds[$sf_-7][$sel_sf-7]){ # sel suppressed n
					print "# $n surpressed by $sel at node $dest\n" if ($debug == 1);
				}
			}
			if (($overlap == 1) && ($full_collision == 1)){ # non-orthogonality
				if (($prx - $prx_) > $thresholds[$sel_sf-7][$sf_-7]){
					if (($prx_ - $prx) <= $thresholds[$sf_-7][$sel_sf-7]){
						print "# $n surpressed by $sel at node $dest\n" if ($debug == 1);
					}
				}else{
					if (($prx_ - $prx) > $thresholds[$sf_-7][$sel_sf-7]){
						$failed = 1;
						print "# ack surpressed by $n at node $dest\n" if ($debug == 1);
					}else{
						$failed = 1;
						print "# ack collided together with $n at node $dest\n" if ($debug == 1);
					}
				}
			}
		}
		my $new_trans = 0;
		if ($failed == 0){
			print "# ack successfully received, $dest 's transmission has been acked\n" if ($debug == 1);
			$ntotretr{$dest} += $nretransmissions{$dest};
			$nretransmissions{$dest} = 0;
			$nacked{$dest} += 1;
			$new_trans = 1;
			if ($rwindow == 2){ # also count the RX1 window
				$nconsumption{$dest} += $preamble*(2**$sf)/500 * ($Prx_w + $Pidle_w);
			}
			my $extra_bytes = 0; # if an ADR request is included in the downlink packet
			if ($pow != -1){
				$nptx{$dest} = $pow;
				$extra_bytes = $adr;
				$nresponse{$dest} = 1;
				print "# transmit power of $dest is set to $Ptx_l[$pow]\n" if ($debug == 1);
			}
			$nconsumption{$dest} += airtime($sel_sf, $overhead_d+$extra_bytes) * ($Prx_w + $Pidle_w);
		}else{ # ack was not received
			if ($nretransmissions{$dest} < $max_retr){
				$nretransmissions{$dest} += 1;
				$sf_retrans{$sf} += 1;
			}else{
				$dropped += 1;
				$ntotretr{$dest} += $nretransmissions{$dest};
				$nretransmissions{$dest} = 0;
				$new_trans = 1;
				print "# $dest 's packet lost (no ack received)!\n" if ($debug == 1);
			}
			$nconsumption{$dest} += $preamble*(2**$sf)/500 * ($Prx_w + $Pidle_w);
			$nconsumption{$dest} += $preamble*(2**$rx2sf)/500 * ($Prx_w + $Pidle_w);
		}
		@{$overlaps{$sel}} = ();
		# plan next transmission
		my $extra_bytes = 0;
		if ($nresponse{$dest} == 1){
			$extra_bytes = $adr;
			$nresponse{$dest} = 0;
		}
		my $at = airtime($sf, $npkt{$dest}+$extra_bytes);
		my $new_start = $sel_sta - $rwindow + $nperiod{$dest} + rand(1);
		$new_start = $sel_sta - $rwindow + rand(3) if ($failed == 1 && $new_trans == 0);
		if (($new_trans == 1) && ($new_start < $sim_time)){ # do not count transmissions that exceed the simulation time
			$nunique{$dest} += 1;
		}
		my $new_end = $new_start + $at;
		my $i = 0;
		foreach my $el (@{$sorted_t{$channels[$ch]}}){
			my ($n, $sta, $end, $ch_, $sf_, $seq) = @$el;
			last if ($sta > $new_start);
			$i += 1;
		}
		splice(@{$sorted_t{$channels[$ch]}}, $i, 0, [$dest, $new_start, $new_end, $ch, $sf, $nunique{$dest}]);
		$total_trans += 1 if ($new_start < $sim_time); # do not count transmissions that exceed the simulation time
		$total_retrans += 1 if (($failed == 1) && ($new_start < $sim_time)); 
		print "# $dest, new transmission at $new_start -> $new_end\n" if ($debug == 1);
		$nconsumption{$dest} += $at * $Ptx_w[$nptx{$dest}] + (airtime($sf, $npkt{$dest})+1) * $Pidle_w;
	}
}
# print "---------------------\n";

my $avg_cons = (sum values %nconsumption)/(scalar keys %nconsumption);
my $min_cons = min values %nconsumption;
my $max_cons = max values %nconsumption;
my $finish_time = time;
printf "Simulation time = %.3f secs\n", $sim_end;
printf "Avg node consumption = %.5f J\n", $avg_cons/1000;
printf "Min node consumption = %.5f J\n", $min_cons/1000;
printf "Max node consumption = %.5f J\n", $max_cons/1000;
print "Total number of transmissions = $total_trans\n";
print "Total number of re-transmissions = $total_retrans\n" if ($confirmed_perc > 0);
printf "Total number of unique transmissions = %d\n", (sum values %nunique);
printf "Stdv of unique transmissions = %.2f\n", stddev(values %nunique);
print "Total packets delivered = $successful\n";
printf "Total packets delivered and acknowledged = %d\n", (sum values %nacked) if ($confirmed_perc > 0);
print "Total confirmed packets dropped = $dropped\n";
print "Total unconfirmed packets dropped = $dropped_unc\n";
printf "Packet Delivery Ratio = %.5f\n", (sum values %nacked)/(sum values %nunique); # unique packets delivered / unique packets transmitted
printf "Packet Reception Ratio = %.5f\n", $successful/$total_trans; # Global PRR
print "No GW available in RX1 = $no_rx1 times\n";
print "No GW available in RX1 or RX2 = $no_rx2 times\n";
print "Total downlink time = $total_down_time sec\n";
printf "Script execution time = %.4f secs\n", $finish_time - $start_time;
print "-----\n";
my @fairs = ();
foreach my $n (keys %ncoords){
	if ($nconfirmed{$n} == 0){
		push(@fairs, $nacked{$n}/$nunique{$n});
	}
}
printf "Unfairness = %.3f\n", stddev(\@fairs);
if ($confirmed_perc > 0){
	foreach my $g (sort keys %gcoords){
		print "GW $g sent out $gresponses{$g} acks\n";
	}
	@fairs = ();
	my $avgretr = 0;
	foreach my $n (keys %ncoords){
		next if ($nconfirmed{$n} == 0);
		$appsuccess{$n} = 1 if ($appsuccess{$n} == 0);
		push(@fairs, $appacked{$n}/$appsuccess{$n});
		$avgretr += $ntotretr{$n}/$nunique{$n};
	}
	printf "Downlink fairness = %.3f\n", stddev(\@fairs);
	printf "Avg number of retransmissions = %.3f\n", $avgretr/(scalar keys %ntotretr);
	printf "Stdev of retransmissions = %.3f\n", (stddev values %ntotretr);
	print "-----\n";
}
for (my $sf=7; $sf<=12; $sf+=1){
	printf "# of nodes with SF%d: %d, Avg retransmissions: %.2f\n", $sf, $sf_distr[$sf-7], $sf_retrans{$sf}/$sf_distr[$sf-7] if ($sf_distr[$sf-7] > 0);
}
printf "Avg SF = %.3f\n", $avg_sf/(scalar keys %ncoords);
printf "Avg packet size = %.3f bytes\n", $avg_pkt/(scalar keys %ncoords);
generate_picture() if ($picture == 1);


sub gs_policy{ # gateway selection policy
	my ($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf, $gw_rc, $win) = @_;
	my ($d_gw, $d_p) = (undef, -9999999999999);
	if ($win == 2){
		if ($sel_sf < $rx2sf){
			@$gw_rc = @{$nreachablegws{$sel}};
		}
		$sel_sf = $rx2sf;
	}
	my ($ack_sta, $ack_end) = ($sel_end+$win, $sel_end+$win+airtime($sel_sf, $overhead_d));
	my $min_resp = 1;
	my @avail = ();
	
	# check for available gws (gws that are not currently receiving)
	foreach my $g (@$gw_rc){
		my ($gw, $p) = @$g;
		my $is_avail = 1;
		foreach my $gu (@{$gunavailability{$gw}}){
			my ($sta, $end, $ch, $sf, $m) = @$gu;
			if ( (($ack_sta >= $sta) && ($ack_sta <= $end)) || (($ack_end <= $end) && ($ack_end >= $sta)) ){
				$is_avail = 0;
				last;
			}
		}
		next if ($is_avail == 0);
		push (@avail, $g);
	}
	return (undef, undef) if (scalar @avail == 0);
	
	if ($policy == 4){ # URCB
		my $avgretr = (sum values %nogwavail)/(scalar keys %ncoords);
		if ( ($nogwavail{$sel} < $avgretr) && ((scalar @avail)/(scalar @$gw_rc) < 2/3) ){
			return (undef, undef);
		}
	}
	if ($policy == 5){ # FBS
		my $avgfair = 0;
		foreach my $n (keys %ncoords){
			next if ($appsuccess{$n} == 0);
			$avgfair += $appacked{$n}/$appsuccess{$n};
		}
		$avgfair /= (scalar keys %ncoords);
		if ( ($appacked{$sel}/$appsuccess{$sel} >= $avgfair) && ((scalar @avail)/(scalar @$gw_rc) < 2/3) && ($avgfair != 0) ){
			return (undef, undef);
		}
	}
	foreach my $g (@avail){
		my ($gw, $p) = @$g;
		$gw =~ s/[0-9].*//; # keep only the letter(s)
		if ($policy == 1){ # FCFS
			my $resp = rand(2)/10;
			if ($resp < $min_resp){
				$min_resp = $resp;
				$d_gw = $gw;
				$d_p = $p;
			}
		}elsif (($policy == 2) || ($policy == 4) || ($policy == 5)){ # RSSI
			if ($p > $d_p){
				$d_gw = $gw;
				$d_p = $p;
			}
		}
	}
	return ($d_gw, $d_p); # return gw ids without the transceiver number (e.g. A instead of A1)
}

sub node_col{ # handle node collisions
	my ($sel, $sel_sta, $sel_end, $sel_ch, $sel_sf) = @_;
	# check for collisions with other transmissions (time, SF, power) per gw
	my @gw_rc = ();
	foreach my $gw (keys %gcoords){
		next if ($gw_mode{$gw} eq 'd');
		next if (($surpressed{$sel}{$gw} == 1) || ($gwsf{$gw} != $sel_sf) || ($gwch{$gw} != $sel_ch));
		my $d = distance($gcoords{$gw}[0], $ncoords{$sel}[0], $gcoords{$gw}[1], $ncoords{$sel}[1]);
		my $G = random_normal(1, 0, 1);
		my $prx = $Ptx_l[$nptx{$sel}] - ($Lpld0 + 10*$gamma * log10($d/$dref) + $G*$var);
		if ($prx < $sensis[$sel_sf-7][bwconv($bw)]){
			$surpressed{$sel}{$gw} = 1;
			print "# packet didn't reach gw $gw ($prx < $sensis[$sel_sf-7][bwconv($bw)])\n" if ($debug == 1);
			next;
		}
		# check if the gw is available for uplink
		my $is_available = 1;
		foreach my $gu (@{$gunavailability{$gw}}){
			my ($sta, $end, $ch, $sf, $m) = @$gu;
			if ( (($sel_sta >= $sta) && ($sel_sta <= $end)) || (($sel_end <= $end) && ($sel_end >= $sta)) || (($sel_sta < $sta) && ($sel_end > $end))){
				# the gw has locked to another transmission with the same ch/sf
				if ( ($m eq "u") && ($sel_ch == $ch) && ($sel_sf == $sf) ){
					$is_available = 0;
					last;
				}
			}
		}
		if ($is_available == 0){
			$surpressed{$sel}{$gw} = 1;
			print "# gw not available for uplink (channel $sel_ch, SF $sel_sf)\n" if ($debug == 1);
			next;
		}
		foreach my $tr (@{$sorted_t{$channels[$sel_ch]}}){
			my ($n, $sta, $end, $ch, $sf, $seq) = @$tr;
			last if ($sta > $sel_end);
			if ($n =~ /^[0-9]/){ # node transmission
				next if (($n == $sel) || ($end < $sel_sta) || ($sf != $sel_sf));
				my $overlap = 0;
				# time overlap
				if ( (($sel_sta >= $sta) && ($sel_sta <= $end)) || (($sel_end <= $end) && ($sel_end >= $sta)) || (($sel_sta < $sta) && ($sel_end > $end)) ){
					$overlap = 1;
				}
				# power 
				my $d_ = distance($gcoords{$gw}[0], $ncoords{$n}[0], $gcoords{$gw}[1], $ncoords{$n}[1]);
				my $prx_ = $Ptx_l[$nptx{$n}] - ($Lpld0 + 10*$gamma * log10($d_/$dref) + random_normal(1, 0, 1)*$var);
				if ($overlap == 1){
					if ((abs($prx - $prx_) <= $thresholds[$sel_sf-7][$sf-7]) ){ # both collide
						$surpressed{$sel}{$gw} = 1;
						$surpressed{$n}{$gw} = 1;
						print "# $sel collided together with $n at gateway $gw\n" if ($debug == 1);
					}
					if (($prx_ - $prx) > $thresholds[$sel_sf-7][$sf-7]){ # n suppressed sel
						$surpressed{$sel}{$gw} = 1;
						print "# $sel surpressed by $n at gateway $gw\n" if ($debug == 1);
					}
					if (($prx - $prx_) > $thresholds[$sf-7][$sel_sf-7]){ # sel suppressed n
						$surpressed{$n}{$gw} = 1;
						print "# $n surpressed by $sel at gateway $gw\n" if ($debug == 1);
					}
				}
			}else{ # n is a gw in this case
				$n =~ s/_[0-9]+//; # keep only the gw id
				next if (($n eq $gw) || ($sta > $sel_end) || ($end < $sel_sta) || ($ch != $sel_ch) || ($sf != $sel_sf));
				# time overlap
				if ( (($sel_sta >= $sta) && ($sel_sta <= $end)) || (($sel_end <= $end) && ($sel_end >= $sta)) || (($sel_sta < $sta) && ($sel_end > $end)) ){
					my $already_there = 0;
					my $G_ = random_normal(1, 0, 1);
					foreach my $ng (@{$overlaps{$sel}}){
						my ($n_, $G_, $sf_) = @$ng;
						if ($n_ eq $n){
							$already_there = 1;
						}
					}
					if ($already_there == 0){
						push(@{$overlaps{$sel}}, [$n, $G_, $sf]); # put in here all overlapping transmissions
					}
					push(@{$overlaps{$n}}, [$sel, $G, $sel_sf]); # check future possible collisions with those transmissions
				}
				foreach my $ng (@{$overlaps{$sel}}){
					my ($n, $G_, $sf_) = @$ng;
					my $overlap = 1;
					# power 
					my $d_ = distance($gcoords{$gw}[0], $gcoords{$n}[0], $gcoords{$gw}[1], $gcoords{$n}[1]);
					my $prx_ = 12.5 - ($Lpld0 + 10*$gamma * log10($d_/$dref) + $G_*$var);
					if ($overlap == 1){
						if ((abs($prx - $prx_) <= $thresholds[$sel_sf-7][$sf_-7]) ){ # both collide
							$surpressed{$sel}{$gw} = 1;
							print "# $sel collided together with $n at gateway $gw\n" if ($debug == 1);
						}
						if (($prx_ - $prx) > $thresholds[$sel_sf-7][$sf_-7]){ # n suppressed sel
							$surpressed{$sel}{$gw} = 1;
							print "# $sel surpressed by $n at gateway $gw\n" if ($debug == 1);
						}
						if (($prx - $prx_) > $thresholds[$sf_-7][$sel_sf-7]){ # sel suppressed n
							print "# $n surpressed by $sel at gateway $gw\n" if ($debug == 1);
						}
					}
				}
			}
		}
		if ($surpressed{$sel}{$gw} == 0){
			push (@gw_rc, [$gw, $prx]);
			# set the gw unavailable (exclude preamble) and lock to the specific Ch/SF
			my $Tsym = (2**$sel_sf)/$bw;
			my $Tpream = ($preamble + 4.25)*$Tsym;
			push(@{$gunavailability{$gw}}, [$sel_sta+$Tpream, $sel_end, $sel_ch, $sel_sf, "u"]);
		}
	}
	@{$overlaps{$sel}} = ();
	return (\@gw_rc);
}

sub min_sf{
	my $n = shift;
	my $G = 0; # assume that variance is 0
	my $Xs = $var*$G;
	my $sf = 13;
	my $bwi = bwconv($bw);
	foreach my $gw (keys %gcoords){
		next if ($gw_mode{$gw} eq 'u'); # just make it faster
		my $gf = 13;
		my $d0 = distance($gcoords{$gw}[0], $ncoords{$n}[0], $gcoords{$gw}[1], $ncoords{$n}[1]);
		foreach my $f (@avail_sfs){
			my $S = $sensis[$f-7][$bwi];
			my $Prx = $Ptx_l[$nptx{$n}] - ($Lpld0 + 10*$gamma * log10($d0/$dref) + $Xs);
			if (($Prx - 10) > $S){ # 10dBm tolerance
				$gf = $f;
				last;
			}
		}
		$sf = $gf if ($gf < $sf);
	}
	if ($sf == 13){
		print "node $n unreachable!\n";
		print "terrain too large?\n";
		exit;
	}
	# check which gateways can be reached with rx2sf
	foreach my $gw (keys %gcoords){
		$nch{$n} = $gwch{$gw} if ($gwsf{$gw} == $sf);
		next if ($gw_mode{$gw} eq 'u');
		my $d0 = distance($gcoords{$gw}[0], $ncoords{$n}[0], $gcoords{$gw}[1], $ncoords{$n}[1]);
		my $S = $sensis[$rx2sf-7][$bwi];
		my $Prx = $Ptx_l[$nptx{$n}] - ($Lpld0 + 10*$gamma * log10($d0/$dref) + $Xs);
		if (($Prx - 10) > $S){ # 10dBm tolerance
			push(@{$nreachablegws{$n}}, [$gw, $Prx]);
		}
	}
	if ($fixed_packet_size == 0){
		if ($packet_size_distr eq "uniform"){
			$npkt{$n} = int(rand($fpl));
		}elsif ($packet_size_distr eq "normal"){
			$npkt{$n} = int(random_normal(1, $packet_size, 10));
		}
	}else{
		$npkt{$n} = $packet_size;
	}
	while ($npkt{$n} % 16 > 0){
		$npkt{$n} += 1;
	}
	$npkt{$n} += $overhead_u;
	print "# $n can reach a gw with SF$sf\n" if ($debug == 1);
	$sf_distr[$sf-7] += 1;
	return $sf;
}

sub airtime{
	my $sf = shift;
	my $pl = shift;
	my $H = 0; # implicit header disabled (H=0) or not (H=1)
	my $Npream = 8;
	my $crc = 16; # bits
	my $Tsym = (2.0**$sf)/$bw;
	my $Tpream = ($Npream + 4.25)*$Tsym;
	my $payloadSymbNB = 0;
	if ($sf >= 7 && $sf <= 10){
		$payloadSymbNB = 8 + ceil( max( (8.0*$pl+$crc-4.0*$sf+8+20*$H), 0 )*($cr+4) / (4*$sf));
	}elsif ($sf > 10){
		$payloadSymbNB = 8 + ceil( max( (8.0*$pl+$crc-4.0*$sf+8+20*$H), 0 )*($cr+4) / (4*($sf-2)));
	}
	my $Tpayload = $payloadSymbNB * $Tsym;
	return ($Tpream + $Tpayload);
}

sub bwconv{
	my $bw = shift;
	$bw *= 1000 if ($bw < 10000);
	my $bwi = 0;
	if ($bw == 812500){
		$bwi = 1;
	}elsif ($bw == 1625000){
		$bwi = 2;
	}
	return $bwi;
}

sub read_data{
	my $terrain_file = $ARGV[2];
	open(FH, "<$terrain_file") or die "Error: could not open terrain file $terrain_file\n";
	my @nodes = ();
	my @gateways = ();
	while(<FH>){
		chomp;
		if (/^# stats: (.*)/){
			my $stats_line = $1;
			if ($stats_line =~ /terrain=([0-9]+\.[0-9]+)m\^2/){
				$terrain = $1;
			}
			$norm_x = sqrt($terrain);
			$norm_y = $norm_x;
		} elsif (/^# node coords: (.*)/){
			my $sensor_coord = $1;
			my @coords = split(/\] /, $sensor_coord);
			@nodes = map { /([0-9]+) \[([0-9]+\.[0-9]+) ([0-9]+\.[0-9]+)/; [$1, $2, $3]; } @coords;
		} elsif (/^# gateway coords: (.*)/){
			my $gw_coord = $1;
			my @coords = split(/\] /, $gw_coord);
			@gateways = map { /([A-Z]+) \[([0-9]+\.[0-9]+) ([0-9]+\.[0-9]+)/; [$1, $2, $3]; } @coords;
		}
	}
	close(FH);
	
	foreach my $gw (@gateways){
		my ($gor, $x, $y) = @$gw;
		my @sfs = @avail_sfs;
		for (my $i=1; $i<=4; $i++){
			my $g = $gor.$i;
			$gcoords{$g} = [$x, $y];
			@{$gunavailability{$g}} = ();
			@{$overlaps{$g}} = ();
			$gresponses{$g} = 0;
			if ($i < 4){
				$gw_mode{$g} = 'u';
				$gwch{$g} = $i-1;
				$gwsf{$g} = shift(@sfs);
			}else{
				$gw_mode{$g} = 'd';
				$gwsf{$g} = $rx2sf;
			}
		}
	}
	
	my $conf_num = int($confirmed_perc * (scalar @nodes));
	foreach my $node (@nodes){
		my ($n, $x, $y) = @$node;
		$ncoords{$n} = [$x, $y];
		@{$overlaps{$n}} = ();
		$nptx{$n} = scalar @Ptx_l - 1; # start with the highest Ptx
		$nresponse{$n} = 0;
		$nretransmissions{$n} = 0;
		if ($conf_num > 0){
			$nconfirmed{$n} = 1;
			$conf_num -= 1;
		}else{
			$nconfirmed{$n} = 0;
		}
		$appacked{$n} = 0;
		$appsuccess{$n} = 0;
		$nacked{$n} = 0;
		$prev_seq{$n} = 0;
		$ntotretr{$n} = 0;
		$nogwavail{$n} = 0;
		if ($fixed_packet_rate == 0){
			my @per = random_exponential(scalar keys @nodes, 2*$period); # other distributions may be used
			foreach my $n (keys %ncoords){
				$nperiod{$n} = pop(@per);
			}
		}else{
			$nperiod{$n} = $period;
		}
		foreach my $g (keys %gcoords){
			$surpressed{$n}{$g} = 0;
		}
	}
	for (my $i=7; $i<13; $i++){
		$sf_retrans{$i} = 0;
	}
}

sub read_data_custom{
	my $terrain_file = $ARGV[2];
	my $settings_file = $ARGV[3];
	open(FH, "<$terrain_file") or die "Error: could not open terrain file $terrain_file\n";
	$norm_x = 1500; #<FH>;
	$norm_y = $norm_x;
	my @nodes = ();
	my @gw_coords = ();
	while(<FH>){
		chomp;
		my @items = split(/ /, $_);
		if (scalar @items == 2){
			push (@gw_coords, [$items[0], $items[1]]);
		}else{
			my $pl = $items[-1];
			my ($id, $nx, $ny) = @items;
			$npkt{$id} = $pl;
			push (@nodes, [$id, $nx, $ny]);
		}
	}
	close(FH);
	
	my $mod = 0;
	my $gw_prefix = 'A';
	my $transceiver = 1;
	my $temp_letter; #
	my @gateways = ();
	open(FH, "<$settings_file") or die "Error: could not open settings file $settings_file\n";
	while(<FH>){
		if (/^([A-Z]+) ([0-9]+)/){
			$temp_letter = $1; #
			my $gw_name = $gw_prefix.$transceiver;
			$gwsf{$gw_name} = $2;
			$gwch{$gw_name} = $transceiver-1;
			$gwsf{$temp_letter} = $2; #
			$gwch{$temp_letter} = $transceiver-1; #
			$gw_mode{$gw_name} = 'u';
			push (@gateways, [$gw_name, $gw_coords[$mod % 3][0], $gw_coords[$mod % 3][1]]);
			$transceiver += 1;
			if ($transceiver == 4){
				$gw_name = $gw_prefix.$transceiver;
				push (@gateways, [$gw_name, $gw_coords[$mod % 3][0], $gw_coords[$mod % 3][1]]);
				$gwsf{$gw_name} = $rx2sf; # give a temporary SF to the downlink transceiver
				$gw_mode{$gw_name} = 'd';
				$mod += 1;
				$transceiver = 1;
				$gw_prefix++;
			}
		}elsif (/^([0-9]+) ([A-Z]+)/){
			$nsf{$1} = $gwsf{$2};
			$nch{$1} = $gwch{$2};
		}
	}
	close(FH);
	
	my $conf_num = int($confirmed_perc * (scalar @nodes));
	foreach my $node (@nodes){
		my ($n, $x, $y) = @$node;
		$npkt{$n} += $overhead_u;
		$sf_distr[$nsf{$n}-7] += 1;
		$ncoords{$n} = [$x, $y];
		@{$overlaps{$n}} = ();
		$nptx{$n} = scalar @Ptx_l - 1; # start with the highest Ptx
		$nresponse{$n} = 0;
		$nretransmissions{$n} = 0;
		if ($conf_num > 0){
			$nconfirmed{$n} = 1;
			$conf_num -= 1;
		}else{
			$nconfirmed{$n} = 0;
		}
		$appacked{$n} = 0;
		$appsuccess{$n} = 0;
		$nacked{$n} = 0;
		$prev_seq{$n} = 0;
		$ntotretr{$n} = 0;
		$nogwavail{$n} = 0;
		if ($fixed_packet_rate == 0){
			my @per = random_exponential(scalar keys @nodes, 2*$period); # other distributions may be used
			foreach my $n (keys %ncoords){
				$nperiod{$n} = pop(@per);
			}
		}else{
			$nperiod{$n} = $period;
		}
	}
	foreach my $gw (@gateways){
		my ($g, $x, $y) = @$gw;
		# print "$g $x $y $gwsf{$g} \n";
		$gcoords{$g} = [$x, $y];
		foreach my $n (keys %ncoords){
			$surpressed{$n}{$g} = 0;
		}
		@{$gunavailability{$g}} = ();
		@{$overlaps{$g}} = ();
		$gresponses{$g} = 0;
	}
	for (my $i=7; $i<13; $i++){
		$sf_retrans{$i} = 0;
	}
}

sub distance {
	my ($x1, $x2, $y1, $y2) = @_;
	return sqrt( (($x1-$x2)*($x1-$x2))+(($y1-$y2)*($y1-$y2)) );
}

sub distance3d {
	my ($x1, $x2, $y1, $y2, $z1, $z2) = @_;
	return sqrt( (($x1-$x2)*($x1-$x2))+(($y1-$y2)*($y1-$y2))+(($z1-$z2)*($z1-$z2)) );
}

sub generate_picture{
	my ($display_x, $display_y) = (800, 800); # 800x800 pixel display pane
	my $im = new GD::SVG::Image($display_x, $display_y);
	my $blue = $im->colorAllocate(0,0,255);
	my $black = $im->colorAllocate(0,0,0);
	my $red = $im->colorAllocate(255,0,0);
	
	foreach my $n (keys %ncoords){
		my ($x, $y) = @{$ncoords{$n}};
		($x, $y) = (int(($x * $display_x)/$norm_x), int(($y * $display_y)/$norm_y));
		my $color = $im->colorAllocate(255*$nconsumption{$n}/$max_cons,0,0);
#		my $color = $im->colorAllocate(255*(min_sf($n)-7)/5,0,0);
		$im->filledArc($x,$y,20,20,0,360,$color);
	}
	
	foreach my $g (keys %gcoords){
		my ($x, $y) = @{$gcoords{$g}};
		($x, $y) = (int(($x * $display_x)/$norm_x), int(($y * $display_y)/$norm_y));
		$im->rectangle($x-5, $y-5, $x+5, $y+5, $red);
		$im->string(gdGiantFont,$x-2,$y-20,$g,$blue);
	}
	my $output_file = $ARGV[3]."-img.svg";
	open(FILEOUT, ">$output_file") or die "could not open file $output_file for writing!";
	binmode FILEOUT;
	print FILEOUT $im->svg;
	close FILEOUT;
}
