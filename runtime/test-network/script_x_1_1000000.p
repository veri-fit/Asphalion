#set terminal postscript eps enhanced color size 800,300
#set output 'pbft_x_1_1000000.eps'

#set term png size 500,300
#set output 'n_pbft_x_1_1000000.png'

set term svg size 800,450
set output 'n_pbft_x_1_1000000.svg'

#set term postscript enhanced "NimbusSanL-Regu" 22 color size 800,300
#set output 'n_pbft_x_1_1000000.ps'

#set multiplot layout 1,1 rowsfirst

set autoscale
#unset log
#unset label
set xtic 200000 font ",20"
set ytic auto font ",20"
#unset key
set key right top
set key spacing 1.5 font ",20"

set style line 1 lt 1 pi 10000  pt 1 linecolor rgb "red"
set style line 2 lt 1 pi 10000  pt 2 linecolor rgb "black"
set style line 3 lt 1 pi 10000  pt 3 linecolor rgb "green"

set style line 4 lt 1 pi 1000  pt 4 linecolor rgb "red"
set style line 5 lt 1 pi 1000  pt 5 linecolor rgb "black"
set style line 6 lt 1 pi 1000  pt 6 linecolor rgb "green"

set xlabel "timestamp/instance" font ",30"
set yr [0.0:16.0]	 
set format x "%g"
#set format x "%.0s*10^%T"


plot "pbft_avg_0_1_1_1000000.dat" using 1:2 title "verif. PBFT f=1" w linespoint ls 1, \
     "log_1_1_0_1000000.dat" using 1:2 title "BFT-SMaRt f=1" w linespoint ls 4
