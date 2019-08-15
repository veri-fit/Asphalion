#set terminal postscript eps enhanced color size 800,300
#set output 'minbft_x_1_100000.eps'

set term png size 800,450
set output 'minbft_x_1_100000.png'

#set term svg size 800,450
#set output 'minbft_x_1_100000.svg'

#set term postscript enhanced "NimbusSanL-Regu" 22 color size 800,300
#set output 'minbft_x_1_100000.ps'

#set multiplot layout 1,1 rowsfirst

set autoscale
#unset log
#unset label
set xtic 20000 font ",25"
set ytic auto font ",25"
#unset key
set key right top
set key spacing 0.8 font ",25"

set style line 1 lt 1 pi 100  pt 1 linecolor rgb "black"
set style line 2 lt 1 pi 100  pt 2 linecolor rgb "black"
set style line 3 lt 1 pi 100  pt 3 linecolor rgb "green"

set style line 4 lt 1 pi 100  pt 4 linecolor rgb "red"
set style line 5 lt 1 pi 100  pt 5 linecolor rgb "red"
set style line 6 lt 1 pi 100  pt 6 linecolor rgb "green"

set xlabel "timestamp/instance" font ",25"
set ylabel "average response time in ms" font ",25"
set yr [0.0:14.0]	 
set format x "%g"
#set format x "%.0s*10^%T"



plot "pbft_avg_0_1_1_100000.dat" using 1:2 title "verif. PBFT f=1" w linespoint ls 3, \
     "pbft_avg_0_2_1_100000.dat" using 1:2 title "verif. PBFT f=2" w linespoint ls 2, \
     "pbft_avg_0_3_1_100000.dat" using 1:2 title "verif. PBFT f=3" w linespoint ls 5, \
     "minbft_avg_0_1_1_100000.dat" using 1:2 title "verif. MinBFT f=1" w linespoint ls 6, \
     "minbft_avg_0_2_1_100000.dat" using 1:2 title "verif. MinBFT f=2" w linespoint ls 1, \
     "minbft_avg_0_3_1_100000.dat" using 1:2 title "verif. MinBFT f=3" w linespoint ls 4
