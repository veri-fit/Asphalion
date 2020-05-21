#set terminal postscript eps enhanced color size 800,300
#set output 'minbft_x_1_100000.eps'

#set term png size 800,450
#set output 'minbft_x_1_100000.png'

set term svg size 800,450
set output 'minbft_x_1_100000.svg'

#set term postscript enhanced "NimbusSanL-Regu" 22 color size 800,300
#set output 'minbft_x_1_100000.ps'

#set multiplot layout 1,1 rowsfirst

set autoscale
#unset log
#unset label
set xtic 20000 font ",20"
set ytic auto font ",20"
#unset key
set key right top
set key spacing 1.05 font ",20"

set style line 1 lt 1 pi 100  pt 1 linecolor rgb "blue"
set style line 2 lt 1 pi 100  pt 2 linecolor rgb "black"
set style line 3 lt 1 pi 100  pt 3 linecolor rgb "red"

set style line 4 lt 1 pi 100  pt 4 linecolor rgb "blue"
set style line 5 lt 1 pi 100  pt 5 linecolor rgb "black"
set style line 6 lt 1 pi 100  pt 6 linecolor rgb "red"

set xlabel "timestamp/instance" font ",30"
set ylabel "average response time in ms" font ",30"
set yr [0.0:14.0]	 
set format x "%g"
#set format x "%.0s*10^%T"



plot "pbft_avg_0_3_1_100000.dat" using 1:2 title "verif. PBFT f=3" w linespoint ls 1, \
     "pbft_avg_0_2_1_100000.dat" using 1:2 title "verif. PBFT f=2" w linespoint ls 2, \
     "minbft_avg_0_3_1_100000.dat" using 1:2 title "verif. MinBFT f=3" w linespoint ls 4, \
     "pbft_avg_0_1_1_100000.dat" using 1:2 title "verif. PBFT f=1" w linespoint ls 3, \
     "minbft_avg_0_2_1_100000.dat" using 1:2 title "verif. MinBFT f=2" w linespoint ls 5, \
     "minbft_avg_0_1_1_100000.dat" using 1:2 title "verif. MinBFT f=1" w linespoint ls 6
