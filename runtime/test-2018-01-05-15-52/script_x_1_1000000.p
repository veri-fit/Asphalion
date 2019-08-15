#set terminal postscript eps enhanced color size 800,300
#set output 'pbft_x_1_10000.eps'

#set term png size 500,300
#set output 'pbft_x_1_10000.png'

set term svg size 800,300
set output 'pbft_x_1_10000.svg'

#set term postscript enhanced "NimbusSanL-Regu" 22 color size 800,300
#set output 'pbft_x_1_10000.ps'

#set multiplot layout 1,1 rowsfirst

set autoscale
#unset log
#unset label
set xtic 10000 font ",20"
set ytic auto font ",20"
#unset key
set key right bottom
set key spacing 1.8 font ",20"

set style line 1 lt 1 pi 5  pt 1 linecolor rgb "red"
set style line 2 lt 1 pi 5  pt 2 linecolor rgb "black"
set style line 3 lt 1 pi 5  pt 3 linecolor rgb "green"

set style line 4 lt 1 pi 5  pt 4 linecolor rgb "red"
set style line 5 lt 1 pi 5  pt 5 linecolor rgb "black"
set style line 6 lt 1 pi 5  pt 6 linecolor rgb "green"

set xlabel "time elapsed in ms" font ",30"
set ylabel "trans. per sec." font ",25"
set xr [0.0:76000.0]	 
set yr [0.0:170.0]	 
set format x "%g"
#set format x "%.0s*10^%T"



plot "pbft_elp_0_1_1_10000.dat" using 1:2 title "verif. PBFT f=1" w linespoint ls 1
# , \

# "log_1_1_0_1000000.dat" using 1:2 title "BFT-SMaRt f=1" w linespoint ls 4

#     "pbft_avg_0_2_1_1000000.dat" using 1:2 title "verif. PBFT f=2" w linespoint ls 2, \
#     "pbft_avg_0_3_1_1000000.dat" using 1:2 title "verif. PBFT f=3" w linespoint ls 3, \
# \
#     "log_2_1_0_1000000.dat" using 1:2 title "BFT-SMaRt f=2" w linespoint ls 5, \
#     "log_3_1_0_1000000.dat" using 1:2 title "BFT-SMaRt f=3" w linespoint ls 6
