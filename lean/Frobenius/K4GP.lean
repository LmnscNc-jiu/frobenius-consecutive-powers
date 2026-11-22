import Frobenius.K4Phi

namespace FrobK4

def gam0 (x : ℤ) : ℤ := (461 * x ^ 6 + 3566 * x ^ 5 + 12066 * x ^ 4 + 22096 * x ^ 3 + 20160 * x ^ 2 + 7200 * x) / 400
def gam1 (x : ℤ) : ℤ := (2564 * x ^ 6 + 8644 * x ^ 5 + 11913 * x ^ 4 + 10556 * x ^ 3 - 1617 * x ^ 2 - 14850 * x - 9210) / 1600
def gam2 (x : ℤ) : ℤ := (4061 * x ^ 6 + 22532 * x ^ 5 + 56736 * x ^ 4 + 84256 * x ^ 3 + 50640 * x ^ 2 - 13056 * x - 19200) / 4000
def gam3 (x : ℤ) : ℤ := (2256 * x ^ 6 + 9864 * x ^ 5 + 20457 * x ^ 4 + 27616 * x ^ 3 + 12543 * x ^ 2 - 11614 * x - 10270) / 2000
def gam4 (x : ℤ) : ℤ := (2033 * x ^ 6 + 10918 * x ^ 5 + 28922 * x ^ 4 + 47248 * x ^ 3 + 34432 * x ^ 2 + 416 * x - 7680) / 2000
def gam5 (x : ℤ) : ℤ := (1612 * x ^ 6 + 8572 * x ^ 5 + 21007 * x ^ 4 + 29812 * x ^ 3 + 14825 * x ^ 2 - 8830 * x - 8550) / 1600
def gam6 (x : ℤ) : ℤ := (290 * x ^ 6 + 2121 * x ^ 5 + 6421 * x ^ 4 + 10152 * x ^ 3 + 7384 * x ^ 2 + 1152 * x - 720) / 200
def gam7 (x : ℤ) : ℤ := (784 * x ^ 6 + 4320 * x ^ 5 + 11057 * x ^ 4 + 16732 * x ^ 3 + 10163 * x ^ 2 - 2538 * x - 3810) / 800
def gam8 (x : ℤ) : ℤ := (3883 * x ^ 6 + 24112 * x ^ 5 + 69796 * x ^ 4 + 115168 * x ^ 3 + 84224 * x ^ 2 + 4928 * x - 15360) / 4000
def gam9 (x : ℤ) : ℤ := (4052 * x ^ 6 + 23032 * x ^ 5 + 59243 * x ^ 4 + 87772 * x ^ 3 + 51313 * x ^ 2 - 14566 * x - 19870) / 4000
def gam10 (x : ℤ) : ℤ := (3883 * x ^ 6 + 22484 * x ^ 5 + 61656 * x ^ 4 + 100000 * x ^ 3 + 71280 * x ^ 2 - 16000) / 4000
def gam11 (x : ℤ) : ℤ := (4064 * x ^ 6 + 27720 * x ^ 5 + 86669 * x ^ 4 + 152828 * x ^ 3 + 129407 * x ^ 2 + 32542 * x - 8730) / 4000
def gam12 (x : ℤ) : ℤ := (290 * x ^ 6 + 1281 * x ^ 5 + 2309 * x ^ 4 + 2344 * x ^ 3 + 224 * x ^ 2 - 2032 * x - 1280) / 200
def gam13 (x : ℤ) : ℤ := (9052 * x ^ 6 + 42548 * x ^ 5 + 86439 * x ^ 4 + 105652 * x ^ 3 + 34281 * x ^ 2 - 61758 * x - 45990) / 8000
def gam14 (x : ℤ) : ℤ := (2033 * x ^ 6 + 13478 * x ^ 5 + 41722 * x ^ 4 + 72688 * x ^ 3 + 59552 * x ^ 2 + 12736 * x - 5280) / 2000
def gam15 (x : ℤ) : ℤ := (1552 * x ^ 6 + 9568 * x ^ 5 + 26915 * x ^ 4 + 43004 * x ^ 3 + 29665 * x ^ 2 - 550 * x - 6750) / 1600
def gam16 (x : ℤ) : ℤ := (4061 * x ^ 6 + 26200 * x ^ 5 + 75076 * x ^ 4 + 118112 * x ^ 3 + 78848 * x ^ 2 - 2752 * x - 17920) / 4000
def gam17 (x : ℤ) : ℤ := (8492 * x ^ 6 + 60764 * x ^ 5 + 196907 * x ^ 4 + 351572 * x ^ 3 + 304045 * x ^ 2 + 87898 * x - 12750) / 8000
def gam18 (x : ℤ) : ℤ := (461 * x ^ 6 + 1966 * x ^ 5 + 4066 * x ^ 4 + 5552 * x ^ 3 + 2528 * x ^ 2 - 2368 * x - 2080) / 400
def gam19 (x : ℤ) : ℤ := (11584 * x ^ 6 + 69504 * x ^ 5 + 182081 * x ^ 4 + 264964 * x ^ 3 + 167291 * x ^ 2 - 10002 * x - 38490) / 8000
def gam20 (x : ℤ) : ℤ := (461 * x ^ 6 + 3566 * x ^ 5 + 12066 * x ^ 4 + 22096 * x ^ 3 + 20160 * x ^ 2 + 7200 * x) / 400
def gam21 (x : ℤ) : ℤ := (8492 * x ^ 6 + 41140 * x ^ 5 + 98787 * x ^ 4 + 151844 * x ^ 3 + 97341 * x ^ 2 - 20214 * x - 35390) / 8000
def gam22 (x : ℤ) : ℤ := (4061 * x ^ 6 + 22532 * x ^ 5 + 56736 * x ^ 4 + 84256 * x ^ 3 + 50640 * x ^ 2 - 13056 * x - 19200) / 4000
def gam23 (x : ℤ) : ℤ := (1552 * x ^ 6 + 9056 * x ^ 5 + 24355 * x ^ 4 + 37916 * x ^ 3 + 24641 * x ^ 2 - 3014 * x - 7230) / 1600
def gam24 (x : ℤ) : ℤ := (2033 * x ^ 6 + 10918 * x ^ 5 + 28922 * x ^ 4 + 47248 * x ^ 3 + 34432 * x ^ 2 + 416 * x - 7680) / 2000
def gam25 (x : ℤ) : ℤ := (9052 * x ^ 6 + 66076 * x ^ 5 + 204079 * x ^ 4 + 332260 * x ^ 3 + 243545 * x ^ 2 + 31250 * x - 29750) / 8000
def gam26 (x : ℤ) : ℤ := (290 * x ^ 6 + 2121 * x ^ 5 + 6421 * x ^ 4 + 10152 * x ^ 3 + 7384 * x ^ 2 + 1152 * x - 720) / 200
def gam27 (x : ℤ) : ℤ := (4064 * x ^ 6 + 21048 * x ^ 5 + 53309 * x ^ 4 + 81964 * x ^ 3 + 50255 * x ^ 2 - 12754 * x - 19050) / 4000
def gam28 (x : ℤ) : ℤ := (3883 * x ^ 6 + 24112 * x ^ 5 + 69796 * x ^ 4 + 115168 * x ^ 3 + 84224 * x ^ 2 + 4928 * x - 15360) / 4000
def gam29 (x : ℤ) : ℤ := (4052 * x ^ 6 + 25592 * x ^ 5 + 72043 * x ^ 4 + 113212 * x ^ 3 + 76433 * x ^ 2 - 2246 * x - 17470) / 4000
def gam30 (x : ℤ) : ℤ := (3883 * x ^ 6 + 22484 * x ^ 5 + 61656 * x ^ 4 + 100000 * x ^ 3 + 71280 * x ^ 2 - 16000) / 4000
def gam31 (x : ℤ) : ℤ := (784 * x ^ 6 + 5088 * x ^ 5 + 14897 * x ^ 4 + 24364 * x ^ 3 + 17699 * x ^ 2 + 1158 * x - 3090) / 800
def gam32 (x : ℤ) : ℤ := (290 * x ^ 6 + 1281 * x ^ 5 + 2309 * x ^ 4 + 2344 * x ^ 3 + 224 * x ^ 2 - 2032 * x - 1280) / 200
def gam33 (x : ℤ) : ℤ := (1612 * x ^ 6 + 10772 * x ^ 5 + 32007 * x ^ 4 + 53284 * x ^ 3 + 41241 * x ^ 2 + 6354 * x - 5110) / 1600
def gam34 (x : ℤ) : ℤ := (2033 * x ^ 6 + 13478 * x ^ 5 + 41722 * x ^ 4 + 72688 * x ^ 3 + 59552 * x ^ 2 + 12736 * x - 5280) / 2000
def gam35 (x : ℤ) : ℤ := (2256 * x ^ 6 + 17208 * x ^ 5 + 57177 * x ^ 4 + 102440 * x ^ 3 + 90135 * x ^ 2 + 29050 * x - 1750) / 2000
def gam36 (x : ℤ) : ℤ := (4061 * x ^ 6 + 26200 * x ^ 5 + 75076 * x ^ 4 + 118112 * x ^ 3 + 78848 * x ^ 2 - 2752 * x - 17920) / 4000
def gam37 (x : ℤ) : ℤ := (2564 * x ^ 6 + 22124 * x ^ 5 + 79313 * x ^ 4 + 149228 * x ^ 3 + 144799 * x ^ 2 + 63694 * x + 7670) / 1600
def gam38 (x : ℤ) : ℤ := (461 * x ^ 6 + 1966 * x ^ 5 + 4066 * x ^ 4 + 5552 * x ^ 3 + 2528 * x ^ 2 - 2368 * x - 2080) / 400
def gam39 (x : ℤ) : ℤ := (260 * x ^ 6 + 1544 * x ^ 5 + 4030 * x ^ 4 + 5881 * x ^ 3 + 4193 * x ^ 2 + 703 * x - 355) / 100

def pfa0 (x : ℤ) : ℤ := (87 * x ^ 6 + 700 * x ^ 5 + 2480 * x ^ 4 + 4640 * x ^ 3 + 4240 * x ^ 2 + 1504 * x - 40) / 40
def pfa1 (x : ℤ) : ℤ := (62 * x ^ 6 + 203 * x ^ 5 + 275 * x ^ 4 + 240 * x ^ 3 - 100 * x ^ 2 - 456 * x - 284) / 20
def pfa2 (x : ℤ) : ℤ := (69 * x ^ 6 + 592 * x ^ 5 + 2060 * x ^ 4 + 3680 * x ^ 3 + 3040 * x ^ 2 + 736 * x - 232) / 40
def pfa3 (x : ℤ) : ℤ := (10 * x ^ 6 + 45 * x ^ 5 + 100 * x ^ 4 + 140 * x ^ 3 + 55 * x ^ 2 - 74 * x - 63) / 5
def pfa4 (x : ℤ) : ℤ := (65 * x ^ 6 + 380 * x ^ 5 + 1080 * x ^ 4 + 1760 * x ^ 3 + 1120 * x ^ 2 - 224 * x - 424) / 40
def pfa5 (x : ℤ) : ℤ := (78 * x ^ 6 + 425 * x ^ 5 + 1125 * x ^ 4 + 1760 * x ^ 3 + 1080 * x ^ 2 - 272 * x - 440) / 40
def pfa6 (x : ℤ) : ℤ := (113 * x ^ 6 + 952 * x ^ 5 + 3300 * x ^ 4 + 5920 * x ^ 3 + 5200 * x ^ 2 + 1760 * x - 40) / 40
def pfa7 (x : ℤ) : ℤ := (16 * x ^ 6 + 113 * x ^ 5 + 355 * x ^ 4 + 600 * x ^ 3 + 430 * x ^ 2 + 12 * x - 94) / 10
def pfa8 (x : ℤ) : ℤ := (75 * x ^ 6 + 500 * x ^ 5 + 1560 * x ^ 4 + 2720 * x ^ 3 + 2160 * x ^ 2 + 352 * x - 296) / 40
def pfa9 (x : ℤ) : ℤ := (70 * x ^ 6 + 535 * x ^ 5 + 1755 * x ^ 4 + 3040 * x ^ 3 + 2360 * x ^ 2 + 368 * x - 312) / 40
def pfa10 (x : ℤ) : ℤ := (31 * x ^ 6 + 220 * x ^ 5 + 700 * x ^ 4 + 1200 * x ^ 3 + 880 * x ^ 2 + 48 * x - 180) / 20
def pfa11 (x : ℤ) : ℤ := (64 * x ^ 6 + 531 * x ^ 5 + 1855 * x ^ 4 + 3360 * x ^ 3 + 2800 * x ^ 2 + 672 * x - 232) / 40
def pfa12 (x : ℤ) : ℤ := (103 * x ^ 6 + 924 * x ^ 5 + 3280 * x ^ 4 + 5920 * x ^ 3 + 5200 * x ^ 2 + 1760 * x - 40) / 40
def pfa13 (x : ℤ) : ℤ := (38 * x ^ 6 + 341 * x ^ 5 + 1205 * x ^ 4 + 2160 * x ^ 3 + 1820 * x ^ 2 + 504 * x - 92) / 20
def pfa14 (x : ℤ) : ℤ := (81 * x ^ 6 + 536 * x ^ 5 + 1700 * x ^ 4 + 3040 * x ^ 3 + 2560 * x ^ 2 + 608 * x - 232) / 40
def pfa15 (x : ℤ) : ℤ := (36 * x ^ 6 + 265 * x ^ 5 + 865 * x ^ 4 + 1520 * x ^ 3 + 1220 * x ^ 2 + 232 * x - 140) / 20
def pfa16 (x : ℤ) : ℤ := (79 * x ^ 6 + 556 * x ^ 5 + 1760 * x ^ 4 + 3040 * x ^ 3 + 2400 * x ^ 2 + 416 * x - 296) / 40
def pfa17 (x : ℤ) : ℤ := (42 * x ^ 6 + 301 * x ^ 5 + 1005 * x ^ 4 + 1840 * x ^ 3 + 1620 * x ^ 2 + 488 * x - 76) / 20
def pfa18 (x : ℤ) : ℤ := (11 * x ^ 6 + 47 * x ^ 5 + 100 * x ^ 4 + 140 * x ^ 3 + 60 * x ^ 2 - 68 * x - 61) / 5
def pfa19 (x : ℤ) : ℤ := (112 * x ^ 6 + 977 * x ^ 5 + 3445 * x ^ 4 + 6240 * x ^ 3 + 5560 * x ^ 2 + 1968 * x + 8) / 40
def pfa20 (x : ℤ) : ℤ := (87 * x ^ 6 + 700 * x ^ 5 + 2480 * x ^ 4 + 4640 * x ^ 3 + 4240 * x ^ 2 + 1504 * x - 40) / 40
def pfa21 (x : ℤ) : ℤ := (74 * x ^ 6 + 371 * x ^ 5 + 935 * x ^ 4 + 1440 * x ^ 3 + 800 * x ^ 2 - 384 * x - 456) / 40
def pfa22 (x : ℤ) : ℤ := (69 * x ^ 6 + 592 * x ^ 5 + 2060 * x ^ 4 + 3680 * x ^ 3 + 3040 * x ^ 2 + 736 * x - 232) / 40
def pfa23 (x : ℤ) : ℤ := (68 * x ^ 6 + 491 * x ^ 5 + 1575 * x ^ 4 + 2720 * x ^ 3 + 2080 * x ^ 2 + 256 * x - 328) / 40
def pfa24 (x : ℤ) : ℤ := (65 * x ^ 6 + 380 * x ^ 5 + 1080 * x ^ 4 + 1760 * x ^ 3 + 1120 * x ^ 2 - 224 * x - 424) / 40
def pfa25 (x : ℤ) : ℤ := (90 * x ^ 6 + 685 * x ^ 5 + 2265 * x ^ 4 + 4000 * x ^ 3 + 3360 * x ^ 2 + 896 * x - 200) / 40
def pfa26 (x : ℤ) : ℤ := (113 * x ^ 6 + 952 * x ^ 5 + 3300 * x ^ 4 + 5920 * x ^ 3 + 5200 * x ^ 2 + 1760 * x - 40) / 40
def pfa27 (x : ℤ) : ℤ := (20 * x ^ 6 + 105 * x ^ 5 + 275 * x ^ 4 + 440 * x ^ 3 + 290 * x ^ 2 - 44 * x - 102) / 10
def pfa28 (x : ℤ) : ℤ := (75 * x ^ 6 + 500 * x ^ 5 + 1560 * x ^ 4 + 2720 * x ^ 3 + 2160 * x ^ 2 + 352 * x - 296) / 40
def pfa29 (x : ℤ) : ℤ := (78 * x ^ 6 + 613 * x ^ 5 + 2065 * x ^ 4 + 3680 * x ^ 3 + 3080 * x ^ 2 + 784 * x - 216) / 40
def pfa30 (x : ℤ) : ℤ := (31 * x ^ 6 + 220 * x ^ 5 + 700 * x ^ 4 + 1200 * x ^ 3 + 880 * x ^ 2 + 48 * x - 180) / 20
def pfa31 (x : ℤ) : ℤ := (76 * x ^ 6 + 569 * x ^ 5 + 1885 * x ^ 4 + 3360 * x ^ 3 + 2800 * x ^ 2 + 672 * x - 232) / 40
def pfa32 (x : ℤ) : ℤ := (103 * x ^ 6 + 924 * x ^ 5 + 3280 * x ^ 4 + 5920 * x ^ 3 + 5200 * x ^ 2 + 1760 * x - 40) / 40
def pfa33 (x : ℤ) : ℤ := (74 * x ^ 6 + 653 * x ^ 5 + 2345 * x ^ 4 + 4320 * x ^ 3 + 3800 * x ^ 2 + 1200 * x - 120) / 40
def pfa34 (x : ℤ) : ℤ := (81 * x ^ 6 + 536 * x ^ 5 + 1700 * x ^ 4 + 3040 * x ^ 3 + 2560 * x ^ 2 + 608 * x - 232) / 40
def pfa35 (x : ℤ) : ℤ := (88 * x ^ 6 + 705 * x ^ 5 + 2485 * x ^ 4 + 4640 * x ^ 3 + 4240 * x ^ 2 + 1504 * x - 40) / 40
def pfa36 (x : ℤ) : ℤ := (79 * x ^ 6 + 556 * x ^ 5 + 1760 * x ^ 4 + 3040 * x ^ 3 + 2400 * x ^ 2 + 416 * x - 296) / 40
def pfa37 (x : ℤ) : ℤ := (126 * x ^ 6 + 1093 * x ^ 5 + 4065 * x ^ 4 + 7840 * x ^ 3 + 7680 * x ^ 2 + 3392 * x + 376) / 40
def pfa38 (x : ℤ) : ℤ := (11 * x ^ 6 + 47 * x ^ 5 + 100 * x ^ 4 + 140 * x ^ 3 + 60 * x ^ 2 - 68 * x - 61) / 5
def pfa39 (x : ℤ) : ℤ := (204 * x ^ 6 + 1849 * x ^ 5 + 6685 * x ^ 4 + 12320 * x ^ 3 + 11600 * x ^ 2 + 4960 * x + 600) / 40

def pfb0 (x : ℤ) : ℤ := (11 * x ^ 6 + 85 * x ^ 5 + 290 * x ^ 4 + 540 * x ^ 3 + 500 * x ^ 2 + 180 * x - 5) / 5
def pfb1 (x : ℤ) : ℤ := (126 * x ^ 6 + 419 * x ^ 5 + 695 * x ^ 4 + 1120 * x ^ 3 + 1000 * x ^ 2 + 80 * x - 280) / 40
def pfb2 (x : ℤ) : ℤ := (79 * x ^ 6 + 392 * x ^ 5 + 940 * x ^ 4 + 1440 * x ^ 3 + 880 * x ^ 2 - 288 * x - 424) / 40
def pfb3 (x : ℤ) : ℤ := (88 * x ^ 6 + 351 * x ^ 5 + 715 * x ^ 4 + 1120 * x ^ 3 + 760 * x ^ 2 - 208 * x - 376) / 40
def pfb4 (x : ℤ) : ℤ := (81 * x ^ 6 + 436 * x ^ 5 + 1200 * x ^ 4 + 2080 * x ^ 3 + 1680 * x ^ 2 + 224 * x - 296) / 40
def pfb5 (x : ℤ) : ℤ := (74 * x ^ 6 + 235 * x ^ 5 + 255 * x ^ 4 + 160 * x ^ 3 - 320 * x ^ 2 - 832 * x - 520) / 40
def pfb6 (x : ℤ) : ℤ := (29 * x ^ 6 + 86 * x ^ 5 + 60 * x ^ 4 - 40 * x ^ 3 - 200 * x ^ 2 - 296 * x - 154) / 10
def pfb7 (x : ℤ) : ℤ := (76 * x ^ 6 + 343 * x ^ 5 + 755 * x ^ 4 + 1120 * x ^ 3 + 600 * x ^ 2 - 400 * x - 440) / 40
def pfb8 (x : ℤ) : ℤ := (31 * x ^ 6 + 152 * x ^ 5 + 360 * x ^ 4 + 560 * x ^ 3 + 320 * x ^ 2 - 176 * x - 212) / 20
def pfb9 (x : ℤ) : ℤ := (78 * x ^ 6 + 323 * x ^ 5 + 615 * x ^ 4 + 800 * x ^ 3 + 240 * x ^ 2 - 608 * x - 488) / 40
def pfb10 (x : ℤ) : ℤ := (75 * x ^ 6 + 400 * x ^ 5 + 1060 * x ^ 4 + 1760 * x ^ 3 + 1280 * x ^ 2 - 32 * x - 360) / 40
def pfb11 (x : ℤ) : ℤ := (20 * x ^ 6 + 135 * x ^ 5 + 425 * x ^ 4 + 760 * x ^ 3 + 650 * x ^ 2 + 164 * x - 54) / 10
def pfb12 (x : ℤ) : ℤ := (29 * x ^ 6 + 102 * x ^ 5 + 140 * x ^ 4 + 120 * x ^ 3 - 40 * x ^ 2 - 216 * x - 138) / 10
def pfb13 (x : ℤ) : ℤ := (90 * x ^ 6 + 395 * x ^ 5 + 815 * x ^ 4 + 1120 * x ^ 3 + 520 * x ^ 2 - 496 * x - 472) / 40
def pfb14 (x : ℤ) : ℤ := (65 * x ^ 6 + 400 * x ^ 5 + 1180 * x ^ 4 + 2080 * x ^ 3 + 1680 * x ^ 2 + 224 * x - 296) / 40
def pfb15 (x : ℤ) : ℤ := (68 * x ^ 6 + 325 * x ^ 5 + 745 * x ^ 4 + 1120 * x ^ 3 + 600 * x ^ 2 - 400 * x - 440) / 40
def pfb16 (x : ℤ) : ℤ := (69 * x ^ 6 + 236 * x ^ 5 + 280 * x ^ 4 + 160 * x ^ 3 - 400 * x ^ 2 - 928 * x - 552) / 40
def pfb17 (x : ℤ) : ℤ := (74 * x ^ 6 + 517 * x ^ 5 + 1665 * x ^ 4 + 3040 * x ^ 3 + 2680 * x ^ 2 + 752 * x - 184) / 40
def pfb18 (x : ℤ) : ℤ := (87 * x ^ 6 + 344 * x ^ 5 + 700 * x ^ 4 + 1120 * x ^ 3 + 800 * x ^ 2 - 160 * x - 360) / 40
def pfb19 (x : ℤ) : ℤ := (112 * x ^ 6 + 367 * x ^ 5 + 395 * x ^ 4 + 160 * x ^ 3 - 480 * x ^ 2 - 1024 * x - 584) / 40
def pfb20 (x : ℤ) : ℤ := (11 * x ^ 6 + 85 * x ^ 5 + 290 * x ^ 4 + 540 * x ^ 3 + 500 * x ^ 2 + 180 * x - 5) / 5
def pfb21 (x : ℤ) : ℤ := (42 * x ^ 6 + 203 * x ^ 5 + 515 * x ^ 4 + 880 * x ^ 3 + 700 * x ^ 2 + 56 * x - 156) / 20
def pfb22 (x : ℤ) : ℤ := (79 * x ^ 6 + 392 * x ^ 5 + 940 * x ^ 4 + 1440 * x ^ 3 + 880 * x ^ 2 - 288 * x - 424) / 40
def pfb23 (x : ℤ) : ℤ := (36 * x ^ 6 + 167 * x ^ 5 + 375 * x ^ 4 + 560 * x ^ 3 + 300 * x ^ 2 - 200 * x - 220) / 20
def pfb24 (x : ℤ) : ℤ := (81 * x ^ 6 + 436 * x ^ 5 + 1200 * x ^ 4 + 2080 * x ^ 3 + 1680 * x ^ 2 + 224 * x - 296) / 40
def pfb25 (x : ℤ) : ℤ := (38 * x ^ 6 + 115 * x ^ 5 + 75 * x ^ 4 - 80 * x ^ 3 - 380 * x ^ 2 - 568 * x - 300) / 20
def pfb26 (x : ℤ) : ℤ := (29 * x ^ 6 + 86 * x ^ 5 + 60 * x ^ 4 - 40 * x ^ 3 - 200 * x ^ 2 - 296 * x - 154) / 10
def pfb27 (x : ℤ) : ℤ := (64 * x ^ 6 + 237 * x ^ 5 + 385 * x ^ 4 + 480 * x ^ 3 + 40 * x ^ 2 - 624 * x - 472) / 40
def pfb28 (x : ℤ) : ℤ := (31 * x ^ 6 + 152 * x ^ 5 + 360 * x ^ 4 + 560 * x ^ 3 + 320 * x ^ 2 - 176 * x - 212) / 20
def pfb29 (x : ℤ) : ℤ := (70 * x ^ 6 + 305 * x ^ 5 + 605 * x ^ 4 + 800 * x ^ 3 + 240 * x ^ 2 - 608 * x - 488) / 40
def pfb30 (x : ℤ) : ℤ := (75 * x ^ 6 + 400 * x ^ 5 + 1060 * x ^ 4 + 1760 * x ^ 3 + 1280 * x ^ 2 - 32 * x - 360) / 40
def pfb31 (x : ℤ) : ℤ := (16 * x ^ 6 + 79 * x ^ 5 + 185 * x ^ 4 + 280 * x ^ 3 + 150 * x ^ 2 - 100 * x - 110) / 10
def pfb32 (x : ℤ) : ℤ := (29 * x ^ 6 + 102 * x ^ 5 + 140 * x ^ 4 + 120 * x ^ 3 - 40 * x ^ 2 - 216 * x - 138) / 10
def pfb33 (x : ℤ) : ℤ := (78 * x ^ 6 + 511 * x ^ 5 + 1555 * x ^ 4 + 2720 * x ^ 3 + 2240 * x ^ 2 + 448 * x - 264) / 40
def pfb34 (x : ℤ) : ℤ := (65 * x ^ 6 + 400 * x ^ 5 + 1180 * x ^ 4 + 2080 * x ^ 3 + 1680 * x ^ 2 + 224 * x - 296) / 40
def pfb35 (x : ℤ) : ℤ := (10 * x ^ 6 + 75 * x ^ 5 + 250 * x ^ 4 + 460 * x ^ 3 + 415 * x ^ 2 + 134 * x - 15) / 5
def pfb36 (x : ℤ) : ℤ := (69 * x ^ 6 + 236 * x ^ 5 + 280 * x ^ 4 + 160 * x ^ 3 - 400 * x ^ 2 - 928 * x - 552) / 40
def pfb37 (x : ℤ) : ℤ := (62 * x ^ 6 + 541 * x ^ 5 + 1965 * x ^ 4 + 3760 * x ^ 3 + 3700 * x ^ 2 + 1640 * x + 180) / 20
def pfb38 (x : ℤ) : ℤ := (87 * x ^ 6 + 344 * x ^ 5 + 700 * x ^ 4 + 1120 * x ^ 3 + 800 * x ^ 2 - 160 * x - 360) / 40
def pfb39 (x : ℤ) : ℤ := (26 * x ^ 6 + 76 * x ^ 5 + 55 * x ^ 4 - 20 * x ^ 3 - 105 * x ^ 2 - 154 * x - 79) / 5

/-- Closed form of the genus (Table A.4) on the residue class `n mod 40`. -/
def Gam (n : ℕ) : ℤ :=
  match n % 40 with
  | 0 => gam0 n
  | 1 => gam1 n
  | 2 => gam2 n
  | 3 => gam3 n
  | 4 => gam4 n
  | 5 => gam5 n
  | 6 => gam6 n
  | 7 => gam7 n
  | 8 => gam8 n
  | 9 => gam9 n
  | 10 => gam10 n
  | 11 => gam11 n
  | 12 => gam12 n
  | 13 => gam13 n
  | 14 => gam14 n
  | 15 => gam15 n
  | 16 => gam16 n
  | 17 => gam17 n
  | 18 => gam18 n
  | 19 => gam19 n
  | 20 => gam20 n
  | 21 => gam21 n
  | 22 => gam22 n
  | 23 => gam23 n
  | 24 => gam24 n
  | 25 => gam25 n
  | 26 => gam26 n
  | 27 => gam27 n
  | 28 => gam28 n
  | 29 => gam29 n
  | 30 => gam30 n
  | 31 => gam31 n
  | 32 => gam32 n
  | 33 => gam33 n
  | 34 => gam34 n
  | 35 => gam35 n
  | 36 => gam36 n
  | 37 => gam37 n
  | 38 => gam38 n
  | 39 => gam39 n
  | _ => 0

/-- Closed form of the pseudo-Frobenius number `F₁ = (l-1)b + (h-y-1)c - a` on the residue class `n mod 40`. -/
def PFa (n : ℕ) : ℤ :=
  match n % 40 with
  | 0 => pfa0 n
  | 1 => pfa1 n
  | 2 => pfa2 n
  | 3 => pfa3 n
  | 4 => pfa4 n
  | 5 => pfa5 n
  | 6 => pfa6 n
  | 7 => pfa7 n
  | 8 => pfa8 n
  | 9 => pfa9 n
  | 10 => pfa10 n
  | 11 => pfa11 n
  | 12 => pfa12 n
  | 13 => pfa13 n
  | 14 => pfa14 n
  | 15 => pfa15 n
  | 16 => pfa16 n
  | 17 => pfa17 n
  | 18 => pfa18 n
  | 19 => pfa19 n
  | 20 => pfa20 n
  | 21 => pfa21 n
  | 22 => pfa22 n
  | 23 => pfa23 n
  | 24 => pfa24 n
  | 25 => pfa25 n
  | 26 => pfa26 n
  | 27 => pfa27 n
  | 28 => pfa28 n
  | 29 => pfa29 n
  | 30 => pfa30 n
  | 31 => pfa31 n
  | 32 => pfa32 n
  | 33 => pfa33 n
  | 34 => pfa34 n
  | 35 => pfa35 n
  | 36 => pfa36 n
  | 37 => pfa37 n
  | 38 => pfa38 n
  | 39 => pfa39 n
  | _ => 0

/-- Closed form of the pseudo-Frobenius number `F₂ = (l-w-1)b + (h-1)c - a` on the residue class `n mod 40`. -/
def PFb (n : ℕ) : ℤ :=
  match n % 40 with
  | 0 => pfb0 n
  | 1 => pfb1 n
  | 2 => pfb2 n
  | 3 => pfb3 n
  | 4 => pfb4 n
  | 5 => pfb5 n
  | 6 => pfb6 n
  | 7 => pfb7 n
  | 8 => pfb8 n
  | 9 => pfb9 n
  | 10 => pfb10 n
  | 11 => pfb11 n
  | 12 => pfb12 n
  | 13 => pfb13 n
  | 14 => pfb14 n
  | 15 => pfb15 n
  | 16 => pfb16 n
  | 17 => pfb17 n
  | 18 => pfb18 n
  | 19 => pfb19 n
  | 20 => pfb20 n
  | 21 => pfb21 n
  | 22 => pfb22 n
  | 23 => pfb23 n
  | 24 => pfb24 n
  | 25 => pfb25 n
  | 26 => pfb26 n
  | 27 => pfb27 n
  | 28 => pfb28 n
  | 29 => pfb29 n
  | 30 => pfb30 n
  | 31 => pfb31 n
  | 32 => pfb32 n
  | 33 => pfb33 n
  | 34 => pfb34 n
  | 35 => pfb35 n
  | 36 => pfb36 n
  | 37 => pfb37 n
  | 38 => pfb38 n
  | 39 => pfb39 n
  | _ => 0

theorem Gam_eq_0 (n : ℕ) (h : n % 40 = 0) : Gam n = gam0 n := by
  simp only [Gam, h]

theorem Gam_eq_1 (n : ℕ) (h : n % 40 = 1) : Gam n = gam1 n := by
  simp only [Gam, h]

theorem Gam_eq_2 (n : ℕ) (h : n % 40 = 2) : Gam n = gam2 n := by
  simp only [Gam, h]

theorem Gam_eq_3 (n : ℕ) (h : n % 40 = 3) : Gam n = gam3 n := by
  simp only [Gam, h]

theorem Gam_eq_4 (n : ℕ) (h : n % 40 = 4) : Gam n = gam4 n := by
  simp only [Gam, h]

theorem Gam_eq_5 (n : ℕ) (h : n % 40 = 5) : Gam n = gam5 n := by
  simp only [Gam, h]

theorem Gam_eq_6 (n : ℕ) (h : n % 40 = 6) : Gam n = gam6 n := by
  simp only [Gam, h]

theorem Gam_eq_7 (n : ℕ) (h : n % 40 = 7) : Gam n = gam7 n := by
  simp only [Gam, h]

theorem Gam_eq_8 (n : ℕ) (h : n % 40 = 8) : Gam n = gam8 n := by
  simp only [Gam, h]

theorem Gam_eq_9 (n : ℕ) (h : n % 40 = 9) : Gam n = gam9 n := by
  simp only [Gam, h]

theorem Gam_eq_10 (n : ℕ) (h : n % 40 = 10) : Gam n = gam10 n := by
  simp only [Gam, h]

theorem Gam_eq_11 (n : ℕ) (h : n % 40 = 11) : Gam n = gam11 n := by
  simp only [Gam, h]

theorem Gam_eq_12 (n : ℕ) (h : n % 40 = 12) : Gam n = gam12 n := by
  simp only [Gam, h]

theorem Gam_eq_13 (n : ℕ) (h : n % 40 = 13) : Gam n = gam13 n := by
  simp only [Gam, h]

theorem Gam_eq_14 (n : ℕ) (h : n % 40 = 14) : Gam n = gam14 n := by
  simp only [Gam, h]

theorem Gam_eq_15 (n : ℕ) (h : n % 40 = 15) : Gam n = gam15 n := by
  simp only [Gam, h]

theorem Gam_eq_16 (n : ℕ) (h : n % 40 = 16) : Gam n = gam16 n := by
  simp only [Gam, h]

theorem Gam_eq_17 (n : ℕ) (h : n % 40 = 17) : Gam n = gam17 n := by
  simp only [Gam, h]

theorem Gam_eq_18 (n : ℕ) (h : n % 40 = 18) : Gam n = gam18 n := by
  simp only [Gam, h]

theorem Gam_eq_19 (n : ℕ) (h : n % 40 = 19) : Gam n = gam19 n := by
  simp only [Gam, h]

theorem Gam_eq_20 (n : ℕ) (h : n % 40 = 20) : Gam n = gam20 n := by
  simp only [Gam, h]

theorem Gam_eq_21 (n : ℕ) (h : n % 40 = 21) : Gam n = gam21 n := by
  simp only [Gam, h]

theorem Gam_eq_22 (n : ℕ) (h : n % 40 = 22) : Gam n = gam22 n := by
  simp only [Gam, h]

theorem Gam_eq_23 (n : ℕ) (h : n % 40 = 23) : Gam n = gam23 n := by
  simp only [Gam, h]

theorem Gam_eq_24 (n : ℕ) (h : n % 40 = 24) : Gam n = gam24 n := by
  simp only [Gam, h]

theorem Gam_eq_25 (n : ℕ) (h : n % 40 = 25) : Gam n = gam25 n := by
  simp only [Gam, h]

theorem Gam_eq_26 (n : ℕ) (h : n % 40 = 26) : Gam n = gam26 n := by
  simp only [Gam, h]

theorem Gam_eq_27 (n : ℕ) (h : n % 40 = 27) : Gam n = gam27 n := by
  simp only [Gam, h]

theorem Gam_eq_28 (n : ℕ) (h : n % 40 = 28) : Gam n = gam28 n := by
  simp only [Gam, h]

theorem Gam_eq_29 (n : ℕ) (h : n % 40 = 29) : Gam n = gam29 n := by
  simp only [Gam, h]

theorem Gam_eq_30 (n : ℕ) (h : n % 40 = 30) : Gam n = gam30 n := by
  simp only [Gam, h]

theorem Gam_eq_31 (n : ℕ) (h : n % 40 = 31) : Gam n = gam31 n := by
  simp only [Gam, h]

theorem Gam_eq_32 (n : ℕ) (h : n % 40 = 32) : Gam n = gam32 n := by
  simp only [Gam, h]

theorem Gam_eq_33 (n : ℕ) (h : n % 40 = 33) : Gam n = gam33 n := by
  simp only [Gam, h]

theorem Gam_eq_34 (n : ℕ) (h : n % 40 = 34) : Gam n = gam34 n := by
  simp only [Gam, h]

theorem Gam_eq_35 (n : ℕ) (h : n % 40 = 35) : Gam n = gam35 n := by
  simp only [Gam, h]

theorem Gam_eq_36 (n : ℕ) (h : n % 40 = 36) : Gam n = gam36 n := by
  simp only [Gam, h]

theorem Gam_eq_37 (n : ℕ) (h : n % 40 = 37) : Gam n = gam37 n := by
  simp only [Gam, h]

theorem Gam_eq_38 (n : ℕ) (h : n % 40 = 38) : Gam n = gam38 n := by
  simp only [Gam, h]

theorem Gam_eq_39 (n : ℕ) (h : n % 40 = 39) : Gam n = gam39 n := by
  simp only [Gam, h]

theorem PFa_eq_0 (n : ℕ) (h : n % 40 = 0) : PFa n = pfa0 n := by
  simp only [PFa, h]

theorem PFa_eq_1 (n : ℕ) (h : n % 40 = 1) : PFa n = pfa1 n := by
  simp only [PFa, h]

theorem PFa_eq_2 (n : ℕ) (h : n % 40 = 2) : PFa n = pfa2 n := by
  simp only [PFa, h]

theorem PFa_eq_3 (n : ℕ) (h : n % 40 = 3) : PFa n = pfa3 n := by
  simp only [PFa, h]

theorem PFa_eq_4 (n : ℕ) (h : n % 40 = 4) : PFa n = pfa4 n := by
  simp only [PFa, h]

theorem PFa_eq_5 (n : ℕ) (h : n % 40 = 5) : PFa n = pfa5 n := by
  simp only [PFa, h]

theorem PFa_eq_6 (n : ℕ) (h : n % 40 = 6) : PFa n = pfa6 n := by
  simp only [PFa, h]

theorem PFa_eq_7 (n : ℕ) (h : n % 40 = 7) : PFa n = pfa7 n := by
  simp only [PFa, h]

theorem PFa_eq_8 (n : ℕ) (h : n % 40 = 8) : PFa n = pfa8 n := by
  simp only [PFa, h]

theorem PFa_eq_9 (n : ℕ) (h : n % 40 = 9) : PFa n = pfa9 n := by
  simp only [PFa, h]

theorem PFa_eq_10 (n : ℕ) (h : n % 40 = 10) : PFa n = pfa10 n := by
  simp only [PFa, h]

theorem PFa_eq_11 (n : ℕ) (h : n % 40 = 11) : PFa n = pfa11 n := by
  simp only [PFa, h]

theorem PFa_eq_12 (n : ℕ) (h : n % 40 = 12) : PFa n = pfa12 n := by
  simp only [PFa, h]

theorem PFa_eq_13 (n : ℕ) (h : n % 40 = 13) : PFa n = pfa13 n := by
  simp only [PFa, h]

theorem PFa_eq_14 (n : ℕ) (h : n % 40 = 14) : PFa n = pfa14 n := by
  simp only [PFa, h]

theorem PFa_eq_15 (n : ℕ) (h : n % 40 = 15) : PFa n = pfa15 n := by
  simp only [PFa, h]

theorem PFa_eq_16 (n : ℕ) (h : n % 40 = 16) : PFa n = pfa16 n := by
  simp only [PFa, h]

theorem PFa_eq_17 (n : ℕ) (h : n % 40 = 17) : PFa n = pfa17 n := by
  simp only [PFa, h]

theorem PFa_eq_18 (n : ℕ) (h : n % 40 = 18) : PFa n = pfa18 n := by
  simp only [PFa, h]

theorem PFa_eq_19 (n : ℕ) (h : n % 40 = 19) : PFa n = pfa19 n := by
  simp only [PFa, h]

theorem PFa_eq_20 (n : ℕ) (h : n % 40 = 20) : PFa n = pfa20 n := by
  simp only [PFa, h]

theorem PFa_eq_21 (n : ℕ) (h : n % 40 = 21) : PFa n = pfa21 n := by
  simp only [PFa, h]

theorem PFa_eq_22 (n : ℕ) (h : n % 40 = 22) : PFa n = pfa22 n := by
  simp only [PFa, h]

theorem PFa_eq_23 (n : ℕ) (h : n % 40 = 23) : PFa n = pfa23 n := by
  simp only [PFa, h]

theorem PFa_eq_24 (n : ℕ) (h : n % 40 = 24) : PFa n = pfa24 n := by
  simp only [PFa, h]

theorem PFa_eq_25 (n : ℕ) (h : n % 40 = 25) : PFa n = pfa25 n := by
  simp only [PFa, h]

theorem PFa_eq_26 (n : ℕ) (h : n % 40 = 26) : PFa n = pfa26 n := by
  simp only [PFa, h]

theorem PFa_eq_27 (n : ℕ) (h : n % 40 = 27) : PFa n = pfa27 n := by
  simp only [PFa, h]

theorem PFa_eq_28 (n : ℕ) (h : n % 40 = 28) : PFa n = pfa28 n := by
  simp only [PFa, h]

theorem PFa_eq_29 (n : ℕ) (h : n % 40 = 29) : PFa n = pfa29 n := by
  simp only [PFa, h]

theorem PFa_eq_30 (n : ℕ) (h : n % 40 = 30) : PFa n = pfa30 n := by
  simp only [PFa, h]

theorem PFa_eq_31 (n : ℕ) (h : n % 40 = 31) : PFa n = pfa31 n := by
  simp only [PFa, h]

theorem PFa_eq_32 (n : ℕ) (h : n % 40 = 32) : PFa n = pfa32 n := by
  simp only [PFa, h]

theorem PFa_eq_33 (n : ℕ) (h : n % 40 = 33) : PFa n = pfa33 n := by
  simp only [PFa, h]

theorem PFa_eq_34 (n : ℕ) (h : n % 40 = 34) : PFa n = pfa34 n := by
  simp only [PFa, h]

theorem PFa_eq_35 (n : ℕ) (h : n % 40 = 35) : PFa n = pfa35 n := by
  simp only [PFa, h]

theorem PFa_eq_36 (n : ℕ) (h : n % 40 = 36) : PFa n = pfa36 n := by
  simp only [PFa, h]

theorem PFa_eq_37 (n : ℕ) (h : n % 40 = 37) : PFa n = pfa37 n := by
  simp only [PFa, h]

theorem PFa_eq_38 (n : ℕ) (h : n % 40 = 38) : PFa n = pfa38 n := by
  simp only [PFa, h]

theorem PFa_eq_39 (n : ℕ) (h : n % 40 = 39) : PFa n = pfa39 n := by
  simp only [PFa, h]

theorem PFb_eq_0 (n : ℕ) (h : n % 40 = 0) : PFb n = pfb0 n := by
  simp only [PFb, h]

theorem PFb_eq_1 (n : ℕ) (h : n % 40 = 1) : PFb n = pfb1 n := by
  simp only [PFb, h]

theorem PFb_eq_2 (n : ℕ) (h : n % 40 = 2) : PFb n = pfb2 n := by
  simp only [PFb, h]

theorem PFb_eq_3 (n : ℕ) (h : n % 40 = 3) : PFb n = pfb3 n := by
  simp only [PFb, h]

theorem PFb_eq_4 (n : ℕ) (h : n % 40 = 4) : PFb n = pfb4 n := by
  simp only [PFb, h]

theorem PFb_eq_5 (n : ℕ) (h : n % 40 = 5) : PFb n = pfb5 n := by
  simp only [PFb, h]

theorem PFb_eq_6 (n : ℕ) (h : n % 40 = 6) : PFb n = pfb6 n := by
  simp only [PFb, h]

theorem PFb_eq_7 (n : ℕ) (h : n % 40 = 7) : PFb n = pfb7 n := by
  simp only [PFb, h]

theorem PFb_eq_8 (n : ℕ) (h : n % 40 = 8) : PFb n = pfb8 n := by
  simp only [PFb, h]

theorem PFb_eq_9 (n : ℕ) (h : n % 40 = 9) : PFb n = pfb9 n := by
  simp only [PFb, h]

theorem PFb_eq_10 (n : ℕ) (h : n % 40 = 10) : PFb n = pfb10 n := by
  simp only [PFb, h]

theorem PFb_eq_11 (n : ℕ) (h : n % 40 = 11) : PFb n = pfb11 n := by
  simp only [PFb, h]

theorem PFb_eq_12 (n : ℕ) (h : n % 40 = 12) : PFb n = pfb12 n := by
  simp only [PFb, h]

theorem PFb_eq_13 (n : ℕ) (h : n % 40 = 13) : PFb n = pfb13 n := by
  simp only [PFb, h]

theorem PFb_eq_14 (n : ℕ) (h : n % 40 = 14) : PFb n = pfb14 n := by
  simp only [PFb, h]

theorem PFb_eq_15 (n : ℕ) (h : n % 40 = 15) : PFb n = pfb15 n := by
  simp only [PFb, h]

theorem PFb_eq_16 (n : ℕ) (h : n % 40 = 16) : PFb n = pfb16 n := by
  simp only [PFb, h]

theorem PFb_eq_17 (n : ℕ) (h : n % 40 = 17) : PFb n = pfb17 n := by
  simp only [PFb, h]

theorem PFb_eq_18 (n : ℕ) (h : n % 40 = 18) : PFb n = pfb18 n := by
  simp only [PFb, h]

theorem PFb_eq_19 (n : ℕ) (h : n % 40 = 19) : PFb n = pfb19 n := by
  simp only [PFb, h]

theorem PFb_eq_20 (n : ℕ) (h : n % 40 = 20) : PFb n = pfb20 n := by
  simp only [PFb, h]

theorem PFb_eq_21 (n : ℕ) (h : n % 40 = 21) : PFb n = pfb21 n := by
  simp only [PFb, h]

theorem PFb_eq_22 (n : ℕ) (h : n % 40 = 22) : PFb n = pfb22 n := by
  simp only [PFb, h]

theorem PFb_eq_23 (n : ℕ) (h : n % 40 = 23) : PFb n = pfb23 n := by
  simp only [PFb, h]

theorem PFb_eq_24 (n : ℕ) (h : n % 40 = 24) : PFb n = pfb24 n := by
  simp only [PFb, h]

theorem PFb_eq_25 (n : ℕ) (h : n % 40 = 25) : PFb n = pfb25 n := by
  simp only [PFb, h]

theorem PFb_eq_26 (n : ℕ) (h : n % 40 = 26) : PFb n = pfb26 n := by
  simp only [PFb, h]

theorem PFb_eq_27 (n : ℕ) (h : n % 40 = 27) : PFb n = pfb27 n := by
  simp only [PFb, h]

theorem PFb_eq_28 (n : ℕ) (h : n % 40 = 28) : PFb n = pfb28 n := by
  simp only [PFb, h]

theorem PFb_eq_29 (n : ℕ) (h : n % 40 = 29) : PFb n = pfb29 n := by
  simp only [PFb, h]

theorem PFb_eq_30 (n : ℕ) (h : n % 40 = 30) : PFb n = pfb30 n := by
  simp only [PFb, h]

theorem PFb_eq_31 (n : ℕ) (h : n % 40 = 31) : PFb n = pfb31 n := by
  simp only [PFb, h]

theorem PFb_eq_32 (n : ℕ) (h : n % 40 = 32) : PFb n = pfb32 n := by
  simp only [PFb, h]

theorem PFb_eq_33 (n : ℕ) (h : n % 40 = 33) : PFb n = pfb33 n := by
  simp only [PFb, h]

theorem PFb_eq_34 (n : ℕ) (h : n % 40 = 34) : PFb n = pfb34 n := by
  simp only [PFb, h]

theorem PFb_eq_35 (n : ℕ) (h : n % 40 = 35) : PFb n = pfb35 n := by
  simp only [PFb, h]

theorem PFb_eq_36 (n : ℕ) (h : n % 40 = 36) : PFb n = pfb36 n := by
  simp only [PFb, h]

theorem PFb_eq_37 (n : ℕ) (h : n % 40 = 37) : PFb n = pfb37 n := by
  simp only [PFb, h]

theorem PFb_eq_38 (n : ℕ) (h : n % 40 = 38) : PFb n = pfb38 n := by
  simp only [PFb, h]

theorem PFb_eq_39 (n : ℕ) (h : n % 40 = 39) : PFb n = pfb39 n := by
  simp only [PFb, h]

end FrobK4
