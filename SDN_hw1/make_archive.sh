#!/bin/bash

UNIFILE=.uni.txt

[ -f ${UNIFILE} ] || (echo Please enter your UNI and press Enter ; read uni_string; (echo $uni_string > $UNIFILE))

tar -jcvf sdn-hw1-`cat $UNIFILE`.bz2 src
