#!/usr/bin/env sh

autoheader
aclocal
automake --add-missing --copy
autoconf

