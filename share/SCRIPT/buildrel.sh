#!/usr/bin/env sh

######
#
# HX-2018-03-17:
# Created based on a version of
# Brandon Barker
# <brandon dot barker at cornell dot edu>
#
# The following packages are built by the script:
# ATS-Postiats, ATS-Postiats-contrib, and ATS-include
#
######
#
# HX-2018-03-18:
# Here is a typical use of this script (for versions 0.3.10+ of ATS only);
# the first argument to the script is the release to be built:
#
# cd /tmp
# sh ${PATSHOME}/share/SCRIPT/buildRelease.sh 0.3.10
# <
# Upload the following three built packages
# /tmp/ATS-Postiats/doc/DISTRIB/ATS2-Postiats-x.y.z.tgz
# /tmp/ATS-Postiats/doc/DISTRIB/ATS2-Postiats-contrib-x.y.z.tgz
# /tmp/ATS-Postiats/doc/DISTRIB/ATS2-Postiats-include-x.y.z.tgz
# >
# rm -rf /tmp/ATS-Postiats
# rm -rf /tmp/ATS-Postiats-contrib
#
######

# PWD=$(pwd)

######


GIT=$(which git)
if [ -x "$GIT" ] ; 
then echo "$GIT found.";
else echo "$GIT not found." exit 1;
fi

######

ATSCC=$(which atscc)
if [ -x "$ATSCC" ] ; 
then echo "$ATSCC found.";
else echo "$ATSCC not found." exit 1;
fi

######

export PATSHOME=${PWD}/ATS-Postiats
export PATSCONTRIB=${PWD}/ATS-Postiats-contrib

######

$GIT clone \
     https://github.com/sparverius/ATS-Postiats.git \
     # https://github.com/githwxi/ATS-Postiats.git \
    || (cd ATS-Postiats && $GIT pull origin master)

######

$GIT clone \
     https://github.com/githwxi/ATS-Postiats-contrib.git \
    || (cd ATS-Postiats-contrib && $GIT pull origin master)

######

PATSVERSION=$1

# check_version() {
if [ -z "$PATSVERSION" ] ; then
    PATSVERSION=$(cat "${PATSHOME}/VERSION")
fi

AC_INIT_VERSION="AC_INIT([ATS2/Postiats], [${PATSVERSION}], [gmpostiats@gmail.com])"
if grep -Fxq "$AC_INIT_VERSION" "${PATSHOME}/doc/DISTRIB/ATS-Postiats/configure.ac"
then
    echo "Correct version found in configure.ac"
else
    echo "Failure: Didn't find correct Postiats version for AC_INIT in configure.ac!"
    exit -1;
fi

######

checkout_build() {
    (cd "$PATSHOME" && \
	 $GIT checkout -b "tags/v${PATSVERSION}")
}

build_release_intmin() {
    (cd "$PATSHOME" && \
	 make -f Makefile_devl KND=intknd && \
	 make -C src -f Makefile CBOOTmin  && \
	 (cp ./bin/*_env.sh.in ./doc/DISTRIB/ATS-Postiats/bin/.) && \
	 (cd ./doc/DISTRIB/ATS-Postiats && \
	      sh ./autogen.sh && ./configure) && \
	 make -C src/CBOOT/libc -f Makefile && \
	 make -C src/CBOOT/libats -f Makefile && \
	 make -C src/CBOOT/prelude -f Makefile && \
	 make -C doc/DISTRIB -f Makefile atspackaging && \
	 make -C doc/DISTRIB -f Makefile atspacktarzvcf_intmin && \
	)
}
######
build_release_gmp() {
    ( cd "$PATSHOME" && \
	  make -f Makefile_devl KND=gmpknd && \
	  make -C src -f Makefile CBOOT  && \
	  (cp ./bin/*_env.sh.in ./doc/DISTRIB/ATS-Postiats/bin/.) && \
	  (cd ./doc/DISTRIB/ATS-Postiats && \
	       sh ./autogen.sh && ./configure) && \
	  make -C src/CBOOT/libc -f Makefile && \
	  make -C src/CBOOT/libats -f Makefile && \
	  make -C src/CBOOT/prelude -f Makefile && \
	  make -C doc/DISTRIB -f Makefile atspackaging && \
	  make -C doc/DISTRIB -f Makefile atspacktarzvcf && \
	  make -C doc/DISTRIB -f Makefile atscontribing && \
	  make -C doc/DISTRIB -f Makefile atscontribtarzvcf && \
	  make -C doc/DISTRIB -f Makefile_inclats tarzvcf \
	)
}


_usage() {
    local usage="usage: $(basename "$0") [VERSION] [KIND]"
    printf "$usage\n\n"
    printf "VERSION"
    printf "x.x.x         release version\n"
    printf "INTEGERKIND"
    printf "intknd        ats-intmin\n"
    printf "gmpknd        full ats install\n"
    printf "all           to build both"
}



main() {
    
    checkout_build

    case $2 in
	gmpknd) build_release_gmp ;;
	intknd) build_release_intmin ;;
	all) build_release_intmin && \
		   build_release_gmp ;;
	*) _usage ;; 
    esac

    ls -alh "$PATSHOME/doc/DISTRIB/"ATS2-*.tgz

}

main "$1" "$2"

###### end of [buildRelease.sh] ######
