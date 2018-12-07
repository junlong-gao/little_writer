- docker build -it tla_plus .
- run the tla toolkit

   docker run -w $(pwd) -v $(pwd):$(pwd) -it tla_plus java tla2sany.SANY "$@"
   docker run -w $(pwd) -v $(pwd):$(pwd) -it tla_plus java tlc2.TLC "$@"
   docker run -w $(pwd) -v $(pwd):$(pwd) -it tla_plus java tla2tex.TLA "$@"

   cd monitors
   docker run -w $(pwd) -v $(pwd):$(pwd) -it tla_plus make parse
