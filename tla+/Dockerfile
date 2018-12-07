FROM ubuntu:16.04

RUN apt-get update && \
    apt-get install -y openjdk-8-jdk && \
    apt-get install -y ant && \
    apt-get install -y wget unzip && \
    apt-get clean;

# Fix certificate issues
RUN apt-get update && \
    apt-get install ca-certificates-java && \
    apt-get clean && \
    update-ca-certificates -f;

# Setup JAVA_HOME -- useful for docker commandline
ENV JAVA_HOME /usr/lib/jvm/java-8-openjdk-amd64
RUN export JAVA_HOME

ENV JARS $JAVA_HOME/jars

RUN mkdir -p $JARS && \
   wget -P $JARS \
   https://github.com/tlaplus/tlaplus/releases/download/v1.5.7/tla.zip && \
   cd $JARS && \
   unzip tla.zip

ENV CLASSPATH $JARS/tla
RUN export CLASSPATH
