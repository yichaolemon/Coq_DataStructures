Various verified data structures in Coq and proofs for their properties. 

### Setup Using Docker

1. Install [Docker](https://www.docker.com)
2. Allow Docker to present GUI windows. These instructions are not cross-platform. For mac: follow [these instructions](https://medium.com/@mreichelt/how-to-show-x11-windows-within-docker-on-mac-50759f4b65cb).
    1. Install [XQuartz](https://www.xquartz.org/), and reboot computer to complete installation.
    2. Enable "Allow connections from network clients" in XQuartz preferences, and restart XQuartz to finalize setting.
    3. Run `xhost +` to allow all incoming connections.
3. Open a shell, and `cd` to the root of this repo.
4. Run `./coqshell` to open a shell into a Docker container running coq and coqide.
